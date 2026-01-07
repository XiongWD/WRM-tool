# -*- coding: utf-8 -*-
"""
TrajectoryManager - 轨迹复用管理器 (v15.5)
============================================
功能：
  - SQLite WAL 模式持久化轨迹库
  - 优胜劣汰进化算法（胜率排序）
  - 全链路统计与批量持久化
  - 线程安全的数据库操作

作者: AI Assistant
版本: 15.5
更新: 2026-01-04
"""

import sqlite3
import json
import hashlib
import threading
import time
import random
from typing import Optional, List, Dict
from pathlib import Path


class TrajectoryManager:
    """
    轨迹复用管理器
    
    核心特性：
    1. WAL 模式：支持高并发读写，避免 database is locked
    2. 优胜劣汰：胜率最低的轨迹优先被替换
    3. 保护机制：新轨迹初始 success_count=1，防止婴儿夭折
    4. 批量持久化：减少 IO 竞争，提升性能
    """
    
    def __init__(self, db_path: str = "assets/tracks.db"):
        """
        初始化轨迹管理器
        
        参数:
            db_path (str): 数据库文件路径
        """
        self.db_path = db_path
        self.lock = threading.Lock()  # 线程安全锁
        self._ensure_db_path()
        self._init_db()
        
    def _ensure_db_path(self):
        """确保数据库目录存在"""
        db_dir = Path(self.db_path).parent
        if not db_dir.exists():
            db_dir.mkdir(parents=True, exist_ok=True)
    
    def _init_db(self):
        """初始化数据库表结构"""
        with sqlite3.connect(self.db_path, timeout=20) as conn:
            cursor = conn.cursor()
            
            # 🔥 WAL 模式：支持读写并发
            cursor.execute("PRAGMA journal_mode=WAL;")
            cursor.execute("PRAGMA synchronous=NORMAL;")  # 🔥 性能优化
            cursor.execute("PRAGMA foreign_keys=ON;")
            
            # 表1：轨迹库
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS trajectory_library (
                    distance INTEGER NOT NULL,
                    track_data TEXT NOT NULL,
                    track_hash TEXT UNIQUE NOT NULL,
                    success_count INTEGER DEFAULT 1,  -- 🔥 保护机制：初始为1
                    failure_count INTEGER DEFAULT 0,
                    last_used INTEGER DEFAULT (strftime('%s', 'now')),
                    PRIMARY KEY (track_hash)
                )
            """)
            
            # 表2：全局统计
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS global_stats (
                    key TEXT PRIMARY KEY,
                    value INTEGER DEFAULT 0
                )
            """)
            
            # 创建索引
            cursor.execute("""
                CREATE INDEX IF NOT EXISTS idx_distance 
                ON trajectory_library(distance)
            """)
            
            conn.commit()
    
    def get_track(self, distance: int, limit: int = 10) -> Optional[List]:
        """
        获取指定距离的轨迹（优胜劣汰算法）
        
        算法逻辑：
        1. 查询该距离下所有轨迹
        2. 过滤失败过多（failure > 5 且 success < 2）
        3. 按胜率排序：success / (success + failure + 1)
        4. 返回胜率最高的轨迹
        
        参数:
            distance (int): 滑块距离
            limit (int): 轨迹容量上限（用于判断是否需要替换）
            
        返回:
            Optional[List] - 轨迹列表或None
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                # 查询该距离下的所有轨迹
                cursor.execute("""
                    SELECT track_data, success_count, failure_count 
                    FROM trajectory_library 
                    WHERE distance = ?
                """, (distance,))
                
                tracks = cursor.fetchall()
                
                if not tracks:
                    conn.close()
                    return None
                
                # 🔥 优胜劣汰：过滤失败过多的轨迹
                valid_tracks = []
                for track_data, s_cnt, f_cnt in tracks:
                    # 剔除失败过多且成功率低的轨迹
                    if not (f_cnt > 5 and s_cnt < 2):
                        valid_tracks.append({
                            'data': json.loads(track_data),
                            'success': s_cnt,
                            'failure': f_cnt,
                            'win_rate': s_cnt / (s_cnt + f_cnt + 1)
                        })
                
                if not valid_tracks:
                    conn.close()
                    return None
                
                # 🔥 按胜率排序（降序）
                valid_tracks.sort(key=lambda x: x['win_rate'], reverse=True)
                
                # 返回胜率最高的轨迹
                best_track = valid_tracks[0]['data']
                conn.close()
                
                return best_track
            
            except Exception as e:
                print(f"❌ get_track 异常: {e}")
                return None
    
    def save_track(self, distance: int, track: List, limit: int = 10) -> bool:
        """
        保存轨迹（包含优胜劣汰替换逻辑）
        
        替换逻辑：
        1. 计算轨迹的 track_hash（去重核心）
        2. 如果已存在，直接更新 last_used
        3. 如果不存在：
           a. 检查该距离的轨迹数量是否达到上限
           b. 如果达到上限，查找胜率最低的轨迹并替换
           c. 否则直接插入
        
        参数:
            distance (int): 滑块距离
            track (List): 轨迹数据
            limit (int): 轨迹容量上限
            
        返回:
            bool - 是否保存成功
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                # 计算 track_hash
                track_json = json.dumps(track)
                track_hash = hashlib.md5(track_json.encode('utf-8')).hexdigest()
                
                # 检查是否已存在
                cursor.execute("""
                    SELECT track_hash FROM trajectory_library 
                    WHERE track_hash = ?
                """, (track_hash,))
                
                exists = cursor.fetchone()
                
                if exists:
                    # 已存在，仅更新 last_used
                    cursor.execute("""
                        UPDATE trajectory_library 
                        SET last_used = strftime('%s', 'now')
                        WHERE track_hash = ?
                    """, (track_hash,))
                else:
                    # 检查该距离的轨迹数量
                    cursor.execute("""
                        SELECT COUNT(*) FROM trajectory_library 
                        WHERE distance = ?
                    """, (distance,))
                    
                    count = cursor.fetchone()[0]
                    
                    can_insert = True ## 默认可以插入
                    if count >= limit:
                        # 🔥 优胜劣汰：查找胜率最低的轨迹
                        # failure_count>=1 起码有一次失败把(自己加的逻辑)此处会造成轨迹保存大于limit的问题
                        cursor.execute("""
                            SELECT track_hash FROM trajectory_library 
                            WHERE distance = ?
                            AND failure_count >= 1
                            ORDER BY (success_count * 1.0 / (success_count + failure_count + 1)) ASC, 
                                     last_used ASC 
                            LIMIT 1
                        """, (distance,))
                        
                        worst_hash = cursor.fetchone()
                        
                        if worst_hash:
                            # 删除胜率最低的轨迹
                            cursor.execute("""
                                DELETE FROM trajectory_library 
                                WHERE track_hash = ?
                            """, (worst_hash[0],))
                        else:
                            # 无法找到可替换的轨迹，放弃插入
                            can_insert = False
                    
                    # 🔥 插入新轨迹（保护机制：success_count=1）
                    if can_insert:
                        cursor.execute("""
                            INSERT INTO trajectory_library 
                            (distance, track_data, track_hash, success_count, failure_count, last_used)
                            VALUES (?, ?, ?, 1, 0, strftime('%s', 'now'))
                        """, (distance, track_json, track_hash))
                
                conn.commit()
                conn.close()
                return True
            
            except Exception as e:
                print(f"❌ save_track 异常: {e}")
                return False
    
    def update_usage_stats(self, track_hash: str, success: bool) -> bool:
        """
        更新轨迹使用统计（成功/失败）
        
        参数:
            track_hash (str): 轨迹哈希
            success (bool): 是否成功
            
        返回:
            bool - 是否更新成功
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                if success:
                    cursor.execute("""
                        UPDATE trajectory_library 
                        SET success_count = success_count + 1,
                            last_used = strftime('%s', 'now')
                        WHERE track_hash = ?
                    """, (track_hash,))
                else:
                    cursor.execute("""
                        UPDATE trajectory_library 
                        SET failure_count = failure_count + 1,
                            last_used = strftime('%s', 'now')
                        WHERE track_hash = ?
                    """, (track_hash,))
                
                conn.commit()
                conn.close()
                return True
            
            except Exception as e:
                print(f"❌ update_usage_stats 异常: {e}")
                return False
    
    def get_track_hash(self, track: List) -> str:
        """
        计算轨迹的哈希值
        
        参数:
            track (List): 轨迹数据
            
        返回:
            str - MD5 哈希值
        """
        track_json = json.dumps(track)
        return hashlib.md5(track_json.encode('utf-8')).hexdigest()
    
    def batch_update_global_stats(self, stats: Dict[str, int]) -> bool:
        """
        批量更新全局统计（性能优化）
        
        参数:
            stats (Dict): 统计字典 {"slider_total": 100, "slider_pass": 80, ...}
            
        返回:
            bool - 是否更新成功
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                for key, value in stats.items():
                    cursor.execute("""
                        INSERT INTO global_stats (key, value)
                        VALUES (?, ?)
                        ON CONFLICT(key) DO UPDATE SET value = value + ?
                    """, (key, value, value))
                
                conn.commit()
                conn.close()
                return True
            
            except Exception as e:
                print(f"❌ batch_update_global_stats 异常: {e}")
                return False
    
    def get_global_stats(self) -> Dict[str, int]:
        """
        获取全局统计
        
        返回:
            Dict[str, int] - 统计字典
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                cursor.execute("SELECT key, value FROM global_stats")
                rows = cursor.fetchall()
                
                stats = {row[0]: row[1] for row in rows}
                conn.close()
                
                return stats
            
            except Exception as e:
                print(f"❌ get_global_stats 异常: {e}")
                return {}
    
    def get_all_tracks_summary(self) -> List[Dict]:
        """
        获取所有轨迹的摘要（用于管理界面）
        
        返回:
            List[Dict] - 轨迹摘要列表
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                cursor.execute("""
                    SELECT 
                        distance,
                        COUNT(*) as count,
                        SUM(success_count) as total_success,
                        SUM(failure_count) as total_failure
                    FROM trajectory_library
                    GROUP BY distance
                    ORDER BY distance
                """)
                
                rows = cursor.fetchall()
                conn.close()
                
                summary = []
                for distance, count, total_success, total_failure in rows:
                    # 🔥 状态判断逻辑
                    if total_success >= 5 and total_failure == 0:
                        status = "优质"
                    elif total_success >= total_failure:
                        status = "普通"
                    else:
                        status = "待观察"
                    
                    summary.append({
                        'distance': distance,
                        'count': count,
                        'total_success': total_success,
                        'total_failure': total_failure,
                        'status': status
                    })
                
                return summary
            
            except Exception as e:
                print(f"❌ get_all_tracks_summary 异常: {e}")
                return []
    
    def clear_all_tracks(self) -> bool:
        """
        清空所有轨迹
        
        返回:
            bool - 是否清空成功
        """
        with self.lock:
            try:
                conn = sqlite3.connect(self.db_path, timeout=20)
                cursor = conn.cursor()
                
                cursor.execute("DELETE FROM trajectory_library")
                conn.commit()
                conn.close()
                return True
            
            except Exception as e:
                print(f"❌ clear_all_tracks 异常: {e}")
                return False
