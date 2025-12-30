# -*- coding: utf-8 -*-
"""
缓存管理器 - SQLite 分片存储 + LRU 内存缓存
"""

import os
import sqlite3
import threading
import time
import atexit
from typing import Optional, Dict, List
from pathlib import Path

import logging
logger = logging.getLogger(__name__)


class CacheManager:
    """SQLite 分片存储 + LRU 内存缓存"""
    
    SHARD_COUNT = 10
    DB_DIR = "db"
    LRU_MAXSIZE = 10000
    
    def __init__(self):
        self.db_dir = Path(self.DB_DIR)
        self.db_dir.mkdir(exist_ok=True)
        
        self.connections: Dict[int, sqlite3.Connection] = {}
        self.lock = threading.Lock()
        
        self._lru_cache = {}
        self._lru_lock = threading.Lock()
        
        self._init_databases()
        atexit.register(self.cleanup)
        
        logger.info(f"✅ 缓存管理器初始化完成 ({self.SHARD_COUNT}个分片)")
    
    def _init_databases(self):
        """初始化所有分片数据库"""
        for shard_id in range(self.SHARD_COUNT):
            db_path = self.db_dir / f"cache_{shard_id}.db"
            
            try:
                conn = sqlite3.connect(str(db_path), check_same_thread=False)
                
                # 启用 WAL 模式
                conn.execute("PRAGMA journal_mode=WAL")
                
                # 创建表
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS codes (
                        code TEXT PRIMARY KEY,
                        update_time INTEGER NOT NULL,
                        status TEXT DEFAULT '已使用'
                    )
                """)
                
                # 创建索引
                conn.execute("CREATE INDEX IF NOT EXISTS idx_code ON codes(code)")
                conn.execute("CREATE INDEX IF NOT EXISTS idx_time ON codes(update_time)")
                
                # 优化设置
                conn.execute("PRAGMA synchronous=NORMAL")
                conn.execute("PRAGMA cache_size=10000")
                conn.execute("PRAGMA temp_store=MEMORY")
                
                conn.commit()
                self.connections[shard_id] = conn
                
                logger.debug(f"  ✓ cache_{shard_id}.db 初始化完成")
                
            except sqlite3.Error as e:
                logger.error(f"❌ 数据库初始化失败 (shard_{shard_id}): {e}")
                raise
    
    def _get_shard_id(self, code: str) -> int:
        """获取分片ID"""
        clean_code = code.strip()
        
        if clean_code.isdigit():
            return int(clean_code) % self.SHARD_COUNT
        else:
            return hash(clean_code) % self.SHARD_COUNT
    
    def _get_connection(self, shard_id: int) -> sqlite3.Connection:
        """获取数据库连接"""
        with self.lock:
            if shard_id not in self.connections:
                raise ValueError(f"❌ 无效的分片 ID: {shard_id}")
            return self.connections[shard_id]
    
    def get(self, code: str) -> Optional[str]:
        """查询缓存"""
        clean_code = code.strip()
        
        # 检查 LRU 内存缓存
        with self._lru_lock:
            if clean_code in self._lru_cache:
                logger.debug(f"  💾 内存命中: {clean_code[:10]}...")
                return "已使用"
        
        # 检查 SQLite 缓存
        shard_id = self._get_shard_id(clean_code)
        conn = self._get_connection(shard_id)
        
        try:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT status FROM codes WHERE code = ? LIMIT 1",
                (clean_code,)
            )
            result = cursor.fetchone()
            
            if result:
                status = result[0]
                logger.debug(f"  🗄️ 数据库命中: {clean_code[:10]}...")
                
                # 更新 LRU 缓存
                with self._lru_lock:
                    if len(self._lru_cache) < self.LRU_MAXSIZE:
                        self._lru_cache[clean_code] = int(time.time())
                
                return status
            else:
                return None
                
        except sqlite3.Error as e:
            logger.error(f"❌ 查询缓存失败 {clean_code}: {e}")
            return None
    
    def set(self, code: str, status: str = "已使用") -> bool:
        """写入缓存"""
        clean_code = code.strip()
        
        # 检查 LRU 缓存
        with self._lru_lock:
            if clean_code in self._lru_cache:
                logger.debug(f"  ⏭️ 跳过已缓存: {clean_code[:10]}...")
                return False
        
        # 数据库插入
        shard_id = self._get_shard_id(clean_code)
        conn = self._get_connection(shard_id)
        
        try:
            cursor = conn.cursor()
            cursor.execute(
                """
                INSERT OR IGNORE INTO codes (code, update_time, status)
                VALUES (?, ?, ?)
                """,
                (clean_code, int(time.time()), status)
            )
            
            conn.commit()
            inserted = cursor.rowcount > 0
            
            if inserted:
                # 更新 LRU 缓存
                with self._lru_lock:
                    if len(self._lru_cache) < self.LRU_MAXSIZE:
                        self._lru_cache[clean_code] = int(time.time())
                
                logger.debug(f"  ✓ 写入缓存: {clean_code[:10]}...")
                return True
            else:
                logger.debug(f"  ⏭️ 已存在: {clean_code[:10]}...")
                return False
                
        except sqlite3.Error as e:
            logger.error(f"❌ 写入缓存失败 {clean_code}: {e}")
            return False
    
    def batch_set(self, codes: List[str], status: str = "已使用") -> Dict[str, int]:
        """批量写入缓存"""
        stats = {"new": 0, "skip": 0, "error": 0}
        
        for code in codes:
            try:
                if self.set(code, status):
                    stats["new"] += 1
                else:
                    stats["skip"] += 1
            except Exception as e:
                logger.error(f"❌ 批量导入失败 {code[:10]}...: {e}")
                stats["error"] += 1
        
        return stats
    
    def get_stats(self) -> Dict:
        """获取统计信息"""
        total = 0
        try:
            for shard_id in range(self.SHARD_COUNT):
                conn = self._get_connection(shard_id)
                cursor = conn.cursor()
                cursor.execute("SELECT COUNT(*) FROM codes")
                total += cursor.fetchone()[0]
        except sqlite3.Error as e:
            logger.error(f"❌ 统计失败: {e}")
        
        return {
            "total_cached": total,
            "lru_cached": len(self._lru_cache),
            "lru_maxsize": self.LRU_MAXSIZE,
            "shard_count": self.SHARD_COUNT
        }
    
    def clear(self) -> int:
        """清空所有缓存"""
        total_deleted = 0
        
        for shard_id in range(self.SHARD_COUNT):
            try:
                conn = self._get_connection(shard_id)
                cursor = conn.cursor()
                cursor.execute("DELETE FROM codes")
                conn.commit()
                total_deleted += cursor.rowcount
            except sqlite3.Error as e:
                logger.error(f"❌ 清空缓存失败 (shard_{shard_id}): {e}")
        
        # 清空 LRU 缓存
        with self._lru_lock:
            self._lru_cache.clear()
        
        logger.info(f"🗑️ 已清空 {total_deleted} 条缓存记录")
        return total_deleted
    
    def export(self, output_path: str) -> int:
        """导出缓存"""
        exported_count = 0
        
        try:
            with open(output_path, 'w', encoding='utf-8') as f:
                for shard_id in range(self.SHARD_COUNT):
                    conn = self._get_connection(shard_id)
                    cursor = conn.cursor()
                    cursor.execute("SELECT code FROM codes ORDER BY update_time DESC")
                    
                    for row in cursor.fetchall():
                        f.write(f"{row[0]}\n")
                        exported_count += 1
            
            logger.info(f"💾 导出成功: {output_path} ({exported_count} 条)")
            return exported_count
            
        except IOError as e:
            logger.error(f"❌ 导出失败: {e}")
            return 0
    
    def cleanup(self):
        """清理资源"""
        logger.info("🛑 正在清理缓存连接...")
        
        try:
            for shard_id, conn in self.connections.items():
                conn.close()
                logger.debug(f"  ✓ cache_{shard_id}.db 已关闭")
            
            self.connections.clear()
            logger.info("✅ 缓存管理器已清理")
        except Exception as e:
            logger.error(f"❌ 清理失败: {e}")


# 全局实例
CACHE_MANAGER: Optional[CacheManager] = None


def init_cache_manager():
    """初始化全局缓存管理器"""
    global CACHE_MANAGER
    if CACHE_MANAGER is None:
        CACHE_MANAGER = CacheManager()
    return CACHE_MANAGER
