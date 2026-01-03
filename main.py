# -*- coding: utf-8 -*-
"""
Walmart礼品卡查询工具 v13.0 - 优化版
========================================
功能：
  - 批量导入卡密数据
  - 支持快代理IP池管理
  - 滑块验证码识别和绕过
  - 并发卡余额查询
  - 结果导出

核心模块：
  1. ConfigManager    - 配置文件管理
  2. GeoLocationServiceSync - IP地理位置查询
  3. EnhancedProxyPool - 代理池（生产-消费-清理）
  4. SmartImporter    - 智能卡密导入器
  5. WalmartWorker    - 核心业务处理线程
  6. WalmartUltraUI   - PySide6图形界面

作者: AI Assistant
版本: 13.0
更新: 2025-11-28
"""

import sys
import os
import json
import time
import random
import math
import base64
import re
import queue
import threading
import logging
import traceback

import numpy as np
import cv2
import pandas as pd
import urllib3
from dataclasses import dataclass
from scipy.special import comb

# 🔥 禁用SSL警告（因为使用代理时可能需要禁用SSL验证）
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
from typing import Optional, List, Dict, Set, Tuple
from datetime import datetime, timezone, timedelta, date
from enum import Enum
from lxml import etree

# 导入缓存管理器
from cache_manager import init_cache_manager, CACHE_MANAGER as _CACHE_MANAGER_MODULE
from concurrent.futures import ThreadPoolExecutor, as_completed

from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
                               QPushButton, QTextEdit, QTableWidget, QTableWidgetItem, QLabel,
                               QFileDialog, QHeaderView, QProgressBar, QGroupBox, QSplitter,
                               QSpinBox, QLineEdit, QCheckBox, QAbstractItemView, QFrame,
                               QGridLayout, QComboBox, QFormLayout, QScrollArea,
                               QStyledItemDelegate, QStyle, QMessageBox, QDialog, QPlainTextEdit)
from PySide6.QtCore import Qt, QThread, Signal, QObject, QTimer
from PySide6.QtGui import QColor, QFont, QBrush, QPen

# 🔥 使用 curl_cffi 的 requests（支持更好的反爬虫和代理）
from curl_cffi import requests
# 导入 curl_cffi 的异常类
from curl_cffi.requests.exceptions import Timeout, ConnectionError

# ========== 日志配置 ==========
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


# ==========================================
# 配置管理 (ConfigManager)
# ==========================================
class ConfigManager:
    """配置文件管理器 - 负责加载和保存应用配置"""
    FILE_PATH = "config.json"

    # 默认配置项
    DEFAULT_CONFIG = {
        "thread_count": 10,         # 最大并发上限 (默认10)
        "thread_ip_ratio": 10,      # 并发系数 (默认10, 即每个IP对应1个线程)
        "min_proxy_to_start": 3,    # 最小启动水位 (默认3, 启动任务所需的最小IP数)
        "proxy_mode": 0,            # 0: 不使用, 1: 快代理
        "secret_id": "",
        "secret_key": "",
        "fetch_num": 10,
        "min_available": 10,
        "expire_threshold": 30,
        "clean_interval": 30,
        "fetch_interval": 10,
        "retry_threshold": 3,       # 重试阈值
        "max_retry_rounds": 3       # 最大重试轮次
    }

    @staticmethod
    def load():
        """
        加载配置文件
        
        返回: Dict - 配置字典（失败时返回默认配置）
        
        静默迁移逻辑: 支持从旧版配置迁移到新版
        """
        if os.path.exists(ConfigManager.FILE_PATH):
            try:
                with open(ConfigManager.FILE_PATH, 'r', encoding='utf-8') as f:
                    cfg = json.load(f)
                    
                    # 🔥 静默迁移: max_thread_limit -> thread_count
                    if 'max_thread_limit' in cfg:
                        cfg['thread_count'] = cfg.pop('max_thread_limit')
                        logger.info(f"🔄 配置迁移: max_thread_limit -> thread_count")
                    
                    logger.info(f"✅ 配置文件加载成功")
                    return {**ConfigManager.DEFAULT_CONFIG, **cfg}
            except json.JSONDecodeError as e:
                logger.error(f"❌ 配置文件JSON格式错误: {e}")
                return ConfigManager.DEFAULT_CONFIG
            except Exception as e:
                logger.error(f"❌ 配置文件读取异常: {e}")
                return ConfigManager.DEFAULT_CONFIG
        else:
            logger.info(f"⚠️ 配置文件不存在，使用默认配置")
            return ConfigManager.DEFAULT_CONFIG

    @staticmethod
    def save(config):
        """
        保存配置到文件
        
        参数:
            config (Dict): 要保存的配置字典
            
        返回: bool - 保存是否成功
        """
        try:
            with open(ConfigManager.FILE_PATH, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=4, ensure_ascii=False)
            logger.info(f"✅ 配置文件保存成功")
            return True
        except IOError as e:
            logger.error(f"❌ 配置文件写入失败: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ 配置保存异常: {e}")
            return False


# ==========================================
# 1. 日志与信号
# ==========================================
class LogSignal(QObject):
    message = Signal(str, str)
    # 额外信号：代理池提取失败
    proxy_error = Signal(str)


GLOBAL_LOG = LogSignal()


def log_proxy(msg, level="info"):
    GLOBAL_LOG.message.emit(msg, level)


# ==========================================
# 2. 地理位置服务
# ==========================================
@dataclass
class GeoLocation:
    ip: str
    country_code: str
    city: str

    def is_china(self) -> bool:
        return self.country_code.upper() in ['CN', 'CHN', 'CHINA']


class GeoLocationServiceSync:
    def query_ip_location(self, ip: str) -> Optional[GeoLocation]:
        # 简化的查询逻辑，实际使用时可替换为真实API
        try:
            url = f"http://ip-api.com/json/{ip}?fields=status,countryCode,city"
            resp = requests.get(url, timeout=3, impersonate="chrome124")
            if resp.status_code == 200:
                data = resp.json()
                if data.get('status') == 'success':
                    return GeoLocation(ip, data.get('countryCode'), data.get('city'))
        except:
            pass
        return None


GEO_SERVICE = GeoLocationServiceSync()


# ==========================================
# 3. 增强代理池
# ==========================================
@dataclass
class EnhancedProxyInfo:
    ip: str
    port: int
    expire_timestamp: int
    geo: Optional[GeoLocation] = None
    latency: int = 9999
    is_reachable: bool = False  # 🆕 是否可连通

    def is_expired(self, threshold=30):
        return (self.expire_timestamp - int(time.time())) <= threshold

    def get_url(self):
        return f"http://{self.ip}:{self.port}"


class EnhancedProxyPool:
    def __init__(self, config: Dict):
        self.config = config
        self.proxy_queue = queue.Queue(maxsize=100)
        self.available_proxies: List[EnhancedProxyInfo] = []
        self.available_set: Set[str] = set()
        self.is_running = False
        self.lock = threading.Lock()

        # 🔥 增强统计信息
        self.stats = {
            "fetched": 0,
            "used": 0,
            "expired": 0,
            "total_unreachable": 0,  # 🆕 无法访问的数量
            "total_slow": 0,         # 🆕 延迟过高的数量
            "total_rejected": 0      # 🆕 总拒绝数（非国内IP）
        }

    def start(self):
        if self.is_running: return
        
        # 🔥 启动前清理旧数据（确保干净启动）
        with self.lock:
            if self.available_proxies or self.available_set:
                old_count = len(self.available_proxies)
                self.available_proxies.clear()
                self.available_set.clear()
                if old_count > 0:
                    log_proxy(f"⚠️ 检测到旧数据，已清理 {old_count} 个代理", "warning")
        
        self.is_running = True
        threading.Thread(target=self._producer, daemon=True, name="ProxyProducer").start()
        threading.Thread(target=self._consumer, daemon=True, name="ProxyConsumer").start()
        threading.Thread(target=self._cleaner, daemon=True, name="ProxyCleaner").start()
        log_proxy("🚀 代理池服务已启动", "success")

    def stop(self):
        if not self.is_running:
            return
        
        log_proxy("🛑 正在停止代理池...", "warning")
        self.is_running = False
        
        # 清空队列，让消费者线程退出
        try:
            while not self.proxy_queue.empty():
                self.proxy_queue.get_nowait()
        except:
            pass
        
        # 🔥 清空所有代理数据（防止数据残留）
        with self.lock:
            proxy_count = len(self.available_proxies)
            self.available_proxies.clear()
            self.available_set.clear()
            if proxy_count > 0:
                log_proxy(f"🗑️ 已清空 {proxy_count} 个可用代理", "info")
        
        # 🔥 异步等待线程结束（避免阻塞GUI）
        def wait_threads():
            time.sleep(2)
            log_proxy("🛑 代理池所有线程已停止", "warning")
        
        threading.Thread(target=wait_threads, daemon=True).start()
        log_proxy("🛑 代理池已停止（线程正在后台清理）", "warning")

    def get_status(self):
        with self.lock:
            return {
                "running": self.is_running,
                "available": len(self.available_proxies),
                "queue": self.proxy_queue.qsize(),
                "stats": self.stats
            }

    def get_proxy(self):
        """
        获取一个可用代理（单次使用）
        
        会自动过滤掉剩余有效期不足30秒的代理
        """
        # MIN_VALID_TIME = 30  # 最小剩余有效期（秒）
        removed_count = 0
        
        with self.lock:
            while self.available_proxies:
                # 取第一个代理
                p = self.available_proxies.pop(0)
                proxy_key = f"{p.ip}:{p.port}"
                self.available_set.discard(proxy_key)
                
                # 🔥 检查剩余有效期
                remaining_time = p.expire_timestamp - int(time.time())
                
                #if p.is_expired(self.config['expire_threshold']) or remaining_time < MIN_VALID_TIME:
                if p.is_expired(self.config['expire_threshold']):
                    # 剩余时间不足，删除并继续下一个
                    removed_count += 1
                    self.stats['expired'] += 1
                    log_proxy(f"⏱️ 代理即将过期，已跳过: {proxy_key} (剩余{remaining_time}秒", "warning")
                    continue
                
                # 找到符合要求的代理
                self.stats['used'] += 1
                
                geo_info = f"{p.geo.city if p.geo else '未知'}"
                log_proxy(f"🎯 分配代理: {p.ip}:{p.port} - {geo_info} | 🚀 延迟: {p.latency}ms | "
                         f"剩余有效期: {remaining_time}秒 | 池剩余: {len(self.available_proxies)}", "info")
                
                if removed_count > 0:
                    log_proxy(f"🗑️ 本次获取过程中删除了{removed_count}个即将过期的代理", "info")
                
                return p
            
            # 没有符合要求的代理
            if removed_count > 0:
                log_proxy(f"⚠️ 可用代理池已空（删除了{removed_count}个即将过期的代理）", "warning")
            else:
                log_proxy("❌ 没有可用代理！", "error")
        return None

    def _producer(self):
        # 启动时立即获取一批
        time.sleep(1)  # 等待其他线程启动
        self._fetch()
        
        # 🔥 等待第一批代理完成验证，避免立即触发第二次获取
        time.sleep(10)
        
        while self.is_running:
            try:
                with self.lock:
                    available_count = len(self.available_proxies)
                
                # 🔥 考虑队列中的待验证代理，避免重复获取
                queue_size = self.proxy_queue.qsize()
                total_count = available_count + queue_size
                
                if total_count < self.config['min_available']:
                    shortage = self.config['min_available'] - total_count
                    fetch_num = max(shortage, self.config['fetch_num'])
                    
                    log_proxy(f"⚠️ 可用代理不足 (可用:{available_count}, 待验证:{queue_size}, "
                             f"目标:{self.config['min_available']})，开始补充{fetch_num}个...", "warning")
                    self._fetch()
                
                time.sleep(self.config['fetch_interval'])
            except Exception as e:
                log_proxy(f"❌ 生产者线程异常: {e}", "error")
                time.sleep(5)

    def _fetch(self):
        """
        从快代理API提取代理 - 支持重试与超时控制
        
        重试机制:
        - 最大重试次数: 3次
        - 每次重试间隔: 2秒
        - 超时时间: 8秒
        - 只有3次全部失败才触发 proxy_error 信号
        - 单次失败仅记录warning级别日志，不中断程序
        - 重试期间保持 is_running 状态为 True
        """
        url = "https://dps.kdlapi.com/api/getdps"
        params = {
            "secret_id": self.config['secret_id'],
            "signature": self.config['secret_key'],
            "num": self.config['fetch_num'],
            "format": "json", "sep": 1, "f_et": 1
        }
        
        # 🔥 超时控制: 8秒硬超时
        FETCH_TIMEOUT = 8
        
        # 🔥 重试逻辑: 最多3次，每次间隔2秒
        for retry_idx in range(3):
            try:
                # 🔥 保持 is_running 状态，避免UI按钮过早回滚
                if not self.is_running:
                    log_proxy("⚠️ 代理池已停止，取消提取", "warning")
                    return
                
                resp = requests.get(url, params=params, timeout=FETCH_TIMEOUT, impersonate="chrome124")
                data = resp.json()
                
                if data.get('code') == 0:
                    # 如果返回成功，但没有代理条目也视为失败
                    if not data['data'].get('proxy_list'):
                        log_proxy(f"⚠️ 代理提取返回空列表 (第{retry_idx+1}次尝试)", "warning")
                        if retry_idx < 2:  # 还有重试机会
                            time.sleep(2)  # 🔥 退避策略: 2秒延迟
                            continue
                        else:
                            self._handle_fetch_failure("Empty proxy list returned")
                            return
                    
                    # 成功获取代理列表
                    for item in data['data']['proxy_list']:
                        ip_port, exp = item.split(',')
                        ip, port = ip_port.split(':')
                        p = EnhancedProxyInfo(ip, int(port), int(time.time()) + int(exp))
                        self.proxy_queue.put(p)
                    self.stats['fetched'] += len(data['data']['proxy_list'])
                    log_proxy(f"📦 提取 {len(data['data']['proxy_list'])} 个IP", "info")
                    return  # 成功则退出重试循环
                else:
                    # 返回非 0，表示提取失败
                    msg = data.get('msg', 'unknown')
                    log_proxy(f"⚠️ 代理提取失败 (第{retry_idx+1}次尝试): {msg}", "warning")
                    if retry_idx < 2:  # 还有重试机会
                        time.sleep(2)  # 🔥 退避策略: 2秒延迟
                        continue
                    else:
                        # 🔥 只有3次全部失败才触发 proxy_error 信号
                        self._handle_fetch_failure(msg)
                    return
                   
            except Exception as e:
                error_msg = str(e)
                log_proxy(f"⚠️ 网络错误 (第{retry_idx+1}次尝试): {error_msg}", "warning")
                
                # 🔥 单次失败仅记录warning，不中断程序
                if retry_idx < 2:  # 还有重试机会
                    time.sleep(2)  # 🔥 退避策略: 2秒延迟
                    continue
                else:
                    # 🔥 只有3次全部失败才触发 proxy_error 信号
                    self._handle_fetch_failure(error_msg)
                    return

    def _handle_fetch_failure(self, reason: str):
        """
        统一处理提取失败：记录日志、停止代理池并通知UI
        """
        try:
            log_proxy(f"❌ 代理提取失败: {reason}", "error")
            self.stats['total_rejected'] += 1
            # 先停止代理池本身
            try:
                self.stop()
            except Exception:
                pass

            # 使用全局日志信号通知 UI（主线程执行）：更安全的线程间回调方式
            # 不在这里清除 GLOBAL_PROXY_POOL，让 UI 的 on_proxy_fetch_error 来处理
            try:
                GLOBAL_LOG.proxy_error.emit(reason)
            except Exception:
                log_proxy("⚠️ 无法通过 GLOBAL_LOG.proxy_error 通知 UI，请手动停止代理池", "warning")
        except Exception as ex:
            log_proxy(f"❌ 处理代理提取失败时发生错误: {ex}", "error")

    def _test_proxy_latency(self, proxy: EnhancedProxyInfo, timeout: int = 8) -> tuple:
        """
        测试代理访问目标网站的延迟
        
        Args:
            proxy: 代理信息
            timeout: 超时时间（秒）
        
        Returns:
            (是否可访问, 延迟毫秒)
        """
        proxy_url = proxy.get_url()
        headers = {'User-Agent': FingerprintPool.get_fingerprint()["ua"]}
        target_url = 'https://www.upcard.com.cn:8091/chinaloyalty/walmart/qrybaltxn.html?link=next'
        
        try:
            start_time = time.time()
            response = requests.get(
                target_url,
                proxy=proxy_url,  # 🔥 使用 proxy 参数（更符合curl_cffi的类型定义）
                timeout=timeout,
                allow_redirects=True,
                headers=headers,
                verify=False,
                impersonate="chrome124"
            )
            elapsed_ms = int((time.time() - start_time) * 1000)
            
            # 🔥 判断是否成功（状态码 200-399 都算成功）
            if 200 <= response.status_code < 400:
                return True, elapsed_ms
            else:
                log_proxy(f"⚠️ 代理 {proxy.ip}:{proxy.port} 目标网站测试失败: 状态码 {response.status_code}", "warning")
                return False, 9999
                
        except Exception as e:
            # curl_cffi 的异常处理
            error_msg = str(e).lower()
            if "timeout" in error_msg or "timed out" in error_msg:
                error_type = "超时"
            elif "ssl" in error_msg or "certificate" in error_msg:
                error_type = "SSL错误"
            elif "proxy" in error_msg or "connection" in error_msg:
                error_type = "连接失败"
            else:
                error_type = "请求异常"
            log_proxy(f"❌ 代理 {proxy.ip}:{proxy.port} 目标网站{error_type} ({type(e).__name__})", "warning")
            return False, 9999

    def _consumer(self):
        """消费者线程：验证queue中的代理（优化版：先测连通性，再验证地理位置）"""
        while self.is_running:
            try:
                # 🔥 阻塞等待新代理（超时1秒，避免无法退出）
                try:
                    p = self.proxy_queue.get(timeout=1)
                except queue.Empty:
                    continue
                
                # 🔥 步骤1：先测试连通性和延迟（快速过滤无效代理）
                # 注意：_test_proxy_latency 内部已输出详细日志
                is_reachable, latency = self._test_proxy_latency(p, timeout=8)
                
                if not is_reachable:
                    self.stats['total_unreachable'] += 1
                    self.stats['total_rejected'] += 1
                    continue
                
                # 记录延迟
                p.latency = latency
                p.is_reachable = True
                
                # 🔥 新增：拒绝延迟过高的代理
                MAX_LATENCY = 5000  # 毫秒
                if latency > MAX_LATENCY:
                    log_proxy(f"❌ 代理延迟过高: {p.ip}:{p.port} ({latency}ms > {MAX_LATENCY}ms), 已拒绝", "warning")
                    self.stats['total_slow'] += 1
                    self.stats['total_rejected'] += 1
                    continue


                with self.lock:
                        key = f"{p.ip}:{p.port}"
                        if key not in self.available_set:
                            # 🔥 双重检查：未过期才添加
                            if not p.is_expired(self.config['expire_threshold']):
                                self.available_proxies.append(p)
                                self.available_set.add(key)
                                # 🔥 按延迟排序（低延迟优先）
                                self.available_proxies.sort(key=lambda x: x.latency)
                                log_proxy(f"✅ 入池: {p.ip} {p.latency}ms", "success")
                            else:
                                log_proxy(f"⚠️ 代理已过期，跳过: {p.ip}:{p.port}", "warning")
                
                # 🔥 步骤2：再查询地理位置（仅对可访问的代理）
                # geo = GEO_SERVICE.query_ip_location(p.ip)
                # # 嘗試用下海外ip 後面可以放到配置裡面
                # # if geo and geo.is_china():
                # if geo:
                #     p.geo = geo
                #     with self.lock:
                #         key = f"{p.ip}:{p.port}"
                #         if key not in self.available_set:
                #             # 🔥 双重检查：未过期才添加
                #             if not p.is_expired(self.config['expire_threshold']):
                #                 self.available_proxies.append(p)
                #                 self.available_set.add(key)
                #                 # 🔥 按延迟排序（低延迟优先）
                #                 self.available_proxies.sort(key=lambda x: x.latency)
                #                 log_proxy(f"✅ 入池: {p.ip} ({geo.city}) {p.latency}ms", "success")
                #             else:
                #                 log_proxy(f"⚠️ 代理已过期，跳过: {p.ip}:{p.port}", "warning")
                # else:
                #     log_proxy(f"❌ 代理非国内IP: {p.ip}:{p.port}", "warning")
                #     self.stats['total_rejected'] += 1
                    
            except Exception as e:
                log_proxy(f"❌ 消费者线程异常: {e}", "error")
                time.sleep(1)

    def _cleaner(self):
        """清理者线程：定期删除过期代理"""
        # 🔥 启动时记录配置的清理间隔
        clean_interval = self.config.get('clean_interval', 30)
        log_proxy(f"🧹 清理线程已启动，清理间隔: {clean_interval}秒", "info")
        
        while self.is_running:
            try:
                # 🔥 每次循环都重新读取配置（支持动态更新）
                clean_interval = self.config.get('clean_interval', 30)
                
                # 🔥 先执行清理，再sleep，确保第一次清理立即执行
                expired_list = []
                with self.lock:
                    # 找出过期的代理
                    for proxy in self.available_proxies[:]:
                        if proxy.is_expired(self.config.get('expire_threshold', 30)):
                            expired_list.append(proxy)
                    
                    # 删除过期代理
                    for proxy in expired_list:
                        self.available_proxies.remove(proxy)
                        proxy_key = f"{proxy.ip}:{proxy.port}"
                        self.available_set.discard(proxy_key)
                        self.stats['expired'] += 1
                    
                    remaining = len(self.available_proxies)
                
                if expired_list:
                    log_proxy(f"🧹 清理 {len(expired_list)} 个过期IP，剩余 {remaining} 个可用", "info")
                
                # 🔥 使用当前配置的清理间隔
                time.sleep(clean_interval)
                
            except Exception as e:
                log_proxy(f"❌ 清理者线程异常: {e}", "error")
                time.sleep(5)

    def remove_proxy(self, ip: str, port: int):
        """
        物理剔除失效代理
        
        Args:
            ip (str): 代理IP地址
            port (int): 代理端口
        """
        proxy_key = f"{ip}:{port}"
        
        with self.lock:
            # 从集合中移除
            if proxy_key in self.available_set:
                self.available_set.discard(proxy_key)
            
            # 从列表中移除
            removed_count = 0
            self.available_proxies = [p for p in self.available_proxies 
                                     if not (p.ip == ip and p.port == port)]
            removed_count = 1  # 假设每次只移除一个
            
            if removed_count > 0:
                log_proxy(f"🗑️ 已剔除失效代理: {ip}:{port} | 剩余可用: {len(self.available_proxies)}", "warning")


GLOBAL_PROXY_POOL: Optional[EnhancedProxyPool] = None
# 记录全局 UI 实例（用于从代理池线程回调到UI线程）
GLOBAL_UI: Optional['WalmartUltraUI'] = None

# 全局缓存管理器
CACHE_MANAGER = init_cache_manager()


# ==========================================
# 4. 业务逻辑 (Worker)
# ==========================================
# [保留原有算法函数: generate_slider_track_original, gen_track_original, get_params_original, get_slide_distance_cv_pro, FingerprintPool, SmartImporter]
# 为节省篇幅，此处省略核心算法函数的重复定义，请确保在运行时包含这些函数
# ... (Insert Core Algorithms Here) ...
# ==========================================
# 核心算法层 - 滑块验证生成
# ==========================================

def generate_slider_track_optimized(distance: int = 120, duration_range: Tuple = (1800, 2500)) -> List:
    """
    生成模拟人类滑动滑块的轨迹（贝塞尔曲线+随机抖动）
    
    参数:
        distance (int): 滑块需要移动的水平总距离（px）
        duration_range (Tuple): 滑动总时间范围（ms）
        
    返回:
        List - 轨迹列表，每个元素为(时间ms, x坐标, y坐标)，均为整数
    """
    # 【步骤1】生成时间轨迹（保证递增的整数）
    total_duration = random.randint(*duration_range)
    num_points = random.randint(40, 60)
    time_stamps = np.linspace(0, total_duration, num_points).round().astype(int).tolist()
    
    # 处理时间戳重复（确保严格递增）
    for i in range(1, num_points):
        if time_stamps[i] <= time_stamps[i - 1]:
            time_stamps[i] = time_stamps[i - 1] + 1

    # 【步骤2】使用贝塞尔曲线生成X方向基础轨迹（模拟自然加速-减速）
    def bezier_curve(points, num=100):
        n = len(points) - 1
        return [
            sum(comb(n, i) * (t ** i) * ((1 - t) ** (n - i)) * points[i] for i in range(n + 1))
            for t in np.linspace(0, 1, num)
        ]

    control_points_x = [
        0,
        random.uniform(distance * 0.08, distance * 0.25),
        random.uniform(distance * 0.65, distance * 0.9),
        distance
    ]
    base_x = bezier_curve(control_points_x, num_points)

    # 【步骤3】加入小幅回退（模拟真实人类操作）
    track_x = []
    backoff_count = random.randint(1, 3)
    backoff_positions = [random.uniform(0.25, 0.75) for _ in range(backoff_count)]

    for i in range(num_points):
        x = base_x[i]
        t_ratio = i / (num_points - 1)
        for pos in backoff_positions:
            if abs(t_ratio - pos) < 0.06:
                x -= random.uniform(2.5, 9)
                break
        track_x.append(x)

    # 【步骤4】修正终点（确保最终到达目标距离）
    final_x = track_x[-1]
    correction = distance - final_x
    track_x = [x + correction * (i / (num_points - 1)) for i, x in enumerate(track_x)]

    # 【步骤5】生成Y方向轨迹（随机抖动）
    track_y = []
    y_base = random.uniform(-3, 3)
    for i in range(num_points):
        t_ratio = i / (num_points - 1)
        jitter_factor = math.sin(t_ratio * math.pi * 0.9) * random.uniform(0.7, 1.3)
        y = y_base + random.gauss(0, 1.5) * jitter_factor
        track_y.append(round(y))

    # 【步骤6】合并轨迹数据（确保X单调递增）
    track = []
    prev_x = 0
    for t, x, y in zip(time_stamps, track_x, track_y):
        current_x = max(prev_x - 1, round(x))
        track.append((t, current_x, y))
        prev_x = current_x

    return track


def gen_track(distance: int, start_time: int) -> Tuple[List, int]:
    """
    生成滑块验证轨迹JSON格式
    
    参数:
        distance (int): 滑块移动距离
        start_time (int): 起始时间戳
        
    返回:
        Tuple - (轨迹列表, 结束时间)
    """
    track = generate_slider_track_optimized(distance)
    tracks = []
    end_t = 0

    for i in range(len(track)):
        if i == 0:
            temp_crack = {"x": 0, "y": 0, "type": "down", "t": start_time}
        elif i == len(track) - 1:
            temp_crack = {
                "x": track[i][1],
                "y": track[i][2],
                "type": "up",
                "t": start_time + track[i][0]
            }
        else:
            end_t = start_time + track[i][0]
            temp_crack = {
                "x": track[i][1],
                "y": track[i][2],
                "type": "move",
                "t": start_time + track[i][0]
            }
        tracks.append(temp_crack)

    return tracks, start_time + track[-1][0]


def get_params_optimized(img_id: str, distance: int) -> bytes:
    """
    生成滑块验证参数（JSON编码）
    
    参数:
        img_id (str): 验证码图片ID
        distance (int): 滑块距离
        
    返回:
        bytes - 编码后的参数JSON
    """
    st_start = datetime.now(timezone.utc)
    f_st_start = st_start.strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"
    
    rand_t = random.randint(200, 500)
    start_t = int(st_start.microsecond / 1000) + rand_t
    track, end_t = gen_track(distance, start_t)
    
    add_ms = end_t - int(st_start.microsecond / 1000)
    f_st_end = (st_start + timedelta(milliseconds=add_ms)).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"
    
    # 等待滑动时间完成
    time.sleep(max(0, add_ms / 1000))
    
    param = {
        "id": img_id,
        "data": {
            "bgImageWidth": 300,
            "bgImageHeight": 180,
            "sliderImageWidth": 55,
            "sliderImageHeight": 180,
            "startSlidingTime": f_st_start,
            "endSlidingTime": f_st_end,
            "trackList": track
        }
    }
    
    return json.dumps(param, separators=(',', ':')).encode('utf-8')


def get_slide_distance_cv(bg_b64: str, slider_b64: str) -> int:
    """
    使用OpenCV识别滑块距离 - 简化版本，直接采用沃尔玛2.py的算法
    
    经测试，复杂的多阶段验证导致识别率下降至20%
    现改为沃尔玛2.py的简单高效算法，识别率恢复到80%+
    
    流程:
    1. 解码base64图片
    2. 滑块图灰度化 → 色差反转 (255 - pixel)
    3. 模板匹配: TM_CCOEFF_NORMED 在背景中查找滑块
    4. 返回最佳匹配的x坐标
    
    参数:
        bg_b64 (str): 背景图base64
        slider_b64 (str): 滑块图base64
        
    返回:
        int - 滑块距离（像素），识别失败返回-1
    """
    try:
        def decode_base64_image(b64_str: str) -> Optional[np.ndarray]:
            """解码base64图片为OpenCV图像"""
            try:
                if ',' in b64_str:
                    b64_str = b64_str.split(',')[1]
                image_data = base64.b64decode(b64_str)
                image_array = np.frombuffer(image_data, np.uint8)
                image = cv2.imdecode(image_array, cv2.IMREAD_COLOR)
                return image
            except Exception as e:
                logger.error(f"❌ Base64解码异常: {e}")
                return None
        
        # 解码图片
        bg_img = decode_base64_image(bg_b64)
        slider_img = decode_base64_image(slider_b64)
        
        if bg_img is None or slider_img is None:
            logger.warning("⚠️ 图片解码失败")
            return -1
        
        # 【关键算法 - 来自沃尔玛2.py】
        # 1. 灰度化滑块图
        slider_gray = cv2.cvtColor(slider_img, cv2.COLOR_BGR2GRAY)
        
        # 2. 灰度化背景图
        bg_gray = cv2.cvtColor(bg_img, cv2.COLOR_BGR2GRAY)
        
        # 3. 色差反转: 获取黑色差异区域 (反转滑块灰度值)
        slider_inverted = 255 - slider_gray
        
        # 4. 模板匹配 - 简单直接的匹配方法
        match_result = cv2.matchTemplate(bg_gray, slider_inverted, cv2.TM_CCOEFF_NORMED)
        
        # 5. 获取最佳匹配位置
        min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(match_result)
        distance = max_loc[0]  # x坐标 = 滑块距离
        
        logger.info(f"✅ CV识别成功: 距离={distance}px, 匹配度={max_val:.4f}")
        return distance
    except Exception as e:
        logger.error(f"❌ CV识别异常: {type(e).__name__}: {e}")
        logger.debug(f"  └─ 完整堆栈信息已记录")
        return -1


class FingerprintPool:
    """
    浏览器指纹生成器 - 随机生成Chrome浏览器指纹
    """
    
    @staticmethod
    def get_fingerprint() -> Dict:
        """
        生成随机浏览器指纹
        
        返回:
            Dict - 包含ua、sec_ch_ua等字段
        """
        versions = [
            ("131", "131.0.6778.205"),
            ("130", "130.0.6723.117")
        ]
        v_major, v_full = random.choice(versions)
        return {
            "ua": f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v_full} Safari/537.36",
            "sec_ch_ua": f'"Google Chrome";v="{v_major}", "Chromium";v="{v_major}", "Not?A_Brand";v="24"',
            "version": v_major
        }


class SmartImporter:
    """
    智能导入器 - 支持Excel和Text文件导入卡密
    
    支持格式:
      - Excel: .xlsx, .xls (自动跳过空行)
      - 文本: .txt (支持多分隔符: 空格、制表符、逗号)
    """
    
    # 卡号正则（以23、86、60开头，18-20位数字）
    RE_CARD = re.compile(r'^(23|86|60)\d{16,18}$')
    # 密码正则（6位数字）
    RE_PIN = re.compile(r'^\d{6}$')

    @staticmethod
    def parse_file(file_path: str) -> List[Dict]:
        """
        解析卡密文件
        
        参数:
            file_path (str): 文件路径
            
        返回: 
            List[Dict] - 卡密列表，格式 [{"card": "xxx", "pin": "yyy"}, ...]
        """
        results = []
        
        if not os.path.exists(file_path):
            logger.error(f"❌ 文件不存在: {file_path}")
            return results
        
        try:
            ext = os.path.splitext(file_path)[1].lower()
            raw_lines = []
            
            # 步骤1：读取文件
            if ext in ['.xlsx', '.xls']:
                logger.info(f"📊 正在读取Excel文件: {file_path}")
                try:
                    df = pd.read_excel(file_path, header=None, dtype=str).fillna('')
                    raw_lines = df.values.tolist()
                except Exception as e:
                    logger.error(f"❌ Excel文件读取失败: {e}")
                    return results
            else:
                logger.info(f"📄 正在读取文本文件: {file_path}")
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        raw_lines = [[line.strip()] for line in f.readlines() if line.strip()]
                except Exception as e:
                    logger.error(f"❌ 文本文件读取失败: {e}")
                    return results
            
            if not raw_lines:
                logger.warning(f"⚠️ 文件为空: {file_path}")
                return results
            
            # 步骤2：解析卡密
            logger.info(f"📋 开始解析卡密数据...")
            for row_idx, row in enumerate(raw_lines, 1):
                # 将行数据转为token列表（支持多种分隔符）
                tokens = []
                for cell in row:
                    if pd.isna(cell):  # 跳过NaN值
                        continue
                    # 按空格、制表符、逗号分割
                    cell_str = str(cell).strip()
                    tokens.extend(re.split(r'[\s\t,]+', cell_str))
                
                if not tokens:
                    continue
                
                card, pin = "", ""
                
                # 先找卡号（去掉所有非数字字符）
                for token in tokens:
                    clean = re.sub(r'\D', '', token)
                    if not card and SmartImporter.RE_CARD.match(clean):
                        card = clean
                        break
                
                # 再找密码
                for token in tokens:
                    if '.' in token:  # 跳过浮点数
                        continue
                    clean = re.sub(r'\D', '', token)
                    if clean == card:  # 跳过与卡号相同的
                        continue
                    if not pin and SmartImporter.RE_PIN.match(clean):
                        pin = clean
                        break
                
                # 只要有卡号就保存（密码可选）
                if card:
                    results.append({"card": card, "pin": pin})
                    logger.debug(f"✓ 第{row_idx}行: 卡={card[:4]}**, 密码={pin if pin else '(无)'}")
            
            # 步骤3：去重
            original_count = len(results)
            results_dedup = []
            seen_cards = set()
            for item in results:
                if item['card'] not in seen_cards:
                    results_dedup.append(item)
                    seen_cards.add(item['card'])
            
            logger.info(f"✅ 导入完成: 原始{original_count}条 → 去重{len(results_dedup)}条")
            return results_dedup
            
        except Exception as e:
            logger.error(f"❌ 文件解析异常: {e}")
            logger.debug(traceback.format_exc())
            return results


# ==========================================
# 表格列索引常量定义
# ==========================================
class TableColumnIndex:
    """表格列索引常量，避免硬编码"""
    SEQ = 0        # 序号
    CHECKBOX = 1   # 选择框
    CARD = 2       # 券码
    PIN = 3        # 密码
    BALANCE = 4    # 面值
    STATUS = 5     # 状态
    TIME = 6       # 时间
    MSG = 7        # 备注


class WalmartWorker(QThread):
    """
    Walmart卡查询工作线程
    
    功能:
      - 逐张查询卡号有效性
      - 支持代理和直连两种模式
      - 滑块验证码自动识别和绕过
      - 并发处理多个卡号
    """
    
    # 信号定义
    result_signal = Signal(int, dict)      # 查询结果 (行号, 结果字典)
    progress_signal = Signal(int)          # 进度 (百分比)
    finished_signal = Signal()             # 完成信号
    log_signal = Signal(str, str)          # 日志 (消息, 级别)

    def __init__(self, tasks: List[Dict], config: Dict):
        """
        初始化工作线程
        
        参数:
            tasks (List[Dict]): 任务列表 [{"row": int, "card": str, "pin": str}, ...]
            config (Dict): 配置字典
        """
        super().__init__()
        self.tasks = tasks
        self.config = config
        self.running = True
        self.done = 0
        self.total = len(tasks)
        
        # 请求头
        self.headers_walmart = {
            "User-Agent": FingerprintPool.get_fingerprint()["ua"],
        }
        self.headers_spider = {
            'sec-ch-ua-platform': '"Windows"',
            'user-agent': FingerprintPool.get_fingerprint()["ua"],
            'accept': 'application/json, text/javascript, */*; q=0.01',
            'sec-ch-ua': FingerprintPool.get_fingerprint()["sec_ch_ua"],
            'content-type': 'application/json;charset=UTF-8',
            'sec-ch-ua-mobile': '?0',
            'origin': 'https://www.upcard.com.cn:8091',
            'sec-fetch-site': 'cross-site',
            'sec-fetch-mode': 'cors',
            'sec-fetch-dest': 'empty',
            'referer': 'https://www.upcard.com.cn:8091/',
            'accept-encoding': 'gzip, deflate, br, zstd',
            'accept-language': 'zh-CN,zh;q=0.9',
            'priority': 'u=1, i'
        }

    def log(self, msg: str, level: str = "info"):
        """发出日志信号"""
        self.log_signal.emit(msg, level)

    def stop(self):
        """停止工作线程"""
        self.running = False
        self.log("⏹️ 收到停止信号", "warning")

    def run(self):
        """
        线程主函数 - 执行所有查询任务
        """
        self.log(f"🚀 任务启动 - 共{self.total}张卡", "info")
        
        # 检查代理池
        use_proxy = self.config.get('use_proxy', False)
        if use_proxy and GLOBAL_PROXY_POOL:
            if not GLOBAL_PROXY_POOL.is_running:
                GLOBAL_PROXY_POOL.start()
            
            self.log("⏳ 等待代理池就绪...", "warning")
            for _ in range(30):
                if not self.running:
                    break
                if GLOBAL_PROXY_POOL.get_status()['available'] > 0:
                    break
                time.sleep(1)
            else:
                self.log("❌ 代理池超时，无可用IP", "error")
                self.finished_signal.emit()
                return
            
            self.log("✅ 代理池已就绪", "success")

        # 使用线程池并发处理
        try:
            with ThreadPoolExecutor(max_workers=self.config['thread_count']) as pool:
                futures = {pool.submit(self.process_card, task): task for task in self.tasks}
                for future in as_completed(futures):
                    if not self.running:
                        pool.shutdown(wait=False)
                        break
                    try:
                        future.result()
                    except Exception as e:
                        logger.error(f"❌ 任务执行异常: {e}")
        except Exception as e:
            logger.error(f"❌ 线程池异常: {e}")
        
        # 【清理代理池】任务完成时自动关闭代理池
        if use_proxy and GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
            self.log("🧹 清理代理池...", "info")
            GLOBAL_PROXY_POOL.stop()
            self.log("✅ 代理池已清理", "success")
        
        self.log("✅ 所有任务执行完毕", "success")
        self.finished_signal.emit()

    def process_card(self, task: Dict):
        """
        处理单张卡的完整流程
        
        参数:
            task (Dict): 任务信息 {"row": int, "card": str, "pin": str}
        """
        if not self.running:
            return
        
        row = task["row"]
        card = task["card"]
        
        logger.info(f"[行{row}] 处理卡: {card[:8]}...")
        
        # ✅ 【第1步】检查缓存（< 1ms 或 < 5ms）
        cached_status = CACHE_MANAGER.get(card)
        if cached_status:
            logger.info(f"[行{row}] 💾 缓存命中: {card[:8]}... → {cached_status}")
            self.result_signal.emit(row, {
                "status": cached_status,
                "balance": "0.00",
                "msg": "来自缓存"
            })
            self._update_progress()
            return
        
        # 获取代理 (支持 3 次重试)
        proxy_url = None
        proxy_ip = "直连"  # 默认为直连
        proxy_info = None  # 初始化代理信息对象
        
        if self.config.get('use_proxy') and GLOBAL_PROXY_POOL:
            # ✅ 新增: 3 次重试获取代理 (10s, 20s, 30s)
            sleep_times = [10, 20, 30]
            
            for retry_idx in range(3):
                proxy_info = GLOBAL_PROXY_POOL.get_proxy()
                if proxy_info:
                    logger.info(f"[行{row}] ✅ 第 {retry_idx+1} 次尝试成功获取代理")
                    break
                
                if retry_idx < 2:  # 不要在第 3 次后等待
                    sleep_time = sleep_times[retry_idx]
                    logger.warning(f"[行{row}] ⚠️ 代理获取失败 (第 {retry_idx+1} 次), 等待 {sleep_time}s 后重试...")
                    time.sleep(sleep_time)
                else:
                    logger.error(f"[行{row}] ❌ 3 次重试都失败，终止当前查询")
            
            # 如果 3 次都失败，记录失败并返回
            if proxy_info is None:
                self.result_signal.emit(row, {
                    "status": "网络异常",
                    "balance": "-",
                    "msg": "代理获取失败 (3次重试)"
                })
                self._update_progress()
                return
            
            # 代理获取成功，提取信息
            proxy_url = proxy_info.get_url()
            proxy_ip = proxy_info.ip  # 获取代理IP
            proxy_port = proxy_info.port
            # 输出代理信息到日志
            self.log(f"[行{row}] 🌐 使用代理: {proxy_ip}:{proxy_port}", "info")
        else:
            # 直连时也输出日志
            self.log(f"[行{row}] 🌐 使用代理: {proxy_ip}", "info")
        
        # 创建Session
        try:
            impersonate_ua = "chrome124"  # 浏览器指纹
            session = requests.Session(impersonate=impersonate_ua)
            session.headers.update(self.headers_walmart)
            if proxy_url:
                session.proxies = {"http": proxy_url, "https": proxy_url}
            
            # 输出指纹信息到日志
            self.log(f"[行{row}] 🔐 浏览器指纹: {impersonate_ua}", "info")
        except Exception as e:
            logger.error(f"❌ Session创建失败: {e}")
            self.result_signal.emit(row, {
                "status": "网络异常",
                "balance": "-",
                "msg": "Session创建失败"
            })
            self._update_progress()
            return
        
        # 执行卡查询流程（传递 proxy_info 以支持代理失效剔除）
        result = self._query_card(session, card, proxy_info)
        
        # ✅ 【缓存写入】查询到"已使用"状态时自动写入缓存
        if result.get("status") == "已使用":
            CACHE_MANAGER.set(card, "已使用")
            logger.debug(f"[行{row}] 📝 已写入缓存: {card[:8]}...")
        
        self.result_signal.emit(row, result)
        self._update_progress()

    def _query_card(self, session, card: str, proxy_info=None) -> Dict:
        """
        查询单张卡的完整流程
        
        参数:
            session: requests Session对象
            card (str): 卡号
            proxy_info: 代理信息对象（用于首页访问失败时移除失效代理）
            
        返回:
            Dict - 查询结果 {"status": str, "balance": str, "msg": str}
        """
        try:
            # 【步骤1】访问首页获取Cookie - 支持代理轮转自愈
            url_home = 'https://www.upcard.com.cn:8091/chinaloyalty/walmart/qrybaltxn.html?link=next'
            
            max_home_retry = 3
            home_success = False
            
            for home_retry_idx in range(max_home_retry):
                logger.debug(f"[步骤1] 访问首页 (尝试 {home_retry_idx+1}/{max_home_retry})...")
                resp = session.get(url_home, timeout=10, verify=False)
                
                if resp.status_code == 200:
                    home_success = True
                    break
                
                # 访问失败，判定当前代理失效
                if home_retry_idx < max_home_retry - 1:  # 不是最后一次尝试
                    logger.warning(f"[步骤1] 首页访问失败，当前代理可能失效")
                    
                    # 调用 remove_proxy 剔除失效代理
                    if GLOBAL_PROXY_POOL and proxy_info:
                        proxy_ip = proxy_info.ip if proxy_info else "未知"
                        proxy_port = proxy_info.port if proxy_info else 0
                        GLOBAL_PROXY_POOL.remove_proxy(proxy_ip, proxy_port)
                    
                    # 原地 while 循环等待新代理
                    new_proxy_info = None
                    wait_count = 0
                    while wait_count < 30:  # 最多等待30秒
                        if GLOBAL_PROXY_POOL:
                            new_proxy_info = GLOBAL_PROXY_POOL.get_proxy()
                        if new_proxy_info:
                            break
                        time.sleep(1)
                        wait_count += 1
                    
                    if not new_proxy_info:
                        logger.error(f"[步骤1] 等待新代理超时")
                        return {"status": "网络异常", "balance": "-", "msg": "代理获取超时"}
                    
                    # 更新 session.proxies 并清空 session.cookies
                    proxy_url = new_proxy_info.get_url()
                    session.proxies = {"http": proxy_url, "https": proxy_url}
                    session.cookies.clear()
                    logger.info(f"[步骤1] 已切换到新代理: {new_proxy_info.ip}:{new_proxy_info.port}")
                    proxy_info = new_proxy_info
            
            if not home_success:
                return {"status": "网络异常", "balance": "-", "msg": "首页访问失败"}
            
            # 【步骤2】获取验证码Token
            logger.debug(f"[步骤2] 获取验证码Token...")
            token = self._get_captcha_token(session)
            if not token:
                return {"status": "网络异常", "balance": "-", "msg": "Token获取失败"}
            
            # 【步骤3】重试滑块验证（最多3次）
            logger.debug(f"[步骤3] 进行滑块验证...")
            max_retry = 3
            check_id = None
            for retry_idx in range(max_retry):
                check_id = self._verify_slider(session, token)
                if check_id:
                    logger.debug(f"✓ 滑块验证成功 (第{retry_idx+1}次)")
                    break
                logger.debug(f"⚠️ 滑块验证失败，重试 ({retry_idx+1}/{max_retry})")
                
                # ✅ 在重试前添加随机延迟 (0.5-1.5 秒)
                if retry_idx < max_retry - 1:  # 不要在最后一次后延迟
                    retry_interval_min = self.config.get('retry_interval_min', 0.5)
                    retry_interval_max = self.config.get('retry_interval_max', 1.5)
                    sleep_time = random.uniform(retry_interval_min, retry_interval_max)
                    logger.debug(f"  ⏳ 等待 {sleep_time:.2f}s 后进行第 {retry_idx+2} 次重试...")
                    time.sleep(sleep_time)
                if retry_idx < max_retry - 1:
                    token = self._get_captcha_token(session)
                    if not token:
                        return {"status": "验证超时", "balance": "-", "msg": "重新获取Token失败"}
            
            if not check_id:
                return {"status": "滑块验证失败", "balance": "-", "msg": "验证次数超限"}
            
            # 【步骤4】提交查询卡号
            logger.debug(f"[步骤4] 提交查询卡号...")
            if not self._bind_card(session, check_id, card):
                return {"status": "查询失败", "balance": "-", "msg": "查询卡号异常"}
            
            # 【步骤5】查询卡余额
            logger.debug(f"[步骤5] 查询余额...")
            result = self._query_balance(session, card)
            logger.info(f"✅ [卡{card[:8]}...] 查询完成: {result['status']}")
            return result
        
        except Exception as e:
            logger.error(f"❌ 查询异常: {e}")
            logger.debug(traceback.format_exc())
            return {"status": "网络异常", "balance": "-", "msg": f"异常: {str(e)[:20]}"}

    def _get_captcha_token(self, session) -> Optional[str]:
        """
        获取验证码Token
        
        返回: str - Token或None
        """
        try:
            url = 'https://www.upcard.com.cn:8091/chinaloyalty/walmart/qrybaltxn.html?link=getCaptchaToken'
            data = {"businesstype": "CULSERVICE20250320"}
            resp = session.post(url, data=data, timeout=10, verify=False)
            if resp.status_code == 200:
                token = resp.text.strip()
                if token and len(token) < 100:
                    # logger.debug(f"✓ Token获取成功: {token[:20]}...")
                    return token
            logger.warning(f"⚠️ Token获取失败或格式错误")
            return None
        except Timeout:
            logger.warning("❌ Token请求超时")
            return None
        except Exception as e:
            logger.error(f"❌ Token获取异常: {e}")
            return None

    def _verify_slider(self, session, token: str) -> Optional[str]:
        """
        滑块验证流程
        
        参数:
            session: requests Session
            token (str): 验证码Token
            
        返回: str - 验证ID或None
        """
        try:
            # 【子步骤1】下载验证码图片
            # logger.debug(f"  └─ 下载验证码图片...")
            url_img = f'https://www.culdata.com/captcha/gen/20213997/CULSERVICE20250320/{token}?type=SLIDER'
            resp = session.post(url_img, verify=False, timeout=10)
            if resp.status_code != 200:
                logger.warning(f"    ❌ 验证码下载失败: {resp.status_code}")
                return None
            
            img_data = resp.json()
            img_id = img_data.get('id')
            bg_b64 = img_data.get('captcha', {}).get('backgroundImage')
            slider_b64 = img_data.get('captcha', {}).get('templateImage')
            
            if not all([img_id, bg_b64, slider_b64]):
                logger.warning(f"    ❌ 验证码数据不完整")
                return None
            
            # 【子步骤2】CV识别滑块距离
            logger.debug(f"  └─ 识别滑块距离...")
            # 记录CV识别开始
            logger.info(f"  ├─ 📸 CV识别开始 (沃尔玛2.py简化算法)")
            distance = get_slide_distance_cv(bg_b64, slider_b64)
            if distance <= 0:
                logger.warning(f"    ❌ 滑块识别失败 (CV匹配或二次验证失败)")
                return None
            
            # 缩放距离
            scale = 0.5
            distance_scaled = round(distance * scale)
            logger.debug(f"    ✓ 识别距离: {distance}px → {distance_scaled}px (缩放{scale})")
            
            # 【子步骤3】生成验证轨迹
            logger.debug(f"  └─ 生成验证轨迹...")
            params_bytes = get_params_optimized(img_id, distance_scaled)
            
            # 【子步骤4】提交验证
            logger.debug(f"  └─ 提交验证...")
            url_verify = f'https://www.culdata.com/captcha/check/20213997/CULSERVICE20250320/{token}'
            resp = session.post(url_verify, data=params_bytes, headers=self.headers_spider, 
                               verify=False, timeout=10)
            if resp.status_code != 200:
                logger.warning(f"    ❌ 验证提交失败: {resp.status_code}")
                return None
            
            verify_result = resp.json()
            if verify_result.get('code') == 200 and verify_result.get('success'):
                check_id = verify_result.get('data')
                logger.debug(f"    ✓ 验证成功: {check_id[:20]}...")
                return check_id
            else:
                logger.warning(f"    ❌ 验证被拒: {verify_result.get('msg')}")
                return None
        
        except Timeout:
            logger.warning("❌ 滑块验证超时")
            return None
        except json.JSONDecodeError:
            logger.warning("❌ 验证返回格式错误")
            return None
        except Exception as e:
            logger.error(f"❌ 滑块验证异常: {e}")
            return None

    def _bind_card(self, session, check_id: str, card: str) -> bool:
        """
        提交查询
        
        参数:
            session: requests Session
            check_id (str): 验证ID
            card (str): 卡号
            
        返回: bool - 提交查询是否成功
        """
        try:
            url = 'https://www.upcard.com.cn:8091/chinaloyalty/walmart/qrybaltxn.html?link=next'
            # 分割卡号为4段
            card1, card2, card3, card4 = card[0:4], card[4:8], card[8:12], card[12:19]
            params = {
                "captchaCheckId": check_id,
                "card1": card1,
                "card2": card2,
                "card3": card3,
                "card4": card4,
            }
            resp = session.post(url, data=params, timeout=10, verify=False)
            if resp.status_code == 200:
                logger.debug(f"  ✓ 查询卡号信息成功")
                return True
            else:
                logger.warning(f"  ❌ 查询卡号信息失败: {resp.status_code}")
                return False
        except Timeout:
            logger.warning("❌ 绑卡请求超时")
            return False
        except Exception as e:
            logger.error(f"❌ 查卡异常: {e}")
            return False

    def _query_balance(self, session, card: str) -> Dict:
        """
        查询卡余额
        
        参数:
            session: requests Session
            card (str): 卡号
            
        返回: Dict - 查询结果
        """
        try:
            url = 'https://www.upcard.com.cn:8091/chinaloyalty/walmart/qrybaltxn.html'
            params = {
                "dateFrom": '',
                "dateTo": '',
                "cardNo": card,
            }
            resp = session.post(url, data=params, timeout=10, verify=False)
            if resp.status_code != 200:
                logger.warning(f"❌ 余额查询失败: {resp.status_code}")
                return {"status": "查询失败", "balance": "-", "msg": "服务器异常"}
            
            # 解析HTML，提取余额
            html = etree.HTML(resp.text)
            if html is None:
                logger.warning(f"❌ HTML解析失败")
                return {"status": "解析失败", "balance": "-", "msg": "页面格式错误"}
            
            # 提取充值记录文本
            elements = html.xpath("//span[@class='STYLE3']")
            full_text = ' '.join([str(elem.text or '') for elem in elements])
            full_text = full_text.replace('\xa0', ' ').replace('\u200b', '')
            
            if not full_text:
                logger.warning(f"❌ 未找到余额信息 - 可能是无效卡或页面异常")
                return {"status": "无效卡", "balance": "-", "msg": "卡号不存在"}
            
            logger.debug(f"  余额信息: {full_text[:50]}...")
            
            # 检查是否已被使用
            if any(keyword in full_text for keyword in ['转出', '消费', '扣款']):
                logger.debug(f"  检测到消费记录")
                # 尝试提取余额
                # balance = self._extract_balance(full_text)
                # if balance and float(balance) > 0:
                #     valid_date = self._extract_valid_date(full_text)
                #     return {
                #         "status": "有效",
                #         "balance": balance,
                #         "msg": f"有效期: {valid_date}"
                #     }
                # else:
                return {"status": "已使用", "balance": "0.00", "msg": ""}
            else:
                # 提取余额信息
                balance = self._extract_balance(full_text)
                valid_date = self._extract_valid_date(full_text)
                
                if balance:
                    return {
                        "status": "未使用",
                        "balance": balance,
                        "msg": f"有效期: {valid_date}"
                    }
                else:
                    return {"status": "查询失败", "balance": "-", "msg": "无法提取余额"}
        
        except Timeout:
            logger.warning("❌ 余额查询超时")
            return {"status": "查询超时", "balance": "-", "msg": "网络超时"}
        except Exception as e:
            logger.error(f"❌ 余额查询异常: {e}")
            return {"status": "查询异常", "balance": "-", "msg": str(e)[:20]}

    @staticmethod
    def _extract_balance(text: str) -> Optional[str]:
        """提取余额 - 格式: 余额：123.45"""
        match = re.search(r'余额：(\d+\.\d+)', text)
        return match.group(1) if match else None

    @staticmethod
    def _extract_valid_date(text: str) -> str:
        """提取有效期 - 格式: 有效期至：2025年12月"""
        match = re.search(r'有效期至：(\d{4}年\d{2}月)', text)
        return match.group(1) if match else "未知"

    def _update_progress(self):
        """更新进度条"""
        self.done += 1
        progress = int((self.done / self.total) * 100) if self.total > 0 else 100
        self.progress_signal.emit(progress)


# ==========================================
# UI 层
# ==========================================
class ReferenceStyleDelegate(QStyledItemDelegate):
    def paint(self, painter, option, index):
        painter.fillRect(option.rect, QColor("#1e1e1e"))
        if option.state & QStyle.StateFlag.State_Selected:
            painter.fillRect(option.rect, QColor("#3a3d41"))
        painter.setPen(QPen(QColor("#333333"), 1))
        painter.drawLine(option.rect.bottomLeft(), option.rect.bottomRight())
        painter.drawLine(option.rect.topRight(), option.rect.bottomRight())
        super().paint(painter, option, index)


class WalmartUltraUI(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Walmart 礼品卡查询终端 v13.0")
        self.resize(1400, 950)
        self.config = ConfigManager.load()
        self.worker = None
        
        # 🔥 初始化本地IP（需要在setup_ui之前初始化，因为load_ui_config会调用update_status_bar）
        self.local_ip = "获取中..."
        
        # ✅ 代理池延迟关闭定时器（用于180s延迟关闭机制）
        self.pool_shutdown_timer = None
        
        # 🔥 自动重试机制相关变量
        self.current_retry_round = 0  # 当前重试轮次
        self.is_retry_mode = False   # 是否处于重试模式

        GLOBAL_LOG.message.connect(self.log_msg)
        # 监听代理提取失败信号（从代理池线程发出）
        GLOBAL_LOG.proxy_error.connect(self.on_proxy_fetch_error)
        # 将UI实例指向全局变量，方便在代理池线程失败时回调UI
        global GLOBAL_UI
        try:
            GLOBAL_UI = self
        except Exception:
            GLOBAL_LOG.message.emit("⚠️ 无法设置 GLOBAL_UI 引用", "warning")
        self.setup_ui()
        self.apply_style()
        self.load_ui_config()

        # 代理池监控定时器
        self.pool_timer = QTimer()
        self.pool_timer.timeout.connect(self.update_pool_status)
        self.pool_timer.start(1000)
        
        # 🔥 本地IP更新定时器
        self.update_local_ip()  # 立即更新一次
        # self.ip_timer = QTimer()
        # self.ip_timer.timeout.connect(self.update_local_ip)
        # self.ip_timer.start(30000)  # 每30秒更新一次
        
        # 初始化状态栏显示
        self.update_status_bar()

    def apply_style(self):
        self.setStyleSheet("""
            * { font-family: "Microsoft YaHei", "Segoe UI"; font-size: 14px; color: #cccccc; }
            QMainWindow { background: #1e1e1e; }
            QScrollArea { border: none; background: #252526; }
            QWidget#ScrollContent { background: #252526; }

            QGroupBox {
                border: 1px solid #3e3e42; border-radius: 4px; margin-top: 10px; padding-top: 15px;
                background: #2d2d30; font-weight: bold; color: #007acc;
            }
            QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 5px; background: #2d2d30; }

            QLineEdit, QSpinBox, QComboBox {
                background: #3c3c3c; border: 1px solid #3e3e42; color: white; padding: 6px; border-radius: 3px;
            }
            /* SpinBox 特殊样式 - 修复文字看不见的问题 */
            QSpinBox {
                min-width: 80px;  /* 设置最小宽度 */
                selection-background-color: #007acc;
                selection-color: white;
            }
            QSpinBox::up-button, QSpinBox::down-button {
                subcontrol-origin: border;
                width: 20px;
                border: none;
                background: #2d2d30;
            }
            QSpinBox::up-button:hover, QSpinBox::down-button:hover {
                background: #3a3d41;
            }
            QSpinBox::up-button:pressed, QSpinBox::down-button:pressed {
                background: #007acc;
            }
            /* SpinBox 内部输入框的文字颜色 */
            QSpinBox QAbstractSpinBox {
                color: white;
            }
            /* SpinBox 内部的 QLineEdit */
            QSpinBox QLineEdit {
                background: transparent;
                border: none;
                color: white;
                padding: 0px;
            }
            /* 修复下拉框看不见的问题 */
            QComboBox QAbstractItemView {
                background-color: #3c3c3c; color: white; selection-background-color: #007acc;
            }

            QPushButton#action_btn {
                background-color: #238636; color: white; border: none; border-radius: 4px;
                font-size: 16px; font-weight: bold; padding: 10px;
            }
            QPushButton#action_btn:hover { background-color: #2ea043; }
            QPushButton#action_btn[running="true"] { background-color: #da3633; }

            QPushButton#pool_btn {
                background-color: #007acc; color: white; border: none; border-radius: 4px; 
                padding: 8px; min-width: 120px; min-height: 35px;
            }
            QPushButton#pool_btn[active="true"] { background-color: #da3633; }

            QPushButton#save_btn { 
                background-color: #3e3e42; border: 1px solid #555; border-radius: 4px;
                padding: 8px; min-width: 120px; min-height: 35px;
            }
            QPushButton#save_btn:hover { background-color: #555; }

            QPushButton.tool-btn {
                background-color: #333333; border: 1px solid #3e3e42; color: #f0f0f0; padding: 6px 12px;
                border-radius: 6px;  /* 🔥 圆角按钮 */
            }
            QPushButton.tool-btn:hover { background-color: #444444; }
            QPushButton#del_btn { background-color: #c93c37; border-color: #c93c37; }

            QTableWidget {
                background-color: #1e1e1e; border: 1px solid #333333; gridline-color: #333333;
                selection-background-color: #3a3d41; outline: none;
            }
            QHeaderView::section {
                background-color: #252526; color: #e0e0e0; padding: 8px; border: none;
                border-bottom: 1px solid #333333; border-right: 1px solid #333333; font-weight: bold;
            }
            QCheckBox::indicator { 
                width: 18px; height: 18px; border: 1px solid #666666; background: #1e1e1e; border-radius: 3px;
            }
            QCheckBox::indicator:checked { background: #007acc; border-color: #007acc; }

            QTextEdit#log { background: #1e1e1e; color: #a0a0a0; border: 1px solid #333333; font-family: Consolas; }
            QLabel#status_lbl { color: #8b949e; font-size: 12px; }
        """)

    def setup_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QHBoxLayout(central)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        # === 左侧滚动区域 ===
        scroll = QScrollArea()
        # ✅ 改进: 不使用 setFixedWidth，让 QSplitter 来控制
        scroll.setMinimumWidth(500)      # 最小宽度
        scroll.setMaximumWidth(900)      # 最大宽度，允许用户拖拽调整
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)

        sidebar = QWidget()
        sidebar.setObjectName("ScrollContent")
        side_layout = QVBoxLayout(sidebar)
        side_layout.setContentsMargins(15, 20, 15, 20)
        side_layout.setSpacing(15)

        # 1. 导入
        grp_import = QGroupBox("数据源")
        imp_layout = QVBoxLayout(grp_import)
        self.btn_import = QPushButton("📂 导入卡密文件")
        self.btn_import.setObjectName("action_btn")
        self.btn_import.clicked.connect(self.import_file)
        imp_layout.addWidget(self.btn_import)
        side_layout.addWidget(grp_import)

        # 2. 运行参数
        grp_run = QGroupBox("运行参数")
        run_layout = QFormLayout(grp_run)
        
        # 🔥 最大并发上限 (重命名并发线程)
        self.spin_thread = QSpinBox()
        self.spin_thread.setRange(1, 100)  # 🔥 扩展范围到 1-100
        self.spin_thread.setValue(10)     # 🔥 默认值改为 10
        run_layout.addRow("最大并发上限:", self.spin_thread)

        # 🔥 新增: 并发系数
        self.spin_ip_ratio = QSpinBox()
        self.spin_ip_ratio.setRange(1, 50)  # 0.1-5.0, 显示为1-50
        self.spin_ip_ratio.setValue(10)     # 默认 10 (即 1.0)
        self.spin_ip_ratio.setToolTip("每个IP对应的线程数 (值10表示1:1)")
        run_layout.addRow("并发系数:", self.spin_ip_ratio)
        
        # 🔥 新增: 最小启动水位
        self.spin_min_proxy = QSpinBox()
        self.spin_min_proxy.setRange(1, 50)
        self.spin_min_proxy.setValue(3)
        self.spin_min_proxy.setToolTip("启动任务所需的最小可用IP数")
        run_layout.addRow("最小启动水位:", self.spin_min_proxy)

        self.combo_mode = QComboBox()
        self.combo_mode.addItems(["不使用代理", "快代理"])
        self.combo_mode.currentIndexChanged.connect(self.toggle_proxy_ui)
        run_layout.addRow("代理模式:", self.combo_mode)

        self.input_sid = QLineEdit()
        self.input_sid.setPlaceholderText("SecretId")
        run_layout.addRow("SecretId:", self.input_sid)

        self.input_skey = QLineEdit()
        self.input_skey.setPlaceholderText("SecretKey")
        self.input_skey.setEchoMode(QLineEdit.EchoMode.Password)
        run_layout.addRow("SecretKey:", self.input_skey)

        # 🔥 自动重试配置
        self.spin_retry_threshold = QSpinBox()
        self.spin_retry_threshold.setRange(1, 100)
        self.spin_retry_threshold.setValue(3)
        self.spin_retry_threshold.setToolTip("失败数量达到此值时触发自动重试")
        run_layout.addRow("重试阈值:", self.spin_retry_threshold)

        self.spin_max_retry_rounds = QSpinBox()
        self.spin_max_retry_rounds.setRange(1, 10)
        self.spin_max_retry_rounds.setValue(3)
        self.spin_max_retry_rounds.setToolTip("最大自动重试轮次")
        run_layout.addRow("最大重试轮次:", self.spin_max_retry_rounds)
        
        # 🔥 新增: 并发监控标签
        self.lbl_concurrency = QLabel("实时并发: 0/0")
        self.lbl_concurrency.setStyleSheet("color: #e0e0e0; font-size: 12px;")
        run_layout.addRow("", self.lbl_concurrency)

        side_layout.addWidget(grp_run)

        # 3. 代理池配置
        self.grp_pool = QGroupBox("代理池配置")
        pool_layout = QFormLayout(self.grp_pool)

        self.spin_fetch_num = QSpinBox()
        self.spin_fetch_num.setRange(1, 200)
        pool_layout.addRow("提取数量:", self.spin_fetch_num)

        self.spin_min_ip = QSpinBox()
        self.spin_min_ip.setRange(1, 100)
        pool_layout.addRow("最小可用:", self.spin_min_ip)

        self.spin_expire = QSpinBox()
        self.spin_expire.setRange(5, 300)
        pool_layout.addRow("过期阈值(秒):", self.spin_expire)

        self.spin_check = QSpinBox()
        self.spin_check.setRange(5, 60)
        pool_layout.addRow("检查间隔(秒):", self.spin_check)
        side_layout.addWidget(self.grp_pool)

        # 4. 代理池控制（参考图2，简化版）
        self.grp_ctrl = QGroupBox("代理池控制")
        ctrl_layout = QVBoxLayout(self.grp_ctrl)

        # 按钮布局（水平排列）
        btn_layout = QHBoxLayout()
        btn_layout.setSpacing(10)
        btn_layout.setContentsMargins(0, 0, 0, 0)
        
        self.btn_pool = QPushButton("启动代理池")
        self.btn_pool.setObjectName("pool_btn")
        self.btn_pool.clicked.connect(self.toggle_proxy_pool)
        btn_layout.addWidget(self.btn_pool)

        self.btn_save = QPushButton("💾 保存配置")
        self.btn_save.setObjectName("save_btn")
        self.btn_save.clicked.connect(self.save_config)
        btn_layout.addWidget(self.btn_save)
        
        ctrl_layout.addLayout(btn_layout)
        side_layout.addWidget(self.grp_ctrl)

        # 5. 任务控制（参考图3）
        grp_task = QGroupBox("任务控制")
        task_layout = QVBoxLayout(grp_task)
        
        self.btn_task = QPushButton("▶ 开始查询")
        self.btn_task.setObjectName("action_btn")
        self.btn_task.setMinimumHeight(50)
        self.btn_task.clicked.connect(self.toggle_task)
        task_layout.addWidget(self.btn_task)

        self.progress = QProgressBar()
        self.progress.setValue(0)
        self.progress.setFormat("%p%")
        task_layout.addWidget(self.progress)
        
        side_layout.addWidget(grp_task)

        side_layout.addStretch()
        
        # 🔥 左下角状态栏（参考图3）
        status_bar = QFrame()
        status_bar.setFrameShape(QFrame.Shape.StyledPanel)
        status_bar.setStyleSheet("background: #252526; border-top: 1px solid #3e3e42; padding: 8px;")
        status_layout = QHBoxLayout(status_bar)
        status_layout.setContentsMargins(10, 5, 10, 5)
        status_layout.setSpacing(15)
        
        self.lbl_local_ip = QLabel("本地IP: 获取中...")
        self.lbl_local_ip.setStyleSheet("color: #8b949e; font-size: 12px;")
        status_layout.addWidget(self.lbl_local_ip)
        
        # 分隔符
        separator1 = QFrame()
        separator1.setFrameShape(QFrame.Shape.VLine)
        separator1.setFrameShadow(QFrame.Shadow.Sunken)
        separator1.setStyleSheet("color: #3e3e42;")
        status_layout.addWidget(separator1)
        
        self.lbl_proxy_status = QLabel("代理: 未启用")
        self.lbl_proxy_status.setStyleSheet("color: #8b949e; font-size: 12px;")
        status_layout.addWidget(self.lbl_proxy_status)
        
        # 分隔符
        separator2 = QFrame()
        separator2.setFrameShape(QFrame.Shape.VLine)
        separator2.setFrameShadow(QFrame.Shadow.Sunken)
        separator2.setStyleSheet("color: #3e3e42;")
        status_layout.addWidget(separator2)
        
        self.lbl_available_proxy = QLabel("可用代理: 0")
        self.lbl_available_proxy.setStyleSheet("color: #8b949e; font-size: 12px;")
        status_layout.addWidget(self.lbl_available_proxy)
        
        status_layout.addStretch()
        side_layout.addWidget(status_bar)
        
        scroll.setWidget(sidebar)

        # === 右侧内容 ===
        content = QWidget()
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(20, 20, 20, 20)
        content_layout.setSpacing(10)

        # 工具栏
        toolbar = QWidget()
        tb_layout = QHBoxLayout(toolbar)
        tb_layout.setContentsMargins(0, 0, 0, 0)
        tb_layout.setSpacing(8)

        lbl_res = QLabel("查询结果")
        lbl_res.setStyleSheet("font-size: 16px; font-weight: bold; color: #e0e0e0;")
        tb_layout.addWidget(lbl_res)
        tb_layout.addSpacing(20)

        # 恢复所有工具按钮
        for text, func, style in [
            ("💾 导入缓存", self.import_cache, ""),
            ("📤 导出缓存", self.export_cache, ""),
            ("🗑️ 清空缓存", self.clear_cache, "del_btn"),
            ("全选", lambda: self.set_sel("all"), ""),
            ("反选", lambda: self.set_sel("inv"), ""),
            ("选中失败", lambda: self.set_sel("failed"), ""),
            ("选中未使用", lambda: self.set_sel("valid"), ""),
            ("去重", self.dedup, ""),
            ("导出选中", self.export, ""),
            ("删除选中", self.delete, "del_btn")
        ]:
            btn = QPushButton(text)
            btn.setProperty("class", "tool-btn")
            if style: btn.setObjectName(style)
            btn.clicked.connect(func)
            tb_layout.addWidget(btn)

        tb_layout.addStretch()
        content_layout.addWidget(toolbar)

        # � 使用 QSplitter 让表格和日志框可以调整大小
        splitter = QSplitter(Qt.Orientation.Vertical)

        # 表格
        self.table = QTableWidget()
        self.table.setColumnCount(8)
        self.table.setHorizontalHeaderLabels(["序号", "选", "券码", "密码", "面值", "状态", "时间", "备注"])
        self.table.setColumnWidth(0, 50)
        self.table.setColumnWidth(1, 40)
        self.table.setColumnWidth(2, 200)
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.verticalHeader().setDefaultSectionSize(40)
        self.table.verticalHeader().setVisible(False)
        self.table.setItemDelegate(ReferenceStyleDelegate())
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setShowGrid(False)
        splitter.addWidget(self.table)

        # 日志（可调整大小）
        self.log_view = QTextEdit()
        self.log_view.setObjectName("log")
        self.log_view.setReadOnly(True)
        self.log_view.setMinimumHeight(100)  # 最小高度
        splitter.addWidget(self.log_view)
        
        # 🔥 设置分割比例（表格占70%，日志占30%）
        splitter.setStretchFactor(0, 7)
        splitter.setStretchFactor(1, 3)
        splitter.setSizes([700, 300])  # 初始大小
        
        content_layout.addWidget(splitter)
        
        # 🔥 统计面板（放置在日志框下方）
        stats_frame = QFrame()
        stats_frame.setFixedHeight(35)
        stats_frame.setStyleSheet("""
            QFrame {
                background-color: #2d2d30;
                border-top: 1px solid #444;
            }
        """)
        stats_layout = QHBoxLayout(stats_frame)
        stats_layout.setContentsMargins(10, 5, 10, 5)
        
        self.lbl_stats = QLabel("📊 查询总数: 0  |  查询成功: 0  |  查询失败: 0  |  未使用: 0")
        self.lbl_stats.setStyleSheet("color: #e0e0e0; font-size: 12px;")
        stats_layout.addWidget(self.lbl_stats)
        stats_layout.addStretch()
        
        content_layout.addWidget(stats_frame)

        # ✅ 使用 QSplitter 替换直接的 addWidget，提高布局稳定性
        main_splitter = QSplitter(Qt.Orientation.Horizontal)
        main_splitter.addWidget(scroll)        # 左侧配置面板
        main_splitter.addWidget(content)       # 右侧日志和表格
        
        # 设置初始大小比例 (左侧700px, 右侧占剩余空间)
        main_splitter.setSizes([700, 600])
        
        # 设置拉伸因子 (左侧固定, 右侧可伸缩)
        main_splitter.setStretchFactor(0, 0)   # 左侧不可伸缩
        main_splitter.setStretchFactor(1, 1)   # 右侧可伸缩
        
        # 分割线配置
        main_splitter.setCollapsible(0, False)  # 左侧不可折叠
        main_splitter.setCollapsible(1, False)  # 右侧不可折叠
        main_splitter.setHandleWidth(5)         # 分割线宽度 5px
        
        main_layout.addWidget(main_splitter)

    def load_ui_config(self):
        c = self.config
        self.spin_thread.setValue(c.get('thread_count', 1))
        proxy_mode = c.get('proxy_mode', 0)
        self.combo_mode.setCurrentIndex(proxy_mode)
        # 🔥 确保配置中的代理模式与UI一致
        self.config['proxy_mode'] = proxy_mode
        self.input_sid.setText(c.get('secret_id', ''))
        self.input_skey.setText(c.get('secret_key', ''))
        self.spin_fetch_num.setValue(c.get('fetch_num', 10))
        self.spin_min_ip.setValue(c.get('min_available', 10))
        self.spin_expire.setValue(c.get('expire_threshold', 30))
        self.spin_check.setValue(c.get('fetch_interval', 10))
        self.toggle_proxy_ui()

    def save_config(self):
        new_conf = {
            "thread_count": self.spin_thread.value(),
            "proxy_mode": self.combo_mode.currentIndex(),
            "secret_id": self.input_sid.text().strip(),
            "secret_key": self.input_skey.text().strip(),
            "fetch_num": self.spin_fetch_num.value(),
            "min_available": self.spin_min_ip.value(),
            "expire_threshold": self.spin_expire.value(),
            "clean_interval": 30,
            "fetch_interval": self.spin_check.value()
        }
        if ConfigManager.save(new_conf):
            self.config = new_conf
            self.log_msg("💾 配置已保存", "success")
        else:
            self.log_msg("❌ 配置保存失败", "error")
    
    def _save_config_silent(self):
        """静默保存配置（不显示提示）"""
        new_conf = {
            "thread_count": self.spin_thread.value(),
            "proxy_mode": self.combo_mode.currentIndex(),
            "secret_id": self.input_sid.text().strip(),
            "secret_key": self.input_skey.text().strip(),
            "fetch_num": self.spin_fetch_num.value(),
            "min_available": self.spin_min_ip.value(),
            "expire_threshold": self.spin_expire.value(),
            "clean_interval": 30,
            "fetch_interval": self.spin_check.value()
        }
        if ConfigManager.save(new_conf):
            self.config = new_conf

    def toggle_proxy_ui(self):
        enabled = self.combo_mode.currentIndex() == 1
        self.input_sid.setEnabled(enabled)
        self.input_skey.setEnabled(enabled)
        self.grp_pool.setEnabled(enabled)
        self.grp_ctrl.setEnabled(enabled)
        # 🔥 更新配置中的代理模式（确保状态栏显示正确）
        self.config['proxy_mode'] = self.combo_mode.currentIndex()
        # 更新状态栏
        if hasattr(self, 'update_status_bar'):
            self.update_status_bar()

    def toggle_proxy_pool(self):
        global GLOBAL_PROXY_POOL
        if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
            GLOBAL_PROXY_POOL.stop()
            self.btn_pool.setText("启动代理池")
            self.btn_pool.setProperty("active", False)
        else:
            # 🔥 先保存配置，确保使用最新配置
            self.save_config()
            # 🔥 重新加载配置，确保代理池使用最新配置
            self.config = ConfigManager.load()
            
            if self.config['proxy_mode'] == 1:
                if not self.config['secret_id']:
                    self.log_msg("❌ 请先填写 SecretId", "error")
                    return
                # 🔥 使用最新配置创建代理池
                GLOBAL_PROXY_POOL = EnhancedProxyPool(self.config)
                GLOBAL_PROXY_POOL.start()
                self.btn_pool.setText("停止代理池")
                self.btn_pool.setProperty("active", True)
                # 验证代理池是否成功启动（2秒后检查）
                try:
                    QTimer.singleShot(2000, self._verify_pool_started)
                except Exception:
                    pass
            else:
                self.log_msg("⚠️ 请先选择快代理模式", "warning")

        self.btn_pool.style().unpolish(self.btn_pool)
        self.btn_pool.style().polish(self.btn_pool)
        # 更新状态栏
        self.update_status_bar()

    def update_pool_status(self):
        """更新代理池状态（已移除统计信息显示）"""
        # 更新状态栏的代理信息
        self.update_status_bar()

    def _verify_pool_started(self):
        """在短延迟后验证代理池是否成功启动并已提取IP；失败则回滚UI并提示用户"""
        global GLOBAL_PROXY_POOL
        # 如果没有代理池或者代理池未运行，则视为启动失败
        if not (GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running):
            self.on_proxy_fetch_error("代理池未能正确启动或被停止")
            return

        # 如果运行，但没有提取到任何IP（fetched == 0 且 available == 0），则也视为失败
        status = GLOBAL_PROXY_POOL.get_status()
        stats = status.get('stats', {})
        fetched = stats.get('fetched', 0)
        available = status.get('available', 0)
        if fetched == 0 and available == 0:
            self.on_proxy_fetch_error("代理池启动成功，但未提取到任何代理")

    def on_proxy_fetch_error(self, reason: str):
        """
        在代理池线程检测到 _fetch 失败时被调用（在主线程中执行），负责停止查询任务、停止代理池并更新UI。
        """
        # 记录日志
        self.log_msg(f"❌ 代理池提取失败，原因: {reason}", "error")

        # 如果存在正在运行的工作线程，则停止它
        if self.worker and getattr(self.worker, 'isRunning', lambda: False)():
            try:
                self.log_msg("⏹️ 代理提取失败，正在停止当前查询任务...", "warning")
                self.worker.stop()
                self.btn_task.setText("正在停止...")
                self.btn_task.setEnabled(False)
            except Exception as e:
                logger.debug(f"⚠️ 停止工作线程时异常: {e}")

        # 停止代理池（如果仍在运行）并更新按钮状态
        global GLOBAL_PROXY_POOL
        if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
            try:
                GLOBAL_PROXY_POOL.stop()
            except Exception:
                pass
        
        # 无论如何都要更新按钮状态（无论 pool 是否真的停止了）
        self.btn_pool.setText("启动代理池")
        self.btn_pool.setProperty("active", False)
        self.btn_pool.style().unpolish(self.btn_pool)
        self.btn_pool.style().polish(self.btn_pool)
        
        # 清除全局池引用
        GLOBAL_PROXY_POOL = None

        # 更新状态栏
        self.update_status_bar()
    
    def update_local_ip(self):
        """更新本地IP"""
        import requests as r
        try:
            response = r.get("https://api.ipify.org?format=json", timeout=5)
            if response.status_code == 200:
                self.local_ip = response.json().get("ip", "未知")
            else:
                self.local_ip = "获取失败"
        except Exception as e:
            self.local_ip = "网络异常"
            self.log_msg(f"⚠️ 网络异常: {e}", "warning")
        self.update_status_bar()
    
    def update_status_bar(self):
        """更新左下角状态栏"""
        # 🔥 检查属性是否存在（防止初始化顺序问题）
        if not hasattr(self, 'lbl_local_ip') or not hasattr(self, 'local_ip'):
            return
        
        # 更新本地IP
        self.lbl_local_ip.setText(f"本地IP: {self.local_ip}")
        
        # 更新代理状态
        proxy_mode = self.config.get('proxy_mode', 0)
        if proxy_mode == 0:
            proxy_text = "未启用"
            proxy_color = "#888"
        else:
            if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
                proxy_text = "快代理（运行中）"
                proxy_color = "#FFD54F"
            else:
                proxy_text = "快代理（未启动）"
                proxy_color = "#888"
        
        self.lbl_proxy_status.setText(f"代理: {proxy_text}")
        self.lbl_proxy_status.setStyleSheet(f"color: {proxy_color}; font-size: 12px;")
        
        # 更新可用代理数
        if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
            available = GLOBAL_PROXY_POOL.get_status()['available']
            self.lbl_available_proxy.setText(f"可用代理: {available}")
        else:
            self.lbl_available_proxy.setText("可用代理: 0")

    def toggle_task(self):
        """
        切换任务状态 - 开始/停止查询
        """
        global GLOBAL_PROXY_POOL
        
        if self.worker and self.worker.isRunning():
            # 停止正在运行的任务
            self.worker.stop()
            self.btn_task.setText("正在停止...")
            self.btn_task.setEnabled(False)
        else:
            # 静默保存配置
            self._save_config_silent()
            
            # ✅ 【取消延迟关闭】如果正在倒计时关闭代理池，则取消
            self._cancel_delayed_pool_shutdown()
            
            # ✅ 【检查代理池】如果启用代理模式，需要先启动代理池
            if self.config['proxy_mode'] == 1 and (not GLOBAL_PROXY_POOL or not GLOBAL_PROXY_POOL.is_running):
                self.log_msg("❌ 已选择快代理模式，但代理池未启动", "error")
                self.log_msg("💡 请先点击 '启动代理池' 按钮启动代理池，然后再进行查询", "warning")
                return
            
            # 收集勾选的任务
            tasks = []
            checked_count = 0
            checked_statuses = {}
            
            for r in range(self.table.rowCount()):
                chk_widget = self.table.cellWidget(r, TableColumnIndex.CHECKBOX)
                if not chk_widget:
                    continue
                
                chk = chk_widget.findChild(QCheckBox)
                if chk and chk.isChecked():
                    checked_count += 1
                    
                    # 获取状态
                    status_item = self.table.item(r, TableColumnIndex.STATUS)
                    status = status_item.text() if status_item else ""
                    checked_statuses[status] = checked_statuses.get(status, 0) + 1
                    
                    # 只处理可查询的状态
                    if status in ["待查询", "网络异常", "CV识别失败", "滑块验证失败", "查询失败"]:
                        card_item = self.table.item(r, TableColumnIndex.CARD)
                        card = card_item.text() if card_item else ""
                        if card:
                            tasks.append({"row": r, "card": card})
            
            if not tasks:
                if checked_count == 0:
                    self.log_msg("⚠️ 无待处理任务：请先勾选要查询的行", "warning")
                else:
                    status_info = "、".join([f"{k}({v}条)" for k, v in checked_statuses.items()])
                    self.log_msg(f"⚠️ 无待处理任务：已勾选的 {checked_count} 行状态为 {status_info}，"
                               f"只有状态为'待查询'、'网络异常'等的行才会被处理", "warning")
                
                # 【清理代理池】无待处理任务时也要清理代理池资源
                if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
                    self.log_msg("🧹 清理代理池资源...", "info")
                    GLOBAL_PROXY_POOL.stop()
                    self.log_msg("✅ 代理池已清理", "success")
                
                return
            
            # 更新UI
            self.btn_task.setText("⏹ 停止任务")
            self.btn_task.setProperty("running", True)
            self.btn_task.style().unpolish(self.btn_task)
            self.btn_task.style().polish(self.btn_task)
            self.btn_import.setEnabled(False)
            
            # 创建工作线程
            conf = self.config.copy()
            conf['use_proxy'] = (conf['proxy_mode'] == 1)
            
            self.worker = WalmartWorker(tasks, conf)
            self.worker.log_signal.connect(self.log_msg)
            self.worker.progress_signal.connect(self.progress.setValue)
            self.worker.result_signal.connect(self.update_row)
            self.worker.finished_signal.connect(self.finish_task)
            self.worker.start()
            
            # 重置查询统计信息
            self.lbl_stats.setText("📊 查询总数: 0  |  查询失败: 0  |  未使用: 0")
            
            self.log_msg(f"🚀 开始查询 {len(tasks)} 张卡", "success")

    def finish_task(self):
        """
        任务完成处理 - 支持自动重试机制
        
        递归调度状态机:
        1. 检查轮次限制
        2. 统计失败数
        3. 条件判定并决定是否重试或结束
        """
        global GLOBAL_PROXY_POOL
        
        # 🔥 检查是否被手动停止（用户点击停止按钮）
        if self.worker and not self.worker.running:
            # 用户手动停止，重置重试状态并正常结束
            self._reset_retry_state()
            self._cleanup_task()
            self.log_msg("⏹️ 任务已被用户停止", "warning")
            return
        
        # 获取配置
        retry_threshold = self.spin_retry_threshold.value()
        max_retry_rounds = self.spin_max_retry_rounds.value()
        
        # 【步骤1】检查轮次限制
        if self.current_retry_round >= max_retry_rounds:
            # 已达到最大重试轮次，结束任务
            self.log_msg(f"⚠️ 已达到最大重试轮次 ({max_retry_rounds} 轮)，停止自动重试", "warning")
            self._reset_retry_state()
            self._cleanup_task()
            return
        
        # 【步骤2】扫描失败任务
        failed_tasks = self._get_failed_tasks()
        failed_count = len(failed_tasks)
        
        self.log_msg(f"📊 当前轮次: {self.current_retry_round + 1}/{max_retry_rounds} | 失败数量: {failed_count}", "info")
        
        # 【步骤3】条件判定
        if failed_count >= retry_threshold:
            # 失败数达到阈值，启动自动重试
            self.current_retry_round += 1
            self.is_retry_mode = True
            
            self.log_msg(f"🔄 检测到 {failed_count} 个失败券码，达到重试阈值，开始第 {self.current_retry_round} 轮自动重试...", "warning")
            
            # 🔥 取消代理池延迟关闭（保持代理池运行）
            self._cancel_delayed_pool_shutdown()
            
            # 🔥 确保代理池在运行
            if GLOBAL_PROXY_POOL and not GLOBAL_PROXY_POOL.is_running:
                GLOBAL_PROXY_POOL.start()
                self.log_msg("🚀 代理池已重新启动", "info")
            
            # 重新启动 Worker 进行重试
            conf = self.config.copy()
            conf['use_proxy'] = (conf['proxy_mode'] == 1)
            
            self.worker = WalmartWorker(failed_tasks, conf)
            self.worker.log_signal.connect(self.log_msg)
            self.worker.progress_signal.connect(self.progress.setValue)
            self.worker.result_signal.connect(self.update_row)
            self.worker.finished_signal.connect(self.finish_task)
            self.worker.start()
            
            # 🔥 重置进度条（基于当前失败任务数）
            self.progress.setValue(0)
            
        else:
            # 失败数低于阈值，正常结束
            self.log_msg(f"✅ 失败数量 ({failed_count}) 低于重试阈值 ({retry_threshold})，无需重试", "success")
            self._reset_retry_state()
            self._cleanup_task()

    def _reset_retry_state(self):
        """重置重试状态"""
        self.current_retry_round = 0
        self.is_retry_mode = False
        self.log_msg("🔄 重试状态已重置", "info")

    def _cleanup_task(self):
        """清理任务资源"""
        self.btn_task.setText("▶ 开始查询")
        self.btn_task.setProperty("running", False)
        self.btn_task.setEnabled(True)
        self.btn_task.style().unpolish(self.btn_task)
        self.btn_task.style().polish(self.btn_task)
        self.btn_import.setEnabled(True)
        
        # 重置代理池按钮状态
        self.btn_pool.setText("启动代理池")
        self.btn_pool.setProperty("active", False)
        self.btn_pool.style().unpolish(self.btn_pool)
        self.btn_pool.style().polish(self.btn_pool)
        
        # 更新统计信息
        self.update_stats()
        
        # ✅ 【代理池延迟关闭】不立即停止代理池，而是180秒后关闭
        global GLOBAL_PROXY_POOL
        if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
            self.log_msg("⏱️ 任务完成！180秒后自动关闭代理池，如需继续查询请立即选择并点击开始查询", "info")
            # 启动 180 秒延迟关闭定时器
            self._schedule_pool_shutdown(180)
        
        self.log_msg("🎉 任务完成", "success")

    def _schedule_pool_shutdown(self, delay_seconds: int):
        """
        安排代理池延迟关闭
        
        参数:
            delay_seconds (int): 延迟秒数
        """
        # 如果已有定时器在运行，先取消
        self._cancel_delayed_pool_shutdown()
        
        # 创建新的定时器
        self.pool_shutdown_timer = QTimer()
        self.pool_shutdown_timer.setSingleShot(True)
        self.pool_shutdown_timer.timeout.connect(self._do_pool_shutdown)
        self.pool_shutdown_timer.start(delay_seconds * 1000)  # 转换为毫秒
        
        logger.info(f"⏱️ 代理池将在 {delay_seconds} 秒后自动关闭")

    def _cancel_delayed_pool_shutdown(self):
        """取消已安排的代理池延迟关闭"""
        if self.pool_shutdown_timer and self.pool_shutdown_timer.isActive():
            self.pool_shutdown_timer.stop()
            self.pool_shutdown_timer = None
            logger.info("✅ 取消了代理池的延迟关闭")

    def _do_pool_shutdown(self):
        """执行代理池关闭"""
        global GLOBAL_PROXY_POOL
        if GLOBAL_PROXY_POOL and GLOBAL_PROXY_POOL.is_running:
            self.log_msg("🧹 180秒已过，自动关闭代理池...", "info")
            GLOBAL_PROXY_POOL.stop()
            self.log_msg("✅ 代理池已关闭", "success")
        self.pool_shutdown_timer = None

    # --- 辅助函数 ---
    
    def _get_checkbox(self, row: int) -> Optional[QCheckBox]:
        """
        安全地获取表格中的复选框
        
        参数:
            row (int): 行号
            
        返回: QCheckBox 或 None
        """
        try:
            widget = self.table.cellWidget(row, TableColumnIndex.CHECKBOX)
            if widget:
                chk = widget.findChild(QCheckBox)
                return chk
        except Exception as e:
            logger.debug(f"⚠️ 获取复选框失败 (行{row}): {e}")
        return None

    def _get_failed_tasks(self) -> List[Dict]:
        """
        扫描表格，获取所有失败且已勾选的任务
        
        返回: List[Dict] - 失败任务列表 [{"row": int, "card": str, "pin": str}, ...]
        """
        # 定义失败状态集（可重试的失败状态）
        failed_statuses = {
            "网络异常", "滑块验证失败", "验证超时", 
            "查询超时", "查询异常", "CV识别失败", "无效卡"
        }
        
        failed_tasks = []
        
        for r in range(self.table.rowCount()):
            # 检查是否勾选
            chk_widget = self.table.cellWidget(r, TableColumnIndex.CHECKBOX)
            if not chk_widget:
                continue
            
            chk = chk_widget.findChild(QCheckBox)
            if not chk or not chk.isChecked():
                continue
            
            # 检查状态是否为失败状态
            status_item = self.table.item(r, TableColumnIndex.STATUS)
            status_text = status_item.text() if status_item else ""
            
            if status_text in failed_statuses:
                card_item = self.table.item(r, TableColumnIndex.CARD)
                card = card_item.text() if card_item else ""
                
                if card:
                    failed_tasks.append({
                        "row": r,
                        "card": card
                    })
        
        return failed_tasks

    def log_msg(self, text: str, level: str = "info"):
        """
        输出日志消息到日志框
        
        参数:
            text (str): 消息内容
            level (str): 消息级别 (info/success/error/warning)
        """
        colors = {
            "success": "#2ea043",
            "error": "#f85149",
            "warning": "#d29922",
            "info": "#58a6ff"
        }
        now = datetime.now().strftime("%H:%M:%S")
        color = colors.get(level, "#ccc")
        html = f'<span style="color:#8b949e">[{now}]</span> <span style="color:{color}">{text}</span>'
        self.log_view.append(html)
        self.log_view.verticalScrollBar().setValue(self.log_view.verticalScrollBar().maximum())

    def update_stats(self):
        """
        更新查询统计信息
        统计：查询总数、查询成功、查询失败、未使用
        
        指标定义:
        - 查询总数: 表格中所有行的总数
        - 查询成功: 网络请求正常返回的次数(无论卡片是有效、无效还是已使用)
        - 查询失败: 因网络超时、代理失效、滑块被拦截等导致的异常次数
        - 未使用: 最终状态确认为"未使用"的卡片总数
        """
        total = self.table.rowCount()
        success = 0
        failed = 0
        valid = 0
        
        # 失败状态列表（网络异常或验证失败）
        failed_statuses = ["网络异常", "滑块验证失败", "验证超时", "查询失败", "查询超时", "查询异常", "CV识别失败", "无效卡"]
        
        # 成功状态列表（网络请求正常返回，获得了明确状态）
        success_statuses = ["未使用", "已使用", "无效卡"]
        
        for r in range(self.table.rowCount()):
            status_item = self.table.item(r, TableColumnIndex.STATUS)
            status_text = status_item.text() if status_item else ""
            
            if status_text in failed_statuses:
                failed += 1
                success += 0  # 失败不计入成功
            elif status_text in success_statuses:
                success += 1
                if status_text == "未使用":
                    valid += 1
            # "待查询"状态不计入成功或失败
        
        # 更新标签文本
        self.lbl_stats.setText(f"📊 查询总数: {total}  |  查询成功: {success}  |  查询失败: {failed}  |  未使用: {valid}")


    def update_row(self, row: int, data: Dict):
        """
        更新表格行的查询结果
        
        参数:
            row (int): 行号
            data (Dict): 结果数据 {"status": str, "balance": str, "msg": str}
        """
        try:
            if row < 0 or row >= self.table.rowCount():
                logger.warning(f"⚠️ 行号越界: {row}")
                return
            
            # 安全地更新每个单元格
            balance_item = self.table.item(row, TableColumnIndex.BALANCE)
            if balance_item:
                balance_item.setText(data.get("balance", "-"))
            
            status_item = self.table.item(row, TableColumnIndex.STATUS)
            if status_item:
                status_item.setText(data.get("status", ""))
            
            msg_item = self.table.item(row, TableColumnIndex.MSG)
            if msg_item:
                msg_item.setText(data.get("msg", ""))
            
            time_item = self.table.item(row, TableColumnIndex.TIME)
            if time_item:
                time_item.setText(datetime.now().strftime("%H:%M:%S"))
            
            # 根据状态设置颜色
            status = data.get("status", "")
            color_map = {
                "未使用": QColor("#2ea043"),        # 绿色
                "已使用": QColor("#d29922"),        # 橙色
                "无效卡": QColor("#f85149"),        # 红色
                "网络异常": QColor("#858585"),      # 灰色
                "查询失败": QColor("#858585"),      # 灰色
                "验证超时": QColor("#858585"),      # 灰色
                "查询超时": QColor("#858585"),      # 灰色
                "查询异常": QColor("#858585"),      # 灰色
                "滑块验证失败": QColor("#f85149"),  # 红色
                "CV识别失败": QColor("#f85149"),    # 红色
            }
            color = color_map.get(status, QColor("#58a6ff"))
            
            for col_idx in [TableColumnIndex.BALANCE, TableColumnIndex.STATUS, TableColumnIndex.MSG]:
                item = self.table.item(row, col_idx)
                if item:
                    item.setForeground(color)
            
            # 更新统计信息
            self.update_stats()
            
            logger.debug(f"✓ [行{row}] 表格更新完成: {status}")
        
        except Exception as e:
            logger.error(f"❌ 表格更新失败: {e}")
            logger.debug(traceback.format_exc())

    def set_sel(self, mode: str):
        """
        表格行选择操作
        
        参数:
            mode (str): 操作模式
              - 'all': 全选
              - 'inv': 反选
              - 'valid': 选中未使用的卡
              - 'failed': 选中失败的卡
        """
        for r in range(self.table.rowCount()):
            chk = self._get_checkbox(r)
            if not chk:
                continue
            
            status_item = self.table.item(r, TableColumnIndex.STATUS)
            status_text = status_item.text() if status_item else ""
            
            if mode == "all":
                chk.setChecked(True)
            elif mode == "inv":
                chk.setChecked(not chk.isChecked())
            elif mode == "valid":
                # 选中未使用的卡
                chk.setChecked(status_text == "未使用")
            elif mode == "failed":
                # 选中所有失败状态的卡
                chk.setChecked(status_text in ["网络异常", "滑块验证失败", "验证超时", "查询失败", "查询超时", "查询异常", "CV识别失败", "无效卡"])

    def delete(self):
        """删除选中的行"""
        rows_to_delete = []
        for r in range(self.table.rowCount()):
            chk = self._get_checkbox(r)
            if chk and chk.isChecked():
                rows_to_delete.append(r)
        
        if not rows_to_delete:
            self.log_msg("⚠️ 请先选择要删除的行", "warning")
            return
        
        # 从后向前删除（避免行号变化）
        for r in sorted(rows_to_delete, reverse=True):
            self.table.removeRow(r)
        
        # 刷新序号
        self._refresh_table_sequence()
        self.log_msg(f"✅ 已删除 {len(rows_to_delete)} 条记录", "success")

    def dedup(self):
        """去重操作 - 删除重复的卡号"""
        seen_cards = set()
        rows_to_remove = []
        
        for r in range(self.table.rowCount()):
            card_item = self.table.item(r, TableColumnIndex.CARD)
            card = card_item.text() if card_item else ""
            
            if card in seen_cards:
                rows_to_remove.append(r)
            else:
                seen_cards.add(card)
        
        # 从后向前删除
        for r in sorted(rows_to_remove, reverse=True):
            self.table.removeRow(r)
        
        # 刷新序号
        self._refresh_table_sequence()
        self.log_msg(f"✅ 已去重 {len(rows_to_remove)} 条", "success")

    def _refresh_table_sequence(self):
        """刷新表格序号列"""
        for r in range(self.table.rowCount()):
            seq_item = QTableWidgetItem(str(r + 1))
            seq_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(r, TableColumnIndex.SEQ, seq_item)

    def export(self):
        """导出选中的行为Excel"""
        data = []
        for r in range(self.table.rowCount()):
            chk_widget = self.table.cellWidget(r, TableColumnIndex.CHECKBOX)
            if chk_widget:
                chk = chk_widget.findChild(QCheckBox)
                if chk and chk.isChecked():
                    card_item = self.table.item(r, TableColumnIndex.CARD)
                    pin_item = self.table.item(r, TableColumnIndex.PIN)
                    balance_item = self.table.item(r, TableColumnIndex.BALANCE)
                    status_item = self.table.item(r, TableColumnIndex.STATUS)
                    msg_item = self.table.item(r, TableColumnIndex.MSG)
                    
                    data.append({
                        "序号": str(r + 1),
                        "券码": card_item.text() if card_item else "",
                        "密码": pin_item.text() if pin_item else "",
                        "面值": balance_item.text() if balance_item else "",
                        "状态": status_item.text() if status_item else "",
                        "备注": msg_item.text() if msg_item else ""
                    })
        
        if not data:
            self.log_msg("⚠️ 没有选中任何数据", "warning")
            return
        
        path, _ = QFileDialog.getSaveFileName(
            self,
            "保存导出文件",
            f"Walmart_{datetime.now().strftime('%Y%m%d_%H%M%S')}.xlsx",
            "Excel Files (*.xlsx)"
        )
        
        if path:
            try:
                pd.DataFrame(data).to_excel(path, index=False)
                self.log_msg(f"💾 导出成功: {path}", "success")
            except Exception as e:
                self.log_msg(f"❌ 导出失败: {e}", "error")

    def import_file(self):
        """
        导入卡密文件 - 高性能版本
        
        性能优化:
        - 禁用表格更新(setUpdatesEnabled)
        - 预分配内存(setRowCount)
        - 阻塞信号(blockSignals)
        预期: 3000条数据导入 < 2秒
        """
        path, _ = QFileDialog.getOpenFileName(self, "选择文件", "", "支持格式 (*.txt *.xlsx *.xls)")
        if not path:
            return
        
        self.log_msg(f"📂 正在导入: {os.path.basename(path)}", "info")
        
        try:
            cards = SmartImporter.parse_file(path)
            
            if not cards:
                self.log_msg(f"❌ 导入失败：未找到有效的卡密数据", "error")
                return
            
            total = len(cards)
            start_row = self.table.rowCount()
            
            # 🔥【性能优化1】禁用表格更新和信号
            self.table.setUpdatesEnabled(False)
            self.table.blockSignals(True)
            
            # 🔥【性能优化2】预分配内存 - 一次性设置行数
            self.table.setRowCount(start_row + total)
            
            # 填充数据
            for i, card_data in enumerate(cards):
                r = start_row + i
                
                # 【列0】序号
                seq_item = QTableWidgetItem(str(r + 1))
                seq_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                self.table.setItem(r, TableColumnIndex.SEQ, seq_item)
                
                # 【列1】复选框
                chk_widget = QWidget()
                chk_layout = QHBoxLayout(chk_widget)
                chk_layout.setContentsMargins(0, 0, 0, 0)
                chk_layout.setAlignment(Qt.AlignmentFlag.AlignCenter)
                chk = QCheckBox()
                chk.setChecked(True)
                chk_layout.addWidget(chk)
                self.table.setCellWidget(r, TableColumnIndex.CHECKBOX, chk_widget)
                
                # 【列2】卡号
                card_item = QTableWidgetItem(card_data.get("card", ""))
                self.table.setItem(r, TableColumnIndex.CARD, card_item)
                
                # 【列3】密码
                pin_item = QTableWidgetItem(card_data.get("pin", ""))
                self.table.setItem(r, TableColumnIndex.PIN, pin_item)
                
                # 【列4-7】初始化为空或待查询
                for col_idx, default_val in [
                    (TableColumnIndex.BALANCE, "-"),
                    (TableColumnIndex.STATUS, "待查询"),
                    (TableColumnIndex.TIME, "-"),
                    (TableColumnIndex.MSG, "")
                ]:
                    item = QTableWidgetItem(default_val)
                    if col_idx == TableColumnIndex.STATUS:
                        item.setForeground(QColor("#58a6ff"))  # 蓝色待查询
                    self.table.setItem(r, col_idx, item)
                
                # ✅ 【进度提示】每导入 100 行更新一次进度提示
                if (i + 1) % 100 == 0 or (i + 1) == total:
                    self.log_msg(f"⏳ 已导入 {i + 1}/{total} 条数据...", "info")
                    QApplication.processEvents()  # 保持 UI 响应
            
            # 🔥【性能优化3】重新启用更新和信号
            self.table.blockSignals(False)
            self.table.setUpdatesEnabled(True)
            # 强制表格重新绘制
            self.table.viewport().update()
            self.table.scrollToTop()  # 滚动到顶部
            
            self.log_msg(f"✅ 成功导入 {len(cards)} 条卡密数据", "success")
        
        except Exception as e:
            # ✅ 确保发生错误时也重新启用更新和信号
            self.table.blockSignals(False)
            self.table.setUpdatesEnabled(True)
            logger.error(f"❌ 导入异常: {e}")
            logger.debug(traceback.format_exc())
            self.log_msg(f"❌ 导入异常: {str(e)[:50]}", "error")
    
    # ========== 缓存管理方法 ==========
    
    def import_cache(self):
        """导入缓存数据"""
        dialog = QDialog(self)
        dialog.setWindowTitle("导入缓存")
        dialog.setMinimumWidth(600)
        dialog.setMinimumHeight(450)
        dialog.setStyleSheet(self.styleSheet())
        
        layout = QVBoxLayout(dialog)
        
        # 说明
        lbl = QLabel("请输入券码，每行一个（长度≥19的有效券码）")
        lbl.setStyleSheet("color: #8b949e;")
        layout.addWidget(lbl)
        
        # 文本框
        text_edit = QPlainTextEdit()
        text_edit.setPlaceholderText("2326992090493451528\n2326990641248817355\n...")
        text_edit.setStyleSheet("""
            QPlainTextEdit {
                background: #3c3c3c; color: white;
                border: 1px solid #3e3e42; border-radius: 3px;
                padding: 8px; font-family: Consolas;
            }
        """)
        layout.addWidget(text_edit)
        
        # 按钮
        btn_layout = QHBoxLayout()
        
        btn_ok = QPushButton("✓ 确定导入")
        btn_ok.setObjectName("action_btn")
        btn_ok.clicked.connect(lambda: self._do_import_cache(text_edit.toPlainText(), dialog))
        btn_layout.addWidget(btn_ok)
        
        btn_cancel = QPushButton("✕ 取消")
        btn_cancel.clicked.connect(dialog.reject)
        btn_layout.addWidget(btn_cancel)
        
        layout.addLayout(btn_layout)
        dialog.exec()
    
    def _do_import_cache(self, text: str, dialog: QDialog):
        """执行缓存导入"""
        if not text.strip():
            self.log_msg("⚠️ 请输入券码", "warning")
            return
        
        # 解析券码
        codes = []
        for line in text.split('\n'):
            clean = line.strip()
            clean = re.sub(r'[\s\t\n\r"\']+', '', clean)
            if clean and len(clean) >= 19:
                codes.append(clean)
        
        if not codes:
            self.log_msg("❌ 未找到有效券码（要求长度≥19）", "error")
            return
        
        # 批量导入
        self.log_msg(f"📥 开始导入 {len(codes)} 个券码到缓存...", "info")
        stats = CACHE_MANAGER.batch_set(codes, "已使用")
        
        # 只在日志框显示结果，不弹窗
        self.log_msg(f"✅ 导入完成: 新增 {stats['new']} 条，跳过 {stats['skip']} 条，失败 {stats['error']} 条", "success")
        total = CACHE_MANAGER.get_stats()['total_cached']
        self.log_msg(f"📊 当前缓存总数: {total} 条", "info")
        
        dialog.accept()
    
    def export_cache(self):
        """导出缓存"""
        path, _ = QFileDialog.getSaveFileName(
            self,
            "导出缓存",
            f"cache_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt",
            "Text Files (*.txt)"
        )
        
        if path:
            count = CACHE_MANAGER.export(path)
            self.log_msg(f"💾 导出成功: {path} ({count} 条记录)", "success")
    
    def clear_cache(self):
        """清空缓存"""
        from PySide6.QtWidgets import QMessageBox as MB
        stats = CACHE_MANAGER.get_stats()
        
        reply = MB.question(
            self,
            "清空缓存",
            f"确定要清空所有缓存数据吗？\n\n当前缓存数: {stats['total_cached']} 条\n\n此操作无法撤销。",
            MB.StandardButton.Yes | MB.StandardButton.No
        )
        
        if reply == MB.StandardButton.Yes:
            count = CACHE_MANAGER.clear()
            self.log_msg(f"🗑️ 已清空 {count} 条缓存记录", "success")


if __name__ == '__main__':
    os.environ["QT_ENABLE_HIGHDPI_SCALING"] = "1"
    QApplication.setHighDpiScaleFactorRoundingPolicy(Qt.HighDpiScaleFactorRoundingPolicy.PassThrough)
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    window = WalmartUltraUI()
    window.show()
    sys.exit(app.exec())
