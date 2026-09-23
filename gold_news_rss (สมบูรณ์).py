#!/usr/bin/env python3
"""
gold_news_rss.py
================
Script for fetching financial RSS news, filtering items relevant to Gold (XAUUSD) & US Dollar (USD),
deduplicating articles across multiple sources, and exporting structured JSON for AI analysis.

Author: Antigravity AI
"""

import argparse
import datetime
import difflib
import email.utils
import html
import json
import re
import sys
import time
from typing import Dict, List, Optional, Tuple, Any

import feedparser

# Reconfigure stdout/stderr to UTF-8 on Windows to handle Thai text and emojis cleanly
if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
if hasattr(sys.stderr, "reconfigure"):
    try:
        sys.stderr.reconfigure(encoding="utf-8")
    except Exception:
        pass

# Timezone support: try pytz first, then zoneinfo, with fixed offset fallback for Windows environments
pytz_available = False
try:
    import pytz
    pytz_available = True
except ImportError:
    pass


def get_timezone(tz_name: str):
    if pytz_available:
        try:
            return pytz.timezone(tz_name)
        except Exception:
            pass

    try:
        from zoneinfo import ZoneInfo
        return ZoneInfo(tz_name)
    except Exception:
        pass

    # Safe fallback for Windows environments without tzdata/pytz
    fallback_offsets = {
        "Asia/Bangkok": datetime.timezone(datetime.timedelta(hours=7)),
        "America/New_York": datetime.timezone(datetime.timedelta(hours=-4)),
        "Europe/London": datetime.timezone(datetime.timedelta(hours=1)),
    }
    return fallback_offsets.get(tz_name, datetime.timezone.utc)


# ==========================================
# 1. Configuration & RSS Sources
# ==========================================

ENTRIES_PER_SOURCE = 10
MIN_SCORE = 3
SIMILARITY_THRESHOLD = 0.5
BANGKOK_TZ = get_timezone("Asia/Bangkok")

RSS_SOURCES = [
    {
        "name": "Bloomberg Markets",
        "url": "https://feeds.bloomberg.com/markets/news.rss",
        "tz": "America/New_York",
    },
    {
        "name": "Financial Times",
        "url": "https://www.ft.com/rss/home",
        "tz": "Europe/London",
    },
    {
        "name": "CNBC Economy",
        "url": "https://www.cnbc.com/id/20910258/device/rss/rss.html",
        "tz": "America/New_York",
    },
    {
        "name": "Yahoo Finance (Gold GC=F)",
        "url": "https://feeds.finance.yahoo.com/rss/2.0/headline?s=GC=F&region=US&lang=en-US",
        "tz": "America/New_York",
    },
    {
        "name": "MarketWatch Top Stories",
        "url": "https://feeds.content.dowjones.io/public/rss/mw_topstories",
        "tz": "America/New_York",
    },
    {
        "name": "BBC Business",
        "url": "https://feeds.bbci.co.uk/news/business/rss.xml",
        "tz": "Europe/London",
    },
    {
        "name": "Guardian Economics",
        "url": "https://www.theguardian.com/business/economics/rss",
        "tz": "Europe/London",
    },
]

# ==========================================
# 2. Relevance Keyword Scoring System
# ==========================================

KEYWORD_SCORES = {
    "fed": 5, "federal reserve": 5, "interest rate": 5, "rate cut": 5,
    "rate hike": 5, "fomc": 5, "powell": 4, "jerome powell": 4,
    "cpi": 5, "inflation": 5, "ppi": 4, "core inflation": 5,
    "pce": 4, "nonfarm payroll": 4, "nfp": 4, "unemployment": 3,
    "jobs report": 4, "gdp": 3,
    "dollar": 4, "usd": 4, "dxy": 4, "treasury": 4, "treasury yield": 5,
    "bond market": 3, "bond yield": 4, "debt": 3, "deficit": 3,
    "national debt": 4,
    "gold": 5, "xau": 5, "bullion": 5, "silver": 3, "precious metal": 4,
    "safe haven": 5, "safe-haven": 5,
    "war": 3, "sanction": 3, "geopolitical": 4, "tension": 2,
    "iran": 3, "russia": 2, "ukraine": 2, "middle east": 3,
    "conflict": 2, "military": 2,
    "tariff": 4, "trade war": 4, "trade deal": 3, "export": 2, "import": 2,
    "ecb": 3, "boe": 3, "bank of england": 3, "boj": 3,
    "bank of japan": 3, "pboc": 3, "central bank": 3,
    "stock market": 2, "recession": 4, "market selloff": 3,
    "economic growth": 2, "economic slowdown": 3,
}

# Pre-compile word-boundary regexes for performance & safety
COMPILED_KEYWORDS = {
    kw: (score, re.compile(rf"\b{re.escape(kw)}\b", re.IGNORECASE))
    for kw, score in KEYWORD_SCORES.items()
}
# ==========================================
# 3. Utility Functions: HTML Cleaning & Text Truncation
# ==========================================

def strip_html(text: str) -> str:
    if not text:
        return ""
    text = re.sub(r'</p>|</li>|<br\s*/?>', ' ', text, flags=re.IGNORECASE)
    text = re.sub(r'<[^>]+>', ' ', text)
    text = re.sub(r'<[^<>]*$', '', text)
    text = html.unescape(text)
    text = re.sub(r'\s+', ' ', text).strip()
    return text


def truncate_summary(summary: str, max_length: int = 280) -> str:
    if not summary:
        return "แหล่งนี้ไม่ส่ง summary มาใน RSS — ต้องเปิดลิงก์อ่านเอง"
    if len(summary) <= max_length:
        return summary
    truncated = summary[:max_length]
    last_space = truncated.rfind(' ')
    if last_space > 0:
        truncated = truncated[:last_space]
    return truncated.rstrip() + "..."


def calculate_relevance(title: str, summary: str) -> Tuple[int, List[str]]:
    combined_text = f"{title} {summary}"
    total_score = 0
    matched_keywords = []
    for kw, (score, pattern) in COMPILED_KEYWORDS.items():
        if pattern.search(combined_text):
            matched_keywords.append(kw)
            total_score += score
    return total_score, matched_keywords


def parse_entry_datetime(entry: dict) -> Optional[datetime.datetime]:
    date_str = entry.get("published") or entry.get("updated")
    if date_str:
        try:
            dt = email.utils.parsedate_to_datetime(date_str)
            if dt is not None:
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=datetime.timezone.utc)
                return dt
        except Exception:
            pass
    struct_t = entry.get("published_parsed") or entry.get("updated_parsed")
    if struct_t:
        try:
            ts = time.mktime(struct_t) - time.timezone
            return datetime.datetime.fromtimestamp(ts, tz=datetime.timezone.utc)
        except Exception:
            try:
                return datetime.datetime(*struct_t[:6], tzinfo=datetime.timezone.utc)
            except Exception:
                pass
    return None


def format_datetime_pair(dt: Optional[datetime.datetime], source_tz_str: str) -> Tuple[str, str]:
    if dt is None:
        return "ไม่ระบุเวลา", "ไม่ระบุเวลา"
    try:
        source_tz = get_timezone(source_tz_str)
        dt_bangkok = dt.astimezone(BANGKOK_TZ)
        dt_source = dt.astimezone(source_tz)
        bkk_str = dt_bangkok.strftime("%d/%m/%Y %H:%M น.")
        src_str = dt_source.strftime("%d/%m/%Y %H:%M ") + f"({source_tz_str})"
        return bkk_str, src_str
    except Exception:
        return "ไม่ระบุเวลา", "ไม่ระบุเวลา"


def deduplicate_news(news_items: List[dict], similarity_threshold: float = SIMILARITY_THRESHOLD) -> List[dict]:
    groups: List[List[dict]] = []
    for item in news_items:
        matched_group = None
        for group in groups:
            rep_title = group[0]["title"].lower()
            item_title = item["title"].lower()
            similarity = difflib.SequenceMatcher(None, rep_title, item_title).ratio()
            if similarity >= similarity_threshold:
                matched_group = group
                break
        if matched_group is not None:
            matched_group.append(item)
        else:
            groups.append([item])

    deduped = []
    for group in groups:
        rep_item = max(group, key=lambda x: len(x["title"]))
        max_score = max(x["score"] for x in group)
        sources = []
        for x in group:
            if x["source"] not in sources:
                sources.append(x["source"])
        confidence = len(sources)
        valid_dts = [x["published_dt"] for x in group if x["published_dt"] is not None]
        oldest_dt = min(valid_dts) if valid_dts else None
        all_keywords = set()
        for x in group:
            all_keywords.update(x["matched_keywords"])
        bkk_time_str, local_time_str = format_datetime_pair(oldest_dt, rep_item["source_tz"])
        deduped.append({
            "title": rep_item["title"],
            "summary": rep_item["summary"],
            "score": max_score,
            "confidence": confidence,
            "sources": sources,
            "published_dt": oldest_dt,
            "matched_keywords": sorted(list(all_keywords)),
            "link": rep_item["link"],
            "bkk_time_str": bkk_time_str,
            "local_time_str": local_time_str,
            "source_tz": rep_item["source_tz"]
        })
    deduped.sort(key=lambda x: (x["score"], x["confidence"]), reverse=True)
    return deduped


def fetch_and_filter() -> Tuple[List[dict], List[dict]]:
    raw_filtered_news = []
    print("=" * 80)
    print("📡 กำลังเริ่มดึงข่าวเศรษฐกิจและวิเคราะห์ความเกี่ยวข้องสำหรับ Gold & USD...")
    print("=" * 80)
    for source in RSS_SOURCES:
        source_name = source["name"]
        url = source["url"]
        source_tz = source["tz"]
        print(f"\n🌐 Source: {source_name}")
        print(f"🔗 URL: {url}")
        try:
            feed = feedparser.parse(url)
            entries = feed.entries[:ENTRIES_PER_SOURCE]
            matched_count_in_source = 0
            for entry in entries:
                title = strip_html(entry.get("title", ""))
                summary = strip_html(entry.get("summary") or entry.get("description") or "")
                link = entry.get("link", "")
                dt = parse_entry_datetime(entry)
                bkk_time_str, local_time_str = format_datetime_pair(dt, source_tz)
                score, keywords = calculate_relevance(title, summary)
                if score >= MIN_SCORE:
                    matched_count_in_source += 1
                    raw_news_item = {
                        "source": source_name,
                        "source_tz": source_tz,
                        "title": title,
                        "summary": summary,
                        "link": link,
                        "score": score,
                        "matched_keywords": keywords,
                        "published_dt": dt,
                        "bkk_time_str": bkk_time_str,
                        "local_time_str": local_time_str,
                    }
                    raw_filtered_news.append(raw_news_item)
                    formatted_summary = truncate_summary(summary)
                    print(f"  ⭐ [{score} คะแนน] {title}")
                    print(f"     📝 {formatted_summary}")
                    print(f"     🕐 เวลาไทย: {bkk_time_str}")
                    print(f"     🕐 เวลาท้องถิ่น: {local_time_str}")
                    print(f"     🔑 คำสำคัญที่พบ: {', '.join(keywords)}")
                    print(f"     🔗 {link}")
            if matched_count_in_source == 0:
                print("  ℹ️  ไม่พบข่าวที่ผ่านเกณฑ์ MIN_SCORE >= 3 ใน 10 รายการล่าสุด")
        except Exception as e:
            print(f"  ❌ เกิดข้อผิดพลาดในการดึงข้อมูลจาก {source_name}: {e}")

    deduped_news = deduplicate_news(raw_filtered_news)
    print("\n" + "=" * 80)
    print("🏆 สรุป 15 อันดับข่าวสำคัญที่สุดสำหรับวิเคราะห์ทองคำ (XAUUSD) & USD (หลัง Deduplicate)")
    print("=" * 80)
    top_15 = deduped_news[:15]
    if not top_15:
        print("⚠️ ไม่พบข่าวที่ผ่านเกณฑ์ความเกี่ยวข้องในทุกแหล่งข่าว")
    else:
        for idx, news in enumerate(top_15, 1):
            badge = f" ✅ ยืนยันจาก {news['confidence']} แหล่ง" if news['confidence'] > 1 else ""
            print(f"\n[{idx}] ⭐ [{news['score']} คะแนน]{badge}")
            print(f"   📌 แหล่งข่าว: {', '.join(news['sources'])}")
            print(f"   📰 หัวข้อ: {news['title']}")
            print(f"   📝 สรุป: {truncate_summary(news['summary'])}")
            print(f"   🕐 เวลาแรกที่รายงาน (ไทย): {news['bkk_time_str']}")
            print(f"   🔑 คำสำคัญ: {', '.join(news['matched_keywords'])}")
            print(f"   🔗 {news['link']}")
    return raw_filtered_news, deduped_news


def export_to_json(deduped_news: List[dict], output_path: str = "gold_news_for_ai.json", top_n: int = 15) -> str:
    now_bkk = datetime.datetime.now(BANGKOK_TZ).strftime("%d/%m/%Y %H:%M น.")
    top_items = deduped_news[:top_n]
    news_json_list = []
    for rank, item in enumerate(top_items, 1):
        news_json_list.append({
            "rank": rank,
            "title": item["title"],
            "relevance_score": item["score"],
            "confirmed_by_n_sources": item["confidence"],
            "sources": item["sources"],
            "reported_time_bangkok": item["bkk_time_str"],
            "matched_keywords": item["matched_keywords"],
            "link": item["link"]
        })
    data = {
        "generated_at_bangkok": now_bkk,
        "news_count": len(news_json_list),
        "news": news_json_list
    }
    if not news_json_list:
        data["note"] = f"ไม่พบข่าวที่ผ่านเกณฑ์ความเกี่ยวข้อง (MIN_SCORE >= {MIN_SCORE}) ในรอบนี้"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    print("\n" + "=" * 80)
    print(f"💾 Export ข่าวจำนวน {len(news_json_list)} รายการลงไฟล์ '{output_path}' สำเร็จเรียบร้อยแล้ว!")
    print("=" * 80)
    return output_path


def run_self_tests():
    print("🧪 กำลังดำเนินการทดสอบระบบ (Self-Check)...")
    raw_html = "<p>Guardian summary with <a href='https://ft.com'>link text</a></p><br>Trailing info <a href='http://cutoff"
    cleaned = strip_html(raw_html)
    expected_clean = "Guardian summary with link text Trailing info"
    assert cleaned == expected_clean, f"strip_html failed!\nExpected: '{expected_clean}'\nGot: '{cleaned}'"
    print("  ✅ 1. strip_html() ผ่านการทดสอบ")

    score_toward, kw_toward = calculate_relevance("Moving toward a new economic policy", "")
    assert "war" not in kw_toward
    print("  ✅ 2. calculate_relevance() word-boundary ผ่านการทดสอบ")

    score_war, kw_war = calculate_relevance("The war in Ukraine impacts Fed interest rate decisions", "")
    assert "war" in kw_war and "ukraine" in kw_war and "fed" in kw_war and "interest rate" in kw_war
    expected_score = KEYWORD_SCORES["war"] + KEYWORD_SCORES["ukraine"] + KEYWORD_SCORES["fed"] + KEYWORD_SCORES["interest rate"]
    assert score_war == expected_score, f"Score calculation mismatch: expected {expected_score}, got {score_war}"
    print("  ✅ 3. calculate_relevance() คำนวณคะแนนผ่านการทดสอบ")

    sample_news = [
        {"source": "CNBC Economy", "source_tz": "America/New_York", "title": "US Debt Hits $40 Trillion Mark",
         "summary": "Short summary", "link": "https://cnbc.com/1", "score": 8,
         "matched_keywords": ["debt", "national debt"],
         "published_dt": datetime.datetime(2026, 8, 19, 10, 0, tzinfo=datetime.timezone.utc),
         "bkk_time_str": "19/08/2026 17:00 น.", "local_time_str": "19/08/2026 06:00 (America/New_York)"},
        {"source": "BBC Business", "source_tz": "Europe/London", "title": "US National Debt Hits $40 Trillion Level",
         "summary": "Another summary", "link": "https://bbc.com/1", "score": 10,
         "matched_keywords": ["debt", "national debt", "treasury"],
         "published_dt": datetime.datetime(2026, 8, 19, 9, 30, tzinfo=datetime.timezone.utc),
         "bkk_time_str": "19/08/2026 16:30 น.", "local_time_str": "19/08/2026 10:30 (Europe/London)"},
        {"source": "Financial Times", "source_tz": "Europe/London", "title": "US Debt Reaches Historic $40 Trillion Level Today",
         "summary": "Detailed summary from FT", "link": "https://ft.com/1", "score": 9,
         "matched_keywords": ["debt", "us debt"],
         "published_dt": datetime.datetime(2026, 8, 19, 11, 0, tzinfo=datetime.timezone.utc),
         "bkk_time_str": "19/08/2026 18:00 น.", "local_time_str": "19/08/2026 12:00 (Europe/London)"},
    ]
    deduped = deduplicate_news(sample_news, similarity_threshold=0.5)
    assert len(deduped) == 1
    assert deduped[0]["confidence"] == 3
    assert deduped[0]["score"] == 10
    print("  ✅ 4. deduplicate_news() ผ่านการทดสอบ")
    print("🎉 การทดสอบ Self-Check ผ่านทุกข้อสมบูรณ์!\n")


def main():
    parser = argparse.ArgumentParser(description="Gold & USD RSS News Aggregator and AI Exporter")
    parser.add_argument("--test", action="store_true", help="Run self-check tests and exit")
    parser.add_argument("--output", type=str, default="gold_news_for_ai.json", help="Output JSON path")
    args = parser.parse_args()
    run_self_tests()
    if args.test:
        sys.exit(0)
    raw_news, deduped_news = fetch_and_filter()
    export_to_json(deduped_news, output_path=args.output, top_n=15)


if __name__ == "__main__":
    main()
    
