#!/usr/bin/env python3
"""
Sorrel OTA Checker
Reads numbered files (1.txt, 2.txt, 3.txt, ...) until no file is found.
Each file: first line = build fingerprint, remaining lines = serial numbers.
Performs checkin requests and reports new OTA URLs to logs and Discord.

Usage:
    python sorrel_checker.py --sorrel
"""

import sys
import os
import re
import gzip
import zlib
import ssl
import urllib.request
import urllib.error
import json
import struct
import time
import argparse
from datetime import datetime, timezone


# ─────────────────────────────────────────────────────────────────────────────
#  Config
# ─────────────────────────────────────────────────────────────────────────────

ARCHIVED_FILE      = "archived.txt"
LOG_FILE           = "sorrel_checker.log"
CHECKIN_URL        = "http://android.googleapis.com/checkin"

DISCORD_WEBHOOK    = os.environ.get("DISCORD_WEBHOOK", "")
DISCORD_WEBHOOK_2  = os.environ.get("DISCORD_WEBHOOK_2", "")

REQUEST_DELAY_SEC  = 0.2   # delay between serial requests to avoid rate-limiting


# ─────────────────────────────────────────────────────────────────────────────
#  Protobuf helpers
# ─────────────────────────────────────────────────────────────────────────────

def encode_varint(value):
    parts = []
    while value > 0x7f:
        parts.append((value & 0x7f) | 0x80)
        value >>= 7
    parts.append(value & 0x7f)
    return bytes(parts)


def encode_string(field_number, value):
    if isinstance(value, str):
        value = value.encode("utf-8")
    tag = (field_number << 3) | 2
    return encode_varint(tag) + encode_varint(len(value)) + value


def encode_int64(field_number, value):
    tag = (field_number << 3) | 0
    return encode_varint(tag) + encode_varint(value & 0xFFFFFFFFFFFFFFFF)


def encode_bool(field_number, value):
    tag = (field_number << 3) | 0
    return encode_varint(tag) + bytes([1 if value else 0])


def decode_varint(data, offset):
    result = 0
    shift = 0
    while True:
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if byte < 0x80:
            break
        shift += 7
    return result, offset


def decode_string(data, offset, length):
    return data[offset : offset + length].decode("utf-8", errors="ignore"), offset + length


# ─────────────────────────────────────────────────────────────────────────────
#  Fingerprint parser
# ─────────────────────────────────────────────────────────────────────────────

def parse_fingerprint(fingerprint):
    """
    Parses a standard Android build fingerprint.
    Format: oem/product/device:api/build_tag/incremental:build_type/key_type
    """
    parts = fingerprint.split("/")
    if len(parts) != 6:
        raise ValueError(
            f"Invalid fingerprint format. Expected 6 parts, got {len(parts)}: {parts}"
        )

    oem     = parts[0]
    product = parts[1]

    device_api = parts[2].split(":")
    if len(device_api) != 2:
        raise ValueError(f"Invalid device:api in part 3: {parts[2]}")
    device    = device_api[0]
    api_level = device_api[1]

    build_tag = parts[3]

    incremental_type = parts[4].split(":")
    if len(incremental_type) != 2:
        raise ValueError(f"Invalid incremental:build_type in part 5: {parts[4]}")
    incremental = incremental_type[0]
    build_type  = incremental_type[1]

    key_type = parts[5]

    return {
        "fingerprint": fingerprint,
        "oem":         oem,
        "product":     product,
        "device":      device,
        "api_level":   api_level,
        "build_tag":   build_tag,
        "incremental": incremental,
        "build_type":  build_type,
        "key_type":    key_type,
    }


# ─────────────────────────────────────────────────────────────────────────────
#  Checkin request builder
# ─────────────────────────────────────────────────────────────────────────────

def build_checkin_request(fingerprint, locale="en-US", timezone_str="America/New_York", device_sn="", imei=""):
    parsed = parse_fingerprint(fingerprint)
    device = parsed["device"]

    build  = b""
    build += encode_string(1, fingerprint)
    build += encode_int64(7, 0)
    build += encode_string(9, device)

    checkin  = b""
    tag      = (1 << 3) | 2
    checkin += encode_varint(tag) + encode_varint(len(build)) + build
    checkin += encode_int64(2, 0)
    checkin += encode_string(8, "WIFI::")
    checkin += encode_int64(9, 0)
    checkin += encode_int64(12, 0)
    checkin += encode_int64(14, 2)
    checkin += encode_bool(18, False)
    checkin += encode_string(19, "WIFI")

    request  = b""
    if imei:
        request += encode_string(1, imei)
    tag       = (4 << 3) | 2
    request  += encode_varint(tag) + encode_varint(len(checkin)) + checkin
    request  += encode_int64(2, 0)
    request  += encode_string(3, "1-0000000000000000000000000000000000000000")
    request  += encode_string(6, locale)
    if imei:
        request += encode_string(10, imei)
    request  += encode_string(12, timezone_str)
    request  += encode_int64(14, 3)
    if device_sn:
        request += encode_string(16, device_sn)
    request  += encode_int64(20, 0)
    request  += encode_int64(22, 0)

    return request


# ─────────────────────────────────────────────────────────────────────────────
#  Protobuf response parser
# ─────────────────────────────────────────────────────────────────────────────

def parse_protobuf_response(data):
    settings = {}
    offset   = 0

    while offset < len(data):
        tag, offset   = decode_varint(data, offset)
        field_number  = tag >> 3
        wire_type     = tag & 0x07

        if field_number == 5 and wire_type == 2:
            length, offset = decode_varint(data, offset)
            end  = offset + length
            name = None
            value = None

            while offset < end:
                inner_tag, offset  = decode_varint(data, offset)
                inner_field        = inner_tag >> 3
                inner_wire         = inner_tag & 0x07

                if inner_wire == 2:
                    str_len, offset = decode_varint(data, offset)
                    if inner_field == 1:
                        name,  offset = decode_string(data, offset, str_len)
                    elif inner_field == 2:
                        value, offset = decode_string(data, offset, str_len)
                else:
                    offset += 1

            if name and value:
                settings[name] = value
        else:
            if wire_type == 0:
                _, offset = decode_varint(data, offset)
            elif wire_type == 2:
                length, offset = decode_varint(data, offset)
                offset += length
            elif wire_type == 5:
                offset += 4
            elif wire_type == 1:
                offset += 8

    return settings


def find_ota_link(settings):
    if "update_url" not in settings:
        return None
    return {
        "url":         settings["update_url"],
        "title":       settings.get("update_title", ""),
        "description": settings.get("update_description", ""),
        "size":        settings.get("update_size", ""),
    }


# ─────────────────────────────────────────────────────────────────────────────
#  Checkin performer
# ─────────────────────────────────────────────────────────────────────────────

def perform_checkin(fingerprint, device_sn="", url=None):
    parsed       = parse_fingerprint(fingerprint)
    request_data = build_checkin_request(fingerprint, device_sn=device_sn)
    compressed   = gzip.compress(request_data)

    url    = (url or CHECKIN_URL).strip()
    device = parsed["device"]
    version = parsed["api_level"]
    build  = parsed["build_tag"]

    headers = {
        "Accept-Encoding": "gzip, deflate",
        "Content-Encoding": "gzip",
        "Content-Type":    "application/x-protobuffer",
        "User-Agent":      f"Dalvik/2.1.0 (Linux; U; Android {version}; {device} Build/{build})",
    }

    req = urllib.request.Request(url, data=compressed, headers=headers, method="POST")
    with urllib.request.urlopen(req, timeout=15) as response:
        response_data = response.read()
        try:
            response_data = gzip.decompress(response_data)
        except Exception:
            pass
        settings = parse_protobuf_response(response_data)
        return settings


# ─────────────────────────────────────────────────────────────────────────────
#  Archived URL helpers
# ─────────────────────────────────────────────────────────────────────────────

def load_archived_urls(path=ARCHIVED_FILE):
    if not os.path.exists(path):
        return set()
    with open(path, "r", encoding="utf-8") as f:
        return {line.strip() for line in f if line.strip()}


def save_archived_url(url, path=ARCHIVED_FILE):
    with open(path, "a", encoding="utf-8") as f:
        f.write(url + "\n")


# ─────────────────────────────────────────────────────────────────────────────
#  Logging
# ─────────────────────────────────────────────────────────────────────────────

def log(message, also_print=True):
    ts  = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    line = f"[{ts}] {message}"
    if also_print:
        print(line, flush=True)
    with open(LOG_FILE, "a", encoding="utf-8") as f:
        f.write(line + "\n")


def format_finding(ota):
    lines = [
        f"URL: {ota['url']}",
    ]
    if ota.get("title"):
        lines.append(f"Title: {ota['title']}")
    if ota.get("description"):
        lines.append(f"Description: {ota['description']}")
    if ota.get("size"):
        lines.append(f"Size: {ota['size']}")
    if ota.get("post_build"):
        lines.append(f"Fingerprint: {ota['post_build']}")
    if ota.get("pre_build"):
        lines.append(f"Pre-build: {ota['pre_build']}")
    return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────────────
#  Discord notifier
# ─────────────────────────────────────────────────────────────────────────────

def _send_to_webhook(webhook_url, payload):
    webhook_url = webhook_url.strip()
    log(f"[Discord] Sending to: {webhook_url[:50]}...")
    try:
        data = json.dumps(payload).encode("utf-8")
        req  = urllib.request.Request(
            webhook_url,
            data=data,
            headers={"Content-Type": "application/json", "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            log(f"[Discord] Notification sent (HTTP {resp.status}).")
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="ignore")
        log(f"[Discord] Failed to send notification: {e} — Response: {body}")
    except Exception as e:
        log(f"[Discord] Failed to send notification: {e}")


def send_discord(findings):
    if not findings:
        return

    ts    = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    count = len(findings)

    body_parts = []
    for ota in findings:
        body_parts.append(format_finding(ota))

    body = "\n\n".join(body_parts)
    if len(body) > 1900:
        body = body[:1900] + "\n...(truncated)"

    content = f"**New Sorrel OTA ({count} update{'s' if count > 1 else ''}) — {ts}**\n```\n{body}\n```"
    payload = {"content": content}

    if DISCORD_WEBHOOK:
        _send_to_webhook(DISCORD_WEBHOOK, payload)
    else:
        log("[Discord] DISCORD_WEBHOOK not set, skipping.")

    if DISCORD_WEBHOOK_2:
        _send_to_webhook(DISCORD_WEBHOOK_2, payload)
    else:
        log("[Discord] DISCORD_WEBHOOK_2 not set, skipping.")



# ─────────────────────────────────────────────────────────────────────────────
#  OTA metadata fetcher (extracts post-build fingerprint etc. from ZIP tail)
# ─────────────────────────────────────────────────────────────────────────────

PAYLOAD_METADATA_PREFIXES = [
    'post-build',
    'pre-build',
    'pre-device',
    'post-build-incremental',
    'post-sdk-level',
    'post-security-patch-level',
    'post-timestamp',
    'ota-type',
    'ota-required-cache',
    'pre-build-incremental',
]

EOCD_SIG  = b'PK\x05\x06'
CDFH_SIG  = b'PK\x01\x02'
LFH_SIG   = b'PK\x03\x04'

_METADATA_UA = ('AndroidDownloadManager/14 (Linux; U; Android 14; '
                'sdk_gphone64_x86_64 Build/UE1A.230829.036)')


def _parse_all_metadata_lines(blob: bytes, known_prefixes) -> dict:
    try:
        text = blob.decode('utf-8', errors='replace')
    except Exception:
        return {}
    all_lines = {}
    order = []
    for raw_line in text.splitlines():
        line = raw_line.strip('\r').strip()
        if not line or '=' not in line:
            continue
        key, _, value = line.partition('=')
        key = key.strip()
        value = value.strip()
        if not key or not value:
            continue
        if key not in all_lines:
            order.append(key)
        all_lines[key] = value
    result = {}
    for prefix in known_prefixes:
        if prefix in all_lines:
            result[prefix] = all_lines[prefix]
    for key in order:
        if key not in result:
            result[key] = all_lines[key]
    return result


def _extract_metadata_kv(blob: bytes, prefixes) -> dict:
    result = {}
    for prefix in prefixes:
        needle = f'{prefix}='.encode('utf-8')
        start = blob.find(needle)
        if start == -1:
            continue
        val_start = start + len(needle)
        end = blob.find(b'\n', val_start)
        if end == -1:
            end = len(blob)
        try:
            value = blob[val_start:end].decode('utf-8', errors='replace').strip('\r')
        except Exception:
            continue
        if value:
            result[prefix] = value
    return result


def _find_zip_metadata_entry(tail_blob: bytes, tail_offset: int):
    eocd_pos = tail_blob.rfind(EOCD_SIG)
    if eocd_pos == -1:
        return None
    try:
        cd_size   = struct.unpack('<I', tail_blob[eocd_pos + 12:eocd_pos + 16])[0]
        cd_offset = struct.unpack('<I', tail_blob[eocd_pos + 16:eocd_pos + 20])[0]
    except struct.error:
        return None
    cd_start = cd_offset - tail_offset
    if cd_start < 0:
        return None
    pos = cd_start
    end = cd_start + cd_size
    while pos < end and pos < len(tail_blob) - 46:
        if tail_blob[pos:pos + 4] != CDFH_SIG:
            break
        compression_method = struct.unpack('<H', tail_blob[pos + 10:pos + 12])[0]
        compressed_size    = struct.unpack('<I', tail_blob[pos + 20:pos + 24])[0]
        name_len           = struct.unpack('<H', tail_blob[pos + 28:pos + 30])[0]
        extra_len          = struct.unpack('<H', tail_blob[pos + 30:pos + 32])[0]
        comment_len        = struct.unpack('<H', tail_blob[pos + 32:pos + 34])[0]
        local_offset       = struct.unpack('<I', tail_blob[pos + 42:pos + 46])[0]
        name               = tail_blob[pos + 46:pos + 46 + name_len]
        if name == b'META-INF/com/android/metadata':
            return local_offset, compressed_size, compression_method, name.decode(errors='replace')
        pos += 46 + name_len + extra_len + comment_len
    return None


def fetch_ota_metadata(url: str, timeout: int = 20) -> dict:
    """
    Downloads only the tail of the OTA ZIP to extract META-INF/com/android/metadata
    without fetching the whole file. Returns a dict with 'found' and 'fields'.
    """
    out = {'found': False, 'fields': {}, 'error': None}

    def _get_range(range_header):
        req_h = {'User-Agent': _METADATA_UA, 'Accept-Encoding': 'identity', 'Range': range_header}
        req = urllib.request.Request(url, headers=req_h)
        ctx = ssl.create_default_context()
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
            return resp.read()

    try:
        head_req = urllib.request.Request(url, method='HEAD',
                                          headers={'User-Agent': _METADATA_UA,
                                                   'Accept-Encoding': 'identity'})
        ctx = ssl.create_default_context()
        with urllib.request.urlopen(head_req, timeout=timeout, context=ctx) as resp:
            total_size = int(resp.headers.get('Content-Length', '0') or '0')
    except Exception as e:
        out['error'] = f"HEAD failed: {e}"
        return out

    if total_size <= 0:
        out['error'] = "Cannot determine file size"
        return out

    chunk = 2 * 1024 * 1024
    tail_offset = max(0, total_size - chunk)
    try:
        tail_data = _get_range(f'bytes={tail_offset}-{total_size - 1}')
    except Exception as e:
        out['error'] = f"Tail fetch failed: {e}"
        return out

    entry = _find_zip_metadata_entry(tail_data, tail_offset)
    if entry:
        local_header_offset, compressed_size, compression_method, _ = entry
        lh_start = local_header_offset - tail_offset
        try:
            if 0 <= lh_start and lh_start + 30 <= len(tail_data):
                lh_blob = tail_data
                lh_pos  = lh_start
            else:
                lh_blob = _get_range(f'bytes={local_header_offset}-{local_header_offset + 4096}')
                lh_pos  = 0

            if lh_blob[lh_pos:lh_pos + 4] == LFH_SIG:
                name_len  = struct.unpack('<H', lh_blob[lh_pos + 26:lh_pos + 28])[0]
                extra_len = struct.unpack('<H', lh_blob[lh_pos + 28:lh_pos + 30])[0]
                data_start = lh_pos + 30 + name_len + extra_len

                if data_start + compressed_size <= len(lh_blob):
                    entry_data = lh_blob[data_start:data_start + compressed_size]
                else:
                    abs_start  = local_header_offset + 30 + name_len + extra_len
                    entry_data = _get_range(f'bytes={abs_start}-{abs_start + compressed_size - 1}')

                if compression_method == 0:
                    plain = entry_data
                elif compression_method == 8:
                    plain = zlib.decompress(entry_data, -15)
                else:
                    plain = b''

                if plain:
                    fields = _parse_all_metadata_lines(plain, PAYLOAD_METADATA_PREFIXES)
                    if fields:
                        out['found'] = True
                        out['fields'] = fields
                        return out
        except Exception as e:
            out['error'] = f"Entry extraction failed: {e}"

    for prefix in PAYLOAD_METADATA_PREFIXES:
        pos = tail_data.find(f'{prefix}='.encode('utf-8'))
        if pos != -1:
            block_end = tail_data.find(LFH_SIG, pos)
            if block_end == -1:
                block_end = tail_data.find(CDFH_SIG, pos)
            if block_end == -1:
                block_end = len(tail_data)
            fields = _parse_all_metadata_lines(tail_data[max(0, pos - 4096):block_end],
                                               PAYLOAD_METADATA_PREFIXES)
            if fields:
                out['found'] = True
                out['fields'] = fields
                return out

    fields = _extract_metadata_kv(tail_data, PAYLOAD_METADATA_PREFIXES)
    if fields:
        out['found'] = True
        out['fields'] = fields

    return out


# ─────────────────────────────────────────────────────────────────────────────
#  Numbered file loader: 1.txt, 2.txt, 3.txt, ...
# ─────────────────────────────────────────────────────────────────────────────

def load_numbered_files():
    """
    Loads 1.txt, 2.txt, 3.txt, ... until a file is not found.
    Each file: first line = fingerprint, remaining lines = serial numbers.
    Returns a list of (fingerprint, [serials], filename) tuples.
    """
    result = []
    idx = 1
    while True:
        filename = f"{idx}.txt"
        if not os.path.exists(filename):
            log(f"File {filename} not found — stopping file scan.")
            break
        with open(filename, "r", encoding="utf-8") as f:
            lines = [line.strip() for line in f if line.strip()]
        if not lines:
            log(f"[WARN] {filename} is empty, skipping.")
            idx += 1
            continue
        fingerprint = lines[0]
        serials     = lines[1:]
        log(f"Loaded {filename}: fingerprint={fingerprint}, {len(serials)} serial(s).")
        result.append((fingerprint, serials, filename))
        idx += 1
    return result


# ─────────────────────────────────────────────────────────────────────────────
#  Main sorrel run
# ─────────────────────────────────────────────────────────────────────────────

def checkin_with_fingerprint_chain(serial, initial_fingerprint, archived_urls, new_findings, indent="  "):
    """
    Given a serial and a starting fingerprint, performs checkin.
    If a new OTA is found:
      - fetches its metadata
      - extracts all fingerprints from post-build (split by |)
      - iterates each fingerprint with the same serial recursively
    Returns list of newly discovered OTA dicts (already appended to new_findings).
    """
    queue = [initial_fingerprint]
    visited_fingerprints = set()

    while queue:
        fingerprint = queue.pop(0)
        if fingerprint in visited_fingerprints:
            continue
        visited_fingerprints.add(fingerprint)

        log(f"{indent}Trying fingerprint: {fingerprint}")

        try:
            settings = perform_checkin(fingerprint, device_sn=serial)
            ota      = find_ota_link(settings)

            if not (ota and ota["url"]):
                log(f"{indent}No OTA update found.")
                continue

            url = ota["url"]
            if url in archived_urls:
                log(f"{indent}URL already archived, skipping.")
                continue

            log(f"{indent}*** NEW URL FOUND ***")
            finding_text = format_finding(ota)
            for line in finding_text.splitlines():
                log(f"{indent}{line}")

            # Fetch metadata from the OTA ZIP
            extra_fingerprints = []
            try:
                log(f"{indent}Fetching OTA metadata...")
                meta = fetch_ota_metadata(url)
                if meta['found'] and meta['fields']:
                    fields = meta['fields']

                    post_build_raw = fields.get('post-build', '')
                    if post_build_raw:
                        # Split by | to get all fingerprints
                        all_fps = [fp.strip() for fp in post_build_raw.split('|') if fp.strip()]
                        # Try to find the fingerprint whose device matches the one we queried with
                        try:
                            current_device = parse_fingerprint(fingerprint)["device"]
                        except Exception:
                            current_device = None
                        matching_fp = None
                        if current_device:
                            for fp in all_fps:
                                try:
                                    if parse_fingerprint(fp)["device"] == current_device:
                                        matching_fp = fp
                                        break
                                except Exception:
                                    continue
                        clean_fp = matching_fp if matching_fp else (all_fps[0] if all_fps else post_build_raw)
                        log(f"{indent}Fingerprint: {clean_fp}")
                        ota['post_build'] = clean_fp
                        # Queue all fingerprints for further checking with same serial
                        extra_fingerprints = all_fps

                    pre_build = fields.get('pre-build', '')
                    if pre_build:
                        # Pick matching device in pre-build too, or trim after |
                        pre_fps = [fp.strip() for fp in pre_build.split('|') if fp.strip()]
                        try:
                            current_device = parse_fingerprint(fingerprint)["device"]
                        except Exception:
                            current_device = None
                        matching_pre = None
                        if current_device:
                            for fp in pre_fps:
                                try:
                                    if parse_fingerprint(fp)["device"] == current_device:
                                        matching_pre = fp
                                        break
                                except Exception:
                                    continue
                        clean_pre = matching_pre if matching_pre else (pre_fps[0] if pre_fps else pre_build)
                        log(f"{indent}Pre-build:   {clean_pre}")
                        ota['pre_build'] = clean_pre
                else:
                    log(f"{indent}Metadata: not found{(' — ' + meta['error']) if meta.get('error') else ''}")
            except Exception as me:
                log(f"{indent}Metadata fetch error: {me}")

            log("")  # blank line separator

            new_findings.append(ota)
            archived_urls.add(url)
            save_archived_url(url)

            # Queue all fingerprints from post-build for the same serial
            if extra_fingerprints:
                log(f"{indent}Queueing {len(extra_fingerprints)} fingerprint(s) from post-build for serial {serial}...")
                for fp in extra_fingerprints:
                    if fp not in visited_fingerprints:
                        queue.append(fp)

        except Exception as e:
            log(f"{indent}[ERROR] {e}")

        time.sleep(REQUEST_DELAY_SEC)


def run_sorrel():
    log("=" * 60)
    log("Sorrel OTA checker started.")

    # Load fingerprint+serials from numbered files
    file_groups = load_numbered_files()

    if not file_groups:
        log("[ERROR] No numbered files (1.txt, 2.txt, ...) found. Aborting.")
        sys.exit(1)

    archived_urls = load_archived_urls()
    log(f"Loaded {len(archived_urls)} archived URL(s) from {ARCHIVED_FILE}.")

    new_findings = []

    for fingerprint, serials, filename in file_groups:
        log(f"\n--- Processing {filename} | Fingerprint: {fingerprint} ---")
        total = len(serials)

        for idx, serial in enumerate(serials, 1):
            log(f"[{idx}/{total}] Checking serial: {serial}")
            checkin_with_fingerprint_chain(serial, fingerprint, archived_urls, new_findings)

    log(f"\nRun complete. {len(new_findings)} new finding(s) this run.")
    log("=" * 60)

    if new_findings:
        send_discord(new_findings)


# ─────────────────────────────────────────────────────────────────────────────
#  Entry point
# ─────────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="OTA Prober")
    parser.add_argument(
        "--sorrel",
        action="store_true",
        help="Run sorrel OTA checker using fingerprint+serials from 1.txt, 2.txt, ...",
    )
    args, _ = parser.parse_known_args()

    if args.sorrel:
        run_sorrel()
    else:
        print("No mode specified. Use --sorrel to run the sorrel OTA checker.")
        print("Example: python sorrel_checker.py --sorrel")
        sys.exit(0)


if __name__ == "__main__":
    main()
