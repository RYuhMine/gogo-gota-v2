#!/usr/bin/env python3
"""
Android XR OTA Checker
Reads numbered files (1.txt, 2.txt, 3.txt, ...) until no file is found.
Each file: first line = build fingerprint, remaining lines = serial numbers.
Performs checkin requests and reports new OTA URLs to logs and Discord.

Also re-checks all post-build fingerprints from archived OTAs on every run.

Usage:
    python sorrel_checker.py --xr
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


def pick_matching_fingerprint(all_fps, reference_fingerprint):
    """
    From a list of fingerprints (split from post-build by |),
    pick the one whose device matches the reference fingerprint's device.
    Falls back to the first entry if no match found.
    """
    try:
        ref_device = parse_fingerprint(reference_fingerprint)["device"]
    except Exception:
        ref_device = None

    if ref_device:
        for fp in all_fps:
            try:
                if parse_fingerprint(fp)["device"] == ref_device:
                    return fp
            except Exception:
                continue

    return all_fps[0] if all_fps else reference_fingerprint


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
#  Archived URL / fingerprint helpers
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

    content = f"**New Android XR OTA ({count} update{'s' if count > 1 else ''}) — {ts}**\n```\n{body}\n```"
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


ZIP64_EOCD_SIG     = b'PK\x06\x06'
ZIP64_LOCATOR_SIG  = b'PK\x06\x07'

def _parse_zip64_eocd(tail_blob: bytes):
    """Returns (total_size, cd_size, cd_offset) or None."""
    pos = tail_blob.rfind(ZIP64_EOCD_SIG)
    if pos == -1:
        return None
    try:
        total_size = struct.unpack('<Q', tail_blob[pos + 40:pos + 48])[0]
        cd_size    = struct.unpack('<Q', tail_blob[pos + 48:pos + 56])[0]
        cd_offset  = struct.unpack('<Q', tail_blob[pos + 56:pos + 64])[0]
        return total_size, cd_size, cd_offset
    except struct.error:
        return None


def _find_zip_entry_central(cd_blob: bytes, wanted_name: bytes):
    """Scans central directory blob, returns (local_header_offset_64bit,
    compressed_size_64bit, compression_method). Handles ZIP64 extra fields."""
    pos = 0
    while pos + 46 <= len(cd_blob):
        if cd_blob[pos:pos + 4] != CDFH_SIG:
            break
        comp_method    = struct.unpack('<H', cd_blob[pos + 10:pos + 12])[0]
        comp_size      = struct.unpack('<I', cd_blob[pos + 20:pos + 24])[0]
        name_len       = struct.unpack('<H', cd_blob[pos + 28:pos + 30])[0]
        extra_len      = struct.unpack('<H', cd_blob[pos + 30:pos + 32])[0]
        comment_len    = struct.unpack('<H', cd_blob[pos + 32:pos + 34])[0]
        lho            = struct.unpack('<I', cd_blob[pos + 42:pos + 46])[0]
        name           = cd_blob[pos + 46:pos + 46 + name_len]

        # Parse ZIP64 extended information extra field (header id 0x0001)
        extra = cd_blob[pos + 46 + name_len : pos + 46 + name_len + extra_len]
        epos = 0
        while epos + 4 <= len(extra):
            hid = struct.unpack('<H', extra[epos:epos+2])[0]
            hsz = struct.unpack('<H', extra[epos+2:epos+4])[0]
            data = extra[epos+4 : epos+4+hsz]
            if hid == 0x0001:
                dpos = 0
                if comp_size == 0xFFFFFFFF and dpos + 8 <= len(data):
                    comp_size = struct.unpack('<Q', data[dpos:dpos+8])[0]; dpos += 8
                if lho == 0xFFFFFFFF and dpos + 8 <= len(data):
                    lho = struct.unpack('<Q', data[dpos:dpos+8])[0]; dpos += 8
            epos += 4 + hsz

        if name == wanted_name:
            return lho, comp_size, comp_method
        pos += 46 + name_len + extra_len + comment_len
    return None

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
#  Core checkin with fingerprint chain
# ─────────────────────────────────────────────────────────────────────────────

def get_post_build_fingerprints(url, reference_fingerprint, indent="  "):
    """
    Fetches OTA metadata from a ZIP URL and returns (all_fps, clean_fp, pre_build_clean).
    all_fps   — full list split by | from post-build (for chaining)
    clean_fp  — the one matching reference_fingerprint's device (for display)
    clean_pre — matching pre-build entry (for display)
    """
    # ── Fast path: EOCD / ZIP64 → central directory → metadata entry ─────
    try:
        window = min(total_size, 128 * 1024)
        start = total_size - window
        tail = _get_range(f'bytes={start}-{total_size - 1}')

        zip64 = _parse_zip64_eocd(tail)
        if zip64:
            _, cd_size, cd_offset = zip64
        else:
            eocd_pos = tail.rfind(EOCD_SIG)
            if eocd_pos == -1:
                raise ValueError("EOCD not found")
            cd_size   = struct.unpack('<I', tail[eocd_pos + 12:eocd_pos + 16])[0]
            cd_offset = struct.unpack('<I', tail[eocd_pos + 16:eocd_pos + 20])[0]

        if cd_size <= 0 or cd_offset < 0 or cd_offset + cd_size > total_size:
            raise ValueError(f"Bad central directory bounds: off={cd_offset} size={cd_size}")

        cd_blob = _get_range(f'bytes={cd_offset}-{cd_offset + cd_size - 1}')
        entry = _find_zip_entry_central(cd_blob, b'META-INF/com/android/metadata')

        if entry:
            lh_off, comp_size, comp_method = entry
            lh_blob = _get_range(f'bytes={lh_off}-{lh_off + 4096}')
            if lh_blob[0:4] == LFH_SIG:
                lh_name_len  = struct.unpack('<H', lh_blob[26:28])[0]
                lh_extra_len = struct.unpack('<H', lh_blob[28:30])[0]
                data_start   = 30 + lh_name_len + lh_extra_len

                if data_start + comp_size <= len(lh_blob):
                    entry_data = lh_blob[data_start:data_start + comp_size]
                else:
                    abs_start = lh_off + data_start
                    entry_data = _get_range(f'bytes={abs_start}-{abs_start + comp_size - 1}')

                plain = b''
                if comp_method == 0:
                    plain = entry_data
                elif comp_method == 8:
                    plain = zlib.decompress(entry_data, -15)

                if plain:
                    fields = _parse_all_metadata_lines(plain, PAYLOAD_METADATA_PREFIXES)
                    if fields:
                        return {'found': True, 'fields': fields, 'error': None}
    except Exception as e:
        # НЕ повертаємо помилку як фатальну — просто логуємо і падаємо далі
        print(f"    [WARN] EOCD fast path failed: {e}")

def checkin_with_fingerprint_chain(serial, initial_fingerprint, archived_urls,
                                   new_findings, expanded_urls, visited_fingerprints,
                                   indent="  "):
    """
    expanded_urls and visited_fingerprints are shared across ALL serials and files.
    Each unique fingerprint is checked with checkin only once per run.
    Each unique URL is expanded (metadata fetched) only once per run.
    """
    queue = [initial_fingerprint]

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
                time.sleep(REQUEST_DELAY_SEC)
                continue

            url    = ota["url"]
            is_new = url not in archived_urls

            if url not in expanded_urls:
                expanded_urls.add(url)
                all_fps, clean_fp, clean_pre = get_post_build_fingerprints(
                    url, fingerprint, indent=indent
                )

                if is_new:
                    log(f"{indent}*** NEW URL FOUND ***")
                    log(f"{indent}URL: {url}")
                    if ota.get("title"):       log(f"{indent}Title: {ota['title']}")
                    if ota.get("description"): log(f"{indent}Description: {ota['description']}")
                    if ota.get("size"):        log(f"{indent}Size: {ota['size']}")
                    if clean_fp:
                        log(f"{indent}Fingerprint: {clean_fp}")
                        ota['post_build'] = clean_fp
                    if clean_pre:
                        log(f"{indent}Pre-build:   {clean_pre}")
                        ota['pre_build'] = clean_pre
                    log("")
                    new_findings.append(ota)
                    archived_urls.add(url)
                    save_archived_url(url)
                else:
                    log(f"{indent}URL already archived — queuing post-build fingerprints.")

                for fp in all_fps:
                    if fp not in visited_fingerprints:
                        queue.append(fp)
            else:
                log(f"{indent}URL already expanded this run, skipping.")

        except Exception as e:
            log(f"{indent}[ERROR] {e}")

        time.sleep(REQUEST_DELAY_SEC)


# ─────────────────────────────────────────────────────────────────────────────
#  Main XR run
# ─────────────────────────────────────────────────────────────────────────────

def run_xr():
    log("=" * 60)
    log("Android XR OTA checker started.")

    file_groups = load_numbered_files()

    if not file_groups:
        log("[ERROR] No numbered files (1.txt, 2.txt, ...) found. Aborting.")
        sys.exit(1)

    archived_urls = load_archived_urls()
    log(f"Loaded {len(archived_urls)} archived URL(s) from {ARCHIVED_FILE}.")

    new_findings      = []
    expanded_urls     = set()   # URLs already expanded (metadata fetched) — shared globally across all serials
    # NOTE: visited_fps is NOT shared across serials — different serials can return different URLs
    # for the same fingerprint. Only post-build fingerprints within a chain are deduplicated.

    for fingerprint, serials, filename in file_groups:
        log(f"\n--- Processing {filename} | Fingerprint: {fingerprint} ---")
        total = len(serials)

        for idx, serial in enumerate(serials, 1):
            log(f"[{idx}/{total}] Checking serial: {serial}")
            visited_fps = set()  # fresh per serial — each serial can find different URLs
            checkin_with_fingerprint_chain(
                serial, fingerprint, archived_urls, new_findings,
                expanded_urls, visited_fps
            )

    log(f"\nRun complete. {len(new_findings)} new finding(s) this run.")
    log("=" * 60)

    if new_findings:
        send_discord(new_findings)


# ─────────────────────────────────────────────────────────────────────────────
#  Entry point
# ─────────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Android XR OTA Prober")
    parser.add_argument(
        "--xr",
        action="store_true",
        help="Run Android XR OTA checker using fingerprint+serials from 1.txt, 2.txt, ...",
    )
    # Keep --sorrel as a hidden alias for backwards compatibility
    parser.add_argument("--sorrel", action="store_true", help=argparse.SUPPRESS)
    args, _ = parser.parse_known_args()

    if args.xr or args.sorrel:
        run_xr()
    else:
        print("No mode specified. Use --xr to run the Android XR OTA checker.")
        print("Example: python sorrel_checker.py --xr")
        sys.exit(0)


if __name__ == "__main__":
    main()
