from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import random
import re
import socket
import subprocess
import sys
import time
import uuid
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable, Optional

import gspread
import requests
from gspread import Worksheet
from selenium import webdriver
from selenium.common.exceptions import TimeoutException, WebDriverException
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.support.ui import WebDriverWait


SPREADSHEET_ID = "1dIXB1bDtD0NdWjVgWj6Cm8o7NZ4F_wD-rYtNatgJNps"
DEFAULT_WORKSHEET = "GTIN"
LOCK_WORKSHEET = "_GTIN_LOCKS"
GS1_URL = "https://www2.gs1.org/services/verified-by-gs1"

# Google Sheet 열 번호(1부터 시작): L, N, P -> Q, R
BARCODE_COLUMNS = (12, 14, 16)
STATUS_COLUMN = 17
RESULT_COLUMN = 18

# 열 순서가 바뀌면 잘못된 칸에 결과를 기록할 수 있으므로, 처리에 사용하는
# 핵심 헤더는 실행 시작 시 반드시 확인한다.
EXPECTED_HEADERS = {
    12: "협력사 상품바코드",
    14: "컴퓨존 상품바코드",
    16: "컴퓨존 상품바코드",
    17: "확인여부",
    18: "결과",
}

STATUS_WORKING = "확인중"
STATUS_DONE = "확인완료"
STATUS_FAILED = "확인불가"
FINAL_STATUSES = {STATUS_DONE, STATUS_FAILED}

LOCK_HEADERS = (
    "worksheet",
    "data_row",
    "claim_id",
    "machine_id",
    "claimed_at_utc",
    "state",
)

CHECK_DIGIT_ERROR_MARKERS = (
    "last digit of your barcode number is incorrect",
    "check digit is incorrect",
    "incorrect check digit",
)
NEGATIVE_MARKERS = (
    "not found",
    "no result",
    "no record",
    "invalid gtin",
    "not a valid",
    "cannot be found",
    "could not be found",
    "does not exist",
    "unable to verify",
    *CHECK_DIGIT_ERROR_MARKERS,
)
BLOCK_MARKERS = (
    "too many requests",
    "maximum of 30",
    "query limit",
    "daily limit",
    "request is blocked",
    "service unavailable",
)

DEFAULT_ADAPTER_KEY = (
    r"HKEY_LOCAL_MACHINE\SYSTEM\CurrentControlSet\Control\Class"
    r"\{4d36e972-e325-11ce-bfc1-08002be10318}\0001"
)
DEFAULT_ADAPTER_INTERFACE = "이더넷"


class ManualActionRequired(RuntimeError):
    """사용자 확인이 필요한 브라우저 화면이 나타난 경우."""


class QueryBlocked(RuntimeError):
    """CAPTCHA, 사용량 제한 또는 차단으로 조회를 계속할 수 없는 경우."""


def generate_mac() -> str:
    return "02" + "".join(random.choice("0123456789ABCDEF") for _ in range(10))


def get_current_ip() -> str:
    try:
        return requests.get("https://api.ipify.org", timeout=10).text.strip()
    except Exception:
        return "unknown"


def change_mac(adapter_key: str, adapter_interface_name: str) -> str:
    """aa.py의 MAC/IP 변경 흐름을 GTIN 조회용으로 사용한다."""

    new_mac = generate_mac()
    logging.warning("MAC 주소 변경 시도: %s", new_mac)
    logging.info("어댑터 레지스트리 키: %s", adapter_key)

    subprocess.call(f'reg add "{adapter_key}" /v NetworkAddress /d {new_mac} /f', shell=True)
    subprocess.call(
        f'netsh interface set interface name="{adapter_interface_name}" admin=disable',
        shell=True,
    )
    time.sleep(3)
    subprocess.call(
        f'netsh interface set interface name="{adapter_interface_name}" admin=enable',
        shell=True,
    )
    time.sleep(3)

    subprocess.call("ipconfig /release", shell=True)
    time.sleep(3)
    try:
        subprocess.run("ipconfig /renew", shell=True, timeout=15)
    except subprocess.TimeoutExpired:
        logging.warning("ipconfig /renew 시간 초과")
    time.sleep(3)

    current_ip = get_current_ip()
    logging.warning("새 IP 확인: %s", current_ip)
    return current_ip


def kill_chrome_processes() -> None:
    try:
        os.system("taskkill /F /IM chrome.exe /T")
        os.system("taskkill /F /IM chromedriver.exe /T")
        logging.info("기존 Chrome 및 chromedriver 프로세스를 정리했습니다.")
    except Exception as exc:
        logging.warning("Chrome 프로세스 정리 중 오류: %s", exc)


@dataclass(frozen=True)
class Claim:
    data_row: int
    claim_id: str
    lock_row: int


@dataclass(frozen=True)
class LookupResult:
    verified: bool
    text: str


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def utc_text(value: Optional[datetime] = None) -> str:
    return (value or utc_now()).isoformat(timespec="seconds")


def parse_utc(value: str) -> Optional[datetime]:
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=timezone.utc)
        return parsed.astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None


def machine_id() -> str:
    source = f"{socket.gethostname()}|{uuid.getnode()}"
    suffix = hashlib.sha256(source.encode("utf-8")).hexdigest()[:10]
    return f"{socket.gethostname()}-{suffix}"


def cell(row: list[str], one_based_column: int) -> str:
    index = one_based_column - 1
    return row[index].strip() if index < len(row) else ""


def normalize_barcode(value: str) -> Optional[str]:
    """시트 표시값에서 숫자 GTIN 후보만 보존한다.

    공백, 하이픈, 작은따옴표는 셀 서식상 자주 들어가므로 제거한다. 지수 표기나
    소수점은 원래 숫자를 안전하게 복원할 수 없으므로 거부한다.
    """

    cleaned = value.strip().lstrip("'")
    if not cleaned or cleaned.lower() in {"미확인", "없음", "none", "n/a", "na"}:
        return None
    cleaned = re.sub(r"[\s-]", "", cleaned)
    if not cleaned.isdigit() or not 8 <= len(cleaned) <= 14:
        return None
    return cleaned


def select_barcode(row: list[str]) -> tuple[Optional[str], Optional[int]]:
    for column in BARCODE_COLUMNS:
        barcode = normalize_barcode(cell(row, column))
        if barcode:
            return barcode, column
    return None, None


def validate_headers(header: list[str]) -> None:
    """조회/기록 대상 열이 사용자가 지정한 시트 구성과 일치하는지 확인한다."""

    problems: list[str] = []
    for column, expected in EXPECTED_HEADERS.items():
        actual = cell(header, column)
        if actual != expected:
            problems.append(f"{column}열: 기대값 '{expected}', 실제값 '{actual or '(비어 있음)'}'")
    if problems:
        raise RuntimeError(
            "워크시트의 핵심 헤더가 예상과 달라 실행을 중단했습니다. "
            "열 순서를 확인해 주세요. " + "; ".join(problems)
        )


def compact_text(value: str, limit: int = 3500) -> str:
    lines: list[str] = []
    for raw in value.splitlines():
        line = re.sub(r"\s+", " ", raw).strip()
        if line and (not lines or line != lines[-1]):
            lines.append(line)
    text = " | ".join(lines)
    return text if len(text) <= limit else text[: limit - 1] + "…"


def check_digit_error_message(barcode: str, result_text: str) -> Optional[str]:
    lower = result_text.lower()
    if not any(marker in lower for marker in CHECK_DIGIT_ERROR_MARKERS):
        return None
    return f"체크 디지트 오류: 입력 {barcode}"


class SheetCoordinator:
    """숨김 로그 시트를 사용해 여러 PC의 같은 행 처리를 조정한다.

    Sheets API에는 조건부 셀 쓰기(CAS)가 없으므로 append 순서가 보장되는 로그를
    선점 순서로 사용한다. 같은 행을 거의 동시에 선택해도 가장 먼저 append된
    CLAIMED 항목만 처리한다.
    """

    def __init__(
        self,
        service_account_file: Path,
        spreadsheet_id: str,
        worksheet_name: str,
        stale_minutes: int,
        owner: str,
    ) -> None:
        client = gspread.service_account(filename=str(service_account_file))
        self.spreadsheet = client.open_by_key(spreadsheet_id)
        self.worksheet = self.spreadsheet.worksheet(worksheet_name)
        self.lock_sheet = self._ensure_lock_sheet()
        self.worksheet_name = worksheet_name
        self.owner = owner
        self.stale_after = timedelta(minutes=stale_minutes)

    def _ensure_lock_sheet(self) -> Worksheet:
        try:
            lock_sheet = self.spreadsheet.worksheet(LOCK_WORKSHEET)
        except gspread.WorksheetNotFound:
            lock_sheet = self.spreadsheet.add_worksheet(
                title=LOCK_WORKSHEET,
                rows=2000,
                cols=len(LOCK_HEADERS),
            )
            lock_sheet.update(
                values=[list(LOCK_HEADERS)],
                range_name="A1:F1",
                value_input_option="RAW",
            )
            try:
                lock_sheet.hide()
            except Exception:
                logging.warning("잠금 시트를 숨기지 못했지만 동작에는 영향이 없습니다.")

        header = lock_sheet.row_values(1)
        if header[: len(LOCK_HEADERS)] != list(LOCK_HEADERS):
            raise RuntimeError(
                f"{LOCK_WORKSHEET} 시트의 헤더가 예상과 다릅니다. "
                "프로그램이 만든 잠금 시트인지 확인해 주세요."
            )
        return lock_sheet

    def rows(self) -> list[list[str]]:
        return self.worksheet.get_all_values()

    def status(self, data_row: int) -> str:
        value = self.worksheet.cell(data_row, STATUS_COLUMN).value
        return value.strip() if value else ""

    def _lock_records(self, data_row: int) -> list[tuple[int, list[str]]]:
        values = self.lock_sheet.get_all_values()
        records: list[tuple[int, list[str]]] = []
        for lock_row, record in enumerate(values[1:], start=2):
            if len(record) < len(LOCK_HEADERS):
                record += [""] * (len(LOCK_HEADERS) - len(record))
            if record[0] == self.worksheet_name and record[1] == str(data_row):
                records.append((lock_row, record))
        return records

    def _active_claims(self, data_row: int) -> list[tuple[int, list[str]]]:
        cutoff = utc_now() - self.stale_after
        active: list[tuple[int, list[str]]] = []
        for lock_row, record in self._lock_records(data_row):
            claimed_at = parse_utc(record[4])
            if record[5] == "CLAIMED" and claimed_at and claimed_at >= cutoff:
                active.append((lock_row, record))
        return active

    def is_stale_working_row(self, data_row: int) -> bool:
        return self.status(data_row) == STATUS_WORKING and not self._active_claims(data_row)

    def try_claim(self, data_row: int) -> Optional[Claim]:
        current_status = self.status(data_row)
        if current_status in FINAL_STATUSES:
            return None
        if current_status == STATUS_WORKING and self._active_claims(data_row):
            return None

        claim_id = uuid.uuid4().hex
        response = self.lock_sheet.append_row(
            [
                self.worksheet_name,
                str(data_row),
                claim_id,
                self.owner,
                utc_text(),
                "CLAIMED",
            ],
            value_input_option="RAW",
        )
        updated_range = response.get("updates", {}).get("updatedRange", "")
        match = re.search(r"!(?:[A-Z]+)(\d+):", updated_range)
        lock_row = int(match.group(1)) if match else self._find_claim_row(claim_id)

        # 거의 동시에 append된 다른 PC의 항목이 보일 시간을 준다.
        time.sleep(random.uniform(1.2, 2.0))
        active = self._active_claims(data_row)
        winner = min(active, key=lambda item: item[0]) if active else None
        if not winner or winner[1][2] != claim_id:
            self._set_claim_state(lock_row, "LOST")
            return None

        current_status = self.status(data_row)
        if current_status in FINAL_STATUSES:
            self._set_claim_state(lock_row, "LOST")
            return None

        self.worksheet.update_cell(data_row, STATUS_COLUMN, STATUS_WORKING)
        time.sleep(0.8)
        active = self._active_claims(data_row)
        winner = min(active, key=lambda item: item[0]) if active else None
        if not winner or winner[1][2] != claim_id:
            self._set_claim_state(lock_row, "LOST")
            return None
        return Claim(data_row=data_row, claim_id=claim_id, lock_row=lock_row)

    def _find_claim_row(self, claim_id: str) -> int:
        match = self.lock_sheet.find(claim_id, in_column=3)
        if not match:
            raise RuntimeError("추가한 잠금 행을 다시 찾지 못했습니다.")
        return match.row

    def _set_claim_state(self, lock_row: int, state: str) -> None:
        self.lock_sheet.update_cell(lock_row, 6, state)

    def finish(self, claim: Claim, status: str, result: str) -> None:
        if status not in FINAL_STATUSES:
            raise ValueError(f"완료 상태가 올바르지 않습니다: {status}")
        self.worksheet.update(
            values=[[status, result]],
            range_name=f"Q{claim.data_row}:R{claim.data_row}",
            value_input_option="RAW",
        )
        self._set_claim_state(claim.lock_row, "DONE")

    def keep_claim_for_manual_action(self, claim: Claim, reason: str) -> None:
        # Q열은 확인중으로 두고 R열에 중단 사유를 남긴다. CLAIMED 상태는
        # stale_minutes 동안 다른 PC가 가져가지 못하도록 유지한다.
        self.worksheet.update(
            values=[[STATUS_WORKING, reason]],
            range_name=f"Q{claim.data_row}:R{claim.data_row}",
            value_input_option="RAW",
        )


class GS1Browser:
    def __init__(self, profile_dir: Path, headless: bool, timeout: int) -> None:
        options = webdriver.ChromeOptions()
        options.add_argument("--window-size=1500,1000")
        options.add_argument("--no-first-run")
        options.add_argument("--disable-popup-blocking")
        options.add_argument(f"--user-data-dir={profile_dir.resolve()}")
        if headless:
            options.add_argument("--headless=new")
        self.driver = webdriver.Chrome(options=options)
        self.wait = WebDriverWait(self.driver, timeout)
        self.timeout = timeout
        self.driver.get(GS1_URL)
        self._dismiss_cookie_banner()
        self._ensure_page_available()

    def close(self) -> None:
        try:
            self.driver.quit()
        except Exception:
            pass

    def _dismiss_cookie_banner(self) -> None:
        for element_id in ("onetrust-reject-all-handler", "onetrust-accept-btn-handler"):
            elements = self.driver.find_elements(By.ID, element_id)
            if elements and elements[0].is_displayed():
                # 분석/광고 쿠키가 필요하지 않으므로 기본적으로 선택 쿠키를 거부한다.
                if element_id == "onetrust-reject-all-handler":
                    self.driver.execute_script("arguments[0].click()", elements[0])
                break

    def _page_text(self) -> str:
        try:
            return self.driver.find_element(By.TAG_NAME, "body").text
        except Exception:
            return ""

    def _ensure_page_available(self) -> None:
        text = self._page_text().lower()
        if any(marker in text for marker in BLOCK_MARKERS):
            raise QueryBlocked("GS1 사이트가 현재 접속 또는 조회를 차단했습니다.")
        self.wait.until(lambda d: d.find_elements(By.ID, "gtin"))

    def _visible_terms_dialog(self) -> bool:
        dialogs = self.driver.find_elements(By.CSS_SELECTOR, ".ui-dialog, [role='dialog']")
        if any(
            dialog.is_displayed()
            and "Terms of Use" in dialog.text
            and "Accept" in dialog.text
            for dialog in dialogs
        ):
            return True

        # GS1의 새 팝업은 dialog role/class 없이 표시되므로 실제 동의 버튼도
        # 함께 확인한다. 숨겨진 템플릿 버튼은 제외해 오탐을 막는다.
        accept_buttons = self.driver.find_elements(By.CSS_SELECTOR, "button.btn-accept")
        return any(
            button.is_displayed() and button.text.strip().lower() == "accept"
            for button in accept_buttons
        )


    def _wait_for_manual_gate(self, description: str, seconds: int) -> None:
        logging.warning("%s 브라우저에서 직접 처리해 주세요. 최대 %d초 기다립니다.", description, seconds)
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            if description.startswith("이용약관"):
                if not self._visible_terms_dialog():
                    return
            
            time.sleep(1)
        raise ManualActionRequired(f"{description} 제한 시간 초과")

    def lookup(self, barcode: str, manual_wait: int) -> LookupResult:
        self.driver.get(GS1_URL)
        self._dismiss_cookie_banner()
        self._ensure_page_available()

        input_element = self.wait.until(lambda d: d.find_element(By.ID, "gtin"))
        input_element.click()
        input_element.send_keys(Keys.CONTROL, "a")
        input_element.send_keys(barcode)
        submit = self.driver.find_element(By.NAME, "gtin_submit")
        self.driver.execute_script("arguments[0].scrollIntoView({block: 'center'})", submit)
        submit.click()  # 실제 mousedown 이벤트가 URL의 ?gtin= 값을 만든다.

        if self._visible_terms_dialog():
            self._wait_for_manual_gate("이용약관 동의", manual_wait)
            # 동의 직후 첫 요청이 자동 재전송되지 않는 사이트 버전도 있어 재조회한다.
            self.driver.get(f"{GS1_URL}?gtin={barcode}")

        try:
            self.wait.until(lambda d: self._lookup_finished(barcode))
        except TimeoutException as exc:
    
            raise QueryBlocked("GS1 조회 결과를 제한 시간 안에 받지 못했습니다.") from exc

        
        text = self._extract_result_text(barcode)
        if not text:
            # 검색 직후 로딩용 요소가 잠깐 결과처럼 보이고, 약관 팝업은 뒤늦게
            # 렌더링되는 경우가 있다. 짧게 재확인해 빈 결과로 오판하지 않는다.
            try:
                WebDriverWait(self.driver, min(5, self.timeout)).until(
                    lambda d: self._visible_terms_dialog()
                    or bool(self._extract_result_text(barcode))
                )
            except TimeoutException:
                pass

            if self._visible_terms_dialog():
                self._wait_for_manual_gate("이용약관 동의", manual_wait)
                self.driver.get(f"{GS1_URL}?gtin={barcode}")
                try:
                    self.wait.until(lambda d: self._lookup_finished(barcode))
                except TimeoutException as exc:
                    raise QueryBlocked("GS1 조회 결과를 제한 시간 안에 받지 못했습니다.") from exc
            text = self._extract_result_text(barcode)

        lower = text.lower()
        if any(marker in lower for marker in BLOCK_MARKERS):
            raise QueryBlocked(text)
        check_digit_error = check_digit_error_message(barcode, text)
        if check_digit_error:
            return LookupResult(verified=False, text=check_digit_error)
        verified = not any(marker in lower for marker in NEGATIVE_MARKERS)
        if not text:
            raise QueryBlocked("GS1 결과 내용을 판독하지 못했습니다.")
        prefix = f"조회 바코드: {barcode}"
        return LookupResult(verified=verified, text=compact_text(f"{prefix}\n{text}"))

    def _lookup_finished(self, barcode: str) -> bool:
        current_url = self.driver.current_url.lower()
        if f"gtin={barcode}" in current_url and self._result_candidates(barcode):
            return True

        text = self._page_text().lower()
        if any(marker in text for marker in BLOCK_MARKERS):
            return True
        if any(marker in text for marker in NEGATIVE_MARKERS):
            return True

        settings = self._settings()
        return any(settings.get(key) not in (None, "", [], {}) for key in (
            "statusMessage",
            "messageStatus",
            "typeError",
            "queryResponse",
        ))

    def _settings(self) -> dict[str, Any]:
        value = self.driver.execute_script(
            "return (window.drupalSettings && "
            "window.drupalSettings.gs1_verified_search) || {};"
        )
        return value if isinstance(value, dict) else {}

  

    def _result_candidates(self, barcode: str) -> list[str]:
        selectors = (
            ".verified-search-results",
            "#verified-search-results",
            ".search-results",
            ".search-result",
            ".verified-result",
            ".vbg-results",
            ".result-wrapper",
            ".query-results",
            ".messages--error",
            ".form-item--error-message",
            "[role='alert']",
        )
        candidates: list[str] = []
        for selector in selectors:
            for element in self.driver.find_elements(By.CSS_SELECTOR, selector):
                if element.is_displayed() and element.text.strip():
                    candidates.append(element.text.strip())

        # 사이트 클래스명이 변경돼도 바코드가 포함된 가장 작은 결과 컨테이너를 찾는다.
        xpath = f"//*[contains(normalize-space(.), '{barcode}')]"
        barcode_elements = self.driver.find_elements(By.XPATH, xpath)
        sized: list[tuple[int, str]] = []
        for element in barcode_elements:
            if not element.is_displayed() or element.tag_name.lower() in {"html", "body", "main", "form"}:
                continue
            text = element.text.strip()
            if 20 <= len(text) <= 8000:
                sized.append((len(text), text))
        if sized:
            candidates.append(min(sized, key=lambda item: item[0])[1])
        return candidates

    def _extract_result_text(self, barcode: str) -> str:
        candidates = self._result_candidates(barcode)
        if candidates:
            # 가장 긴 결과 블록이 회사/상품 속성을 더 온전히 포함하는 경향이 있다.
            return max((compact_text(text) for text in candidates), key=len)

        settings = self._settings()
        parts: list[str] = []
        for key in ("statusMessage", "messageStatus", "typeError", "queryResponse"):
            value = settings.get(key)
            if value not in (None, "", [], {}):
                if isinstance(value, (dict, list)):
                    value = json.dumps(value, ensure_ascii=False, separators=(",", ":"))
                parts.append(f"{key}: {value}")
        return "\n".join(parts)


def pending_rows(values: list[list[str]], coordinator: SheetCoordinator) -> Iterable[tuple[int, list[str]]]:
    for data_row, row in enumerate(values[1:], start=2):
        status = cell(row, STATUS_COLUMN)
        if status in FINAL_STATUSES:
            continue
        if status == STATUS_WORKING and not coordinator.is_stale_working_row(data_row):
            continue
        yield data_row, row


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Google Sheet의 GTIN을 Verified by GS1에서 확인합니다.")
    parser.add_argument("--service-account", default="service_account.json")
    parser.add_argument("--spreadsheet-id", default=SPREADSHEET_ID)
    parser.add_argument("--worksheet", default=DEFAULT_WORKSHEET)
    parser.add_argument("--stale-minutes", type=int, default=30, help="중단된 확인중 작업의 만료 시간")
    parser.add_argument("--timeout", type=int, default=90, help="GS1 결과 대기 시간(초)")
    parser.add_argument("--limit", type=int, default=0, help="한 번 실행할 때 처리할 최대 조회 건수. 0이면 제한 없음")
    parser.add_argument("--dry-run", action="store_true", help="처리 대상만 출력하고 조회하지 않음")
    parser.add_argument("--headless", action="store_true", help="Chrome을 headless 모드로 실행")
    parser.add_argument("--profile-dir", default=".chrome-gs1-profile", help="Chrome 사용자 프로필 디렉터리")
    parser.add_argument("--manual-wait", type=int, default=180, help="수동 동의/확인 대기 시간(초)")
    parser.add_argument(
        "--mac-change-interval",
        type=int,
        default=20,
        help="지정한 조회 횟수마다 MAC 주소와 IP를 변경합니다. 0이면 비활성화",
    )
    parser.add_argument("--adapter-key", default=DEFAULT_ADAPTER_KEY, help="MAC 변경 대상 어댑터 레지스트리 키")
    parser.add_argument("--adapter-interface", default=DEFAULT_ADAPTER_INTERFACE, help="netsh에서 사용할 네트워크 인터페이스 이름")
   
    return parser


def run(args: argparse.Namespace) -> int:
    if args.limit < 0:
        raise ValueError("--limit 값은 0 이상이어야 합니다.")
    if args.mac_change_interval < 0:
        raise ValueError("--mac-change-interval 값은 0 이상이어야 합니다.")
    credentials = Path(args.service_account).resolve()
    if not credentials.is_file():
        raise FileNotFoundError(f"서비스 계정 파일을 찾을 수 없습니다: {credentials}")

    owner = machine_id()
    logging.info("작업 PC: %s", owner)
    coordinator = SheetCoordinator(
        credentials,
        args.spreadsheet_id,
        args.worksheet,
        args.stale_minutes,
        owner,
    )
    values = coordinator.rows()
    if not values:
        raise RuntimeError("워크시트가 비어 있습니다.")
    if len(values[0]) < RESULT_COLUMN:
        raise RuntimeError("워크시트에 Q(확인여부), R(결과) 열이 없습니다.")
    validate_headers(values[0])

    candidates = list(pending_rows(values, coordinator))
    logging.info("처리 후보 %d개를 찾았습니다.", len(candidates))
    if args.dry_run:
        for index, (data_row, row) in enumerate(candidates, start=1):
            if args.limit and index > args.limit:
                break
            barcode, source_column = select_barcode(row)
            logging.info("행 %d: 바코드=%s, 원본열=%s", data_row, barcode, source_column)
        return 0

    profile_dir = Path(args.profile_dir).resolve()
    browser: Optional[GS1Browser] = None
    lookup_count = 0
    write_count = 0

    def open_browser() -> GS1Browser:
        logging.info("GS1 조회 브라우저를 시작합니다.")
        return GS1Browser(profile_dir, args.headless, args.timeout)

    def rotate_network() -> None:
        nonlocal browser
        if browser:
            browser.close()
            browser = None
        kill_chrome_processes()
        change_mac(args.adapter_key, args.adapter_interface)
        time.sleep(5)

    try:
        browser = open_browser()
        for data_row, row in candidates:
            if args.limit and lookup_count >= args.limit:
                break

            barcode, source_column = select_barcode(row)
            claim = coordinator.try_claim(data_row)
            if not claim:
                continue

            if not barcode:
                coordinator.finish(claim, STATUS_FAILED, "조회 가능한 GTIN 바코드가 없습니다.")
                write_count += 1
                continue

            try:
                assert browser is not None
                logging.info("행 %d 조회 시작: %s열 바코드 %s", data_row, source_column, barcode)
                result = browser.lookup(barcode, args.manual_wait)
                status = STATUS_DONE if result.verified else STATUS_FAILED
                coordinator.finish(claim, status, result.text)
                lookup_count += 1
                write_count += 1
                logging.info("행 %d 조회 완료: %s", data_row, status)
            except ManualActionRequired as exc:
                coordinator.keep_claim_for_manual_action(claim, str(exc))
                logging.warning("수동 처리가 필요해 중단합니다: %s", exc)
                return 2
            except QueryBlocked as exc:
                coordinator.keep_claim_for_manual_action(claim, str(exc))
                logging.warning("조회 차단 감지: %s", exc)
                if args.mac_change_interval:
                    rotate_network()
                    browser = open_browser()
                return 3
            except WebDriverException as exc:
                coordinator.keep_claim_for_manual_action(claim, f"브라우저 오류: {exc}")
                logging.warning("브라우저 오류로 네트워크를 변경하고 중단합니다: %s", exc)
                if args.mac_change_interval:
                    rotate_network()
                return 4

            if (
                args.mac_change_interval
                and lookup_count > 0
                and lookup_count % args.mac_change_interval == 0
            ):
                logging.warning("%d회 조회 완료 → MAC 주소 및 IP 변경을 진행합니다.", lookup_count)
                rotate_network()
                if not args.limit or lookup_count < args.limit:
                    browser = open_browser()
    finally:
        if browser:
            browser.close()

    logging.info("완료: 조회 %d건, 상태 기록 %d건", lookup_count, write_count)
    return 0


def main() -> int:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
    try:
        return run(build_parser().parse_args())
    except KeyboardInterrupt:
        logging.warning("사용자가 프로그램을 중단했습니다.")
        return 130
    except Exception as exc:
        logging.exception("프로그램을 시작하거나 계속할 수 없습니다: %s", exc)
        return 1


if __name__ == "__main__":
    sys.exit(main())
