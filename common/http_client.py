from __future__ import annotations

import logging  # [prof]

# === adições no topo ===
import os  # [prof]
import random
import time
from functools import lru_cache
from typing import Any

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

from .errors import ExternalError

# [prof] flag para ligar/desligar telemetria via env (sem mudar chamadas)
_HTTP_PROF = os.getenv("HTTP_CLIENT_PROF", "0") in ("1", "true", "True")
_log = logging.getLogger(__name__)

# (connect, read) em segundos — pode ser sobrescrito em cada chamada
DEFAULT_TIMEOUT: tuple[int, int] = (5, 30)

# Forcelist de status considerados transitórios
TRANSIENT_STATUSES = (429, 500, 502, 503, 504)

# Métodos que podem ser automaticamente repetidos com segurança
IDEMPOTENT_METHODS = frozenset({"GET", "HEAD", "OPTIONS", "POST"})


def _build_retry(
    total: int = 5,
    backoff_factor: float = 0.5,
    statuses: tuple[int, ...] = TRANSIENT_STATUSES,
    methods: frozenset[str] = IDEMPOTENT_METHODS,
) -> Retry:
    """Cria política de retry exponencial com respeito a Retry-After (429/503).

    Compatível com urllib3 novo (allowed_methods) e antigo (method_whitelist), sem esbarrar no mypy.
    """
    common_kwargs: dict[str, Any] = {
        "total": total,
        "connect": total,
        "read": total,
        "status": total,
        "backoff_factor": backoff_factor,
        "status_forcelist": statuses,
        "raise_on_status": False,
        "respect_retry_after_header": True,
    }

    # Primeiro tentamos com a API nova (allowed_methods)
    try:
        kwargs_new = {"allowed_methods": methods, **common_kwargs}
        return Retry(**kwargs_new)
    except TypeError:
        # Fallback: API antiga (method_whitelist)
        kwargs_old = {"method_whitelist": methods, **common_kwargs}
        return Retry(**kwargs_old)


def _build_session() -> requests.Session:
    s = requests.Session()

    # Headers padrão (pode ser sobrescrito por kwargs da chamada)
    s.headers.update(
        {
            "User-Agent": "lg-logistica-v2/HTTPClient (+https://example.invalid)",
            "Accept": "application/json, */*;q=0.1",
        }
    )

    retry = _build_retry()
    adapter = HTTPAdapter(max_retries=retry, pool_connections=50, pool_maxsize=50)
    s.mount("https://", adapter)
    s.mount("http://", adapter)
    return s


@lru_cache(maxsize=1)
def _get_cached_session() -> requests.Session:
    """Sessão padrão (singleton leve, sem global mutável)."""
    return _build_session()


def get_session(session: requests.Session | None = None) -> requests.Session:
    """Retorna uma sessão global com retries/backoff configurados.

    Permite ser trocada em testes passando `session=` nas funções http_*.
    """
    return session or _get_cached_session()


# Em testes, se precisar reinicializar a sessão padrão:
# _get_cached_session.cache_clear()


def http_get(url: str, **kwargs: Any) -> requests.Response:
    """GET com timeout padrão, retries exponenciais (inclui 429/5xx), e tradução de erros para ExternalError."""
    timeout = kwargs.pop("timeout", DEFAULT_TIMEOUT)
    session: requests.Session = kwargs.pop("session", get_session())
    jitter_max: float = kwargs.pop("jitter_max", 0.0)

    if jitter_max and jitter_max > 0:
        time.sleep(random.uniform(0, jitter_max))

    # telemetria opcional (não quebra se não existir)
    _prof_enabled = bool(globals().get("_HTTP_PROF", False))
    _logger = globals().get("_log", None)

    t0 = time.perf_counter()
    try:
        res = session.get(url, timeout=timeout, **kwargs)

        if _prof_enabled and _logger:
            elapsed_ms = int((time.perf_counter() - t0) * 1000)
            hdr = getattr(res, "headers", {}) or {}
            _logger.error(
                "http_prof",
                extra={
                    "method": "GET",
                    "url": url,
                    "status": getattr(res, "status_code", None),
                    "elapsed_ms": elapsed_ms,
                    "size_bytes": len(res.content) if getattr(res, "content", None) is not None else None,
                    "shopify_limit": hdr.get("X-Shopify-Shop-Api-Call-Limit"),
                    "retry_after": hdr.get("Retry-After"),
                    "cf_ray": hdr.get("cf-ray") or hdr.get("CF-RAY"),
                    "ce": hdr.get("Content-Encoding"),
                },
            )

        res.raise_for_status()
        return res

    except requests.Timeout as e:
        if _prof_enabled and _logger:
            _logger.error("http_prof_timeout", extra={"method": "GET", "url": url})
        raise ExternalError(
            f"Timeout ao chamar {url}",
            code="HTTP_TIMEOUT",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e

    except requests.HTTPError as e:
        if _prof_enabled and _logger:
            elapsed_ms = int((time.perf_counter() - t0) * 1000)
            status_code = getattr(e.response, "status_code", None)
            _logger.error(
                "http_prof_http_error",
                extra={"method": "GET", "url": url, "status": status_code, "elapsed_ms": elapsed_ms},
            )

        raw_status: Any = getattr(e.response, "status_code", None)
        status_: int | None = raw_status if isinstance(raw_status, int) else None
        retryable = bool(status_ in TRANSIENT_STATUSES)
        raise ExternalError(
            f"Falha HTTP {status_} ao chamar {url}",
            code="HTTP_ERROR",
            cause=e,
            retryable=retryable,
            data={"url": url, "status": status_, "text": getattr(e.response, "text", None)},
        ) from e

    except requests.RequestException as e:
        if _prof_enabled and _logger:
            elapsed_ms = int((time.perf_counter() - t0) * 1000)
            _logger.error("http_prof_req_error", extra={"method": "GET", "url": url, "elapsed_ms": elapsed_ms})
        raise ExternalError(
            f"Erro de rede ao chamar {url}",
            code="HTTP_REQUEST_ERROR",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e


def http_post(url: str, **kwargs: Any) -> requests.Response:
    """POST com timeout padrão, retries (inclui 429/5xx, respeita Retry-After), e tradução de erros para ExternalError."""
    timeout = kwargs.pop("timeout", DEFAULT_TIMEOUT)
    session: requests.Session = kwargs.pop("session", get_session())
    jitter_max: float = kwargs.pop("jitter_max", 0.0)

    if jitter_max and jitter_max > 0:
        time.sleep(random.uniform(0, jitter_max))

    # telemetria opcional (não quebra se não existir)
    _prof_enabled = bool(globals().get("_HTTP_PROF", False))
    _logger = globals().get("_log", None)

    t0 = time.perf_counter()
    try:
        res = session.post(url, timeout=timeout, **kwargs)

        if _prof_enabled and _logger:
            elapsed_ms = int((time.perf_counter() - t0) * 1000)
            hdr = getattr(res, "headers", {}) or {}
            _logger.error(
                "http_prof",
                extra={
                    "method": "POST",
                    "url": url,
                    "status": getattr(res, "status_code", None),
                    "elapsed_ms": elapsed_ms,
                    "size_bytes": len(res.content) if getattr(res, "content", None) is not None else None,
                    "shopify_limit": hdr.get("X-Shopify-Shop-Api-Call-Limit"),
                    "retry_after": hdr.get("Retry-After"),
                    "cf_ray": hdr.get("cf-ray") or hdr.get("CF-RAY"),
                    "ce": hdr.get("Content-Encoding"),
                },
            )

        res.raise_for_status()
        return res

    except requests.Timeout as e:
        if _prof_enabled and _logger:
            _logger.error("http_prof_timeout", extra={"method": "POST", "url": url})
        raise ExternalError(
            f"Timeout ao chamar {url}",
            code="HTTP_TIMEOUT",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e

    except requests.HTTPError as e:
        if _prof_enabled and _logger:
            elapsed_ms = int((time.perf_counter() - t0) * 1000)
            status_code = getattr(e.response, "status_code", None)
            _logger.error(
                "http_prof_http_error",
                extra={
                    "method": "POST",
                    "url": url,
                    "status": status_code,
                    "elapsed_ms": elapsed_ms,
                },
            )

        raw_status: Any = getattr(e.response, "status_code", None)
        status_: int | None = raw_status if isinstance(raw_status, int) else None
        retryable = bool(status_ in TRANSIENT_STATUSES)
        raise ExternalError(
            f"Falha HTTP {status_} ao chamar {url}",
            code="HTTP_ERROR",
            cause=e,
            retryable=retryable,
            data={
                "url": url,
                "status": status_,
                "text": getattr(e.response, "text", None),
            },
        ) from e

    except requests.RequestException as e:
        if _prof_enabled and _logger:
            elapsed_ms = int((time.perf_counter() - t0) * 1000)
            _logger.error("http_prof_req_error", extra={"method": "POST", "url": url, "elapsed_ms": elapsed_ms})
        raise ExternalError(
            f"Erro de rede ao chamar {url}",
            code="HTTP_REQUEST_ERROR",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e
