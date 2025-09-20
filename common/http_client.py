from __future__ import annotations

import random
from typing import Any

import requests
from requests.adapters import HTTPAdapter

try:
    # urllib3 < 2.0
    from urllib3.util.retry import Retry

    _URLLIB3_V2 = False
except Exception:
    # urllib3 >= 2.0 (mesmo nome, mas alguns kwargs mudaram de comportamento)
    from urllib3.util import Retry  # type: ignore

    _URLLIB3_V2 = True

from .errors import ExternalError

# (connect, read) em segundos — pode ser sobrescrito em cada chamada
DEFAULT_TIMEOUT: tuple[float, float] = (5.0, 30.0)

# Forcelist de status considerados transitórios
TRANSIENT_STATUSES = (429, 500, 502, 503, 504)

# Métodos que podem ser automaticamente repetidos com segurança
IDEMPOTENT_METHODS = frozenset({"GET", "HEAD", "OPTIONS", "POST"})

# Sessão singleton (thread-safe o suficiente para a maioria dos casos de uso do requests)
_SESSION: requests.Session | None = None


def _build_retry(
    total: int = 5,
    backoff_factor: float = 0.5,
    statuses: tuple[int, ...] = TRANSIENT_STATUSES,
    methods: frozenset[str] = IDEMPOTENT_METHODS,
) -> Retry:
    """
    Cria política de retry exponencial com respeito a Retry-After (429/503).
    """
    # kwargs compatíveis com urllib3 1.26.x e 2.x
    retry = Retry(
        total=total,
        connect=total,
        read=total,
        status=total,
        backoff_factor=backoff_factor,
        status_forcelist=statuses,
        allowed_methods=methods,  # era 'method_whitelist' em versões antigas
        raise_on_status=False,
        respect_retry_after_header=True,
    )
    return retry


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


def get_session() -> requests.Session:
    """
    Retorna uma sessão global com retries/backoff configurados.
    Permite ser trocada em testes passando `session=` nas funções http_*
    """
    global _SESSION
    if _SESSION is None:
        _SESSION = _build_session()
    return _SESSION


def http_get(url: str, **kwargs: Any) -> requests.Response:
    """
    GET com timeout padrão, retries exponenciais (inclui 429/5xx),
    e tradução de erros para ExternalError.
    Aceita:
      - timeout=(connect, read) ou float
      - params, headers, etc. (requests)
      - session: requests.Session (para testes/mocks)
      - jitter_max: float -> jitter aleatório extra (segundos) antes da 1ª tentativa
    """
    timeout = kwargs.pop("timeout", DEFAULT_TIMEOUT)
    session: requests.Session = kwargs.pop("session", get_session())
    jitter_max: float = kwargs.pop("jitter_max", 0.0)

    # Jitter opcional antes da 1ª tentativa (útil quando muitos workers disparam juntos)
    if jitter_max and jitter_max > 0:
        # Import local para evitar custo quando não usado
        import time

        time.sleep(random.uniform(0, jitter_max))

    try:
        res = session.get(url, timeout=timeout, **kwargs)
        # Se a política de retry esgotou, ainda podemos chegar aqui com status 4xx/5xx
        res.raise_for_status()
        return res

    except requests.Timeout as e:
        # Timeout de conexão ou leitura
        raise ExternalError(
            f"Timeout ao chamar {url}",
            code="HTTP_TIMEOUT",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e

    except requests.HTTPError as e:
        # Pode ser 4xx/5xx após esgotar retries. Capturamos status (se houver)
        raw_status: Any = getattr(e.response, "status_code", None)
        status: int | None = raw_status if isinstance(raw_status, int) else None

        # 429 e 5xx são geralmente transitórios; 4xx (exceto 429) normalmente não.
        retryable = bool(status in TRANSIENT_STATUSES)

        raise ExternalError(
            f"Falha HTTP {status} ao chamar {url}",
            code="HTTP_ERROR",
            cause=e,
            retryable=retryable,
            data={"url": url, "status": status, "text": getattr(e.response, "text", None)},
        ) from e

    except requests.RequestException as e:
        # DNS, conexão abortada, TLS, etc. — tratar como transitório por padrão
        raise ExternalError(
            f"Erro de rede ao chamar {url}",
            code="HTTP_REQUEST_ERROR",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e


def http_post(url: str, **kwargs: Any) -> requests.Response:
    """
    POST com timeout padrão, retries (inclui 429/5xx, respeita Retry-After),
    e tradução de erros para ExternalError.

    Aceita:
      - timeout=(connect, read) ou float
      - json, data, headers, etc. (kwargs do requests)
      - session: requests.Session (para testes/mocks)
      - jitter_max: float -> atraso aleatório opcional antes da 1ª tentativa
    """
    timeout = kwargs.pop("timeout", DEFAULT_TIMEOUT)
    session: requests.Session = kwargs.pop("session", get_session())
    jitter_max: float = kwargs.pop("jitter_max", 0.0)

    if jitter_max and jitter_max > 0:
        import time

        time.sleep(random.uniform(0, jitter_max))

    try:
        res = session.post(url, timeout=timeout, **kwargs)
        res.raise_for_status()
        return res

    except requests.Timeout as e:
        raise ExternalError(
            f"Timeout ao chamar {url}",
            code="HTTP_TIMEOUT",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e

    except requests.HTTPError as e:
        raw_status: Any = getattr(e.response, "status_code", None)
        status: int | None = raw_status if isinstance(raw_status, int) else None
        retryable = bool(status in TRANSIENT_STATUSES)  # 429/5xx
        raise ExternalError(
            f"Falha HTTP {status} ao chamar {url}",
            code="HTTP_ERROR",
            cause=e,
            retryable=retryable,
            data={"url": url, "status": status, "text": getattr(e.response, "text", None)},
        ) from e

    except requests.RequestException as e:
        raise ExternalError(
            f"Erro de rede ao chamar {url}",
            code="HTTP_REQUEST_ERROR",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e
