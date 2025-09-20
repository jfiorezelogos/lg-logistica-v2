from __future__ import annotations

from typing import Any

import requests

from .errors import ExternalError

DEFAULT_TIMEOUT = (5, 30)  # (connect, read) em segundos


def http_get(url: str, **kwargs: Any) -> requests.Response:
    timeout = kwargs.pop("timeout", DEFAULT_TIMEOUT)
    try:
        res = requests.get(url, timeout=timeout, **kwargs)
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
        raw_status: Any = e.response.status_code if e.response is not None else None

        status: int | None = raw_status if isinstance(raw_status, int) else None
        # 5xx normalmente é recuperável; 4xx costuma ser erro de entrada.
        retryable = (status is not None) and (500 <= status < 600)

        raise ExternalError(
            f"Falha HTTP {status} ao chamar {url}",
            code="HTTP_ERROR",
            cause=e,
            retryable=retryable,
            data={"url": url, "status": status},
        ) from e
    except requests.RequestException as e:
        raise ExternalError(
            f"Erro de rede ao chamar {url}",
            code="HTTP_REQUEST_ERROR",
            cause=e,
            retryable=True,
            data={"url": url},
        ) from e
