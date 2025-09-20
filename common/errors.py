# common/errors.py
from __future__ import annotations

import os
from typing import Any


class AppError(Exception):
    def __init__(
        self,
        message: str,
        *,
        code: str = "APP_ERROR",
        cause: BaseException | None = None,
        data: dict[str, Any] | None = None,
        retryable: bool = False,
    ) -> None:
        super().__init__(message)
        self.code = code
        self.cause = cause
        self.data = data or {}
        self.retryable = retryable


class UserError(AppError):
    def __init__(self, message: str, *, code: str = "USER_ERROR", **kw: Any) -> None:
        super().__init__(message, code=code, **kw)


class ExternalError(AppError):
    def __init__(
        self,
        message: str,
        *,
        code: str = "EXTERNAL_ERROR",
        retryable: bool = True,
        **kw: Any,
    ) -> None:
        super().__init__(message, code=code, retryable=retryable, **kw)


class SystemError(AppError):
    def __init__(self, message: str, *, code: str = "SYSTEM_ERROR", **kw: Any) -> None:
        super().__init__(message, code=code, **kw)


def to_user_message(exc: BaseException, *, debug: bool | None = None) -> str:
    if debug is None:
        debug = bool(os.getenv("DEBUG"))
    if isinstance(exc, AppError):
        base = f"[{exc.code}] {exc}"
        if debug and getattr(exc, "data", None):
            base += f" | data={exc.data}"
        if debug and getattr(exc, "cause", None):
            base += f" | cause={type(exc.cause).__name__}: {exc.cause}"
        return base
    return "Ocorreu um erro inesperado. " "Tente novamente e, se persistir, fale com o suporte."
