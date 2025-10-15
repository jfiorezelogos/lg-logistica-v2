# common/paths.py
from __future__ import annotations

import os
import sys
from pathlib import Path

from platformdirs import user_cache_dir, user_config_dir, user_data_dir, user_log_dir

APP_NAME = "lg-logistica"
APP_AUTHOR = "Logos Editora"


def is_frozen() -> bool:
    return getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS")


def app_root() -> Path:
    # onde estão os arquivos do app (repo, venv, ou pasta de extração do PyInstaller)
    if is_frozen():
        return Path(sys._MEIPASS)  # type: ignore[attr-defined]
    return Path(__file__).resolve().parents[1]  # raiz do projeto


def user_config_dir_path() -> Path:
    return Path(user_config_dir(APP_NAME, APP_AUTHOR))


def user_data_dir_path() -> Path:
    return Path(user_data_dir(APP_NAME, APP_AUTHOR))


def user_cache_dir_path() -> Path:
    return Path(user_cache_dir(APP_NAME, APP_AUTHOR))


def user_log_dir_path() -> Path:
    return Path(user_log_dir(APP_NAME, APP_AUTHOR))


def ensure_dirs() -> None:
    for p in [user_config_dir_path(), user_data_dir_path(), user_cache_dir_path(), user_log_dir_path()]:
        p.mkdir(parents=True, exist_ok=True)


def env_path(key: str) -> Path | None:
    v = os.getenv(key, "").strip()
    return Path(v) if v else None


def default_config_path() -> Path:
    # 1) ENV > 2) %APPDATA%\lg-logistica\config.json > 3) app_root\config.json (somente leitura)
    p = env_path("LG_CONFIG_PATH")
    if p and p.exists():
        return p
    uc = user_config_dir_path() / "config.json"
    if uc.exists():
        return uc
    return app_root() / "config.json"


def resolve_input_output_paths(cfg: dict) -> tuple[Path, Path]:
    """
    Converte 'input_path' e 'output_dir' do config para paths absolutos e Windows-safe.
    - Se caminho vier relativo, assume raiz = user_data_dir (não a pasta do código)
    - Garante criação de output_dir
    """
    ensure_dirs()
    in_raw = str(cfg.get("input_path", "dados.csv")).strip()
    out_raw = str(cfg.get("output_dir", "out")).strip()

    in_path = Path(in_raw)
    if not in_path.is_absolute():
        in_path = user_data_dir_path() / in_raw

    out_dir = Path(out_raw)
    if not out_dir.is_absolute():
        out_dir = user_data_dir_path() / out_raw

    out_dir.mkdir(parents=True, exist_ok=True)
    return in_path, out_dir


def resolve_output_dir_only(out_raw: str | os.PathLike[str]) -> Path:
    """
    Converte 'output_dir' para path absoluto e Windows-safe.
    - Se vier relativo, baseia em user_data_dir.
    - Cria o diretório.
    """
    ensure_dirs()
    out_dir = Path(out_raw)
    if not out_dir.is_absolute():
        out_dir = user_data_dir_path() / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    return out_dir


def default_log_file() -> Path:
    ensure_dirs()
    return user_log_dir_path() / "sistema.log"
