# common/config_bootstrap.py
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, TypedDict, cast

from dotenv import load_dotenv

from common.paths import (
    default_config_path,
    resolve_output_dir_only,
    user_config_dir_path,
)


# ---- Esquema de configuração (sem input_path) ----
class AppConfig(TypedDict, total=False):
    # diretório onde o app pode escrever artefatos (CSVs, PDFs, exports, etc.)
    output_dir: str
    # flags e limites
    dry_run: bool
    max_rows: int
    # integrações (exemplos; valores preferencialmente via .env)
    guru_base_url: str
    shop_url: str  # domínio Shopify sem https://
    # qualquer outro campo específico do app...


DEFAULTS: AppConfig = {
    "output_dir": "out",
    "dry_run": True,
    "max_rows": 1000,
}


def load_env(dotenv_filename: str = ".env") -> None:
    """
    Carrega variáveis do .env (se existir), sem sobrepor variáveis já setadas no ambiente.
    """
    load_dotenv(dotenv_path=Path(dotenv_filename), override=False)


def load_config() -> tuple[AppConfig, Path]:
    """
    Carrega config.json com ordem de precedência:
      1) LG_CONFIG_PATH (se existir)
      2) %APPDATA%/lg-logistica/config.json (Windows) ou equivalente (Platformdirs)
      3) app_root/config.json (somente leitura)
    Aplica defaults e validações básicas.
    """
    cfg_path = default_config_path()
    if not cfg_path.exists():
        # cria um config de usuário com defaults (primeira execução)
        user_cfg = user_config_dir_path() / "config.json"
        user_cfg.parent.mkdir(parents=True, exist_ok=True)
        with user_cfg.open("w", encoding="utf-8") as f:
            json.dump(DEFAULTS, f, ensure_ascii=False, indent=2)
        cfg_path = user_cfg

    with cfg_path.open("r", encoding="utf-8") as f:
        raw: dict[str, Any] = json.load(f)

    # aplica defaults sem input_path
    merged: dict[str, Any] = {**DEFAULTS, **raw}  # <- dict “solto”
    cfg: AppConfig = cast(AppConfig, merged)  # <- agora declaramos o tipo correto

    # normaliza e garante output_dir absoluto (em diretório de usuário)
    OUTPUT_DIR = resolve_output_dir_only(cfg.get("output_dir", DEFAULTS["output_dir"]))
    cfg["output_dir"] = str(OUTPUT_DIR)

    # validações leves
    if not isinstance(cfg.get("max_rows"), int) or cfg["max_rows"] <= 0:
        cfg["max_rows"] = DEFAULTS["max_rows"]
    if not isinstance(cfg.get("dry_run"), bool):
        cfg["dry_run"] = DEFAULTS["dry_run"]

    return cfg, cfg_path
