# common/settings.py
from pathlib import Path

from pydantic_settings import BaseSettings, SettingsConfigDict

BASE_DIR = Path(__file__).resolve().parent.parent  # sobe até a pasta do main.py


class Settings(BaseSettings):
    API_KEY_GURU: str
    SHOP_URL: str
    SHOPIFY_TOKEN: str
    OPENAI_API_KEY: str
    FRETEBARATO_URL: str
    APP_ENV: str = "dev"

    model_config = SettingsConfigDict(
        env_file=str(BASE_DIR / ".env"),  # garante que busca o .env na raiz do projeto
        env_file_encoding="utf-8",
        extra="ignore",
    )


settings = Settings()
