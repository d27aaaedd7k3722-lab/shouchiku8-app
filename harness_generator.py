"""ハーネス Generator: planner が出したパラメータを params.json に書込む。"""
from __future__ import annotations
import os, json

HERE = os.path.dirname(os.path.abspath(__file__))
PARAMS_PATH = os.path.join(HERE, '_harness', 'params.json')


def write_params(iteration: int, params: dict, history: list = None) -> None:
    data = {
        'iteration': iteration,
        'params':    params,
        'history':   history or [],
    }
    os.makedirs(os.path.dirname(PARAMS_PATH), exist_ok=True)
    with open(PARAMS_PATH, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def read_params() -> dict:
    if not os.path.exists(PARAMS_PATH):
        return {'iteration': 0, 'params': {}, 'history': []}
    with open(PARAMS_PATH, encoding='utf-8') as f:
        return json.load(f)
