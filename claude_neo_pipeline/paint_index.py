"""
paint_index.py — コグニセブン塗装指数の再現（ADDATA 車種別 20.DB / 23.DB / CHM ＋ COM T_KEI_3 / BOOTH）

補修塗装指数 = ①塗り数値（パネル別・CHM 表）＋ ②加算基礎数値（塗料×塗膜×高機能×枚数・T_KEI_3.DB）＋ ③付加数値
実 NEO（C-HR W69 / N-BOX J97）で以下を確認済み:
  PaintingPanel.TimeStandardNew/1/2/3 = CHM「塗り数値」(複数塗) + 高機能塗装加算（耐スリ傷: floor10(0.3 + 0.01×面積)）
  PaintingPanel.PanelArea / PanelName / PanelDivision / PanelTypeDivision / PanelCode / ButtonNo = 20.DB
  PaintingPlan.BaseTime = T_KEI_3.DB (車形, 塗料, 塗膜, B/F/S/T, 枚数)
  PaintingPlan.BoothTime = BOOTH.DB (車形, 塗料, 塗膜, B/F/S/T)
  PaintingBumper.fb_Time = <car>23.DB (F/R, 塗膜クラス, 取替一色/二色, 外傷大, 外傷小, 変形)
"""
from __future__ import annotations

import glob
import html
import math
import os
import re
import shutil
import struct
import subprocess
import tempfile
import time
from typing import Optional

HERE = os.path.dirname(os.path.abspath(__file__))
PAINT_CODE = {'速乾': 1, '速乾ウレタン': 1, '２Ｋ': 3, '2K': 3, '水性': 4}
COAT_CODE = {'ソリッド': 1, 'メタリック': 2, '２コートパール': 3, '2コートパール': 3, '３コートパール': 4, '3コートパール': 4}
HF_CODE = {'しない': 0, 'フッ素': 1, '耐スリ傷': 2, 'スクラッチ': 3, 'スクラッチシールド': 3, 'ｽｸﾗｯﾁ': 3}
HF_NAME = {0: 'しない', 1: 'フッ素', 2: '耐スリ傷', 3: 'ｽｸﾗｯﾁ'}  # PaintingPlan.HFPaintingName（実 NEO の書き方。スクラッチは半角）
HF_KIND = {0: 'B', 1: 'F', 2: 'T', 3: 'S'}  # T_KEI_3 / BOOTH の種別列。S = スクラッチ（実案件 NEO 100 本で HFPainting 3 'ｽｸﾗｯﾁ'。2026-09-12）
COAT_CLASS_BUMPER = {1: 1, 2: 2, 3: 3, 4: 4}  # 23.DB 第 8 列 = PaintingPlan.Coat（1 ソリッド / 2 メタリック / 3 2コートパール / 4 3コートパール）。実機 J52: ソリッド 1.1=行1、2コートパール 1.3=行3、3コートパール 1.5=行4（2026-09-05）


def _panel_key(name: str) -> str:
    """20.DB のパネル名を突き合わせる用に揃える（前後の空白と中の空白を落とす）"""
    return (name or '').replace(' ', '').replace('　', '')


def floor10(x: float) -> float:
    return math.floor(x * 10 + 1e-9) / 10.0


def _xor_lines(path: str) -> list[str]:
    raw = bytes(b ^ 0xFF for b in open(path, 'rb').read())
    return [l for l in raw.decode('cp932', 'replace').splitlines() if l.strip()]


class PaintIndex:
    _warned_chm = False  # CHM を展開できない旨の警告は 1 プロセスに 1 回だけ

    def __init__(self, root: str, car: str, com_dir: Optional[str] = None, body: str = ''):
        # ボディコード（KA81 の 2 桁）。20.DB は同じパネルでもボディで面積が違う行を持つ
        self.body_code = int(str(body).strip()) if str(body).strip().isdigit() else 0
        self.body_unresolved: list = []  # このボディ用の行を選べなかったパネル（面積が実機とずれる可能性がある）
        self.root = root
        self.car = car
        self.car_dir = os.path.join(root, car[0], car)
        if com_dir is None:  # 使用中の ADDATA の COM.CAB を展開したもの（ADDATA の月次更新に追従）。展開できなければ同梱の予備
            try:
                import com_tables
                com_dir = com_tables.com_dir(root)
            except Exception:  # noqa: BLE001
                com_dir = None
        self.com_dir = com_dir or os.path.join(HERE, 'reference')
        self.panels = self._load_20()
        # CHM（塗り数値）は **最初に使うときに読む**（2026-09-21）。76.DB はボディだけでなく年式群・グレードでも
        # 別の CHM を指すので、`set_vehicle()` で車両条件が入ってから読まないと条件行を選べない（Codex 指摘）
        self._chm_done = False
        self._chm_rows: list = []
        self._chm_base: dict = {}
        # <car>77/87/97/99.DB（パネル別の塗り数値。収録のある車種だけ）は要求時に読む（_load_panel_tbl）
        self._chm_water: Optional[list[dict]] = None  # 水性ページ（CHM「車種別補修塗装指数（水性）」）は要求時に読む

    def _chm_ready(self) -> None:
        """CHM をまだ読んでいなければここで読む（車両条件が決まってからで間に合うように遅らせている）"""
        if self._chm_done:
            return
        self._chm_done = True
        self._chm_rows, self._chm_base = self._load_chm()
        # CHM（車種別補修塗装指数）を **展開できなかった** PC では、修正塗装の標準指数が取れない。
        # 黙って別の値で通ると見積が静かにずれるので 1 回だけ知らせる（hh.exe が無い／ポリシーで使えない PC 対策）。
        # 展開はできたが補修塗装指数のページが無い車種（古い車種の CHM）は正常なので警告しない
        if bool(getattr(self, '_chm_extract_failed', False)) and PaintIndex._warned_chm is not True:
            PaintIndex._warned_chm = True
            hh_ = os.path.join(os.environ.get('WINDIR', ''), 'hh.exe')
            print(f'★ 塗装指数表（CHM）を展開できない: {self.car}。修正塗装の標準指数が取れないので '
                  f'paint.panels[].index を見積書の値で書くこと（{hh_} が使えるか確認）')

    @property
    def chm_rows(self) -> list:
        self._chm_ready()
        return self._chm_rows

    @property
    def chm_base(self) -> dict:
        self._chm_ready()
        return self._chm_base

    @property
    def chm_unavailable(self) -> bool:
        self._chm_ready()
        return bool(getattr(self, '_chm_extract_failed', False))

    # ------------------------------------------------------------ 20.DB: 塗装パネルマスタ
    def _load_20(self) -> list[dict]:
        """400B ヘッダ（部品コード上2桁 → レコード範囲）+ 39B レコード×N
        [code u16][area u16][0x20][body u8][5B][flag 1][name 20B][PanelDivision 1][PanelTypeDivision 1][PanelCode 1|' '][ButtonNo 2][' ']

        body = ボディコード（0 = 全ボディ共通、10 / 20 = そのボディ専用。KA81 の id と同じ 1 バイト整数）。
        同じパネルコードでもボディで面積が変わる（W90 ハイエース: L ｽﾗｲﾄﾞﾄﾞｱﾊﾟﾈﾙ 178（共通/10）と 196（20））ので、
        車のボディに合う行を選ばないと塗装指数が実機と食い違う（2026-09-11 に 20.DB の生バイトで確認）"""
        p = os.path.join(self.car_dir, f'{self.car}20.DB')
        out = []
        if not os.path.exists(p):
            return out
        b = open(p, 'rb').read()
        for o in range(400, len(b) - 38, 39):
            r = b[o:o + 39]
            code, area = struct.unpack_from('<HH', r, 0)
            dv = r[33:36].decode('cp932', 'replace')
            btn = r[36:38].decode('cp932', 'replace')
            out.append({'code': f'{code:04d}', 'area': area, 'name': r[13:33].decode('cp932', 'replace'),
                        'body': r[5], 'flag': chr(r[11]) if 32 <= r[11] < 127 else ' ',
                        'div': int(dv[0]) if dv[0].strip() else 0, 'type': int(dv[1]) if dv[1].strip() else 0,
                        'pcode': int(dv[2]) if dv[2].strip() else 0, 'btn': int(btn) if btn.strip() else 0})
        return out

    def _note_areas(self, rows: list, note: bool = True) -> None:
        """同じコード・同じ条件の行が複数あって**面積が違う**ときは控える。
        面積 = 塗装指数なので、どちらを採るかで見積が変わる。黙って先頭を採ると誰も気づけない。
        ADDATA 全 1,204 車種で 258 組ある（C39 ﾌ-ﾄﾞ 0600 が 131 と 149、C48 LRﾄﾞｱ 2700 が 67 と 80 など。
        2026-09-12 に 20.DB を全走査して集計）"""
        if not note or len(rows) < 2:
            return
        areas = sorted({int(r.get('area') or 0) for r in rows})
        if len(areas) > 1:
            self._note_unresolved(rows[0]['code'], [], areas=areas)

    def _pick_body(self, rows: list, note: bool = True) -> Optional[dict]:
        """同じパネルコードの行から、この車のボディに合うものを選ぶ。
        ボディ専用行 → 全ボディ共通（body 0）→ 先頭 の順（ボディが分からない車は従来どおり先頭）。
        選んだ先に面積の違う行が残っていたら控える（黙って先頭を採らない）"""
        if not rows:
            return None
        b = self.body_code
        if b:
            hit = [r for r in rows if r.get('body') == b]
            if hit:
                self._note_areas(hit, note)
                return hit[0]
            common = [r for r in rows if not r.get('body')]
            if common:
                self._note_areas(common, note)
                return common[0]
            if note:
                # このボディ用も全ボディ共通も無い。他ボディの面積を使うことになるので控える
                self._note_unresolved(rows[0]['code'], [])
        else:
            self._note_areas(rows, note)   # ボディが分からない車でも、面積が割れていれば知らせる
        return rows[0]

    def panel_for_body(self, code: str) -> Optional[dict]:
        """20.DB に**この車のボディ用（またはボディ共通）の行がある**ときだけ、その行を返す。無ければ None。
        panel_exact と違って他ボディ専用行へ逃げない。PaintingLinkParts（W/S 連動の紐付け）用:
        コグニは、この車のボディに載っていないパネルは連動しない
        （コグニ実機 2026-09-12 W90 ハイエース ボディ 20: 明細 4800 取替は 20.DB にボディ 10 専用行しか無く、
        PaintingLinkParts に出なかった。生成器は panel_exact で他ボディ行を拾って書いていた）"""
        c = str(code).zfill(4)
        rows = [r for r in self.panels if r['code'] == c]
        b = self.body_code
        if not rows:
            return None
        if not b:
            return rows[0]
        hit = [r for r in rows if r.get('body') == b] or [r for r in rows if not r.get('body')]
        return hit[0] if hit else None

    def panel_exact(self, code: str):
        """20.DB に完全一致するパネル行（前方一致フォールバックを使わない）。この車のボディに合う行を選ぶ。
        同じコードにこのボディ用が無いときは他ボディ専用行を返す —— **枝番違い（4800 → 4801）の補正が要るなら
        `panel()` を使う**（ボディで別コードになっている車がある）"""
        c = str(code).zfill(4)
        return self._pick_body([r for r in self.panels if r['code'] == c], note=False)

    def _note_unresolved(self, code: str, cands: list, areas=None) -> None:
        """選べなかったパネルを控える（面積＝塗装指数が実機とずれる可能性）。
        cands … 枝番の行き先が複数（コードが違う） / areas … 同じコードに面積の違う行が複数 /
        どちらも空 … このボディ用の行が無く、他ボディの面積を使う"""
        if not any(u['code'] == code for u in self.body_unresolved):
            self.body_unresolved.append({'code': code, 'body': self.body_code,
                                         'candidates': cands, 'areas': list(areas or [])})

    def panel(self, code: str) -> Optional[dict]:
        code = re.sub(r'\D', '', code or '')[:4].zfill(4)
        same = [r for r in self.panels if r['code'] == code]
        b = self.body_code
        if same and not b:
            self._note_areas(same, True)   # 同じコードで面積が割れていたら知らせる（黙って先頭を採らない）
            return same[0]
        if same:
            hit = [r for r in same if r.get('body') == b] or [r for r in same if not r.get('body')]
            if hit:
                self._note_areas(hit, True)
                return hit[0]
            # 同じコードに、このボディ用も全ボディ共通も無い（他ボディ専用しか無い）。
            # そのときは枝番違いにこのボディ用の行があることがある
            # （W90 ハイエース: 4800 = ボディ 10 専用 / 4801 = ボディ 20 専用）
        pre = [r for r in self.panels if r['code'][:3] == code[:3]]
        if b and same:
            # 枝番へ飛ぶのは **同じパネル名** のときだけ。3 桁が同じでも別物のことがある
            # （4800 ｸｵ-ﾀﾊﾟﾈﾙ と 4801 ｸｵ-ﾀﾊﾟﾈﾙ(工賃) のような組）
            base = _panel_key(same[0]['name'])
            hit = [r for r in pre if r.get('body') == b and _panel_key(r['name']) == base]
            # 行き先が 1 コードに定まるときだけ飛ぶ。同じ名前・同じボディでも面積が違う枝番があるので
            # （ADDATA 120 車種で 2,539 組中 20 組。C39 ﾌ-ﾄﾞ 131/149 など）、複数あるなら選べない
            codes = {r['code'] for r in hit}
            if len(codes) == 1:
                return hit[0]
            if codes:
                # 候補が複数。黙って他ボディの面積を使うと塗装指数が実機とずれるので、選べなかったことを残す
                self._note_unresolved(code, sorted(codes))
        if same:
            if b and not any(r.get('body') in (b, 0) for r in same):
                self._note_unresolved(code, [])  # このボディ用も共通も無い（他ボディ専用しか無い）
            return same[0]  # 枝番でも見つからなければ同じコードの先頭（従来どおり）
        # 枝番違い（4801 → 4800 等）
        if len({r['code'] for r in pre}) == 1:  # 3 桁前方一致は行き先が 1 コードのときだけ（複数あると別パネルの面積・名称を黙って使ってしまう。監査 6）
            return self._pick_body(pre)
        return None

    # ------------------------------------------------------------ CHM: 補修塗装指数（溶剤系）
    def _chm_path(self) -> Optional[str]:
        """76.DB からこの車の「塗り数値」CHM を選ぶ。行 = `車種 3, 年式群 1, ボディ 2, ?, グレード 1, ?, 索引 3, ファイル名, 見出し`。

        **ボディで CHM が変わる車種が 88 ある**（例 C34: ボディ 00 は C3400LTB / ボディ 10 は C3401LTB）。
        2026-09-21 まで、ファイル名の正規表現が行の接頭辞まで拾って（`9970000C3400LTB.CHM`）必ず
        「そんなファイルは無い」となり、フォルダ内の先頭 CHM ＝ ボディ 00 用に落ちていた。
        ボディ別の表はパネルの面積・行の構成が違うので、塗り数値がずれる"""
        p76 = os.path.join(self.car_dir, f'{self.car}76.DB')
        if os.path.exists(p76):
            have = {os.path.basename(x).lower(): x for x in glob.glob(os.path.join(self.car_dir, '*'))}
            cand = []
            for l in _xor_lines(p76):
                if '塗り数値' not in l:
                    continue
                m = re.search(r'([A-Za-z][0-9A-Za-z]*LTB\.CHM)', l, re.I)   # 行末のファイル名（接頭辞の数字を含めない）
                if not m:
                    continue
                q = have.get(m.group(1).lower())   # 同じフォルダに .CHM と .chm が混ざっている車種がある（Codex 指摘）
                if q:
                    # 年式群 [3]・グレード [7] の条件。CHM は最初に使うときに読むので、ここでは車両条件が入っている
                    _y, _g = l[3].strip(), l[7].strip()
                    _cy = str(getattr(self, 'year_grp', '') or '').strip()
                    _cg = str(getattr(self, 'grade', '') or '').strip().upper()
                    if _y and _cy and _y != _cy:
                        continue    # 年式群が違う行は使わない
                    if _g and _cg and _g.upper() != _cg:
                        continue    # グレードが違う行は使わない
                    # 順位: ①行の条件が**すべて**この車に当てはまる ②条件の無い行 ③条件はあるが車両側の値が無くて
                    # 確かめられない行。②を③より先にするのが要点（グレードが分からない車で、グレード専用の表を
                    # 当ててしまわないため。Codex 指摘 2026-09-21）
                    _spec = bool(_y or _g)
                    _all_ok = (not _y or (_cy and _y == _cy)) and (not _g or (_cg and _g.upper() == _cg))
                    rank = 0 if (_spec and _all_ok) else (1 if not _spec else 2)
                    cand.append((l[4:6].strip(), q, rank))
            if cand:
                want = ('%02d' % self.body_code) if self.body_code else '00'
                for cond in (0, 1, 2):
                    for key in (want, '00', ''):
                        for body, q, c_ in cand:
                            if c_ == cond and (body == key or key == ''):
                                return q
        c = glob.glob(os.path.join(self.car_dir, '*LTB.CHM')) + glob.glob(os.path.join(self.car_dir, '*LTB.chm'))
        return c[0] if c else None

    @staticmethod
    def _cache_ok(d: str) -> bool:
        """CHM を展開したフォルダとして使えるか（索引 .hhc と本文 html/*.html が揃っている）。
        hh.exe が途中で終わると .hhc だけ残ることがあり、それを使うと本文の読み込みで落ちる"""
        # 本文の拡張子は車種によって .html と .htm がある（C88 C9500LTB は .htm）ので両方を見る
        return bool(glob.glob(os.path.join(d, '*.hhc'))
                    and (glob.glob(os.path.join(d, 'html', '*.htm')) or glob.glob(os.path.join(d, 'html', '*.html'))))

    @staticmethod
    def _extract_chm_hh(hh: str, chm: str, tmp: str) -> bool:
        """hh.exe -decompile を起動する（Windows 付属。非同期に書くので、揃ったかは呼び出し側が _cache_ok で待つ）。起動できたら True"""
        if not os.path.isfile(hh):
            return False
        try:
            subprocess.run([hh, '-decompile', tmp, chm], timeout=60)
            return True
        except Exception:  # noqa: BLE001  失敗・時間切れ
            return False

    @staticmethod
    def _extract_chm_7z(chm: str, tmp: str) -> bool:
        """7z x で CHM を展開する（Linux / Streamlit Cloud の p7zip、または Windows の 7-Zip。同期）。
        7z の展開は hh.exe -decompile と同じ .hhc / html/*.htm を作る（内部ファイル #SYSTEM 等が余分に出るが害はない。
        2026-09-14 に J8200LTB.CHM で 155 ファイル全部一致を確認）"""
        import com_tables
        sz = com_tables.find_7z()
        if not sz:
            return False
        try:
            os.makedirs(tmp, exist_ok=True)
            r = subprocess.run([sz, 'x', '-y', '-o' + tmp, chm], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=120)
            return r.returncode == 0
        except Exception:  # noqa: BLE001
            return False

    def _decompile(self, chm: str) -> Optional[str]:
        """CHM を LOCALAPPDATA に展開してそのフォルダを返す。展開済みなら再利用する。
        途中で終わったキャッシュ（.hhc だけ等）はそのまま使わずに作り直す。
        展開は一時フォルダで行い、揃ってから本来の場所へ移すので、同時に 2 つ動いても壊れない"""
        base = os.path.join(os.environ.get('LOCALAPPDATA') or tempfile.gettempdir(), 'claude_neo_pipeline', 'chm')  # LOCALAPPDATA の無い Linux では一時フォルダ（配布物の中に書かない: アプリは vendor の内容ハッシュを照合する）
        try:  # キャッシュ名に CHM の内容ハッシュを入れる（別の ADDATA の版・置き場の同名 CHM を取り違えない。Linux の共有一時フォルダでも安全。Codex 指摘）
            import hashlib
            h = hashlib.sha1()
            with open(chm, 'rb') as f_:
                for chunk in iter(lambda: f_.read(1 << 20), b''):
                    h.update(chunk)
            ident = '_' + h.hexdigest()[:12]
        except OSError:  # 読めない CHM は「展開できない」扱い（名前だけのキャッシュに落として別物を掴まない。Codex 指摘）
            return None
        cache = os.path.join(base, os.path.splitext(os.path.basename(chm))[0] + ident)
        if self._cache_ok(cache):
            return cache
        hh = os.path.join(os.environ.get('WINDIR', r'C:\Windows'), 'hh.exe')
        # 一時フォルダは呼び出しごとに一意にする（同じプロセスの別スレッドが同時に展開しても混ざらない）。
        # rename で公開するので、置き場所はキャッシュと同じドライブでなければならない
        try:
            os.makedirs(base, exist_ok=True)
            self._sweep_tmp(cache)  # 前回異常終了で残った一時フォルダを片付ける
            tmp = tempfile.mkdtemp(dir=base, prefix=os.path.basename(cache) + '.', suffix='.tmp')
        except OSError:
            return cache if self._cache_ok(cache) else None
        launched = self._extract_chm_hh(hh, chm, tmp)
        if launched:
            for _ in range(40):  # hh.exe は非同期で書き終わるので、揃うまで待つ
                if self._cache_ok(tmp):
                    time.sleep(0.5)
                    break
                time.sleep(0.25)
        if not self._cache_ok(tmp):
            # hh.exe が無い（Linux / Streamlit Cloud）か、起動はしたが揃わない（ポリシーで止められる等）→ 7z（p7zip / 7-Zip）で同期展開（Codex 指摘）
            shutil.rmtree(tmp, ignore_errors=True)
            used_7z = self._extract_chm_7z(chm, tmp)
            if not used_7z or not self._cache_ok(tmp):
                shutil.rmtree(tmp, ignore_errors=True)
                if not launched and not used_7z:  # どの道具も無い: 待っても揃わないので待たない
                    return cache if self._cache_ok(cache) else None
                return cache if self._cache_ok(cache) else self._wait_cache(cache)
        if self._cache_ok(cache):  # 展開している間に別プロセスが完成させた → 相手のものを使う（消さない）
            shutil.rmtree(tmp, ignore_errors=True)
            return cache
        # 公開済みのフォルダは決して消さない（読んでいる別プロセスの足元を崩さないため）。
        # まず「置いてみる」。置き場所が空なら rename は成功し、誰のものも触らずに済む
        try:
            os.rename(tmp, cache)
            return cache if self._cache_ok(cache) else self._wait_cache(cache)
        except OSError:  # 既に何かある（Windows は中身のあるフォルダへは rename できない）
            pass
        if self._cache_ok(cache):  # 直前に別プロセスが完成させていた → 相手のものを使う（消さない）
            shutil.rmtree(tmp, ignore_errors=True)
            return cache
        # 途中で終わった不完全なキャッシュが居座っている → どけてから自分のものを置く
        if self._retire(cache):
            try:
                os.rename(tmp, cache)
            except OSError:  # その隙に別プロセスが置いた
                pass
        shutil.rmtree(tmp, ignore_errors=True)
        return cache if self._cache_ok(cache) else self._wait_cache(cache)

    @staticmethod
    def _sweep_tmp(cache: str, age: float = 3600.0) -> None:
        """異常終了で残った展開途中の一時フォルダを捨てる。動いている展開を巻き込まないよう、
        更新から age 秒より古いものだけを対象にする"""
        now = time.time()
        for d in glob.glob(f'{cache}.*.tmp'):
            try:
                if os.path.isdir(d) and now - os.path.getmtime(d) > age:
                    shutil.rmtree(d, ignore_errors=True)
            except OSError:  # 消えた / 触れない
                pass

    @staticmethod
    def _retire(d: str) -> bool:
        """公開済みのキャッシュを **消さずに** どける。読んでいる別プロセスがいれば rename が失敗するので何もしない。
        （公開フォルダを直接 rmtree すると、既にそれを使い始めた別プロセスの足元を崩す）"""
        stale = f'{d}.stale.{os.getpid()}.{time.time_ns()}'
        try:
            os.rename(d, stale)
        except OSError:  # 無い / 使用中 / 別プロセスが処理中
            return False
        shutil.rmtree(stale, ignore_errors=True)
        return True

    @classmethod
    def _wait_cache(cls, cache: str, seconds: float = 8.0) -> Optional[str]:
        """別のプロセスが同じ CHM を展開している最中かもしれないので、少しだけ完成を待つ。
        2 人が同時に見積を作ると hh.exe が競合し、自分の展開だけ間に合わないことがあるため"""
        end = time.time() + seconds
        while time.time() < end:
            if cls._cache_ok(cache):
                return cache
            time.sleep(0.25)
        return None

    def _chm_page(self, d: str, water: bool) -> tuple:
        """展開フォルダ d から「補修塗装指数（溶剤/水性）」のページ位置と本文を返す。
        (ページ位置, 本文) を返し、ページが索引に無ければ (None, None)、位置は分かるが読めなければ (位置, None)"""
        hhc_list = glob.glob(os.path.join(d, '*.hhc'))
        if not hhc_list:
            return None, None
        h = open(hhc_list[0], 'rb').read().decode('cp932', 'replace')
        items = re.findall(r'<param name="Name" value="([^"]*)">\s*<param name="Local" value="([^"]*)">', h)
        key = '水性' if water else '溶剤'
        page = next((l for n, l in items if n.startswith('補修塗装指数') and key in n and '#' not in l), None)
        if not page:
            return None, None
        try:
            return page, open(os.path.join(d, page.replace('/', os.sep)), 'rb').read().decode('cp932', 'replace')
        except OSError:
            return page, None

    def _load_chm(self, water: bool = False) -> tuple[list[dict], dict]:
        """water=True で CHM の「車種別補修塗装指数（水性）」ページ（76.DB 997600）を読む。コグニ実機 W66: 塗料を水性にするとクォータ 2.3→2.6、ロッカ 1.4→1.6（2026-09-05）"""
        chm = self._chm_path()
        if not chm:
            return [], {}
        d = self._decompile(chm)
        self._chm_extract_failed = not d  # 展開そのものに失敗したか（ページが無いだけの車種と区別する）
        if not d:
            return [], {}
        page, t = self._chm_page(d, water)
        if t is None and page is not None:
            # 本文が読めない = 展開が途中（hh.exe は非同期に書く）か壊れたキャッシュ。
            # その見積 1 回ぶんを指数なしで作ってしまわないよう、**この呼び出しの中で**作り直して 1 度だけやり直す。
            # 使っている別プロセスがいるかもしれないので、公開フォルダは消さずに「どける」
            # どけられなければ（別プロセスが展開・使用中）壊さない。代わりに相手が書き終わるのを待って読み直す
            if self._retire(d):
                d2 = self._decompile(chm)
                if d2:
                    page, t = self._chm_page(d2, water)
                    d = d2
            else:
                for _ in range(6):  # 3 秒まで待つ
                    time.sleep(0.5)
                    page, t = self._chm_page(d, water)
                    if t is not None:
                        break
        if t is None:
            if page is not None:  # 目的のページが見つかっているのに読めない = 展開に失敗している
                self._chm_extract_failed = True
                self._retire(d)  # 次回作り直せるようどける（使用中なら何もしない）
            return [], {}
        t = re.sub(r'<script.*?</script>|<style.*?</style>', '', t, flags=re.S)
        t = re.sub(r'<[^>]+>', ' ', t)
        t = html.unescape(t).replace('\xa0', ' ').replace('　', ' ')
        t = re.sub(r'\s+', ' ', t)
        rows = []
        seg = t.split('①塗り数値', 2)[-1] if '①塗り数値' in t else t
        seg = seg.split('②加算基礎数値')[0]
        num = r'(\d+\.\d|-)'
        for m in re.finditer(r'(?<![\d.])(\d{1,2}) (.+?) (\d{1,3}) ' + ' '.join([num] * 6), seg, flags=re.ASCII):
            no, name, area = int(m.group(1)), m.group(2).strip(), int(m.group(3))
            vals = [None if v == '-' else float(v) for v in m.groups()[3:9]]
            rows.append({'no': no, 'name': name, 'area': area, 'new_multi': vals[0], 'new_single': vals[1],
                         'r11': vals[2], 'r12': vals[3], 'r13': vals[4], 'hf': vals[5]})
        base = {}
        if '②加算基礎数値' in t:
            seg2 = t.split('②加算基礎数値', 1)[1]
            for m in re.finditer(r'(ソリッド|メタリック|２コートパール|３コートパール)?\s*(速乾|２Ｋ|水性)\s+' + r'\s+'.join([r'(\d\.\d)'] * 5), seg2):
                pass
        return rows, base

    def chm_rows_for_paint(self, paint: int) -> list[dict]:
        """PaintingPlan.Paint 4（水性）は CHM の水性ページ、それ以外は溶剤系ページ。水性ページが無い CHM は溶剤系で代用"""
        if int(paint or 0) == 4:
            if self._chm_water is None:
                self._chm_water = self._load_chm(water=True)[0]
            if self._chm_water:
                return self._chm_water
        return self.chm_rows

    def chm_row_for(self, pn: dict, paint: int = 3) -> Optional[dict]:
        """20.DB のパネル → CHM 表の行（面積一致を優先、次に種別語で近似）"""
        rows_ = self.chm_rows_for_paint(paint)
        if not rows_:
            return None
        cand = [r for r in rows_ if r['area'] == pn['area']]
        if len(cand) == 1:
            return cand[0]
        nm = pn['name']
        kw = {2: ('ボンネット', 'フード'), 5: ('フェンダ',), 6: ('クォータ', 'アウトサイド', 'クオータ'), 4: ('ロワーバック', 'ロワバック', 'リヤーパネル', 'リヤパネル'),
              3: ('ルーフ',) if pn['div'] == 1 else ('サイドシル', 'ロッカ')}
        if pn['type'] == 1:
            if 'F' in nm[:2]:
                keys = ('フロントドア',)
            elif nm[:2].strip() in ('LR', 'RR', 'L', 'R') or 'ｽﾗｲﾄﾞ' in nm:
                keys = ('リヤドア', 'リヤードア', 'スライドドア')
            else:
                keys = ('バックドア', 'テールゲート', 'トランク')
        else:
            keys = kw.get(pn['type'], ())
        pool = cand or rows_
        for r in pool:
            if any(k in r['name'] for k in keys):
                return r
        return cand[0] if cand else None

    # ------------------------------------------------------------ 標準値
    # ------------------------------------------------------------ 係数表による式（CHM が無いときの補完・高機能塗装）
    @staticmethod
    def _r1(x: float) -> float:
        return math.floor(x * 10 + 0.5 + 1e-9) / 10.0

    def form_codes(self) -> tuple[str, str, str, str]:
        """<car>25.DB（13B レコード）= [枝番 1][ボディ 1（u8。0 = 共通）][年式・ボディ・グレード・FVA 7][CarFormCode][FormCode1][FormCode2][FinishCode]。

        **ボディで車形が変わる車種が 227/1,209 ある**ので、この車のボディ以下でいちばん大きいボディの行を採る
        （2026-09-21。それまで先頭 13 バイトだけを見ていたので、ボディ 10/20/… の車で車形を取り違えていた。
        車形は加算基礎 T_KEI_3・ブース BOOTH・バンパ加算基礎 BAN・FBANPA・Scrach・F_S・H_N_SSZ のキー）"""
        p = os.path.join(self.car_dir, f'{self.car}25.DB')
        if not os.path.exists(p):
            return ('', '', '', '')
        b = open(p, 'rb').read()
        best = None
        for i in range(len(b) // 13):
            r = b[i * 13:(i + 1) * 13]
            c = r[9:13].decode('latin1')
            if not (len(c) == 4 and c[:3].isdigit() and (c[3].isdigit() or c[3] == ' ')):
                continue   # FinishCode（4 桁目）は空白の車種がある
            if self.body_code and r[1] > self.body_code:
                continue      # この車のボディより大きいボディ専用の行は使わない
            # [2:9] の条件（年式群・ボディ・グレード・駆動）が空でない行は、この車に合うときだけ使う
            # （条件行を持つのは 1,209 ファイル中 5 ファイル。set_vehicle 前は grade も年式群も空なので無条件行が選ばれる）
            # [2:9] は**該当するグレードコードの列挙**（'B      ' / 'ABCDP  '）。条件行を持つのは 1,209 ファイル中 5
            cond = r[2:9].decode('latin1').strip().upper()
            score = 0
            if cond:
                _g = str(getattr(self, 'grade', '') or '').strip().upper()
                if not _g or _g not in cond:
                    continue
                score = 1
            # 条件が合った行を優先し、同点ならボディ（分かる車は最大・分からない車は共通行 0）で決める（Codex 指摘）
            rank = (score, r[1] if self.body_code else -r[1])
            if best is None or rank > best[0]:
                best = (rank, c)
        if not best:
            return ('', '', '', '')
        c = best[1]
        return (c[0], c[1], c[2], c[3])

    def _kei1(self, form: str, div: int, typ: int, disp: str, pa: int, area: int, paint: str = '1') -> Optional[tuple[int, int]]:
        for r in self._com_rows('T_KEI_1.DB'):
            if len(r) >= 10 and r[0] == form and r[1] == str(div) and r[2] == str(typ) and r[3] == disp and r[4] == str(pa) and r[5] == paint \
                    and r[6].isdigit() and r[7].isdigit() and int(r[6]) <= area <= int(r[7]):
                return int(r[8]), int(r[9])
        return None

    def _c12(self, form: str, div: int) -> Optional[tuple[int, int]]:
        for r in self._com_rows('T_KEI_2.DB'):
            if len(r) >= 4 and r[0] == form and r[1] == str(div):
                return int(r[2]), int(r[3])
        return None

    def _hn_prep(self, form: str, f1: str, f2: str, pcode: int, finish: str) -> float:
        """H_N_SSZ: 溶接パネル（PanelCode≠0）取替時の関連部下処理加算"""
        if not pcode:
            return 0.0
        for r in self._com_rows('H_N_SSZ.DB'):
            if len(r) >= 7 and r[0] == form and r[3].isdigit() and int(r[3]) == pcode and (r[6] == '' or r[6] == finish):
                if (r[1] == f1 and r[2] == f2) or (r[1] == f1 and r[2] == '9') or (r[1] == '9'):
                    return int(r[4]) / 100.0
        return 0.0

    def _hju_max(self, div: int, typ: int) -> int:
        """HJU_SS のその区分での index の上限（(1,2)=(1,3)=(1,4)=49 / (1,9)=99 / (2,9)=40）"""
        tbl = {}
        for r in self._com_rows('HJU_SS.DB'):
            if len(r) >= 4 and r[0].isdigit() and r[1].isdigit() and r[2].isdigit():
                tbl.setdefault((int(r[0]), int(r[1])), []).append(int(r[2]))
        return max(tbl.get((div, typ)) or tbl.get((div, 9)) or [0])

    def _hju(self, div: int, typ: int, idx: int) -> float:
        """HJU_SS: 修正塗装の下処理時間（PanelDivision, PanelTypeDivision 2/3/4 以外は 9, index=ceil(S'/3)、最大行で頭打ち）"""
        tbl = {}
        for r in self._com_rows('HJU_SS.DB'):
            if len(r) >= 4 and r[0].isdigit() and r[1].isdigit() and r[2].isdigit():
                tbl[(int(r[0]), int(r[1]), int(r[2]))] = int(r[3]) / 100.0
        t = typ if any(k[0] == div and k[1] == typ for k in tbl) else 9
        mx = max([k[2] for k in tbl if k[0] == div and k[1] == t] or [0])
        if not mx:
            return 0.0
        return tbl[(div, t, max(1, min(idx, mx)))]

    def formula_times(self, pn: dict, paint: str = '1') -> Optional[dict]:
        """係数表だけから CHM 相当の行を作る: {new_multi, new_single, r11, r12, r13}（CHM が無い車種・パネル用）"""
        form, f1, f2, fin = self.form_codes()
        if not form:
            return None
        div, typ, S, pcode = int(pn['div']), int(pn['type']), int(pn['area']), int(pn.get('pcode') or 0)
        ab = self._kei1(form, div, typ, 'K', 9, S, paint); c = self._c12(form, div)
        if not ab or ab == (0, 0) or not c:
            return None
        A, B = ab; C1, C2 = c; add = self._hn_prep(form, f1, f2, pcode, fin)
        out = {'name': pn['name'].strip(), 'area': S, 'hf': None,
               'new_multi': self._r1((B + A * S / 1000) * C2 / 100000 + add), 'new_single': self._r1((B + A * S / 1000) * C1 / 100000 + add)}
        for n, key in ((1, 'r11'), (2, 'r12'), (3, 'r13')):
            Sn = S if n == 1 else int(math.ceil(S / n - 1e-9))
            abn = (self._kei1(form, div, typ, 'S', n, Sn, paint) or self._kei1(form, div, 9, 'S', n, Sn, paint)
                   or self._kei1(form, div, typ, 'S', 9, Sn, paint) or self._kei1(form, div, 9, 'S', 9, Sn, paint))  # 汎用行（PaintingArea 9 / Type 9）へフォールバック
            out[key] = None if (not abn or abn == (0, 0)) else self._r1((abn[1] + abn[0] * Sn / 1000) * C2 / 100000 + self._hju(div, typ, int(math.ceil(Sn / 3 - 1e-9))))
        return out

    PANEL_TABLES = {(False, False): '77', (True, False): '97', (False, True): '87', (True, True): '99'}

    def _load_panel_tbl(self, suf: str) -> dict:
        """パネル別の塗り数値の表（`<car>77/87/97/99.DB`）。XOR 0xff の CSV で
        `車種, 年式群, ボディ, グレード, EVA, 部品コード, 取替複数塗, 取替単体塗, 修正1/1, 1/2, 1/3, 高機能塗装[, 高機能塗装2]`（各 ×100）。

        | 表 | 収録車種（ADDATA 2026/08） | 塗料 | 高機能塗装の列 |
        |---|---|---|---|
        | 77.DB | 434 | 溶剤系 | 6 列目・**7 列目 = 耐スリ傷**（2 列が違う 92 行はすべて 7 列目が実案件と一致） |
        | 97.DB | 357 | 水性 | 同上 |
        | 87.DB | 27（日産 P/Q 系） | 溶剤系 | 6 列目（スクラッチ） |
        | 99.DB | 27（同） | 水性 | 同上 |

        値は CHM の「塗り数値」表と一致する（J87 ボンネット 1.0/1.4/2.0/1.5/1.3・水性 1.2/1.6/2.1/1.6/1.5 で確認）ので、
        **CHM を展開できない PC でもこの表があれば標準指数が出せる**。`0000` は CHM の '-' と同じ「収録なし」なので None にする"""
        key = '_rtbl_' + suf
        if getattr(self, key, None) is not None:
            return getattr(self, key)
        out: dict = {}
        p = os.path.join(self.car_dir, self.car + suf + '.DB')
        if os.path.exists(p):
            for l in _xor_lines(p):
                f = [x.strip() for x in l.split(',')]
                if len(f) < 12 or not f[5].isdigit():
                    continue
                vals = [(int(x) / 100.0 if (x.isdigit() and int(x)) else None) for x in f[6:13]]
                out.setdefault(f[5], []).append({'grp': f[1], 'body': f[2], 'grade': f[3], 'eva': f[4], 'vals': vals})
        setattr(self, key, out)
        return out

    def set_vehicle(self, car: dict, eva=None) -> 'PaintIndex':
        """条件行のある表（77/87/97/99.DB のパネル別塗り数値、23/93.DB のバンパ）を引くための
        車両条件をまとめて渡す。生成器・突合せ（inspect_estimate）・下書き（draft_estimate）の
        3 か所が**同じ行**を選ぶようにするための入口（2026-09-21。それまでは生成器だけが渡していて、
        突合せの表示と実際に書かれる NEO が別の行を見ていた）。`eva` を省くと装備は変えない"""
        if eva is not None:
            self.eva = {str(x).strip().upper() for x in eva if str(x).strip()}
        self.grade = str((car or {}).get('GradeCode', '') or '')
        _yc = str((car or {}).get('YearCode', '') or '').strip()
        self.year_grp = _yc[-1] if (_yc.isdigit() and int(_yc)) else ''
        return self

    def _pick_panel_row(self, rows: list) -> Optional[dict]:
        """77/87/97/99.DB の行をこの車で選ぶ。ボディ専用行 → 共通行（'00'）、その中で
        **装備（EVA）・グレードの条件に合う行**を優先する（条件のある行 > 無条件の行）。
        同じ部品コードに装備別の行がある例: J57 4300 テールゲート = 無条件 2.5 / EVA 'Z'（4WD）2.3
        （ADDATA 2026/08 の 77.DB では 3,952 コード中 291 コードが複数行。2026-09-21）"""
        b = '%02d' % self.body_code if self.body_code else ''
        evas = {str(x).strip().upper() for x in (getattr(self, 'eva', None) or set()) if str(x).strip()}
        grade = str(getattr(self, 'grade', '') or '').strip().upper()

        ygrp = str(getattr(self, 'year_grp', '') or '').strip()

        def fits(r):
            e = str(r.get('eva') or '').strip().upper()
            g = str(r.get('grade') or '').strip().upper()
            y = str(r.get('grp') or '').strip()   # 年式群（8,359 行中 47 行だけ条件がある）
            return ((not e or all(ch in evas for ch in e)) and (not g or (grade and grade in g))
                    and (not y or y == ygrp))

        # ボディ専用行 → 共通行（'00'）の順に、**条件に合う行**を探す。
        # ボディ専用行が装備専用しか無くてこの車に合わないときは共通行の無条件行を使う（Codex 指摘 2026-09-21）
        for grp in ([r for r in rows if b and r['body'] == b], [r for r in rows if r['body'] in ('00', '')]):
            fit = [r for r in grp if fits(r)]
            if not fit:
                continue
            # **条件の具体的な行を優先**（EVA の文字数 → グレードの文字数）。
            # 例 M89 4500 ボディ 20: 無条件 / 'R' / 'W' / 'WR' の 4 行。装備 W と R の車は 'WR' の行が正しい（Codex 指摘）
            fit.sort(key=lambda r: (len(str(r.get('eva') or '').strip()), len(str(r.get('grade') or '').strip()),
                                    1 if str(r.get('grp') or '').strip() else 0), reverse=True)
            return fit[0]
        # どの行もこの車の装備・グレードに合わない（合わない行は当てずに CHM・係数表へ）
        return None

    def panel87(self, code: str, paint: int = 3, hf: int = 0) -> Optional[dict]:
        """パネル別塗り数値の表の行を、CHM 表の行と同じ形で返す（無ければ None）。
        塗料（溶剤/水性）と高機能塗装の種類（スクラッチかどうか）で表を選び、
        ボディ専用行 → 共通行（'00'）の順で選ぶ。どちらも無ければ使わない（他ボディの値を当てない）"""
        water = int(paint or 0) == 4
        scratch = (int(hf or 0) == 3) or (self.car_hf_kind() == 3)
        # なぜ None を返したかを残す（'none' = 表にこのパネルが無い / 'mismatch' = 行はあるが装備・グレードが合わない）。
        # 呼び出し側は 'mismatch' のとき別の表を見に行かない（Codex 指摘 2026-09-21）
        self.panel_tbl_reason = 'none'
        # 目的の表 → 同じ塗料の別の表（塗り数値は同じ値だが高機能の列の意味が違うので、そのときは高機能を返さない）
        order = [(self.PANEL_TABLES[(water, scratch)], True), (self.PANEL_TABLES[(water, not scratch)], False)]
        for suf, same_kind in order:
            rows = self._load_panel_tbl(suf).get(str(code).zfill(4))
            if not rows:
                continue
            pick = self._pick_panel_row(rows)
            if pick is None:
                # その表にこのパネルの行はあるのに、この車の装備・グレードに合う行が無い
                # → 別の表の無条件行を当てに行かず、CHM・係数表に落とす（Codex 指摘 2026-09-21）
                self.panel_tbl_reason = 'mismatch'
                return None
            v = pick['vals'] + [None] * 7
            # 高機能塗装: スクラッチの表（87/99）は 6 列目、通常の表（77/97）は **7 列目 = 耐スリ傷**。
            # 種類の違う表に落ちたときは高機能を返さない（呼び出し側が Scrach.DB / CHM / 係数表で出す）
            hv = (v[5] if suf in ('87', '99') else v[6]) if same_kind else None
            return {'no': 0, 'name': '', 'area': None, 'new_multi': v[0], 'new_single': v[1],
                    'r11': v[2], 'r12': v[3], 'r13': v[4], 'hf': hv, 'src': suf + '.DB'}
        return None

    def car_hf_kind(self) -> Optional[int]:
        """この車種で使う高機能塗装の種類を COM/S_Est.DB から引く（2 = 耐スリ傷 / 3 = スクラッチ）。分からなければ None。

        S_Est.DB は 1 行 1 車種（`C10 00       50` = 車種コード・ボディ・2 桁）。**2 桁目が高機能塗装の種類**で、
        実案件 NEO 1,800 本の突き合わせでは `x0` の車は耐スリ傷 250 件・`x1` の車はスクラッチ 27 件（例外 2 件）。
        1 桁目は `car_paint_kind()` を見ること。2026-09-21 に同定"""
        v = self._s_est()
        return {0: 2, 1: 3}.get(int(v[1])) if v else None

    def _s_est(self) -> str:
        """COM/S_Est.DB のこの車種の 2 桁（`C10 00       50` の末尾）。無ければ ''"""
        for l in self._com_rows('S_Est.DB'):
            if not l or not l[0]:
                continue
            t = l[0]
            if t[:3].strip().upper() == str(self.car).upper():
                v = t[-2:].strip()
                if len(v) == 2 and v.isdigit():
                    return v
        return ''

    def car_paint_kind(self) -> Optional[int]:
        """この車種のパネル塗装指数の**素性**（COM/S_Est.DB の 1 桁目 = RTTI の `PanelPaintingTimes`）。

        - `1` 正規の指数 ＋ CHM の「車種別補修塗装指数」ページあり（631 車種）
        - `5` 正規の指数 ＋ CHM ページなし（係数表 T_KEI で計算。464 車種）
        - **`2` 暫定指数 ＋ CHM あり（76 車種）／`6` 暫定 ＋ CHM なし（38 車種）** … コグニは塗装パネルの印を `$`
          （弊社独自の参考値）で書く。値そのものは ADDATA どおりで、実案件の暫定行 1,025 行のうち
          1,024 行が生成器の計算と一致する ＝ **違うのは印だけ**
        - `0` その車種には塗装指数が無い（98 車種。97 車種は 20.DB すら持たない。汎用車種 Z10/Z30 もここ）。
          実案件でもパネル行はすべて手入力（区分 9）

        2026-09-21 に実案件 7,004 本・パネル 16,531 行の層別で同定"""
        v = self._s_est()
        return int(v[0]) if v else None

    def car_paint_provisional(self) -> bool:
        """この車種の塗装パネルの標準指数が**暫定**（コグニの印 `$`）か。**1 桁目が 2 のときだけ**。

        実案件の外板パネル行で: 1 桁目 2 → `$` 179 / `*` 2 / `#` 5・`''` は **0**、
        1 桁目 1 → `''` 2,859 / `$` 22、1 桁目 5 → `''` 87。
        **1 桁目 6 は `$` 8 / `''` 7 で割れている**（9 車種・15 行と少なく、分ける条件が分からない）ので
        暫定にはしない（2026-09-21）"""
        return self.car_paint_kind() == 2

    def _scrach_time(self, form: str, paint: int, pn: dict, area: int) -> Optional[float]:
        """スクラッチ（高機能塗装 3）のパネル別加算: COM/Scrach.DB。
        行は `車形, 塗料, 'S', PanelDivision, PanelTypeDivision, PanelCode, A…, B…` で、
        **A = 7 列目の先頭 4 桁**（2105 固定）・**B = 8 列目の先頭 4 桁 ÷ 10**（224.0 / 279.0 / 344.0 の 3 つだけ）。
        式は F_S と同じ round1((B + A×面積/1000) × C2/100000)。
        行の選び方は (div, type, PanelCode) の完全一致 → (9,9,9) の汎用行
        （実案件 NEO の スクラッチ 82 パネルで 78 行が一致。2026-09-20 に解読）"""
        c = self._c12(form, int(pn['div']))
        if not c:
            return None
        rows = [r for r in self._com_rows('Scrach.DB') if len(r) >= 8 and r[0] == str(form) and r[1] == str(paint)]
        for key in ((str(pn['div']), str(pn['type']), str(pn.get('pcode') or 0)), ('9', '9', '9')):
            for r in rows:
                # 4 桁に満たないセル（桁落ち・壊れた行）は使わない。汎用行へ落とす（Codex 指摘）
                if (r[3], r[4], r[5]) == key and len(r[6]) >= 4 and len(r[7]) >= 4 and r[6][:4].isdigit() and r[7][:4].isdigit():
                    return self._r1((int(r[7][:4]) / 10.0 + int(r[6][:4]) * area / 1000) * c[1] / 100000)
        return None

    def hf_time(self, area: int, hf: int, pn: Optional[dict] = None, paint: int = 3) -> Optional[float]:
        """高機能塗装（フッ素 1 / 耐スリ傷 2 / スクラッチ 3）のパネル別加算。

        **まず CHM「塗り数値」表の高機能の列**を使う（車種別に載っている値。塗料が水性なら水性ページ）。
        実案件 NEO 825 パネルで、CHM で説明できるのが 775 行・式で 40 行 = 98%
        （F_S の式だけだったときは 耐スリ傷 89%・スクラッチは対応できず。2026-09-20）。
        CHM に高機能の列が無い車種は係数表の式: フッ素・耐スリ傷は COM/F_S.DB
        （実 NEO 4 パネル 31/58/79/92 d㎡ → 0.6/0.8/1.0/1.2 一致）、スクラッチは COM/Scrach.DB（`_scrach_time`）。
        どちらも引けなければ経験式 floor10(0.3 + 0.01×面積)。スクラッチだけは式も引けなければ None
        （分からない値で埋めず、呼び出し側が見積書の指数を要求する）"""
        if not hf:
            return 0.0
        # 車種の表（87/97.DB・CHM）の高機能列は「**その車種の**高機能塗装」の値。見積の指定が車種の種類
        # （COM/S_Est.DB の 2 桁目）と食い違うときは使わない —— 加算基礎（T_KEI_3 の T 列 / S 列）と
        # ちぐはぐな値になるので、種類ごとの式（F_S / Scrach.DB）で出す（Codex 指摘 2026-09-21）
        # 車種の表（77/97/87/99.DB・CHM）の高機能列は「その車種の高機能塗装」= 耐スリ傷かスクラッチの値。
        # **フッ素（1）はこの列を使わない**（F_S.DB の F 行で出す。実案件 1,800 本にフッ素の例が無く裏が取れないため。Codex 指摘）
        _kind_ok = int(hf) in (2, 3) and self.car_hf_kind() in (None, int(hf))
        if _kind_ok and pn and pn.get('code'):  # 87.DB / 97.DB（収録のある車種だけ。CHM より優先）
            # 溶剤表（87.DB）の高機能列を先に見る: スクラッチの車（日産 P/Q 系）は水性の見積でもこの値だった
            # （実案件 P31 3100: 実測 0.9 = 87.DB。97.DB の 7 列目は 1.1）
            r87 = self.panel87(pn['code'], paint, hf)
            if r87 and r87.get('hf') is not None:
                return r87['hf']
            # 水性でその車に水性の表が無い（＝この部品の行が 1 つも無い）ときだけ、溶剤の表を見る。
            # 実案件 U15（77.DB だけ持つ車）の水性の見積は溶剤表の値 1.5 / 1.3 が実測と一致した。
            # 水性の表に**行はあるのに高機能の欄が空**のときは溶剤の値を当てない（水性と溶剤で値が違うため。Codex 指摘 2026-09-21）。
            # 「装備・グレードが合わない」と分かったときも見に行かない（その車の変種が無いだけ）
            if int(paint or 0) == 4 and r87 is None and getattr(self, 'panel_tbl_reason', 'none') == 'none':
                r87s = self.panel87(pn['code'], 3, hf)
                if r87s and r87s.get('hf') is not None:
                    return r87s['hf']
        if _kind_ok and pn:  # CHM の高機能列（面積が一致する行だけ採る。近似で拾った別パネルの値は使わない）
            row = self.chm_row_for(pn, paint)
            if row and row.get('hf') is not None and row.get('area') == pn.get('area'):
                return row['hf']
        form = self.form_codes()[0]
        if int(hf) == 3:
            return self._scrach_time(form, paint, pn, area) if (form and pn) else None
        if form and pn:
            kind = {1: 'F', 2: 'T'}.get(int(hf), 'T')
            c = self._c12(form, int(pn['div']))
            rows_fs = [r for r in self._com_rows('F_S.DB') if len(r) >= 7 and r[0] == form and r[1] == str(paint) and r[2] == kind and r[3] == str(pn['div'])]
            for typ_key in (str(pn['type']), '9'):  # 完全一致 → 汎用行（Type 9）
                for r in rows_fs:
                    if r[4] == typ_key and c:
                        return self._r1((int(r[6]) + int(r[5]) * area / 1000) * c[1] / 100000)
        return floor10(0.3 + 0.01 * area)

    def prepare_area(self, area: int, ratio: str, div: int = 0, typ: int = 0) -> int:
        """修正パネルの `PaintingPanel.PrepareArea`。**HJU_SS（修正塗装の下処理時間）を引くときの index そのもの**:

        ```
        S = 切上(パネル面積 × 1/1・1/2・1/3)      下処理面積 = min(切上(S ÷ 3), HJU_SS のその区分の上限)
        ```

        上限は (区分 1, 種別 2/3/4) = 49 / (1, 9) = 99 / (2, 9) = 40。取替（新品）は -1。

        2026-09-21 に訂正（実案件 1,097 行で 旧式 51% → 新式 59%。2 式が割れた 188 行のうち**旧式が正しい行は 0**。
        残差はすべて「塗装割合を変えたのに再計算されていない古い値」で説明できる）。
        それまでは `四捨五入(S × 0.345)` の近似で、W66 のルーフ 287（既知差 W66y）が合わなかったが、新式では
        1/2 → 48・1/3 → 32 と実機に一致する。金額に影響しない表示列（判断規則 10-18）"""
        r = {'1/1': 1.0, '1/2': 0.5, '1/3': 1.0 / 3}.get(ratio)
        if not r:
            return -1
        part = int(math.ceil(area * r - 1e-9))
        idx = max(1, int(math.ceil(part / 3 - 1e-9)))
        mx = self._hju_max(div, typ) if (div or typ) else 0
        return min(idx, mx) if mx else idx

    def standard_times(self, code: str, hf: int, n_panels: int, paint: int = 3) -> Optional[dict]:
        """paint: PaintingPlan.Paint（1 速乾 / 3 ２Ｋ / 4 水性）。係数表（T_KEI_1 / F_S）の塗料列に渡す"""
        pn = self.panel(code)
        if not pn:
            return None
        row = self.panel87(pn['code'], paint, hf)   # 77/87/97/99.DB → CHM → 係数表 の順。**解決後のパネルコード**で引く
        if row is not None:
            row = dict(row, area=pn['area'], name=pn['name'].strip())
        else:
            row = self.chm_row_for(pn, paint)
            if row is None or row.get('area') != pn['area']:  # CHM に無い／面積が合わないパネルは係数表の式で補う。補えなければ None（呼び出し側が index を要求）
                row = self.formula_times(pn, str(paint))
        add = self.hf_time(pn['area'], hf, pn, paint)
        single = n_panels <= 1
        res = {'panel': pn, 'chm': row, 'hf': add}
        if add is None:  # 高機能加算が求まらない（スクラッチ）: 標準指数は無しとして扱う（呼び出し側が index を要求し、手入力 # で書く）
            res.update({'new': None, 's1': None, 's2': None, 's3': None})
            return res
        if row:
            new = row['new_single'] if single and row['new_single'] is not None else row['new_multi']
            r11 = row['r11']
            r12 = row['r12'] if row['r12'] is not None else r11
            r13 = row['r13'] if row['r13'] is not None else r12
            bump = 0.4 if single else 0.0  # 修正パネルを単体塗装する場合は 0.4 加算（CHM 注2）
            def _v(base: Optional[float], extra: float) -> Optional[float]:  # CHM の '-'（None）は None のまま（呼び出し側が index を要求）
                return None if base is None else round(base + extra + add, 1)
            res.update({'new': _v(new, 0.0), 's1': _v(r11, bump), 's2': _v(r12, bump), 's3': _v(r13, bump)})
        return res

    def _com_rows(self, name: str) -> list[list[str]]:
        p = os.path.join(self.com_dir, name)
        if not os.path.exists(p):
            p = os.path.join(HERE, 'reference', name)  # 展開キャッシュに無い表は同梱の予備
        if not os.path.exists(p):
            return []
        return [[x.strip() for x in l.split(',')] for l in _xor_lines(p)]

    def base_time(self, form: str, paint: int, coat: int, hf: int, n_panels: int) -> Optional[float]:
        kind = HF_KIND.get(hf, 'B')
        for r in self._com_rows('T_KEI_3.DB'):
            if len(r) >= 9 and r[0] == str(form) and r[1] == str(paint) and r[2] == str(coat) and r[3] == kind:
                return int(r[4 + min(max(n_panels, 1), 5) - 1]) / 100.0
        return None

    def bumper_base_time(self, form: str, coat: int) -> Optional[float]:
        """バンパ加算基礎（COM/BAN.DB: 車形, 塗膜クラス 1-4, 値×1/100, 予備, 予備）。
        外板パネルが 1 枚も無くバンパだけ塗装するときに PaintingPlan.BumperBaseTime に入る
        （実機 2026-09-12 W66 車形 6・2コートパール: 0.5、cogni_W66w。パネルがあるときは -1 = 加算基礎数値の側で見る）"""
        for r in self._com_rows('BAN.DB'):
            if len(r) >= 3 and r[0] == str(form) and r[1] == str(coat):
                try:
                    return int(r[2]) / 100.0
                except ValueError:
                    return None
        return None

    def booth_time(self, form: str, paint: int, coat: int, hf: int) -> Optional[float]:
        kind = HF_KIND.get(hf, 'B')
        for r in self._com_rows('BOOTH.DB'):
            if len(r) >= 5 and r[0] == str(form) and r[1] == str(paint) and r[2] == str(coat) and r[3] == kind:
                return int(r[4]) / 100.0
        return None

    def bumper_time(self, front: bool, coat: int, kind: str = '取替', two_tone: bool = False, paint: int = 3) -> Optional[float]:
        """<car>23.DB（溶剤）/ <car>93.DB（水性 paint=4、同形）のバンパ塗装標準指数。

        行 = `23/93, 車種, 年式群, ボディ, グレード, 装備(EVA), F/R, 塗膜クラス, 値×8, 予備`
        （RTTI の列名 Year / Body / Grade / EVA と同じ並び。パネル表 77/97/87/99.DB とも同じ）。
        値の並びは [取替一色, 取替二色, 外傷大一色, 外傷大二色, 外傷小一色, 外傷小二色, 変形一色, 変形二色]。

        **同じ車種に 年式群・ボディ・グレード・装備 別の行がある**（1,430 ファイル中 316 ファイル。
        例: D62 は 無条件 / グレード A / B / H の 4 組で F メタリック取替一色 2.5 対 2.2）。
        パネル表と同じ規則で絞る（2026-09-21。それまでは先頭行を当てていたので、条件行のある車で標準指数がずれていた）"""
        p = os.path.join(self.car_dir, f'{self.car}{93 if paint == 4 else 23}.DB')
        if not os.path.exists(p):
            return None
        cls = COAT_CLASS_BUMPER.get(coat, 2)
        base_idx = {'取替': 0, '新品': 0, '外傷大': 2, '外傷修正大': 2, '外傷小': 4, '外傷修正小': 4, '変形': 6, '変形修正': 6}.get(kind)
        if base_idx is None:
            return None  # '外傷修正'（小/大の区別なし）は 23.DB 車種では選べない（FBANPA 車種専用）
        idx = base_idx + (1 if two_tone else 0)
        cand = []
        for l in _xor_lines(p):
            f = [x.strip() for x in l.split(',')]
            if len(f) >= 16 and f[6] == ('F' if front else 'R') and f[7] == str(cls):
                cand.append({'grp': f[2], 'body': f[3], 'grade': f[4], 'eva': f[5],
                             'vals': [int(x or 0) / 100.0 for x in f[8:16]]})
        if not cand:
            return None
        pick = self._pick_panel_row(cand)  # 行が 1 つでも通す: 条件行しか無い車（ボディ・年式限定）で
                                          # その行を無条件に当てない（Codex 指摘 2026-09-21）
        if pick is None:  # この車の装備・グレードに合う行が無い（無条件行も無い）→ 標準なし
            return None
        v = pick['vals'][idx]
        return v if v > 0 else None  # 0 埋めは未収録扱い


    def has_bumper_table(self, paint: int = 3) -> bool:
        """車種別のバンパ表（<car>23.DB、水性は 93.DB）があるか。無い車種は COM/FBANPA.DB（bumper_time_generic）"""
        return os.path.exists(os.path.join(self.car_dir, f'{self.car}{93 if paint == 4 else 23}.DB'))

    def bumper_time_generic(self, coat: int, kind: str, form_code: int, col_code: int,
                            bumper_only: bool) -> Optional[float]:
        """<car>23.DB の無い車種（586 車種 = 01.DB を持つ 1,299 車種中、うち 20.DB あり 489。例: ミニキャブ・パートナー・アクティ・ダイナ等）の樹脂バンパ塗装 = COM/FBANPA.DB。
        行 `車形 0, K/S, 塗膜クラス 1-4, 副区分(S: 1=変形修正 2=外傷修正), v1..v6`。
        **6 つの値は 3 列ずつ 2 群**で、どちらを使うかは「塗装パネルがあるか」で決まる（2026-09-21 実案件 23 行で確定）:

        - **塗装パネルがある見積 → v1/v2/v3**（一色/黒ライン/二色）。パネル側に加算基礎が立つので、バンパは単体の値。
          実案件 20 行すべてこちら（うち 1 行はバンパ加算基礎 0.4 も別に立っている）
        - **バンパだけを塗る見積（塗装パネル 0 枚）→ v4/v5/v6**。加算基礎相当（v4 − v1 ＝ 塗膜別 0.3/0.4/0.4/0.6
          ＝ バンパ加算基礎 − 0.1）が内包されている。実案件 2 行と、コグニ実機 J69（2026-09-06 夕。画面 19 値・
          保存 NEO FBANPA_J69.neo。どちらも塗装パネル 0 枚）がこちら

        標準形状は 大型 − 0.1（実機 3コートパール 新品: 大型 2.6/3.0/3.3、標準 2.5/2.9/3.2。
        メタリック 変形 大型黒ライン 4.6 = S,2,1 の v5、外傷 4.0 = S,2,2 の v5）。絞模様有りは呼び出し側で +0.4"""
        cls = COAT_CLASS_BUMPER.get(coat, 2)
        ks = 'K' if kind in ('取替', '新品') else 'S'
        sub = '0' if ks == 'K' else ('1' if kind.startswith('変形') else '2')
        form = (self.form_codes()[0] or '0').strip()  # 行の第 1 列 = 車形（25.DB の CarFormCode。0〜9 の 10 車形 × 12 行。車形 6（J69/W66）は 0 と同値、7（軽）は別値）
        rows = self._com_rows('FBANPA.DB')
        cand = [f for f in rows if len(f) >= 10 and f[0].strip() == form] or [f for f in rows if len(f) >= 10 and f[0].strip() == '0']
        for f in cand:
            if f[1].strip() == ks and f[2].strip() == str(cls) and f[3].strip() == sub:
                v = int(f[4 + (3 if bumper_only else 0) + min(max(col_code, 0), 2)] or 0)  # パネルがあれば v1..v3、バンパだけなら v4..v6
                if v <= 0:
                    return None
                t = v / 100.0 - (0.1 if form_code == 1 else 0.0)
                return round(t, 1)
        return None


if __name__ == '__main__':
    import sys
    pi = PaintIndex(r'C:\Addata', sys.argv[1] if len(sys.argv) > 1 else 'W69')
    for r in pi.panels:
        print(r)
    for r in pi.chm_rows:
        print(r)
    for c in ('1000', '3100', '3500', '5000'):
        print(c, {k: v for k, v in (pi.standard_times(c, 2, 4) or {}).items() if k not in ('panel', 'chm')})
    print('base', pi.base_time('6', 3, 3, 2, 4), 'booth', pi.booth_time('6', 3, 3, 2), 'bumper', pi.bumper_time(True, 3))
