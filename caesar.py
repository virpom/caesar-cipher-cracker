#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CAESAR CIPHER CRACKER — ULTIMATE EDITION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Многоуровневый анализ для идеальной расшифровки:
  1. Chi-squared частотный анализ (реальные частоты русского языка)
  2. Биграммный анализ (для коротких текстов)
  3. Index of Coincidence (определение: зашифрован ли текст?)
  4. Словарный анализ с морфологическим стеммингом
  5. Скользящее окно для смешанных шифров
  6. Адаптивные веса в зависимости от длины текста
"""

import sys
import re
import math
import argparse
from pathlib import Path
from typing import List, Tuple, Dict, Optional, Set
from dataclasses import dataclass, field
from functools import lru_cache
from collections import Counter

try:
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn
    from rich import box
    from rich.prompt import Prompt, Confirm
    from rich.text import Text
    HAS_RICH = True
except ImportError:
    HAS_RICH = False


# ═══════════════════════════════════════════════════════════════════════════════
# ЛИНГВИСТИЧЕСКИЕ КОНСТАНТЫ
# Реальные частоты русского языка (исследования НКРЯ)
# ═══════════════════════════════════════════════════════════════════════════════

RU_ALPHA = 'абвгдеёжзийклмнопрстуфхцчшщъыьэюя'
RU_SET   = frozenset(RU_ALPHA)
RU_SIZE  = len(RU_ALPHA)  # 33

EN_ALPHA = 'abcdefghijklmnopqrstuvwxyz'
EN_SET   = frozenset(EN_ALPHA)
EN_SIZE  = len(EN_ALPHA)  # 26

# Частоты букв русского языка (НКРЯ)
RU_LETTER_FREQ = {
    'о': 0.1097, 'е': 0.0845, 'а': 0.0801, 'и': 0.0735, 'н': 0.0670,
    'т': 0.0626, 'с': 0.0547, 'р': 0.0473, 'в': 0.0454, 'л': 0.0440,
    'к': 0.0349, 'м': 0.0321, 'д': 0.0298, 'п': 0.0281, 'у': 0.0262,
    'я': 0.0201, 'ы': 0.0190, 'ь': 0.0174, 'г': 0.0170, 'з': 0.0165,
    'б': 0.0159, 'ч': 0.0144, 'й': 0.0121, 'х': 0.0097, 'ж': 0.0094,
    'ш': 0.0073, 'ю': 0.0064, 'ц': 0.0048, 'щ': 0.0036, 'э': 0.0032,
    'ф': 0.0026, 'ъ': 0.0004, 'ё': 0.0004,
}

# Частоты букв английского языка (Cornell)
EN_LETTER_FREQ = {
    'e': 0.1270, 't': 0.0906, 'a': 0.0817, 'o': 0.0751, 'i': 0.0697,
    'n': 0.0675, 's': 0.0633, 'h': 0.0609, 'r': 0.0599, 'd': 0.0425,
    'l': 0.0403, 'c': 0.0278, 'u': 0.0276, 'm': 0.0241, 'w': 0.0236,
    'f': 0.0223, 'g': 0.0202, 'y': 0.0197, 'p': 0.0193, 'b': 0.0129,
    'v': 0.0098, 'k': 0.0077, 'j': 0.0015, 'x': 0.0015, 'q': 0.0010,
    'z': 0.0007,
}

# Самые частые биграммы
RU_COMMON_BIGRAMS = frozenset({
    'ст', 'но', 'то', 'на', 'ен', 'ни', 'ко', 'ра', 'ов', 'ро',
    'ос', 'ал', 'ер', 'он', 'не', 'ли', 'по', 'ре', 'ор', 'ан',
    'пр', 'ет', 'ол', 'та', 'ел', 'ка', 'во', 'ти', 'ва', 'од',
    'ат', 'ле', 'от', 'те', 'ла', 'ом', 'де', 'ес', 'ве', 'ло',
    'ог', 'за', 'ск', 'ть', 'ин', 'ит', 'пе', 'се', 'об', 'да',
    'ем', 'го', 'ас', 'из', 'ие', 'ри', 'ил', 'ед', 'ар', 'ам',
    'до', 'ис', 'тр', 'ны', 'ми', 'ча', 'бо', 'ор', 'ег', 'ру',
    'ме', 'мо', 'ги', 'ди', 'ви', 'бе', 'ак', 'ки', 'ое', 'ём',
})

EN_COMMON_BIGRAMS = frozenset({
    'th', 'he', 'in', 'er', 'an', 're', 'on', 'at', 'en', 'nd',
    'ti', 'es', 'or', 'te', 'of', 'ed', 'is', 'it', 'al', 'ar',
    'st', 'to', 'nt', 'ng', 'se', 'ha', 'as', 'ou', 'io', 'le',
    've', 'co', 'me', 'de', 'hi', 'ri', 'ro', 'ic', 'ne', 'ea',
    'ra', 'ce', 'li', 'ch', 'll', 'be', 'ma', 'si', 'om', 'ur',
    'ca', 'el', 'ta', 'la', 'ns', 'ge', 'ha', 'ec', 'it', 'il',
    'pe', 'ol', 'no', 'na', 'us', 'di', 'wa', 'em', 'ac', 'ss',
})

# Суффиксы для стемминга
RU_SUFFIXES = (
    'ость', 'ение', 'ание', 'ться', 'ются', 'ится', 'ного', 'ному',
    'ским', 'ской', 'ных', 'ные', 'ный', 'ная', 'ное', 'ной',
    'ого', 'ому', 'ыми', 'ами', 'ями', 'ать', 'ять', 'еть', 'ить',
    'ует', 'ает', 'ёт', 'ют', 'ут', 'ит', 'ет',
    'ов', 'ев', 'ей', 'ий', 'ый', 'ой', 'ая', 'ое', 'ие',
    'ом', 'ем', 'ам', 'ям', 'ах', 'ях', 'ых', 'их',
    'ал', 'ил', 'ел', 'ол', 'ул',
    'ть', 'ся', 'сь',
)

EN_SUFFIXES = (
    'tion', 'ness', 'ment', 'able', 'ible', 'ious', 'eous',
    'ing', 'ous', 'ful', 'ive', 'ity', 'ent', 'ant', 'ion',
    'ism', 'ist', 'ory', 'ary', 'ery', 'ure', 'age', 'ise', 'ize',
    'ly', 'er', 'ed', 'es', 'al', 'en', 'ty',
    'or', 'ic', 'le',
    's',
)


# ═══════════════════════════════════════════════════════════════════════════════
# DATA CLASSES
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ShiftResult:
    """Результат анализа одного сдвига"""
    shift: int
    text: str
    chi_sq: float          # Chi-squared (меньше = лучше)
    bigram_score: float    # Биграммная оценка [0..1]
    dict_score: float      # Словарная оценка [0..1]
    stem_score: float      # Стемминг-оценка [0..1]
    combined: float        # Финальная оценка [0..1]
    matches: int           # Словарных слов
    total_words: int       # Всего слов

    @property
    def confidence(self) -> float:
        return min(self.combined * 100, 100.0)


@dataclass(frozen=True)
class Segment:
    """Сегмент текста (для смешанного шифра)"""
    text: str
    start: int
    end: int
    best_result: ShiftResult


# ═══════════════════════════════════════════════════════════════════════════════
# СЛОВАРЬ
# ═══════════════════════════════════════════════════════════════════════════════

_SCRIPT_DIR = Path(__file__).resolve().parent


class Dictionary:
    """Синглтон-словарь с ленивой загрузкой (русский + английский)"""
    _inst = None
    _ru_words: Optional[Set[str]] = None
    _en_words: Optional[Set[str]] = None

    def __new__(cls):
        if cls._inst is None:
            cls._inst = super().__new__(cls)
        return cls._inst

    @property
    def ru_words(self) -> Set[str]:
        if self._ru_words is None:
            self._load_ru()
        return self._ru_words

    @property
    def en_words(self) -> Set[str]:
        if self._en_words is None:
            self._load_en()
        return self._en_words

    def words(self, lang: str) -> Set[str]:
        return self.ru_words if lang == 'ru' else self.en_words

    @staticmethod
    def _find(name: str) -> Optional[Path]:
        """1. Рядом со скриптом  2. CWD  3. HOME"""
        for p in [_SCRIPT_DIR / name, Path(name), Path.home() / name]:
            if p.exists() and p.stat().st_size > 100:
                return p
        return None

    def _load_file(self, path: Path) -> Set[str]:
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                return {
                    w.lower() for line in f
                    if (w := line.strip()) and 2 <= len(w) <= 50 and w.isalpha()
                }
        except Exception:
            return set()

    def _load_ru(self):
        p = self._find('russian_dict.txt')
        self._ru_words = self._load_file(p) if p else set()
        self._ru_words |= {
            'и', 'в', 'не', 'на', 'он', 'что', 'как', 'а', 'то', 'все',
            'она', 'так', 'его', 'но', 'да', 'ты', 'же', 'вы', 'за', 'бы',
            'по', 'от', 'из', 'для', 'это', 'мы', 'они', 'был', 'быть',
        }

    def _load_en(self):
        p = self._find('english_dict.txt')
        self._en_words = self._load_file(p) if p else set()
        self._en_words |= {
            'the', 'be', 'to', 'of', 'and', 'in', 'that', 'have', 'it', 'for',
            'not', 'on', 'with', 'he', 'as', 'you', 'do', 'at', 'this', 'but',
            'his', 'by', 'from', 'they', 'we', 'say', 'her', 'she', 'or', 'an',
            'will', 'my', 'one', 'all', 'would', 'there', 'their', 'what', 'so',
            'if', 'about', 'who', 'get', 'which', 'go', 'when', 'can', 'no',
        }

    def __len__(self) -> int:
        return len(self.ru_words) + len(self.en_words)


# ═══════════════════════════════════════════════════════════════════════════════
# ДЕШИФРОВЩИК
# ═══════════════════════════════════════════════════════════════════════════════

class Decryptor:
    """Дешифровка через str.translate() — O(n), реализация на C"""

    @staticmethod
    @lru_cache(maxsize=128)
    def _table(shift: int, lang: str) -> dict:
        alpha = RU_ALPHA if lang == 'ru' else EN_ALPHA
        size = len(alpha)
        lo = alpha
        up = lo.upper()
        s_lo = ''.join(lo[(i - shift) % size] for i in range(size))
        s_up = ''.join(up[(i - shift) % size] for i in range(size))
        return str.maketrans(lo + up, s_lo + s_up)

    @staticmethod
    def decrypt(text: str, shift: int, lang: str = 'ru') -> str:
        return text.translate(Decryptor._table(shift, lang))


# ═══════════════════════════════════════════════════════════════════════════════
# СКОРЕРЫ (многоуровневая система оценки)
# ═══════════════════════════════════════════════════════════════════════════════

def chi_squared(text: str, lang: str = 'ru') -> float:
    """
    Chi-squared тест: сравнение частоты букв с эталоном.
    Меньше = лучше.
    """
    charset = RU_SET if lang == 'ru' else EN_SET
    freqs = RU_LETTER_FREQ if lang == 'ru' else EN_LETTER_FREQ

    letters = [c for c in text.lower() if c in charset]
    n = len(letters)
    if n == 0:
        return float('inf')

    observed = Counter(letters)
    chi_sq = 0.0
    for char, expected_freq in freqs.items():
        expected = expected_freq * n
        actual = observed.get(char, 0)
        if expected > 0:
            chi_sq += (actual - expected) ** 2 / expected

    return chi_sq


def bigram_score(text: str, lang: str = 'ru') -> float:
    """Оценка по биграммам."""
    charset = RU_SET if lang == 'ru' else EN_SET
    common = RU_COMMON_BIGRAMS if lang == 'ru' else EN_COMMON_BIGRAMS

    letters = [c for c in text.lower() if c in charset]
    if len(letters) < 4:
        return 0.0

    bigrams = [letters[i] + letters[i+1] for i in range(len(letters) - 1)]
    if not bigrams:
        return 0.0

    hits = sum(1 for bg in bigrams if bg in common)
    return hits / len(bigrams)


def index_of_coincidence(text: str, lang: str = 'ru') -> float:
    """
    Index of Coincidence.
    RU ≈ 0.0553, EN ≈ 0.0667, random_ru ≈ 0.0303, random_en ≈ 0.0385
    """
    charset = RU_SET if lang == 'ru' else EN_SET

    letters = [c for c in text.lower() if c in charset]
    n = len(letters)
    if n < 2:
        return 0.0

    freq = Counter(letters)
    ic = sum(f * (f - 1) for f in freq.values()) / (n * (n - 1))
    return ic


def stem_word(word: str, lang: str = 'ru') -> str:
    """Лёгкий стемминг: отрезает суффиксы."""
    suffixes = RU_SUFFIXES if lang == 'ru' else EN_SUFFIXES
    min_base = 2 if lang == 'en' else 3  # Англ. основы короче
    for suffix in suffixes:
        if len(word) > len(suffix) + min_base and word.endswith(suffix):
            return word[:-len(suffix)]
    return word


def normalize_yo(text: str) -> str:
    """Нормализация ё→е для устойчивости к вариативному написанию"""
    return text.replace('ё', 'е').replace('Ё', 'Е')


# ═══════════════════════════════════════════════════════════════════════════════
# СЛОВАРНЫЙ АНАЛИЗ
# ═══════════════════════════════════════════════════════════════════════════════

_RU_WORD_RE = re.compile(r'[а-яёА-ЯЁ]{2,}')
_EN_WORD_RE = re.compile(r'[a-zA-Z]{2,}')


def extract_words(text: str, lang: str = 'ru') -> Tuple[str, ...]:
    """Извлекает слова из текста"""
    pattern = _RU_WORD_RE if lang == 'ru' else _EN_WORD_RE
    return tuple(w.lower() for w in pattern.findall(text))


def dict_score(text: str, dictionary: Set[str], lang: str = 'ru') -> Tuple[float, int, int]:
    """
    Словарный анализ с многоуровневым поиском:
    1. Точное совпадение
    2. Без ё (е вместо ё) [только RU]
    3. Стемминг + поиск
    """
    words = extract_words(text, lang)
    if not words:
        return 0.0, 0, 0

    matches = 0
    match_weight = 0
    total_weight = 0

    for word in words:
        wlen = len(word)
        total_weight += wlen

        # 1. Точное совпадение
        if word in dictionary:
            matches += 1
            match_weight += wlen
            continue

        # 2. Замена ё→е (только RU)
        if lang == 'ru':
            word_no_yo = normalize_yo(word)
            if word_no_yo != word and word_no_yo in dictionary:
                matches += 1
                match_weight += wlen
                continue
        else:
            word_no_yo = word

        # 3. Стемминг
        stem = stem_word(word, lang)
        if stem != word and stem in dictionary:
            matches += 1
            match_weight += wlen * 0.8
            continue

        # 4. Стемминг + нормализация
        if lang == 'ru':
            stem_no_yo = stem_word(word_no_yo, lang)
            if stem_no_yo != word_no_yo and stem_no_yo in dictionary:
                matches += 1
                match_weight += wlen * 0.7
                continue

    ratio = matches / len(words) if words else 0.0
    weighted = match_weight / total_weight if total_weight > 0 else 0.0

    return ratio * 0.5 + weighted * 0.5, matches, len(words)


def stem_dict_score(text: str, dictionary: Set[str], lang: str = 'ru') -> float:
    """Агрессивный стемминг: обрезаем до нахождения корня."""
    words = extract_words(text, lang)
    if not words:
        return 0.0

    min_stem = 2 if lang == 'en' else 3
    hits = 0
    for word in words:
        stem = stem_word(normalize_yo(word) if lang == 'ru' else word, lang)
        candidate = stem
        while len(candidate) >= min_stem:
            if candidate in dictionary:
                hits += 1
                break
            candidate = candidate[:-1]

    return hits / len(words) if words else 0.0


# ═══════════════════════════════════════════════════════════════════════════════
# ГЛАВНЫЙ АНАЛИЗАТОР
# ═══════════════════════════════════════════════════════════════════════════════

class Analyzer:
    """
    Многоуровневый анализатор со адаптивными весами.
    
    Для длинных текстов (>50 букв):
      — Chi-squared доминирует (очень надёжен)
      — Словарь подтверждает
    
    Для коротких текстов (<20 букв):
      — Биграммы спасают
      — Словарь + стемминг критичны
      — Chi-squared ненадёжен (мало данных)
    
    Для средних:
      — Баланс всех методов
    """

    def __init__(self):
        self.dict = Dictionary()

    def detect_language(self, text: str) -> str:
        """Определяет язык текста"""
        ru = sum(1 for c in text.lower() if c in RU_SET)
        en = sum(1 for c in text.lower() if c in EN_SET)
        return 'ru' if ru > en else 'en'

    def _letter_count(self, text: str, lang: str = 'ru') -> int:
        charset = RU_SET if lang == 'ru' else EN_SET
        return sum(1 for c in text if c.lower() in charset)

    def analyze_shift(self, text: str, shift: int, lang: str = 'ru') -> ShiftResult:
        """Полный анализ одного варианта сдвига"""
        decrypted = Decryptor.decrypt(text, shift, lang)
        dictionary = self.dict.words(lang)

        # 1. Chi-squared
        chi = chi_squared(decrypted, lang)

        # 2. Биграммы
        bg = bigram_score(decrypted, lang)

        # 3. Словарь
        ds, matches, total = dict_score(decrypted, dictionary, lang)

        # 4. Стемминг
        ss = stem_dict_score(decrypted, dictionary, lang)

        # 5. Адаптивная комбинация
        letter_count = self._letter_count(text, lang)
        combined = self._combine(chi, bg, ds, ss, letter_count)

        return ShiftResult(
            shift=shift,
            text=decrypted,
            chi_sq=chi,
            bigram_score=bg,
            dict_score=ds,
            stem_score=ss,
            combined=combined,
            matches=matches,
            total_words=total,
        )

    def _combine(
        self, chi: float, bg: float, ds: float, ss: float, n_letters: int
    ) -> float:
        """
        Адаптивная комбинация скоров.
        Веса меняются в зависимости от длины текста.
        """
        # Нормализуем chi-squared в [0..1] (инвертируем: меньше chi = лучше)
        # Типичный диапазон: 20-1000
        chi_norm = max(0.0, 1.0 - chi / 500.0)

        if n_letters >= 100:
            # Длинный текст: chi-squared очень надёжен
            w_chi, w_bg, w_dict, w_stem = 0.35, 0.10, 0.35, 0.20
        elif n_letters >= 30:
            # Средний текст: баланс
            w_chi, w_bg, w_dict, w_stem = 0.20, 0.20, 0.35, 0.25
        elif n_letters >= 10:
            # Короткий текст: биграммы и словарь важнее
            w_chi, w_bg, w_dict, w_stem = 0.10, 0.30, 0.35, 0.25
        else:
            # Очень короткий: биграммы доминируют
            w_chi, w_bg, w_dict, w_stem = 0.05, 0.45, 0.30, 0.20

        return w_chi * chi_norm + w_bg * bg + w_dict * ds + w_stem * ss

    def crack(self, text: str, lang: str = None) -> List[ShiftResult]:
        """Перебирает все сдвиги, возвращает отсортированный список"""
        if lang is None:
            lang = self.detect_language(text)
        alpha_size = RU_SIZE if lang == 'ru' else EN_SIZE
        results = [self.analyze_shift(text, s, lang) for s in range(alpha_size)]
        results.sort(key=lambda r: r.combined, reverse=True)
        return results

    def is_already_plaintext(self, text: str) -> bool:
        """Проверяет, не является ли текст уже открытым"""
        lang = self.detect_language(text)
        dictionary = self.dict.words(lang)
        ds, matches, total = dict_score(text, dictionary, lang)

        if total > 0 and matches / total >= 0.7:
            return True

        if self._letter_count(text, lang) >= 30:
            ic = index_of_coincidence(text, lang)
            ic_threshold = 0.045 if lang == 'ru' else 0.055
            return ic > ic_threshold and ds > 0.4

        return False


# ═══════════════════════════════════════════════════════════════════════════════
# ДЕТЕКТОР СМЕШАННЫХ ШИФРОВ
# ═══════════════════════════════════════════════════════════════════════════════

class MixedDetector:
    """
    Скользящее окно для обнаружения границ смены ключа.
    
    Алгоритм:
    1. Сначала пробуем единый ключ
    2. Если confidence < порога — проверяем гипотезу смешанного шифра
    3. Используем скользящее окно: на каждой позиции вычисляем
       оптимальный ключ для окрестности
    4. Находим точки смены ключа (где ключ меняется)
    5. Разбиваем текст по этим точкам
    6. Для каждого сегмента — полный анализ
    """

    def __init__(self):
        self.analyzer = Analyzer()
        self.window_size = 40  # Символов в окне

    def detect(self, text: str) -> List[Segment]:
        """Определяет сегменты с разными ключами"""
        lang = self.analyzer.detect_language(text)
        charset = RU_SET if lang == 'ru' else EN_SET
        letters_only = [c for c in text if c.lower() in charset]
        n = len(letters_only)

        if n < self.window_size * 2:
            results = self.analyzer.crack(text, lang)
            best = results[0]
            return [Segment(text=best.text, start=0, end=len(text), best_result=best)]

        shift_map = self._compute_shift_map(text, lang)
        boundaries = self._find_boundaries(shift_map, text)

        segments = []
        for start, end in boundaries:
            segment_text = text[start:end]
            results = self.analyzer.crack(segment_text, lang)
            best = results[0]
            segments.append(Segment(
                text=best.text, start=start, end=end, best_result=best
            ))

        return segments

    def _compute_shift_map(self, text: str, lang: str = 'ru') -> List[int]:
        """Для каждого символа определяет оптимальный ключ через окно"""
        charset = RU_SET if lang == 'ru' else EN_SET
        alpha_size = RU_SIZE if lang == 'ru' else EN_SIZE
        n = len(text)
        shift_map = []
        half_w = self.window_size // 2

        for i in range(n):
            if text[i].lower() not in charset:
                shift_map.append(shift_map[-1] if shift_map else 0)
                continue

            start = max(0, i - half_w)
            end = min(n, i + half_w)
            window = text[start:end]

            best_shift = 0
            best_score = -1.0

            for s in range(alpha_size):
                dec = Decryptor.decrypt(window, s, lang)
                chi = chi_squared(dec, lang)
                bg = bigram_score(dec, lang)
                score = bg * 0.6 + max(0, 1 - chi / 500) * 0.4

                if score > best_score:
                    best_score = score
                    best_shift = s

            shift_map.append(best_shift)

        return shift_map

    def _find_boundaries(
        self, shift_map: List[int], text: str
    ) -> List[Tuple[int, int]]:
        """
        Находит границы сегментов по карте сдвигов.
        Использует сглаживание голосованием большинства.
        """
        n = len(shift_map)
        if n == 0:
            return [(0, len(text))]

        # Сглаживание: для каждой позиции берём моду окрестности
        smooth_window = 15
        smoothed = []
        for i in range(n):
            start = max(0, i - smooth_window // 2)
            end = min(n, i + smooth_window // 2 + 1)
            neighborhood = shift_map[start:end]
            mode = Counter(neighborhood).most_common(1)[0][0]
            smoothed.append(mode)

        # Находим точки смены
        boundaries = []
        seg_start = 0
        current_shift = smoothed[0]

        for i in range(1, n):
            if smoothed[i] != current_shift:
                boundaries.append((seg_start, i))
                seg_start = i
                current_shift = smoothed[i]

        boundaries.append((seg_start, n))

        # Фильтруем: сливаем слишком маленькие сегменты с соседями
        min_segment = 15
        merged = []
        for start, end in boundaries:
            if end - start < min_segment and merged:
                prev_start, _ = merged[-1]
                merged[-1] = (prev_start, end)
            else:
                merged.append((start, end))

        if not merged:
            return [(0, len(text))]

        # Корректируем границы: ищем ближайший пробел/знак препинания
        adjusted = []
        for i, (start, end) in enumerate(merged):
            # Начало: сдвигаем к началу слова
            if i > 0 and start > 0:
                # Ищем ближайший пробел/знак назад (до 5 символов)
                for delta in range(min(5, start)):
                    if text[start - delta] in ' .,!?;:\n\t':
                        start = start - delta + 1
                        break
            # Конец: сдвигаем к концу слова
            if i < len(merged) - 1 and end < len(text):
                for delta in range(min(5, len(text) - end)):
                    if text[end + delta] in ' .,!?;:\n\t':
                        end = end + delta
                        break
            adjusted.append((start, end))

        # Убираем перекрытия
        final = [adjusted[0]]
        for start, end in adjusted[1:]:
            prev_start, prev_end = final[-1]
            if start < prev_end:
                start = prev_end
            if start < end:
                final.append((start, end))

        return final


# ═══════════════════════════════════════════════════════════════════════════════
# UI (Rich / Fallback)
# ═══════════════════════════════════════════════════════════════════════════════

class UI:
    def __init__(self):
        self.c = Console() if HAS_RICH else None

    def header(self):
        if self.c:
            self.c.print(Panel(
                "[bold cyan]CAESAR CRACKER — ULTIMATE EDITION[/bold cyan]\n"
                "[dim]Chi² • Биграммы • Стемминг • Смешанные шифры[/dim]",
                border_style="cyan", box=box.DOUBLE
            ))
            self.c.print()
        else:
            print("=" * 70)
            print("  CAESAR CRACKER — ULTIMATE EDITION")
            print("=" * 70)
            print()

    def info(self, dict_size: int, is_plain: bool, lang_name: str = ""):
        if self.c:
            status = "[green]✓ Текст открытый (не зашифрован)[/green]" if is_plain else "[yellow]🔐 Текст зашифрован[/yellow]"
            self.c.print(Panel(
                f"📖 Словарь: [bold]{dict_size:,}[/bold] слов\n"
                f"🌐 Язык: [bold]{lang_name}[/bold]\n"
                f"📊 Статус: {status}",
                title="[bold]Конфигурация[/bold]", border_style="blue"
            ))
            self.c.print()
        else:
            status = "открытый" if is_plain else "зашифрован"
            print(f"Словарь: {dict_size:,} слов | Язык: {lang_name} | Статус: {status}")
            print()

    def result_single(self, best: ShiftResult, top5: List[ShiftResult]):
        if self.c:
            # Основной результат — без рамки, легко копировать
            self.c.print()
            self.c.print("[bold green]💬 РАСШИФРОВАННЫЙ ТЕКСТ:[/bold green]")
            self.c.print()
            self.c.print(best.text)
            self.c.print()

            # Метрики
            self.c.print(
                f"[dim]🔑 Ключ: [bold yellow]{best.shift}[/bold yellow]  "
                f"📊 {self._conf_colored(best.confidence)}  "
                f"📖 {best.matches}/{best.total_words} слов  "
                f"Chi²={best.chi_sq:.0f}  "
                f"Бигр.: {best.bigram_score:.0%}  "
                f"Слов.: {best.dict_score:.0%}  "
                f"Стем.: {best.stem_score:.0%}[/dim]"
            )
            self.c.print()

            # Топ-5
            t5 = Table(
                box=box.SIMPLE, show_header=True,
                header_style="bold", title="[bold]Альтернативы[/bold]"
            )
            t5.add_column("#", width=4)
            t5.add_column("Ключ", width=6)
            t5.add_column("Достов.", width=10)
            t5.add_column("Текст")

            for i, r in enumerate(top5, 1):
                marker = "⭐" if i == 1 else str(i)
                preview = r.text[:60] + "…" if len(r.text) > 60 else r.text
                t5.add_row(marker, str(r.shift), self._conf_colored(r.confidence), preview)

            self.c.print(t5)
        else:
            print(f"\n💬 РАСШИФРОВАННЫЙ ТЕКСТ:")
            print(best.text)
            print(f"\n🔑 Ключ: {best.shift}  Достоверность: {best.confidence:.1f}%  "
                  f"Слов: {best.matches}/{best.total_words}")
            print(f"Chi²={best.chi_sq:.1f}  Бигр.={best.bigram_score:.0%}  "
                  f"Слов.={best.dict_score:.0%}  Стем.={best.stem_score:.0%}")
            print("\nАльтернативы:")
            for i, r in enumerate(top5, 1):
                m = "⭐" if i == 1 else f"{i}."
                p = r.text[:60] + "…" if len(r.text) > 60 else r.text
                print(f"  {m} ключ={r.shift} ({r.confidence:.0f}%) {p}")

    def result_mixed(self, segments: List[Segment]):
        keys = [s.best_result.shift for s in segments]
        is_mixed = len(set(keys)) > 1

        full_text = ''.join(s.text for s in segments)
        avg_conf = sum(s.best_result.confidence for s in segments) / len(segments)

        if self.c:
            if is_mixed:
                self.c.print(Panel(
                    f"[bold yellow]⚠️  СМЕШАННЫЙ ШИФР: {len(set(keys))} разных ключей[/bold yellow]\n"
                    f"Ключи: [bold]{', '.join(str(k) for k in keys)}[/bold]",
                    border_style="yellow", box=box.HEAVY
                ))
                self.c.print()

            tbl = Table(
                box=box.ROUNDED, show_header=True,
                header_style="bold magenta", title="[bold]Сегменты[/bold]"
            )
            tbl.add_column("#", width=4, style="cyan")
            tbl.add_column("Ключ", width=6, style="yellow")
            tbl.add_column("Достов.", width=10)
            tbl.add_column("Слова", width=8, style="blue")
            tbl.add_column("Текст")

            for i, seg in enumerate(segments, 1):
                r = seg.best_result
                preview = seg.text[:50] + "…" if len(seg.text) > 50 else seg.text
                tbl.add_row(
                    str(i), str(r.shift),
                    self._conf_colored(r.confidence),
                    f"{r.matches}/{r.total_words}",
                    preview
                )

            self.c.print(tbl)
            self.c.print()

            self.c.print("[bold green]💬 ПОЛНЫЙ ТЕКСТ:[/bold green]")
            self.c.print()
            self.c.print(full_text)
            self.c.print()
        else:
            if is_mixed:
                print(f"\n⚠️  СМЕШАННЫЙ ШИФР: ключи {keys}")
            for i, seg in enumerate(segments, 1):
                r = seg.best_result
                print(f"  Сегмент {i}: ключ={r.shift} ({r.confidence:.0f}%) {seg.text[:60]}")
            print(f"\nПолный текст ({avg_conf:.0f}%):\n{full_text}")

    def _conf_colored(self, conf: float) -> str:
        if not self.c:
            return f"{conf:.1f}%"
        if conf >= 80:
            return f"[bold green]{conf:.1f}%[/bold green]"
        elif conf >= 50:
            return f"[yellow]{conf:.1f}%[/yellow]"
        else:
            return f"[red]{conf:.1f}%[/red]"

    def ask_multiline(self, prompt: str) -> str:
        """Многострочный ввод: пустая строка или Ctrl+D завершает"""
        if self.c:
            self.c.print(f"[bold yellow]{prompt}[/bold yellow]")
            self.c.print("[dim](пустая строка = конец ввода)[/dim]")
        else:
            print(f"{prompt}")
            print("(пустая строка = конец ввода)")

        lines = []
        try:
            while True:
                line = input()
                if line == '':
                    break
                lines.append(line)
        except EOFError:
            pass
        return '\n'.join(lines)

    def confirm(self, question: str) -> bool:
        if self.c:
            return Confirm.ask(f"[bold]{question}[/bold]")
        return input(f"{question} (y/n): ").strip().lower() in ('y', 'д', 'да')


# ═══════════════════════════════════════════════════════════════════════════════
# ПРИЛОЖЕНИЕ
# ═══════════════════════════════════════════════════════════════════════════════

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog='caesar',
        description='Caesar Cipher Cracker — автоматическая дешифровка шифра Цезаря',
    )
    p.add_argument('text', nargs='*', help='Зашифрованный текст')
    p.add_argument('-r', '--raw', action='store_true',
                   help='Вывести только расшифрованный текст (удобно для копирования и pipe)')
    p.add_argument('-m', '--mixed', action='store_true',
                   help='Принудительно проверить смешанный шифр')
    p.add_argument('-l', '--lang', choices=['ru', 'en'],
                   help='Принудительно задать язык (иначе авто)')
    return p.parse_args()


def run():
    args = parse_args()
    raw = args.raw

    analyzer = Analyzer()
    detector = MixedDetector()

    # Ввод текста
    if args.text:
        text = ' '.join(args.text)
        auto = True
    elif not sys.stdin.isatty():
        text = sys.stdin.read().strip()
        auto = True
    else:
        if raw:
            print("Ошибка: в режиме --raw нужно передать текст аргументом или через pipe", file=sys.stderr)
            sys.exit(1)
        ui = UI()
        ui.header()
        text = ui.ask_multiline("Введите зашифрованный текст:")
        auto = False

    if not text or text.lower() in ('exit', 'quit', 'q'):
        return

    lang = args.lang or analyzer.detect_language(text)

    # --- RAW MODE: только текст ---
    if raw:
        results = analyzer.crack(text, lang)
        best = results[0]
        if best.confidence < 60 and len(text) > 60:
            segments = detector.detect(text)
            keys = set(s.best_result.shift for s in segments)
            if len(keys) > 1:
                print(''.join(s.text for s in segments))
                return
        print(best.text)
        return

    # --- FULL UI MODE ---
    if auto:
        ui = UI()
        ui.header()

    lang_name = "Русский" if lang == 'ru' else "English"
    is_plain = analyzer.is_already_plaintext(text)
    ui.info(len(analyzer.dict), is_plain, lang_name)

    if is_plain:
        if auto:
            results = analyzer.crack(text, lang)
            ui.result_single(results[0], results[:5])
            return
        else:
            proceed = ui.confirm("Текст похож на незашифрованный. Продолжить?")
            if not proceed:
                return

    results = analyzer.crack(text, lang)
    best = results[0]

    use_mixed = args.mixed
    if not use_mixed and best.confidence < 60 and len(text) > 60:
        if auto:
            use_mixed = True
        else:
            use_mixed = ui.confirm(
                f"Достоверность низкая ({best.confidence:.0f}%). Проверить смешанный шифр?"
            )

    if not use_mixed and not auto:
        use_mixed = ui.confirm("Проверить смешанный шифр (разные ключи)?")

    if use_mixed:
        segments = detector.detect(text)
        keys = set(s.best_result.shift for s in segments)

        if len(keys) > 1:
            ui.result_mixed(segments)
        else:
            ui.result_single(best, results[:5])
    else:
        ui.result_single(best, results[:5])


if __name__ == '__main__':
    try:
        run()
    except KeyboardInterrupt:
        print("\n👋")
    except Exception as e:
        print(f"\n❌ {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)
