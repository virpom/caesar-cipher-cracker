// ============================================================================
// CAESAR CIPHER CRACKER — C++ EDITION
// ============================================================================
// Полный порт Python-реализации с 6 уровнями анализа:
//   1. Chi-squared частотный анализ (частоты НКРЯ / Cornell)
//   2. Биграммный анализ (80 частых пар букв)
//   3. Index of Coincidence (статистическая мера)
//   4. Словарный анализ с морфологическим стеммингом
//   5. Скользящее окно для смешанных шифров
//   6. Адаптивные веса в зависимости от длины текста
//
// Сборка: make  (или c++ -std=c++17 -O2 -o caesar caesar.cpp)
// ============================================================================

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <array>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <numeric>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <cassert>
#include <unistd.h>

namespace fs = std::filesystem;

// ============================================================================
// УТИЛИТЫ UTF-8
// Русские буквы в UTF-8 занимают 2 байта (0xD0..0xD1 + продолжение).
// Для корректной работы с кириллицей все операции идут через кодпоинты.
// ============================================================================

/// Декодирует UTF-8 строку в вектор кодпоинтов (char32_t)
static std::vector<char32_t> utf8_decode(const std::string& s) {
    std::vector<char32_t> out;
    out.reserve(s.size()); // верхняя граница, для ASCII точно хватит
    for (size_t i = 0; i < s.size(); ) {
        unsigned char c = s[i];
        char32_t cp;
        int len;
        if      (c < 0x80)             { cp = c;          len = 1; }
        else if ((c & 0xE0) == 0xC0)   { cp = c & 0x1F;   len = 2; }
        else if ((c & 0xF0) == 0xE0)   { cp = c & 0x0F;   len = 3; }
        else if ((c & 0xF8) == 0xF0)   { cp = c & 0x07;   len = 4; }
        else { ++i; continue; } // пропускаем битый байт
        for (int j = 1; j < len && (i + j) < s.size(); ++j)
            cp = (cp << 6) | (s[i + j] & 0x3F);
        out.push_back(cp);
        i += len;
    }
    return out;
}

/// Кодирует один кодпоинт обратно в UTF-8
static void utf8_append(std::string& r, char32_t cp) {
    if      (cp < 0x80)    { r += (char)cp; }
    else if (cp < 0x800)   { r += (char)(0xC0|(cp>>6));   r += (char)(0x80|(cp&0x3F)); }
    else if (cp < 0x10000) { r += (char)(0xE0|(cp>>12));   r += (char)(0x80|((cp>>6)&0x3F)); r += (char)(0x80|(cp&0x3F)); }
    else                   { r += (char)(0xF0|(cp>>18));   r += (char)(0x80|((cp>>12)&0x3F)); r += (char)(0x80|((cp>>6)&0x3F)); r += (char)(0x80|(cp&0x3F)); }
}

/// Кодирует вектор кодпоинтов в UTF-8 строку
static std::string utf8_encode(const std::vector<char32_t>& cps) {
    std::string r;
    r.reserve(cps.size() * 2); // для кириллицы ~2 байта на символ
    for (auto cp : cps) utf8_append(r, cp);
    return r;
}

/// Длина строки в символах (не в байтах)
static size_t utf8_charlen(const std::string& s) {
    size_t len = 0;
    for (size_t i = 0; i < s.size(); ) {
        unsigned char c = s[i];
        if      (c < 0x80)           i += 1;
        else if ((c & 0xE0) == 0xC0) i += 2;
        else if ((c & 0xF0) == 0xE0) i += 3;
        else                          i += 4;
        ++len;
    }
    return len;
}

// ============================================================================
// КЛАССИФИКАЦИЯ СИМВОЛОВ (RU / EN)
// ============================================================================

// Русские буквы: а-я (U+0430..U+044F) + ё (U+0451)
//                А-Я (U+0410..U+042F) + Ё (U+0401)
static bool is_ru_lower(char32_t c) { return (c >= 0x0430 && c <= 0x044F) || c == 0x0451; }
static bool is_ru_upper(char32_t c) { return (c >= 0x0410 && c <= 0x042F) || c == 0x0401; }
static bool is_ru(char32_t c) { return is_ru_lower(c) || is_ru_upper(c); }

// Латинские буквы: a-z, A-Z
static bool is_en_lower(char32_t c) { return c >= 'a' && c <= 'z'; }
static bool is_en_upper(char32_t c) { return c >= 'A' && c <= 'Z'; }
static bool is_en(char32_t c) { return is_en_lower(c) || is_en_upper(c); }

/// Перевод в нижний регистр (RU + EN)
static char32_t to_lower(char32_t c) {
    if (c == 0x0401) return 0x0451; // Ё → ё
    if (c >= 0x0410 && c <= 0x042F) return c + 0x20; // А-Я → а-я
    if (c >= 'A' && c <= 'Z') return c + 32;
    return c;
}

/// Перевод в верхний регистр (RU + EN)
static char32_t to_upper(char32_t c) {
    if (c == 0x0451) return 0x0401; // ё → Ё
    if (c >= 0x0430 && c <= 0x044F) return c - 0x20; // а-я → А-Я
    if (c >= 'a' && c <= 'z') return c - 32;
    return c;
}

// Русский алфавит в порядке: а б в г д е ё ж з и й к л м н о п р с т у ф х ц ч ш щ ъ ы ь э ю я
// Индексы:                    0 1 2 3 4 5 6 7 8 9 ...                                          32
// Ё (U+0451) стоит в Unicode отдельно, но в алфавите на позиции 6

static constexpr int RU_SIZE = 33; // размер русского алфавита
static constexpr int EN_SIZE = 26; // размер английского алфавита

/// Индекс буквы в русском алфавите (0-32), или -1 если не русская
static int ru_index(char32_t c) {
    c = to_lower(c);
    if (c == 0x0451) return 6;                                     // ё
    if (c >= 0x0430 && c <= 0x0435) return (int)(c - 0x0430);     // а-е → 0-5
    if (c >= 0x0436 && c <= 0x044F) return (int)(c - 0x0436) + 7; // ж-я → 7-32
    return -1;
}

/// Кодпоинт русской буквы по индексу в алфавите (строчная)
static char32_t ru_from_index(int idx) {
    if (idx == 6) return 0x0451;       // ё
    if (idx < 6)  return 0x0430 + idx; // а-е
    return 0x0436 + (idx - 7);         // ж-я
}

/// Индекс буквы в английском алфавите (0-25), или -1
static int en_index(char32_t c) {
    c = to_lower(c);
    if (c >= 'a' && c <= 'z') return (int)(c - 'a');
    return -1;
}

static char32_t en_from_index(int idx) { return 'a' + idx; }
static bool is_upper_cp(char32_t c) { return is_ru_upper(c) || is_en_upper(c); }


// ============================================================================
// ANSI-ЦВЕТА ДЛЯ ТЕРМИНАЛА
// ============================================================================

static bool g_color = true; // отключается в --raw или если stdout не терминал

static std::string clr(const char* code, const std::string& s) {
    return g_color ? std::string("\033[") + code + "m" + s + "\033[0m" : s;
}
static std::string bold(const std::string& s)        { return clr("1", s); }
static std::string dim(const std::string& s)         { return clr("2", s); }
static std::string green(const std::string& s)       { return clr("32", s); }
static std::string yellow(const std::string& s)      { return clr("33", s); }
static std::string bold_green(const std::string& s)  { return clr("1;32", s); }
static std::string bold_yellow(const std::string& s) { return clr("1;33", s); }
static std::string bold_cyan(const std::string& s)   { return clr("1;36", s); }
static std::string bold_red(const std::string& s)    { return clr("1;31", s); }

/// Цветная строка уверенности: зелёная ≥80%, жёлтая ≥50%, красная <50%
static std::string conf_colored(double conf) {
    char buf[16]; snprintf(buf, sizeof(buf), "%.1f%%", conf);
    if (conf >= 80) return bold_green(buf);
    if (conf >= 50) return yellow(buf);
    return bold_red(buf);
}

// ============================================================================
// ЛИНГВИСТИЧЕСКИЕ КОНСТАНТЫ
// ============================================================================

// Частоты букв по позиции в алфавите
// Русский: данные НКРЯ (Национальный корпус русского языка)
static const double RU_FREQ[33] = {
    0.0801, 0.0159, 0.0454, 0.0170, 0.0298, // а б в г д
    0.0845, 0.0004, 0.0094, 0.0165, 0.0735, // е ё ж з и
    0.0121, 0.0349, 0.0440, 0.0321, 0.0670, // й к л м н
    0.1097, 0.0281, 0.0473, 0.0547, 0.0626, // о п р с т
    0.0262, 0.0026, 0.0097, 0.0048, 0.0144, // у ф х ц ч
    0.0073, 0.0036, 0.0004, 0.0190, 0.0174, // ш щ ъ ы ь
    0.0032, 0.0064, 0.0201,                  // э ю я
};

// Английский: данные Cornell University
static const double EN_FREQ[26] = {
    0.0817, 0.0129, 0.0278, 0.0425, 0.1270, // a b c d e
    0.0223, 0.0202, 0.0609, 0.0697, 0.0015, // f g h i j
    0.0077, 0.0403, 0.0241, 0.0675, 0.0751, // k l m n o
    0.0193, 0.0010, 0.0599, 0.0633, 0.0906, // p q r s t
    0.0276, 0.0098, 0.0236, 0.0015, 0.0197, // u v w x y
    0.0007,                                   // z
};

// Таблицы биграмм (плоские bool-массивы для O(1) поиска)
// Индекс: первая_буква * РАЗМЕР_АЛФАВИТА + вторая_буква
static bool RU_BG_TABLE[33 * 33] = {};
static bool EN_BG_TABLE[26 * 26] = {};

/// Инициализация таблицы биграмм из списка строк
static void init_bigram(bool* table, int sz,
                         int (*idx_fn)(char32_t),
                         const std::vector<std::string>& bigrams) {
    std::fill(table, table + sz * sz, false);
    for (auto& bg : bigrams) {
        auto cps = utf8_decode(bg);
        if (cps.size() == 2) {
            int a = idx_fn(cps[0]), b = idx_fn(cps[1]);
            if (a >= 0 && b >= 0) table[a * sz + b] = true;
        }
    }
}

/// Заполняет обе таблицы биграмм (вызывается один раз при старте)
static void init_bigrams() {
    // 78 частых русских биграмм
    std::vector<std::string> ru = {
        "ст","но","то","на","ен","ни","ко","ра","ов","ро",
        "ос","ал","ер","он","не","ли","по","ре","ор","ан",
        "пр","ет","ол","та","ел","ка","во","ти","ва","од",
        "ат","ле","от","те","ла","ом","де","ес","ве","ло",
        "ог","за","ск","ть","ин","ит","пе","се","об","да",
        "ем","го","ас","из","ие","ри","ил","ед","ар","ам",
        "до","ис","тр","ны","ми","ча","бо","ег","ру",
        "ме","мо","ги","ди","ви","бе","ак","ки","ое",
    };
    init_bigram(RU_BG_TABLE, RU_SIZE, ru_index, ru);

    // 68 частых английских биграмм
    std::vector<std::string> en = {
        "th","he","in","er","an","re","on","at","en","nd",
        "ti","es","or","te","of","ed","is","it","al","ar",
        "st","to","nt","ng","se","ha","as","ou","io","le",
        "ve","co","me","de","hi","ri","ro","ic","ne","ea",
        "ra","ce","li","ch","ll","be","ma","si","om","ur",
        "ca","el","ta","la","ns","ge","ec","il",
        "pe","ol","no","na","us","di","wa","em","ac","ss",
    };
    init_bigram(EN_BG_TABLE, EN_SIZE, en_index, en);
}

// Суффиксы для морфологического стемминга
// Отсортированы по длине (длинные первыми) — первое совпадение отрезается
static const std::vector<std::string> RU_SUFFIXES = {
    "ость","ение","ание","ться","ются","ится","ного","ному",
    "ским","ской","ных","ные","ный","ная","ное","ной",
    "ого","ому","ыми","ами","ями","ать","ять","еть","ить",
    "ует","ает","ют","ут","ит","ет",
    "ов","ев","ей","ий","ый","ой","ая","ое","ие",
    "ом","ем","ам","ям","ах","ях","ых","их",
    "ал","ил","ел","ол","ул","ть","ся","сь",
};

static const std::vector<std::string> EN_SUFFIXES = {
    "tion","ness","ment","able","ible","ious","eous",
    "ing","ous","ful","ive","ity","ent","ant","ion",
    "ism","ist","ory","ary","ery","ure","age","ise","ize",
    "ly","er","ed","es","al","en","ty","or","ic","le","s",
};

// ============================================================================
// СТРУКТУРЫ ДАННЫХ
// ============================================================================

/// Результат анализа одного сдвига
struct ShiftResult {
    int shift = 0;
    std::string text;        // расшифрованный текст
    double chi_sq = 0;       // Chi-squared (меньше = лучше)
    double bigram_sc = 0;    // биграммная оценка [0..1]
    double dict_sc = 0;      // словарная оценка [0..1]
    double stem_sc = 0;      // стемминг-оценка [0..1]
    double combined = 0;     // итоговая комбинированная оценка [0..1]
    int matches = 0;         // найденных слов в словаре
    int total_words = 0;     // всего слов в тексте

    /// Уверенность в процентах (0-100%)
    double confidence() const { return std::min(combined * 100.0, 100.0); }
};

/// Сегмент текста (для смешанного шифра)
struct Segment {
    std::string text;
    int start = 0, end = 0;
    ShiftResult best;
};

/// Сегмент текста на одном языке (для двуязычного режима)
struct LangSegment {
    std::string text;
    std::string lang; // "ru" или "en"
    int start = 0, end = 0;
};


// ============================================================================
// СЛОВАРЬ
// Ленивая загрузка: RU и EN загружаются отдельно, только при необходимости.
// Поиск файлов: рядом с exe → родительская папка → CWD → HOME
// ============================================================================

static fs::path g_exe_dir; // директория исполняемого файла (из argv[0])

/// Ищет файл словаря в нескольких директориях
static fs::path find_dict(const std::string& name) {
    for (auto& dir : {g_exe_dir, g_exe_dir.parent_path(), fs::current_path(),
                       fs::path(std::getenv("HOME") ? std::getenv("HOME") : "")}) {
        auto p = dir / name;
        std::error_code ec;
        if (fs::exists(p, ec) && fs::file_size(p, ec) > 100) return p;
    }
    return {};
}

class Dictionary {
    std::unordered_set<std::string> ru_words_, en_words_;
    bool ru_loaded_ = false, en_loaded_ = false;

    /// Загружает слова из файла: строчные, только буквы, длина 2-50
    void load_file(const fs::path& path, std::unordered_set<std::string>& dict) {
        std::ifstream f(path, std::ios::binary);
        if (!f.is_open()) return;
        std::string line;
        while (std::getline(f, line)) {
            // Обрезаем пробелы и \r
            while (!line.empty() && (line.back() == '\r' || line.back() == '\n' || line.back() == ' '))
                line.pop_back();
            if (line.empty()) continue;

            auto cps = utf8_decode(line);
            if (cps.size() < 2 || cps.size() > 50) continue;

            bool alpha = true;
            for (auto& cp : cps) {
                cp = to_lower(cp);
                if (!is_ru(cp) && !is_en(cp)) { alpha = false; break; }
            }
            if (!alpha) continue;
            dict.insert(utf8_encode(cps));
        }
    }

    void load_ru() {
        auto p = find_dict("russian_dict.txt");
        if (!p.empty()) load_file(p, ru_words_);
        // Встроенные частые слова (fallback)
        for (auto& w : {"и","в","не","на","он","что","как","а","то","все",
                         "она","так","его","но","да","ты","же","вы","за","бы",
                         "по","от","из","для","это","мы","они","был","быть"})
            ru_words_.insert(w);
        ru_loaded_ = true;
    }

    void load_en() {
        auto p = find_dict("english_dict.txt");
        if (!p.empty()) load_file(p, en_words_);
        for (auto& w : {"the","be","to","of","and","in","that","have","it","for",
                         "not","on","with","he","as","you","do","at","this","but",
                         "his","by","from","they","we","say","her","she","or","an",
                         "will","my","one","all","would","there","their","what","so",
                         "if","about","who","get","which","go","when","can","no"})
            en_words_.insert(w);
        en_loaded_ = true;
    }

public:
    const std::unordered_set<std::string>& ru() { if (!ru_loaded_) load_ru(); return ru_words_; }
    const std::unordered_set<std::string>& en() { if (!en_loaded_) load_en(); return en_words_; }
    const std::unordered_set<std::string>& words(const std::string& lang) {
        return lang == "ru" ? ru() : en();
    }
    size_t size() { return ru().size() + en().size(); }
};

static Dictionary g_dict;

// ============================================================================
// ДЕШИФРОВЩИК
// Сдвигает буквы указанного языка на заданный ключ.
// Буквы другого языка и знаки препинания остаются без изменений.
// ============================================================================

static std::string decrypt(const std::string& text, int shift, const std::string& lang) {
    auto cps = utf8_decode(text);
    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    auto idx_fn  = (lang == "ru") ? ru_index  : en_index;
    auto from_fn = (lang == "ru") ? ru_from_index : en_from_index;

    for (auto& cp : cps) {
        bool up = is_upper_cp(cp);
        int idx = idx_fn(to_lower(cp));
        if (idx < 0) continue; // не буква нужного языка — пропускаем
        int ni = ((idx - shift) % sz + sz) % sz; // сдвиг с защитой от отрицательного остатка
        cp = from_fn(ni);
        if (up) cp = to_upper(cp);
    }
    return utf8_encode(cps);
}

// ============================================================================
// ФУНКЦИИ ОЦЕНКИ (СКОРЕРЫ)
//
// ОПТИМИЗАЦИЯ: скореры принимают предвычисленные индексы букв,
// чтобы не декодировать UTF-8 повторно (экономия 5+ utf8_decode на сдвиг).
// ============================================================================

/// Извлекает индексы букв из предекодированных кодпоинтов
static std::vector<int> letter_indices(const std::vector<char32_t>& cps, const std::string& lang) {
    auto idx_fn = (lang == "ru") ? ru_index : en_index;
    std::vector<int> out;
    out.reserve(cps.size());
    for (auto cp : cps) {
        int i = idx_fn(to_lower(cp));
        if (i >= 0) out.push_back(i);
    }
    return out;
}

/// 1. Chi-squared тест: сравнение частот с эталоном. Меньше = лучше.
static double chi_squared(const std::vector<int>& idxs, const std::string& lang) {
    int n = (int)idxs.size();
    if (n == 0) return 1e9;

    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    const double* freq = (lang == "ru") ? RU_FREQ : EN_FREQ;

    std::vector<int> counts(sz, 0);
    for (int i : idxs) counts[i]++;

    double chi = 0;
    for (int i = 0; i < sz; ++i) {
        double expected = freq[i] * n;
        if (expected > 0) {
            double diff = counts[i] - expected;
            chi += diff * diff / expected;
        }
    }
    return chi;
}

/// 2. Биграммный анализ: доля распознанных пар букв
static double bigram_score(const std::vector<int>& idxs, const std::string& lang) {
    if ((int)idxs.size() < 4) return 0.0;

    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    const bool* table = (lang == "ru") ? RU_BG_TABLE : EN_BG_TABLE;

    int hits = 0, total = (int)idxs.size() - 1;
    for (int i = 0; i < total; ++i)
        if (table[idxs[i] * sz + idxs[i + 1]]) ++hits;

    return (double)hits / total;
}

/// 3. Index of Coincidence (IC): RU≈0.0553, EN≈0.0667, случайный≈0.03
static double index_of_coincidence(const std::vector<int>& idxs, const std::string& lang) {
    int n = (int)idxs.size();
    if (n < 2) return 0.0;

    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    std::vector<int> counts(sz, 0);
    for (int i : idxs) counts[i]++;

    double ic = 0;
    for (int i = 0; i < sz; ++i) ic += (double)counts[i] * (counts[i] - 1);
    return ic / ((double)n * (n - 1));
}

/// Извлекает слова из кодпоинтов (≥2 буквы нужного языка)
static std::vector<std::string> extract_words(const std::vector<char32_t>& cps, const std::string& lang) {
    auto is_letter = (lang == "ru") ? is_ru : is_en;
    std::vector<std::string> words;
    std::vector<char32_t> cur;

    for (auto cp : cps) {
        if (is_letter(cp)) {
            cur.push_back(to_lower(cp));
        } else {
            if (cur.size() >= 2) words.push_back(utf8_encode(cur));
            cur.clear();
        }
    }
    if (cur.size() >= 2) words.push_back(utf8_encode(cur));
    return words;
}

/// Проверка: строка заканчивается на суффикс
static bool str_ends_with(const std::string& s, const std::string& suffix) {
    return s.size() >= suffix.size() &&
           s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0;
}

/// Нормализация ё→е для устойчивости к вариативному написанию
static std::string normalize_yo(const std::string& s) {
    auto cps = utf8_decode(s);
    for (auto& cp : cps) {
        if (cp == 0x0451) cp = 0x0435; // ё → е
        if (cp == 0x0401) cp = 0x0415; // Ё → Е
    }
    return utf8_encode(cps);
}

/// Лёгкий стемминг: отрезает первый подходящий суффикс
static std::string stem_word(const std::string& word, const std::string& lang) {
    const auto& suffixes = (lang == "ru") ? RU_SUFFIXES : EN_SUFFIXES;
    size_t min_base = (lang == "en") ? 2 : 3; // минимальная длина основы
    size_t wlen = utf8_charlen(word);

    for (auto& suf : suffixes) {
        size_t slen = utf8_charlen(suf);
        if (wlen > slen + min_base && str_ends_with(word, suf))
            return word.substr(0, word.size() - suf.size());
    }
    return word;
}

/// Результат словарного анализа
struct DictScoreResult { double score; int matches; int total; };

/// 4. Словарный анализ с 4-уровневым поиском:
///    1) Точное совпадение  2) Без ё  3) Стемминг  4) Стемминг+ё
static DictScoreResult dict_score(const std::vector<std::string>& words,
                                   const std::unordered_set<std::string>& dictionary,
                                   const std::string& lang) {
    if (words.empty()) return {0, 0, 0};

    int matches = 0;
    double match_w = 0, total_w = 0;

    for (auto& word : words) {
        size_t wlen = utf8_charlen(word);
        total_w += wlen;

        // Уровень 1: точное совпадение
        if (dictionary.count(word)) { matches++; match_w += wlen; continue; }

        // Уровень 2: замена ё→е (только RU)
        std::string no_yo = (lang == "ru") ? normalize_yo(word) : word;
        if (lang == "ru" && no_yo != word && dictionary.count(no_yo)) {
            matches++; match_w += wlen; continue;
        }

        // Уровень 3: стемминг
        auto st = stem_word(word, lang);
        if (st != word && dictionary.count(st)) { matches++; match_w += wlen * 0.8; continue; }

        // Уровень 4: стемминг + нормализация ё
        if (lang == "ru") {
            auto st2 = stem_word(no_yo, lang);
            if (st2 != no_yo && dictionary.count(st2)) { matches++; match_w += wlen * 0.7; continue; }
        }
    }

    double ratio = (double)matches / words.size();
    double weighted = (total_w > 0) ? match_w / total_w : 0;
    return {ratio * 0.5 + weighted * 0.5, matches, (int)words.size()};
}

/// 5. Агрессивный стемминг: обрезает по 1 символу, пока не найдёт корень в словаре
///    ОПТИМИЗАЦИЯ: работает с кодпоинтами, избегая decode→pop→encode в цикле
static double stem_dict_score(const std::vector<std::string>& words,
                               const std::unordered_set<std::string>& dictionary,
                               const std::string& lang) {
    if (words.empty()) return 0;

    int min_stem = (lang == "en") ? 2 : 3;
    int hits = 0;
    for (auto& word : words) {
        std::string w = (lang == "ru") ? normalize_yo(word) : word;
        auto st = stem_word(w, lang);
        // Работаем через кодпоинты — без повторного decode на каждой итерации
        auto cps = utf8_decode(st);
        while ((int)cps.size() >= min_stem) {
            std::string candidate = utf8_encode(cps);
            if (dictionary.count(candidate)) { hits++; break; }
            cps.pop_back(); // отрезаем последний символ
        }
    }
    return (double)hits / words.size();
}


// ============================================================================
// АНАЛИЗАТОР
// ============================================================================

/// Определяет язык текста по количеству RU/EN символов
static std::string detect_language(const std::string& text) {
    auto cps = utf8_decode(text);
    int ru = 0, en = 0;
    for (auto cp : cps) {
        if (is_ru(cp)) ru++;
        else if (is_en(cp)) en++;
    }
    return (ru > en) ? "ru" : "en";
}

/// Проверяет, содержит ли текст оба языка (>5% минорного)
static bool is_bilingual(const std::string& text) {
    auto cps = utf8_decode(text);
    int ru = 0, en = 0;
    for (auto cp : cps) {
        if (is_ru(cp)) ru++;
        else if (is_en(cp)) en++;
    }
    int total = ru + en;
    if (total == 0) return false;
    return (double)std::min(ru, en) / total > 0.05;
}

/// Считает количество букв нужного языка
static int letter_count(const std::vector<char32_t>& cps, const std::string& lang) {
    auto fn = (lang == "ru") ? is_ru : is_en;
    int n = 0;
    for (auto cp : cps) if (fn(cp)) n++;
    return n;
}

/// Адаптивная комбинация скоров в зависимости от длины текста
/// Длинный текст → chi² надёжен; короткий → биграммы и словарь важнее
static double combine_scores(double chi, double bg, double ds, double ss, int n_letters) {
    double chi_norm = std::max(0.0, 1.0 - chi / 500.0);
    double w_chi, w_bg, w_dict, w_stem;

    if      (n_letters >= 100) { w_chi=0.35; w_bg=0.10; w_dict=0.35; w_stem=0.20; }
    else if (n_letters >= 30)  { w_chi=0.20; w_bg=0.20; w_dict=0.35; w_stem=0.25; }
    else if (n_letters >= 10)  { w_chi=0.10; w_bg=0.30; w_dict=0.35; w_stem=0.25; }
    else                       { w_chi=0.05; w_bg=0.45; w_dict=0.30; w_stem=0.20; }

    return w_chi * chi_norm + w_bg * bg + w_dict * ds + w_stem * ss;
}

/// Полный анализ одного сдвига
/// ОПТИМИЗАЦИЯ: utf8_decode вызывается ОДИН раз, результат передаётся всем скорерам
static ShiftResult analyze_shift(const std::string& text, int shift, const std::string& lang) {
    std::string dec = decrypt(text, shift, lang);
    auto dec_cps = utf8_decode(dec);               // единственный decode!
    auto& dictionary = g_dict.words(lang);

    auto idxs = letter_indices(dec_cps, lang);     // индексы для chi²/биграмм/IC
    auto words = extract_words(dec_cps, lang);     // слова для словарного анализа

    double chi = chi_squared(idxs, lang);
    double bg  = bigram_score(idxs, lang);
    auto [ds, matches, total] = dict_score(words, dictionary, lang);
    double ss  = stem_dict_score(words, dictionary, lang);
    int lc = letter_count(dec_cps, lang);
    double combined = combine_scores(chi, bg, ds, ss, lc);

    return {shift, std::move(dec), chi, bg, ds, ss, combined, matches, total};
}

/// Перебирает все сдвиги, сортирует по убыванию уверенности
static std::vector<ShiftResult> crack(const std::string& text, const std::string& lang) {
    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    std::vector<ShiftResult> results;
    results.reserve(sz);
    for (int s = 0; s < sz; ++s)
        results.push_back(analyze_shift(text, s, lang));

    std::sort(results.begin(), results.end(),
              [](const ShiftResult& a, const ShiftResult& b) {
                  return a.combined > b.combined;
              });
    return results;
}

/// Проверяет, не является ли текст уже открытым (незашифрованным)
static bool is_plaintext(const std::string& text) {
    auto lang = detect_language(text);
    auto& dictionary = g_dict.words(lang);
    auto cps = utf8_decode(text);
    auto words = extract_words(cps, lang);
    auto [ds, matches, total] = dict_score(words, dictionary, lang);

    if (total > 0 && (double)matches / total >= 0.7) return true;

    auto idxs = letter_indices(cps, lang);
    if ((int)idxs.size() >= 30) {
        double ic = index_of_coincidence(idxs, lang);
        double ic_thresh = (lang == "ru") ? 0.045 : 0.055;
        return ic > ic_thresh && ds > 0.4;
    }
    return false;
}

// ============================================================================
// РАЗБИЕНИЕ ПО ЯЗЫКАМ
// Нейтральные символы (пробелы, цифры, знаки) приклеиваются к текущему языку.
// Граница ставится на ближайшем пробеле при смене языка.
// ============================================================================

static std::vector<LangSegment> split_by_language(const std::string& text) {
    if (text.empty()) return {};

    auto cps = utf8_decode(text);
    std::vector<LangSegment> segments;
    std::string cur_lang;
    int cur_start = 0;

    for (int i = 0; i < (int)cps.size(); ++i) {
        std::string det;
        if (is_ru(cps[i]))      det = "ru";
        else if (is_en(cps[i])) det = "en";
        else continue; // нейтральный символ — пропускаем

        if (cur_lang.empty()) {
            cur_lang = det;
        } else if (det != cur_lang) {
            // Смена языка — ищем ближайший пробел назад для границы слова
            int split_at = i;
            for (int j = i - 1; j >= std::max(i - 10, cur_start); --j) {
                if (cps[j] == ' ' || cps[j] == '\n' || cps[j] == '\t') {
                    split_at = j + 1;
                    break;
                }
            }
            if (split_at > cur_start) {
                std::vector<char32_t> seg_cps(cps.begin() + cur_start, cps.begin() + split_at);
                segments.push_back({utf8_encode(seg_cps), cur_lang, cur_start, split_at});
            }
            cur_start = split_at;
            cur_lang = det;
        }
    }

    // Последний сегмент
    if (cur_start < (int)cps.size() && !cur_lang.empty()) {
        std::vector<char32_t> seg_cps(cps.begin() + cur_start, cps.end());
        segments.push_back({utf8_encode(seg_cps), cur_lang, cur_start, (int)cps.size()});
    }

    if (segments.empty())
        segments.push_back({text, "ru", 0, (int)cps.size()});

    return segments;
}

// ============================================================================
// ДЕТЕКТОР СМЕШАННЫХ ШИФРОВ
// Скользящее окно определяет оптимальный ключ для каждой позиции.
// Сглаживание мажоритарным голосованием убирает шум.
// Мелкие сегменты (<15 символов) сливаются с соседями.
// ============================================================================

static constexpr int WINDOW_SIZE = 40;

/// Для каждого символа определяет оптимальный ключ через скользящее окно
static std::vector<int> compute_shift_map(const std::string& text, const std::string& lang) {
    auto cps = utf8_decode(text);
    int n = (int)cps.size();
    int alpha_size = (lang == "ru") ? RU_SIZE : EN_SIZE;
    auto is_letter = (lang == "ru") ? is_ru : is_en;
    int half_w = WINDOW_SIZE / 2;
    std::vector<int> smap;
    smap.reserve(n);

    for (int i = 0; i < n; ++i) {
        if (!is_letter(cps[i])) {
            smap.push_back(smap.empty() ? 0 : smap.back());
            continue;
        }
        // Вырезаем окно вокруг позиции
        int start = std::max(0, i - half_w);
        int end_  = std::min(n, i + half_w);
        std::vector<char32_t> win(cps.begin() + start, cps.begin() + end_);
        std::string win_str = utf8_encode(win);

        // Перебираем все ключи, выбираем лучший по chi² + биграммам
        int best_s = 0; double best_sc = -1;
        for (int s = 0; s < alpha_size; ++s) {
            std::string dec = decrypt(win_str, s, lang);
            auto dec_cps = utf8_decode(dec);
            auto idxs = letter_indices(dec_cps, lang);
            double chi = chi_squared(idxs, lang);
            double bg = bigram_score(idxs, lang);
            double sc = bg * 0.6 + std::max(0.0, 1.0 - chi / 500.0) * 0.4;
            if (sc > best_sc) { best_sc = sc; best_s = s; }
        }
        smap.push_back(best_s);
    }
    return smap;
}

/// Находит границы сегментов по карте сдвигов (сглаживание + слияние мелких)
static std::vector<std::pair<int,int>> find_boundaries(const std::vector<int>& smap, int text_len) {
    int n = (int)smap.size();
    if (n == 0) return {{0, text_len}};

    // Сглаживание: для каждой позиции берём моду окрестности (±7)
    std::vector<int> smoothed(n);
    for (int i = 0; i < n; ++i) {
        int start = std::max(0, i - 7);
        int end_  = std::min(n, i + 8);
        std::unordered_map<int, int> cnt;
        for (int j = start; j < end_; ++j) cnt[smap[j]]++;
        int mode = smap[i]; int mode_cnt = 0;
        for (auto& [k, v] : cnt) if (v > mode_cnt) { mode = k; mode_cnt = v; }
        smoothed[i] = mode;
    }

    // Находим точки смены ключа
    std::vector<std::pair<int,int>> bounds;
    int seg_start = 0;
    int cur = smoothed[0];
    for (int i = 1; i < n; ++i) {
        if (smoothed[i] != cur) {
            bounds.push_back({seg_start, i});
            seg_start = i;
            cur = smoothed[i];
        }
    }
    bounds.push_back({seg_start, n});

    // Сливаем слишком маленькие сегменты (<15 символов) с предыдущим
    std::vector<std::pair<int,int>> merged;
    for (auto [s, e] : bounds) {
        if (e - s < 15 && !merged.empty())
            merged.back().second = e;
        else
            merged.push_back({s, e});
    }
    if (merged.empty()) return {{0, text_len}};
    return merged;
}

/// Детектирует смешанный шифр: разбивает текст на сегменты с разными ключами
static std::vector<Segment> detect_mixed(const std::string& text) {
    auto lang = detect_language(text);
    auto cps = utf8_decode(text);
    int lc = letter_count(cps, lang);

    // Слишком короткий текст — не разбиваем
    if (lc < WINDOW_SIZE * 2) {
        auto results = crack(text, lang);
        return {{results[0].text, 0, (int)text.size(), results[0]}};
    }

    auto smap = compute_shift_map(text, lang);
    auto bounds = find_boundaries(smap, (int)cps.size());

    std::vector<Segment> segments;
    for (auto [s, e] : bounds) {
        std::vector<char32_t> seg_cps(cps.begin() + s,
                                       cps.begin() + std::min(e, (int)cps.size()));
        std::string seg_text = utf8_encode(seg_cps);
        auto results = crack(seg_text, lang);
        segments.push_back({results[0].text, s, e, results[0]});
    }
    return segments;
}


// ============================================================================
// ИНТЕРФЕЙС КОМАНДНОЙ СТРОКИ
// ============================================================================

/// Аргументы командной строки
struct Args {
    std::vector<std::string> text_parts;
    bool raw = false;      // -r: только расшифрованный текст
    bool mixed = false;    // -m: принудительная проверка смешанного шифра
    std::string lang;      // -l: принудительный язык ("ru"/"en"), "" = авто
    bool help = false;
};

static Args parse_args(int argc, char* argv[]) {
    Args args;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "-r" || a == "--raw")       args.raw = true;
        else if (a == "-m" || a == "--mixed") args.mixed = true;
        else if (a == "-l" || a == "--lang") {
            if (i + 1 < argc) args.lang = argv[++i];
        }
        else if (a == "-h" || a == "--help") args.help = true;
        else if (!a.empty() && a[0] != '-')  args.text_parts.push_back(a);
    }
    return args;
}

static void print_help() {
    std::cout
        << "Caesar Cipher Cracker — C++ Edition\n\n"
        << "Использование: caesar [ОПЦИИ] [ТЕКСТ...]\n\n"
        << "Опции:\n"
        << "  -r, --raw        Вывести только расшифрованный текст\n"
        << "  -m, --mixed      Принудительно проверить смешанный шифр\n"
        << "  -l, --lang LANG  Принудительно задать язык: ru или en\n"
        << "  -h, --help       Показать эту справку\n\n"
        << "Примеры:\n"
        << "  caesar \"Фхнжйч снх\"\n"
        << "  echo \"Khoor\" | caesar -r\n"
        << "  caesar -l en \"Khoor zruog\"\n";
}

// ============================================================================
// ФУНКЦИИ ВЫВОДА
// ============================================================================

/// Форматирование числа с разделителями тысяч: 6933944 → "6,933,944"
static std::string format_num(size_t n) {
    std::string s = std::to_string(n);
    for (int i = (int)s.size() - 3; i > 0; i -= 3)
        s.insert(i, ",");
    return s;
}

/// Обрезает текст до max_chars символов, добавляя "…"
static std::string truncate(const std::string& text, size_t max_chars) {
    auto cps = utf8_decode(text);
    if (cps.size() <= max_chars) return text;
    cps.resize(max_chars);
    return utf8_encode(cps) + "…";
}

static void print_header() {
    std::cout << bold_cyan("╔══════════════════════════════════════════════════════════════╗") << "\n"
              << bold_cyan("║") << " " << bold_cyan("CAESAR CRACKER — C++ EDITION") << "                                " << bold_cyan("║") << "\n"
              << bold_cyan("║") << " " << dim("Chi² • Биграммы • Стемминг • Смешанные шифры") << "              " << bold_cyan("║") << "\n"
              << bold_cyan("╚══════════════════════════════════════════════════════════════╝") << "\n\n";
}

static void print_info(size_t dict_size, bool plain, const std::string& lang_name) {
    std::string status = plain
        ? green("✓ Текст открытый")
        : yellow("🔐 Текст зашифрован");
    std::cout << dim("📖 Словарь: ") << bold(format_num(dict_size)) << dim(" слов") << "\n"
              << dim("🌐 Язык: ") << bold(lang_name) << "\n"
              << dim("📊 Статус: ") << status << "\n\n";
}

/// Вывод основного результата + топ-5 альтернатив
static void print_result(const ShiftResult& best, const std::vector<ShiftResult>& top5) {
    std::cout << "\n" << bold_green("💬 РАСШИФРОВАННЫЙ ТЕКСТ:") << "\n\n"
              << best.text << "\n\n";

    // Метрики (строим через string, чтобы избежать переполнения snprintf)
    std::cout << dim("🔑 Ключ: " + std::to_string(best.shift)
        + "  📊 " + conf_colored(best.confidence())
        + "  📖 " + std::to_string(best.matches) + "/" + std::to_string(best.total_words) + " слов"
        + "  Chi²=" + std::to_string((int)best.chi_sq)
        + "  Бигр.: " + std::to_string((int)(best.bigram_sc * 100)) + "%"
        + "  Слов.: " + std::to_string((int)(best.dict_sc * 100)) + "%"
        + "  Стем.: " + std::to_string((int)(best.stem_sc * 100)) + "%") << "\n\n";

    std::cout << bold("Альтернативы:") << "\n";
    for (int i = 0; i < (int)top5.size() && i < 5; ++i) {
        auto& r = top5[i];
        std::string mark = (i == 0) ? "⭐" : " " + std::to_string(i + 1);
        std::cout << "  " << mark << "  ключ=" << r.shift
                  << " " << conf_colored(r.confidence())
                  << "  " << truncate(r.text, 60) << "\n";
    }
    std::cout << "\n";
}

/// Вывод результата для смешанного шифра
static void print_mixed(const std::vector<Segment>& segments) {
    std::unordered_set<int> keys;
    for (auto& s : segments) keys.insert(s.best.shift);
    std::string full;
    for (auto& s : segments) full += s.text;

    if (keys.size() > 1)
        std::cout << "\n" << bold_yellow("⚠️  СМЕШАННЫЙ ШИФР: "
            + std::to_string(keys.size()) + " разных ключей") << "\n\n";

    std::cout << bold("Сегменты:") << "\n";
    for (int i = 0; i < (int)segments.size(); ++i) {
        auto& r = segments[i].best;
        std::cout << "  " << (i+1) << ". ключ=" << r.shift
                  << " " << conf_colored(r.confidence())
                  << "  " << r.matches << "/" << r.total_words << " слов"
                  << "  " << truncate(segments[i].text, 50) << "\n";
    }
    std::cout << "\n" << bold_green("💬 ПОЛНЫЙ ТЕКСТ:") << "\n\n" << full << "\n\n";
}

/// Вывод результата для двуязычного текста
static void print_bilingual(const std::vector<std::pair<LangSegment, ShiftResult>>& parts) {
    std::string full;
    for (auto& [ls, r] : parts) full += r.text;

    std::cout << "\n" << bold_green("💬 РАСШИФРОВАННЫЙ ТЕКСТ:") << "\n\n"
              << full << "\n\n";

    for (auto& [ls, r] : parts) {
        std::string tag = (ls.lang == "ru") ? "RU" : "EN";
        std::cout << dim("  [" + tag + "] ключ=" + std::to_string(r.shift)
            + "  " + conf_colored(r.confidence())
            + "  " + std::to_string(r.matches) + "/" + std::to_string(r.total_words) + " слов") << "\n";
    }
    std::cout << "\n";
}

/// Многострочный ввод: пустая строка = конец
static std::string read_multiline() {
    std::cout << bold_yellow("Введите зашифрованный текст:") << "\n"
              << dim("(пустая строка = конец ввода)") << "\n";
    std::string result, line;
    while (std::getline(std::cin, line)) {
        if (line.empty()) break;
        if (!result.empty()) result += "\n";
        result += line;
    }
    return result;
}

// ============================================================================
// ГЛАВНАЯ ФУНКЦИЯ
// ============================================================================

int main(int argc, char* argv[]) {
    // Определяем директорию исполняемого файла (для поиска словарей)
    if (argc > 0) {
        std::error_code ec;
        auto p = fs::weakly_canonical(argv[0], ec);
        g_exe_dir = p.parent_path();
    }
    if (g_exe_dir.empty()) g_exe_dir = fs::current_path();

    init_bigrams(); // заполняем таблицы биграмм

    auto args = parse_args(argc, argv);
    if (args.help) { print_help(); return 0; }

    bool raw = args.raw;
    g_color = !raw && isatty(fileno(stdout)); // цвета только в терминале

    // --- Получение текста ---
    std::string text;
    bool is_auto = true; // true = текст из аргументов/pipe, false = интерактив

    if (!args.text_parts.empty()) {
        // Текст из аргументов командной строки
        for (size_t i = 0; i < args.text_parts.size(); ++i) {
            if (i > 0) text += " ";
            text += args.text_parts[i];
        }
    } else if (!isatty(fileno(stdin))) {
        // Текст из pipe (stdin)
        std::ostringstream ss;
        ss << std::cin.rdbuf();
        text = ss.str();
        while (!text.empty() && (text.back() == '\n' || text.back() == '\r' || text.back() == ' '))
            text.pop_back();
    } else {
        // Интерактивный режим
        if (raw) {
            std::cerr << "Ошибка: в режиме --raw нужно передать текст аргументом или через pipe\n";
            return 1;
        }
        is_auto = false;
        print_header();
        text = read_multiline();
    }

    if (text.empty()) return 0;

    // --- Определение режима ---
    std::string forced_lang = args.lang;
    bool bilingual = forced_lang.empty() && is_bilingual(text);

    if (!raw && is_auto) print_header();

    // --- Двуязычный режим ---
    if (bilingual) {
        auto lang_segs = split_by_language(text);
        std::vector<std::pair<LangSegment, ShiftResult>> parts;
        for (auto& ls : lang_segs) {
            auto results = crack(ls.text, ls.lang);
            parts.push_back({ls, results[0]});
        }

        if (raw) {
            for (auto& [ls, r] : parts) std::cout << r.text;
            std::cout << "\n";
            return 0;
        }

        std::unordered_set<std::string> langs;
        for (auto& ls : lang_segs) langs.insert(ls.lang);
        std::string lang_name = (langs.size() > 1) ? "Russian + English"
                              : (langs.count("ru") ? "Русский" : "English");
        print_info(g_dict.size(), false, lang_name);
        print_bilingual(parts);
        return 0;
    }

    // --- Одноязычный режим ---
    std::string lang = forced_lang.empty() ? detect_language(text) : forced_lang;

    // Режим --raw: только текст, без оформления
    if (raw) {
        auto results = crack(text, lang);
        auto& best = results[0];
        // При низкой уверенности проверяем смешанный шифр
        if (best.confidence() < 60 && (int)text.size() > 60) {
            auto segments = detect_mixed(text);
            std::unordered_set<int> keys;
            for (auto& s : segments) keys.insert(s.best.shift);
            if (keys.size() > 1) {
                for (auto& s : segments) std::cout << s.text;
                std::cout << "\n";
                return 0;
            }
        }
        std::cout << best.text << "\n";
        return 0;
    }

    // Интерактивный/автоматический режим с оформлением
    std::string lang_name = (lang == "ru") ? "Русский" : "English";
    bool plain = is_plaintext(text);
    print_info(g_dict.size(), plain, lang_name);

    if (plain) {
        if (is_auto) {
            // В авто-режиме показываем результат даже для открытого текста
            auto results = crack(text, lang);
            print_result(results[0], {results.begin(), results.begin() + std::min((int)results.size(), 5)});
            return 0;
        } else {
            // В интерактиве спрашиваем
            std::cout << yellow("Текст похож на незашифрованный. Продолжить? (y/n): ");
            std::string ans;
            std::getline(std::cin, ans);
            if (ans.empty() || (ans[0] != 'y' && ans[0] != 'Y' && ans[0] != 'd')) return 0;
        }
    }

    auto results = crack(text, lang);
    auto& best = results[0];

    // При низкой уверенности или --mixed проверяем смешанный шифр
    if (args.mixed || (best.confidence() < 60 && (int)text.size() > 60)) {
        auto segments = detect_mixed(text);
        std::unordered_set<int> keys;
        for (auto& s : segments) keys.insert(s.best.shift);
        if (keys.size() > 1) {
            print_mixed(segments);
            return 0;
        }
    }

    print_result(best, {results.begin(), results.begin() + std::min((int)results.size(), 5)});
    return 0;
}
