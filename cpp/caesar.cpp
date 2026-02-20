// ============================================================================
// CAESAR CIPHER CRACKER — C++ EDITION
// ============================================================================
// Full port of the Python implementation with all 6 analysis layers:
//   1. Chi-squared frequency analysis
//   2. Bigram analysis
//   3. Index of Coincidence
//   4. Dictionary analysis with morphological stemming
//   5. Sliding window for mixed ciphers
//   6. Adaptive weights based on text length
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
#include <functional>
#include <cassert>
#include <unistd.h>

namespace fs = std::filesystem;

// ============================================================================
// UTF-8 UTILITIES
// ============================================================================

static std::vector<char32_t> utf8_decode(const std::string& s) {
    std::vector<char32_t> out;
    out.reserve(s.size());
    for (size_t i = 0; i < s.size(); ) {
        unsigned char c = s[i];
        char32_t cp;
        int len;
        if (c < 0x80)        { cp = c;                              len = 1; }
        else if ((c & 0xE0) == 0xC0) { cp = c & 0x1F;               len = 2; }
        else if ((c & 0xF0) == 0xE0) { cp = c & 0x0F;               len = 3; }
        else if ((c & 0xF8) == 0xF0) { cp = c & 0x07;               len = 4; }
        else { ++i; continue; }
        for (int j = 1; j < len && i + j < s.size(); ++j)
            cp = (cp << 6) | (s[i + j] & 0x3F);
        out.push_back(cp);
        i += len;
    }
    return out;
}

static std::string utf8_encode_cp(char32_t cp) {
    std::string r;
    if (cp < 0x80)        { r += (char)cp; }
    else if (cp < 0x800)  { r += (char)(0xC0|(cp>>6));   r += (char)(0x80|(cp&0x3F)); }
    else if (cp < 0x10000){ r += (char)(0xE0|(cp>>12));   r += (char)(0x80|((cp>>6)&0x3F)); r += (char)(0x80|(cp&0x3F)); }
    else                  { r += (char)(0xF0|(cp>>18));   r += (char)(0x80|((cp>>12)&0x3F)); r += (char)(0x80|((cp>>6)&0x3F)); r += (char)(0x80|(cp&0x3F)); }
    return r;
}

static std::string utf8_encode(const std::vector<char32_t>& cps) {
    std::string r;
    for (auto cp : cps) r += utf8_encode_cp(cp);
    return r;
}

static size_t utf8_charlen(const std::string& s) {
    size_t len = 0;
    for (size_t i = 0; i < s.size(); ) {
        unsigned char c = s[i];
        if (c < 0x80) i += 1;
        else if ((c & 0xE0) == 0xC0) i += 2;
        else if ((c & 0xF0) == 0xE0) i += 3;
        else i += 4;
        ++len;
    }
    return len;
}

// ============================================================================
// CHARACTER CLASSIFICATION (RU / EN)
// ============================================================================

static bool is_ru_lower(char32_t c) { return (c >= 0x0430 && c <= 0x044F) || c == 0x0451; }
static bool is_ru_upper(char32_t c) { return (c >= 0x0410 && c <= 0x042F) || c == 0x0401; }
static bool is_ru(char32_t c) { return is_ru_lower(c) || is_ru_upper(c); }
static bool is_en_lower(char32_t c) { return c >= 'a' && c <= 'z'; }
static bool is_en_upper(char32_t c) { return c >= 'A' && c <= 'Z'; }
static bool is_en(char32_t c) { return is_en_lower(c) || is_en_upper(c); }

static char32_t to_lower(char32_t c) {
    if (c == 0x0401) return 0x0451;
    if (c >= 0x0410 && c <= 0x042F) return c + 0x20;
    if (c >= 'A' && c <= 'Z') return c + 32;
    return c;
}
static char32_t to_upper(char32_t c) {
    if (c == 0x0451) return 0x0401;
    if (c >= 0x0430 && c <= 0x044F) return c - 0x20;
    if (c >= 'a' && c <= 'z') return c - 32;
    return c;
}

// Russian alphabet: а б в г д е ё ж з и й к л м н о п р с т у ф х ц ч ш щ ъ ы ь э ю я
// Indices:          0 1 2 3 4 5 6 7 8 9 ...                                          32
// Note: ё (U+0451) is at index 6, but out of sequence in Unicode

static constexpr int RU_SIZE = 33;
static constexpr int EN_SIZE = 26;

static int ru_index(char32_t c) {
    c = to_lower(c);
    if (c == 0x0451) return 6;                            // ё
    if (c >= 0x0430 && c <= 0x0435) return (int)(c - 0x0430);      // а-е → 0-5
    if (c >= 0x0436 && c <= 0x044F) return (int)(c - 0x0436) + 7;  // ж-я → 7-32
    return -1;
}

static char32_t ru_from_index(int idx) {
    if (idx == 6) return 0x0451;           // ё
    if (idx < 6)  return 0x0430 + idx;     // а-е
    return 0x0436 + (idx - 7);             // ж-я
}

static int en_index(char32_t c) {
    c = to_lower(c);
    if (c >= 'a' && c <= 'z') return (int)(c - 'a');
    return -1;
}

static char32_t en_from_index(int idx) { return 'a' + idx; }

static bool is_upper_cp(char32_t c) { return is_ru_upper(c) || is_en_upper(c); }


// ============================================================================
// ANSI COLOR UTILITIES
// ============================================================================

static bool g_color = true;

static std::string clr(const char* code, const std::string& s) {
    return g_color ? std::string("\033[") + code + "m" + s + "\033[0m" : s;
}
static std::string bold(const std::string& s)        { return clr("1", s); }
static std::string dim(const std::string& s)         { return clr("2", s); }
static std::string green(const std::string& s)       { return clr("32", s); }
static std::string yellow(const std::string& s)      { return clr("33", s); }
static std::string cyan(const std::string& s)        { return clr("36", s); }
static std::string bold_green(const std::string& s)  { return clr("1;32", s); }
static std::string bold_yellow(const std::string& s) { return clr("1;33", s); }
static std::string bold_cyan(const std::string& s)   { return clr("1;36", s); }
static std::string bold_red(const std::string& s)    { return clr("1;31", s); }

static std::string conf_colored(double conf) {
    char buf[16]; snprintf(buf, sizeof(buf), "%.1f%%", conf);
    if (conf >= 80) return bold_green(buf);
    if (conf >= 50) return yellow(buf);
    return bold_red(buf);
}

// ============================================================================
// LINGUISTIC CONSTANTS
// ============================================================================

// Letter frequencies (indexed by alphabet position)
// Russian: НКРЯ research data
static const double RU_FREQ[33] = {
    0.0801, 0.0159, 0.0454, 0.0170, 0.0298, // а б в г д
    0.0845, 0.0004, 0.0094, 0.0165, 0.0735, // е ё ж з и
    0.0121, 0.0349, 0.0440, 0.0321, 0.0670, // й к л м н
    0.1097, 0.0281, 0.0473, 0.0547, 0.0626, // о п р с т
    0.0262, 0.0026, 0.0097, 0.0048, 0.0144, // у ф х ц ч
    0.0073, 0.0036, 0.0004, 0.0190, 0.0174, // ш щ ъ ы ь
    0.0032, 0.0064, 0.0201,                  // э ю я
};

// English: Cornell data
static const double EN_FREQ[26] = {
    0.0817, 0.0129, 0.0278, 0.0425, 0.1270, // a b c d e
    0.0223, 0.0202, 0.0609, 0.0697, 0.0015, // f g h i j
    0.0077, 0.0403, 0.0241, 0.0675, 0.0751, // k l m n o
    0.0193, 0.0010, 0.0599, 0.0633, 0.0906, // p q r s t
    0.0276, 0.0098, 0.0236, 0.0015, 0.0197, // u v w x y
    0.0007,                                   // z
};

// Bigram lookup tables (flat bool arrays, idx = i1 * ALPHA_SIZE + i2)
static bool RU_BG_TABLE[33 * 33] = {};
static bool EN_BG_TABLE[26 * 26] = {};

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

static void init_bigrams() {
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

// Suffixes for stemming
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
// DATA STRUCTURES
// ============================================================================

struct ShiftResult {
    int shift = 0;
    std::string text;
    double chi_sq = 0;
    double bigram_sc = 0;
    double dict_sc = 0;
    double stem_sc = 0;
    double combined = 0;
    int matches = 0;
    int total_words = 0;
    double confidence() const { return std::min(combined * 100.0, 100.0); }
};

struct Segment {
    std::string text;
    int start = 0, end = 0;
    ShiftResult best;
};

struct LangSegment {
    std::string text;
    std::string lang; // "ru" or "en"
    int start = 0, end = 0;
};


// ============================================================================
// DICTIONARY
// ============================================================================

static fs::path g_exe_dir; // set from argv[0]

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

    void load_file(const fs::path& path, std::unordered_set<std::string>& dict) {
        std::ifstream f(path, std::ios::binary);
        if (!f.is_open()) return;
        std::string line;
        while (std::getline(f, line)) {
            // Trim
            while (!line.empty() && (line.back() == '\r' || line.back() == '\n' || line.back() == ' '))
                line.pop_back();
            if (line.empty()) continue;

            auto cps = utf8_decode(line);
            size_t clen = cps.size();
            if (clen < 2 || clen > 50) continue;

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
        // Built-in common words
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
    const std::unordered_set<std::string>& ru() {
        if (!ru_loaded_) load_ru();
        return ru_words_;
    }
    const std::unordered_set<std::string>& en() {
        if (!en_loaded_) load_en();
        return en_words_;
    }
    const std::unordered_set<std::string>& words(const std::string& lang) {
        return lang == "ru" ? ru() : en();
    }
    size_t size() { return ru().size() + en().size(); }
};

static Dictionary g_dict;

// ============================================================================
// DECRYPTOR
// ============================================================================

static std::string decrypt(const std::string& text, int shift, const std::string& lang) {
    auto cps = utf8_decode(text);
    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    auto idx_fn  = (lang == "ru") ? ru_index  : en_index;
    auto from_fn = (lang == "ru") ? ru_from_index : en_from_index;

    for (auto& cp : cps) {
        bool up = is_upper_cp(cp);
        int idx = idx_fn(to_lower(cp));
        if (idx < 0) continue;
        int ni = ((idx - shift) % sz + sz) % sz;
        cp = from_fn(ni);
        if (up) cp = to_upper(cp);
    }
    return utf8_encode(cps);
}

// ============================================================================
// SCORING FUNCTIONS
// ============================================================================

// Helpers: extract letter indices from text
static std::vector<int> letter_indices(const std::string& text, const std::string& lang) {
    auto cps = utf8_decode(text);
    auto idx_fn = (lang == "ru") ? ru_index : en_index;
    std::vector<int> out;
    out.reserve(cps.size());
    for (auto cp : cps) {
        int i = idx_fn(to_lower(cp));
        if (i >= 0) out.push_back(i);
    }
    return out;
}

// 1. Chi-squared
static double chi_squared(const std::string& text, const std::string& lang) {
    auto idxs = letter_indices(text, lang);
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

// 2. Bigram score
static double bigram_score(const std::string& text, const std::string& lang) {
    auto idxs = letter_indices(text, lang);
    if ((int)idxs.size() < 4) return 0.0;

    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    const bool* table = (lang == "ru") ? RU_BG_TABLE : EN_BG_TABLE;

    int hits = 0, total = (int)idxs.size() - 1;
    for (int i = 0; i < total; ++i)
        if (table[idxs[i] * sz + idxs[i + 1]]) ++hits;

    return (double)hits / total;
}

// 3. Index of Coincidence
static double index_of_coincidence(const std::string& text, const std::string& lang) {
    auto idxs = letter_indices(text, lang);
    int n = (int)idxs.size();
    if (n < 2) return 0.0;

    int sz = (lang == "ru") ? RU_SIZE : EN_SIZE;
    std::vector<int> counts(sz, 0);
    for (int i : idxs) counts[i]++;

    double ic = 0;
    for (int i = 0; i < sz; ++i) ic += (double)counts[i] * (counts[i] - 1);
    return ic / ((double)n * (n - 1));
}

// Extract words from text
static std::vector<std::string> extract_words(const std::string& text, const std::string& lang) {
    auto cps = utf8_decode(text);
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

// String ends_with helper
static bool str_ends_with(const std::string& s, const std::string& suffix) {
    return s.size() >= suffix.size() &&
           s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0;
}

// Normalize ё → е
static std::string normalize_yo(const std::string& s) {
    auto cps = utf8_decode(s);
    for (auto& cp : cps) {
        if (cp == 0x0451) cp = 0x0435; // ё → е
        if (cp == 0x0401) cp = 0x0415; // Ё → Е
    }
    return utf8_encode(cps);
}

// Stem word
static std::string stem_word(const std::string& word, const std::string& lang) {
    const auto& suffixes = (lang == "ru") ? RU_SUFFIXES : EN_SUFFIXES;
    size_t min_base = (lang == "en") ? 2 : 3;
    size_t wlen = utf8_charlen(word);

    for (auto& suf : suffixes) {
        size_t slen = utf8_charlen(suf);
        if (wlen > slen + min_base && str_ends_with(word, suf))
            return word.substr(0, word.size() - suf.size());
    }
    return word;
}

// 4. Dictionary score
struct DictScoreResult { double score; int matches; int total; };

static DictScoreResult dict_score(const std::string& text,
                                   const std::unordered_set<std::string>& dictionary,
                                   const std::string& lang) {
    auto words = extract_words(text, lang);
    if (words.empty()) return {0, 0, 0};

    int matches = 0;
    double match_w = 0, total_w = 0;

    for (auto& word : words) {
        size_t wlen = utf8_charlen(word);
        total_w += wlen;

        // 1. Exact match
        if (dictionary.count(word)) { matches++; match_w += wlen; continue; }

        // 2. Without ё (RU only)
        std::string no_yo = (lang == "ru") ? normalize_yo(word) : word;
        if (lang == "ru" && no_yo != word && dictionary.count(no_yo)) {
            matches++; match_w += wlen; continue;
        }

        // 3. Stemming
        auto st = stem_word(word, lang);
        if (st != word && dictionary.count(st)) { matches++; match_w += wlen * 0.8; continue; }

        // 4. Stem + normalize
        if (lang == "ru") {
            auto st2 = stem_word(no_yo, lang);
            if (st2 != no_yo && dictionary.count(st2)) { matches++; match_w += wlen * 0.7; continue; }
        }
    }

    double ratio = (double)matches / words.size();
    double weighted = (total_w > 0) ? match_w / total_w : 0;
    return {ratio * 0.5 + weighted * 0.5, matches, (int)words.size()};
}

// 5. Aggressive stemming score
static double stem_dict_score(const std::string& text,
                               const std::unordered_set<std::string>& dictionary,
                               const std::string& lang) {
    auto words = extract_words(text, lang);
    if (words.empty()) return 0;

    int min_stem = (lang == "en") ? 2 : 3;
    int hits = 0;
    for (auto& word : words) {
        std::string w = (lang == "ru") ? normalize_yo(word) : word;
        auto st = stem_word(w, lang);
        std::string candidate = st;
        while ((int)utf8_charlen(candidate) >= min_stem) {
            if (dictionary.count(candidate)) { hits++; break; }
            // Remove last char (UTF-8 aware)
            auto cps = utf8_decode(candidate);
            cps.pop_back();
            candidate = utf8_encode(cps);
        }
    }
    return (double)hits / words.size();
}


// ============================================================================
// ANALYZER
// ============================================================================

static std::string detect_language(const std::string& text) {
    auto cps = utf8_decode(text);
    int ru = 0, en = 0;
    for (auto cp : cps) {
        if (is_ru(cp)) ru++;
        else if (is_en(cp)) en++;
    }
    return (ru > en) ? "ru" : "en";
}

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

static int letter_count(const std::string& text, const std::string& lang) {
    auto cps = utf8_decode(text);
    auto fn = (lang == "ru") ? is_ru : is_en;
    int n = 0;
    for (auto cp : cps) if (fn(cp)) n++;
    return n;
}

static double combine_scores(double chi, double bg, double ds, double ss, int n_letters) {
    double chi_norm = std::max(0.0, 1.0 - chi / 500.0);
    double w_chi, w_bg, w_dict, w_stem;

    if (n_letters >= 100)      { w_chi=0.35; w_bg=0.10; w_dict=0.35; w_stem=0.20; }
    else if (n_letters >= 30)  { w_chi=0.20; w_bg=0.20; w_dict=0.35; w_stem=0.25; }
    else if (n_letters >= 10)  { w_chi=0.10; w_bg=0.30; w_dict=0.35; w_stem=0.25; }
    else                       { w_chi=0.05; w_bg=0.45; w_dict=0.30; w_stem=0.20; }

    return w_chi * chi_norm + w_bg * bg + w_dict * ds + w_stem * ss;
}

static ShiftResult analyze_shift(const std::string& text, int shift, const std::string& lang) {
    std::string dec = decrypt(text, shift, lang);
    auto& dictionary = g_dict.words(lang);

    double chi = chi_squared(dec, lang);
    double bg  = bigram_score(dec, lang);
    auto [ds, matches, total] = dict_score(dec, dictionary, lang);
    double ss  = stem_dict_score(dec, dictionary, lang);
    int lc = letter_count(text, lang);
    double combined = combine_scores(chi, bg, ds, ss, lc);

    return {shift, std::move(dec), chi, bg, ds, ss, combined, matches, total};
}

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

static bool is_plaintext(const std::string& text) {
    auto lang = detect_language(text);
    auto& dictionary = g_dict.words(lang);
    auto [ds, matches, total] = dict_score(text, dictionary, lang);

    if (total > 0 && (double)matches / total >= 0.7) return true;

    if (letter_count(text, lang) >= 30) {
        double ic = index_of_coincidence(text, lang);
        double ic_thresh = (lang == "ru") ? 0.045 : 0.055;
        return ic > ic_thresh && ds > 0.4;
    }
    return false;
}

// ============================================================================
// LANGUAGE SPLITTING
// ============================================================================

static std::vector<LangSegment> split_by_language(const std::string& text) {
    if (text.empty()) return {};

    auto cps = utf8_decode(text);
    std::vector<LangSegment> segments;
    std::string cur_lang;
    int cur_start = 0;

    // We work in codepoint indices, then convert back
    for (int i = 0; i < (int)cps.size(); ++i) {
        std::string det;
        if (is_ru(cps[i]))      det = "ru";
        else if (is_en(cps[i])) det = "en";
        else continue; // neutral

        if (cur_lang.empty()) {
            cur_lang = det;
        } else if (det != cur_lang) {
            // Find word boundary
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

    // Last segment
    if (cur_start < (int)cps.size() && !cur_lang.empty()) {
        std::vector<char32_t> seg_cps(cps.begin() + cur_start, cps.end());
        segments.push_back({utf8_encode(seg_cps), cur_lang, cur_start, (int)cps.size()});
    }

    if (segments.empty())
        segments.push_back({text, "ru", 0, (int)cps.size()});

    return segments;
}

// ============================================================================
// MIXED CIPHER DETECTOR
// ============================================================================

static constexpr int WINDOW_SIZE = 40;

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
        int start = std::max(0, i - half_w);
        int end_  = std::min(n, i + half_w);
        std::vector<char32_t> win(cps.begin() + start, cps.begin() + end_);
        std::string win_str = utf8_encode(win);

        int best_s = 0; double best_sc = -1;
        for (int s = 0; s < alpha_size; ++s) {
            std::string dec = decrypt(win_str, s, lang);
            double chi = chi_squared(dec, lang);
            double bg = bigram_score(dec, lang);
            double sc = bg * 0.6 + std::max(0.0, 1.0 - chi / 500.0) * 0.4;
            if (sc > best_sc) { best_sc = sc; best_s = s; }
        }
        smap.push_back(best_s);
    }
    return smap;
}

static std::vector<std::pair<int,int>> find_boundaries(const std::vector<int>& smap, int text_len) {
    int n = (int)smap.size();
    if (n == 0) return {{0, text_len}};

    // Smoothing
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

    // Find change points
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

    // Merge small segments
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

static std::vector<Segment> detect_mixed(const std::string& text) {
    auto lang = detect_language(text);
    int lc = letter_count(text, lang);

    if (lc < WINDOW_SIZE * 2) {
        auto results = crack(text, lang);
        return {{results[0].text, 0, (int)text.size(), results[0]}};
    }

    auto smap = compute_shift_map(text, lang);
    auto bounds = find_boundaries(smap, (int)text.size());

    auto cps = utf8_decode(text);
    std::vector<Segment> segments;
    for (auto [s, e] : bounds) {
        std::vector<char32_t> seg_cps(cps.begin() + s, cps.begin() + std::min(e, (int)cps.size()));
        std::string seg_text = utf8_encode(seg_cps);
        auto results = crack(seg_text, lang);
        segments.push_back({results[0].text, s, e, results[0]});
    }
    return segments;
}


// ============================================================================
// CLI & OUTPUT
// ============================================================================

struct Args {
    std::vector<std::string> text_parts;
    bool raw = false;
    bool mixed = false;
    std::string lang; // "" = auto
    bool help = false;
};

static Args parse_args(int argc, char* argv[]) {
    Args args;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "-r" || a == "--raw") args.raw = true;
        else if (a == "-m" || a == "--mixed") args.mixed = true;
        else if (a == "-l" || a == "--lang") {
            if (i + 1 < argc) args.lang = argv[++i];
        }
        else if (a == "-h" || a == "--help") args.help = true;
        else if (a[0] != '-') args.text_parts.push_back(a);
    }
    return args;
}

static void print_help() {
    std::cout << "Caesar Cipher Cracker — C++ Edition\n\n"
              << "Usage: caesar [OPTIONS] [TEXT...]\n\n"
              << "Options:\n"
              << "  -r, --raw        Output decrypted text only\n"
              << "  -m, --mixed      Force mixed cipher check\n"
              << "  -l, --lang LANG  Force language: ru or en\n"
              << "  -h, --help       Show this help\n\n"
              << "Examples:\n"
              << "  caesar \"Фхнжйч снх\"\n"
              << "  echo \"Khoor\" | caesar -r\n"
              << "  caesar -l en \"Khoor zruog\"\n";
}

static std::string format_num(size_t n) {
    std::string s = std::to_string(n);
    for (int i = (int)s.size() - 3; i > 0; i -= 3)
        s.insert(i, ",");
    return s;
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

static void print_result(const ShiftResult& best, const std::vector<ShiftResult>& top5) {
    std::cout << "\n" << bold_green("💬 РАСШИФРОВАННЫЙ ТЕКСТ:") << "\n\n"
              << best.text << "\n\n";

    char buf[256];
    snprintf(buf, sizeof(buf),
             "🔑 Ключ: %d  📊 %s  📖 %d/%d слов  Chi²=%.0f  Бигр.: %.0f%%  Слов.: %.0f%%  Стем.: %.0f%%",
             best.shift, conf_colored(best.confidence()).c_str(),
             best.matches, best.total_words,
             best.chi_sq, best.bigram_sc * 100, best.dict_sc * 100, best.stem_sc * 100);
    std::cout << dim(buf) << "\n\n";

    std::cout << bold("Альтернативы:") << "\n";
    for (int i = 0; i < (int)top5.size() && i < 5; ++i) {
        auto& r = top5[i];
        std::string mark = (i == 0) ? "⭐" : " " + std::to_string(i + 1);
        std::string preview = r.text;
        auto pcps = utf8_decode(preview);
        if (pcps.size() > 60) {
            pcps.resize(60);
            preview = utf8_encode(pcps) + "…";
        }
        char line[256];
        snprintf(line, sizeof(line), "  %s  ключ=%-2d %s  %s",
                 mark.c_str(), r.shift, conf_colored(r.confidence()).c_str(), preview.c_str());
        std::cout << line << "\n";
    }
    std::cout << "\n";
}

static void print_mixed(const std::vector<Segment>& segments) {
    std::unordered_set<int> keys;
    for (auto& s : segments) keys.insert(s.best.shift);
    bool is_mixed = keys.size() > 1;
    std::string full;
    for (auto& s : segments) full += s.text;

    if (is_mixed) {
        std::cout << "\n" << bold_yellow("⚠️  СМЕШАННЫЙ ШИФР: " + std::to_string(keys.size()) + " разных ключей") << "\n\n";
    }

    std::cout << bold("Сегменты:") << "\n";
    for (int i = 0; i < (int)segments.size(); ++i) {
        auto& seg = segments[i];
        auto& r = seg.best;
        std::string preview = seg.text;
        auto pcps = utf8_decode(preview);
        if (pcps.size() > 50) {
            pcps.resize(50);
            preview = utf8_encode(pcps) + "…";
        }
        char line[256];
        snprintf(line, sizeof(line), "  %d. ключ=%-2d %s  %d/%d слов  %s",
                 i + 1, r.shift, conf_colored(r.confidence()).c_str(),
                 r.matches, r.total_words, preview.c_str());
        std::cout << line << "\n";
    }

    std::cout << "\n" << bold_green("💬 ПОЛНЫЙ ТЕКСТ:") << "\n\n" << full << "\n\n";
}

static void print_bilingual(const std::vector<std::pair<LangSegment, ShiftResult>>& parts) {
    std::string full;
    for (auto& [ls, r] : parts) full += r.text;

    std::cout << "\n" << bold_green("💬 РАСШИФРОВАННЫЙ ТЕКСТ:") << "\n\n"
              << full << "\n\n";

    for (auto& [ls, r] : parts) {
        std::string tag = (ls.lang == "ru") ? "RU" : "EN";
        char line[128];
        snprintf(line, sizeof(line), "  [%s] ключ=%d  %s  %d/%d слов",
                 tag.c_str(), r.shift, conf_colored(r.confidence()).c_str(),
                 r.matches, r.total_words);
        std::cout << dim(line) << "\n";
    }
    std::cout << "\n";
}

// Read multiline input (empty line = end)
static std::string read_multiline() {
    std::cout << bold_yellow("Введите зашифрованный текст:") << "\n"
              << dim("(пустая строка = конец ввода)") << "\n";
    std::string result;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.empty()) break;
        if (!result.empty()) result += "\n";
        result += line;
    }
    return result;
}

// ============================================================================
// MAIN
// ============================================================================

int main(int argc, char* argv[]) {
    // Determine exe directory for dictionary lookup
    if (argc > 0) {
        std::error_code ec;
        auto p = fs::weakly_canonical(argv[0], ec);
        g_exe_dir = p.parent_path();
    }
    if (g_exe_dir.empty()) g_exe_dir = fs::current_path();

    init_bigrams();

    auto args = parse_args(argc, argv);
    if (args.help) { print_help(); return 0; }

    bool raw = args.raw;
    g_color = !raw && isatty(fileno(stdout));

    // Get input text
    std::string text;
    bool is_auto = true;

    if (!args.text_parts.empty()) {
        for (size_t i = 0; i < args.text_parts.size(); ++i) {
            if (i > 0) text += " ";
            text += args.text_parts[i];
        }
    } else if (!isatty(fileno(stdin))) {
        std::ostringstream ss;
        ss << std::cin.rdbuf();
        text = ss.str();
        // Trim trailing whitespace
        while (!text.empty() && (text.back() == '\n' || text.back() == '\r' || text.back() == ' '))
            text.pop_back();
    } else {
        if (raw) {
            std::cerr << "Ошибка: в режиме --raw нужно передать текст аргументом или через pipe\n";
            return 1;
        }
        is_auto = false;
        print_header();
        text = read_multiline();
    }

    if (text.empty()) return 0;

    std::string forced_lang = args.lang;
    bool bilingual = forced_lang.empty() && is_bilingual(text);

    // Create UI for non-raw auto mode
    if (!raw && is_auto) print_header();

    if (bilingual) {
        // Bilingual mode
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

        // Determine language display name
        std::unordered_set<std::string> langs;
        for (auto& ls : lang_segs) langs.insert(ls.lang);
        std::string lang_name = (langs.size() > 1) ? "Russian + English"
                              : (langs.count("ru") ? "Русский" : "English");
        print_info(g_dict.size(), false, lang_name);
        print_bilingual(parts);

    } else {
        // Single-language mode
        std::string lang = forced_lang.empty() ? detect_language(text) : forced_lang;

        if (raw) {
            auto results = crack(text, lang);
            auto& best = results[0];
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

        std::string lang_name = (lang == "ru") ? "Русский" : "English";
        bool plain = is_plaintext(text);
        print_info(g_dict.size(), plain, lang_name);

        if (plain) {
            if (is_auto) {
                auto results = crack(text, lang);
                print_result(results[0], {results.begin(), results.begin() + std::min((int)results.size(), 5)});
                return 0;
            } else {
                std::cout << yellow("Текст похож на незашифрованный. Продолжить? (y/n): ");
                std::string ans;
                std::getline(std::cin, ans);
                if (ans.empty() || (ans[0] != 'y' && ans[0] != 'Y' && ans[0] != 'd')) return 0;
            }
        }

        auto results = crack(text, lang);
        auto& best = results[0];

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
    }

    return 0;
}
