#!/bin/bash
# Скачивание словарей из Wiktionary
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"

echo "📖 Скачивание русского словаря..."
if [ ! -f "$DIR/russian_dict.txt" ]; then
    curl -L "https://kaikki.org/dictionary/Russian/kaikki.org-dictionary-Russian.json" \
        | python3 -c "
import sys, json
for line in sys.stdin:
    try:
        w = json.loads(line).get('word','')
        if w and w.isalpha():
            print(w)
    except: pass
" > "$DIR/russian_dict.txt"
    echo "  ✅ $(wc -l < "$DIR/russian_dict.txt" | tr -d ' ') слов"
else
    echo "  ⏭️  Уже существует ($(wc -l < "$DIR/russian_dict.txt" | tr -d ' ') слов)"
fi

echo "📖 Скачивание английского словаря..."
if [ ! -f "$DIR/english_dict.txt" ]; then
    curl -L "https://kaikki.org/dictionary/English/kaikki.org-dictionary-English.json" \
        | python3 -c "
import sys, json
for line in sys.stdin:
    try:
        w = json.loads(line).get('word','')
        if w and w.isalpha():
            print(w)
    except: pass
" > "$DIR/english_dict.txt"
    echo "  ✅ $(wc -l < "$DIR/english_dict.txt" | tr -d ' ') слов"
else
    echo "  ⏭️  Уже существует ($(wc -l < "$DIR/english_dict.txt" | tr -d ' ') слов)"
fi

echo ""
echo "✅ Готово! Словари сохранены в $DIR/"
