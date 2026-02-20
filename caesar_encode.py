#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Шифровальщик текста шифром Цезаря"""

import sys

RU_ALPHABET = 'абвгдеёжзийклмнопрстуфхцчшщъыьэюя'
EN_ALPHABET = 'abcdefghijklmnopqrstuvwxyz'


def caesar_encrypt(text: str, shift: int) -> str:
    """Шифрует текст шифром Цезаря"""
    result = []
    
    for char in text:
        if char.lower() in RU_ALPHABET:
            is_upper = char.isupper()
            idx = RU_ALPHABET.index(char.lower())
            new_idx = (idx + shift) % len(RU_ALPHABET)
            new_char = RU_ALPHABET[new_idx]
            result.append(new_char.upper() if is_upper else new_char)
        elif char.lower() in EN_ALPHABET:
            is_upper = char.isupper()
            idx = EN_ALPHABET.index(char.lower())
            new_idx = (idx + shift) % len(EN_ALPHABET)
            new_char = EN_ALPHABET[new_idx]
            result.append(new_char.upper() if is_upper else new_char)
        else:
            result.append(char)
    
    return ''.join(result)


if __name__ == '__main__':
    if len(sys.argv) < 3:
        print("Использование: python3 caesar_encode.py <ключ> <текст>")
        print("Пример: python3 caesar_encode.py 3 'привет мир'")
        sys.exit(1)
    
    try:
        key = int(sys.argv[1])
        text = ' '.join(sys.argv[2:])
        
        encrypted = caesar_encrypt(text, key)
        
        print(f"Ключ: {key}")
        print(f"Исходный текст: {text}")
        print(f"Зашифрованный: {encrypted}")
    except ValueError:
        print("❌ Ошибка: ключ должен быть числом")
        sys.exit(1)
