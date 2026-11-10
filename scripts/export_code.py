#!/usr/bin/env python3
"""Concatenate the active LeanML sources and project configuration into UTF-8 text."""
from pathlib import Path
import argparse
import hashlib


def source_files(root):
    files = [root/name for name in (
        '.gitignore', 'README.md', 'CONTRIBUTING.md', 'LeanML.lean',
        'lakefile.lean', 'lean-toolchain', 'lake-manifest.json',
    )]
    for directory, extensions in (
        ('LeanML', {'.lean'}), ('LeanMLTest', {'.lean'}),
        ('scripts', {'.py', '.sh'}), ('.github/workflows', {'.yml', '.yaml'}),
        ('docs', {'.md'}),
    ):
        files.extend(path for path in (root/directory).rglob('*')
                     if path.is_file() and path.suffix in extensions)
    return sorted(files, key=lambda path: path.relative_to(root).as_posix())


def render(root):
    files = source_files(root)
    output = [
        'LeanML — código-fonte e configuração concatenados (UTF-8)\n',
        'Este arquivo reúne o código textual; não é um executável nem um artefato binário.\n',
        'Inclui fontes ativos, testes, scripts, CI, configurações e documentação.\n',
        'O histórico em legacy/ e as dependências do Mathlib não integram esta exportação.\n',
        'A evidência de compilação está em docs/VALIDATION.md e o escopo em docs/STATUS.md.\n\n',
        f'ARQUIVOS: {len(files)}\n\nÍNDICE (caminho | bytes | SHA-256)\n',
    ]
    contents = []
    for path in files:
        data = path.read_bytes()
        name = path.relative_to(root).as_posix()
        output.append(f'{name} | {len(data)} | {hashlib.sha256(data).hexdigest()}\n')
        contents.append((name, data.decode('utf-8')))
    for name, content in contents:
        output.extend((f'\n===== INÍCIO DO ARQUIVO: {name} =====\n', content))
        if not content.endswith('\n'):
            output.append('\n')
        output.append(f'===== FIM DO ARQUIVO: {name} =====\n')
    return ''.join(output)


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=root/'exports/LeanML_codigo_completo.txt')
    args = parser.parse_args()
    result = render(root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(result, encoding='utf-8', newline='')
    print(f'{args.output}: {len(source_files(root))} files, {len(result.encode("utf-8"))} bytes')


if __name__ == '__main__':
    main()
