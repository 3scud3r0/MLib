# Ambiente de desenvolvimento na nuvem

Use o checkout existente `/workspace/MLib`. Cada tarefa na nuvem é isolada;
não crie worktrees sem solicitação explícita. Preserve alterações existentes.

Execute `bash scripts/setup-cloud.sh` a partir do checkout para criar/atualizar
`.venv`, instalar o pacote editável e executar regressões e o certificado de
conservação publicado. O Python não exige serviços, segredos ou variáveis
adicionais. A instalação consulta PyPI para as dependências de construção.

Em tarefas futuras, use `.venv/bin/python` no diretório `/workspace/MLib`.
Processos não precisam ser mantidos em execução. Consulte
`README_MLIB_0_6.md` para as APIs e seus domínios.

Lean/Mathlib seguem `.github/workflows/lean-verify.yml`. Não se deve promover
certificados Python a resultados verificados pelo kernel Lean. A compilação
Lean local não foi validada nesta entrega.

O serviço de configuração retornou erro tanto na leitura quanto na tentativa
de salvar `install_script` e `start_skill`. Portanto, a persistência no rascunho
não foi confirmada. Estes arquivos fornecem os comandos locais reproduzíveis;
não constituem uma configuração publicada do ambiente.
