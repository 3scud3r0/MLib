# Source this file to select an existing elan installation without downloading anything.
if command -v lake >/dev/null 2>&1; then
  :
elif [ -x /workspace/.leanml-elan/bin/lake ]; then
  export ELAN_HOME=/workspace/.leanml-elan
  export PATH="/workspace/.leanml-elan/bin:$PATH"
elif [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
else
  echo 'LeanML: install elan first: https://github.com/leanprover/elan' >&2
  return 1
fi
