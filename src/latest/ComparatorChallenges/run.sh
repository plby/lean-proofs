#!/usr/bin/env bash
set -euo pipefail

comparator_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
src_root="$(cd -- "$comparator_dir/.." && pwd)"

raw_configs=("$@")
if [[ ${#raw_configs[@]} -eq 0 ]]; then
  while IFS= read -r -d '' config; do
    raw_configs+=("$config")
  done < <(find "$comparator_dir" -type f -name '*.json' -print0 | sort -z)
fi

if [[ ${#raw_configs[@]} -eq 0 ]]; then
  echo "No Comparator configurations found under $comparator_dir." >&2
  exit 1
fi

configs=()
for config in "${raw_configs[@]}"; do
  if [[ "$config" != /* ]]; then
    config="$src_root/$config"
  fi
  if [[ ! -f "$config" ]]; then
    echo "Comparator configuration does not exist: $config" >&2
    exit 1
  fi
  configs+=("$config")
done

comparator_bin="${COMPARATOR_BIN:-$src_root/.lake/packages/Comparator/.lake/build/bin/comparator}"
lean4export_bin="${COMPARATOR_LEAN4EXPORT:-$src_root/.lake/packages/lean4export/.lake/build/bin/lean4export}"
landrun_bin="${COMPARATOR_LANDRUN:-$(command -v landrun || true)}"

cd "$src_root"

if [[ ! -x "$comparator_bin" || ! -x "$lean4export_bin" ]]; then
  lake build @Comparator/comparator @lean4export/lean4export
fi

if [[ -z "$landrun_bin" || ! -x "$landrun_bin" ]]; then
  echo "Comparator requires landrun in PATH or COMPARATOR_LANDRUN to be set." >&2
  exit 1
fi

for config in "${configs[@]}"; do
  echo "Running Comparator configuration: ${config#"$src_root/"}"
  systemd-run \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --user \
    --pty \
    -E PATH="$PATH" \
    -E COMPARATOR_LANDRUN="$landrun_bin" \
    -E COMPARATOR_LEAN4EXPORT="$lean4export_bin" \
    --working-directory "$src_root" \
    -- \
    bash -c 'lake env "$1" "$2"' _ "$comparator_bin" "$config"
done
