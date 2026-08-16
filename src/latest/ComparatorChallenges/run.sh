#!/usr/bin/env bash
set -euo pipefail

comparator_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
src_root="$(cd -- "$comparator_dir/.." && pwd)"

raw_configs=("$@")
if [[ ${#raw_configs[@]} -eq 0 ]]; then
  while IFS= read -r -d '' config; do
    raw_configs+=("$config")
  done < <(
    find "$comparator_dir" \
      -path "$comparator_dir/.lake" -prune -o \
      -type f -name '*.json' ! -name 'lake-manifest.json' -print0 |
      sort -z
  )
fi

if [[ ${#raw_configs[@]} -eq 0 ]]; then
  echo "No Comparator configurations found under $comparator_dir." >&2
  exit 1
fi

if ! command -v realpath >/dev/null; then
  echo "ComparatorChallenges/run.sh requires realpath to resolve configuration paths." >&2
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
  config="$(realpath -- "$config")"
  configs+=("$config")
done

comparator_bin="${COMPARATOR_BIN:-$src_root/.lake/packages/Comparator/.lake/build/bin/comparator}"
lean4export_bin="${COMPARATOR_LEAN4EXPORT:-$src_root/.lake/packages/lean4export/.lake/build/bin/lean4export}"
landrun_bin="${COMPARATOR_LANDRUN:-$(command -v landrun || true)}"
cache_dir="${COMPARATOR_CACHE_DIR:-$comparator_dir/.success-cache}"
force_run="${COMPARATOR_FORCE:-0}"

cd "$src_root"

if [[ ! -x "$comparator_bin" || ! -x "$lean4export_bin" ]]; then
  lake build @Comparator/comparator @lean4export/lean4export
fi

if [[ -z "$landrun_bin" || ! -x "$landrun_bin" ]]; then
  echo "Comparator requires landrun in PATH or COMPARATOR_LANDRUN to be set." >&2
  exit 1
fi

if ! command -v jq >/dev/null; then
  echo "ComparatorChallenges/run.sh requires jq to read its configurations." >&2
  exit 1
fi

if ! command -v sha256sum >/dev/null; then
  echo "ComparatorChallenges/run.sh requires sha256sum to maintain its success cache." >&2
  exit 1
fi

mkdir -p "$cache_dir"

fingerprint_inputs=(
  "$comparator_dir/run.sh"
  "$comparator_dir/lakefile.toml"
  "$comparator_bin"
  "$lean4export_bin"
  "$landrun_bin"
)
for input in \
    "$src_root/lakefile.toml" \
    "$src_root/lake-manifest.json" \
    "$comparator_dir/lake-manifest.json" \
    "$comparator_dir/lean-toolchain"; do
  if [[ -f "$input" ]]; then
    fingerprint_inputs+=("$input")
  fi
done

global_fingerprint="$({
  printf '%s\n' "ComparatorChallenges success cache v2"
  lake --version
  sha256sum -- "${fingerprint_inputs[@]}"
} | sha256sum | cut -d ' ' -f 1)"

artifact_fingerprint() {
  local olean_path="$1"
  local trace_path="${olean_path%.olean}.trace"
  if [[ ! -f "$olean_path" || ! -f "$trace_path" ]]; then
    return 1
  fi
  sha256sum -- "$olean_path" "$trace_path" | sha256sum | cut -d ' ' -f 1
}

artifacts_match_paths() {
  local index="$1"
  local challenge_olean="$2"
  local solution_olean="$3"
  local challenge_artifact
  local solution_artifact
  challenge_artifact="$(artifact_fingerprint "$challenge_olean")" || return 1
  solution_artifact="$(artifact_fingerprint "$solution_olean")" || return 1
  [[ "$challenge_artifact" == "${cached_challenge_artifacts[$index]}" &&
      "$solution_artifact" == "${cached_solution_artifacts[$index]}" ]]
}

cache_artifacts_match() {
  local index="$1"
  local artifact_output
  local -a artifact_paths=()
  if ! artifact_output="$(lake --no-build --quiet --text query \
      "+${challenge_modules[$index]}:olean" \
      "+${solution_modules[$index]}:olean" 2>/dev/null)"; then
    return 1
  fi
  mapfile -t artifact_paths <<< "$artifact_output"
  if [[ ${#artifact_paths[@]} -ne 2 ]]; then
    return 1
  fi
  artifacts_match_paths "$index" "${artifact_paths[0]}" "${artifact_paths[1]}"
}

challenge_modules=()
solution_modules=()
cache_files=()
cache_fingerprints=()
cached_challenge_artifacts=()
cached_solution_artifacts=()
cache_candidates=()
skip_cached=()
freshness_targets=()

for config in "${configs[@]}"; do
  if ! challenge_module="$(jq -er \
      '.challenge_module | strings | select(length > 0)' "$config")"; then
    echo "Comparator configuration has no valid challenge_module: $config" >&2
    exit 1
  fi

  if ! solution_module="$(jq -er \
      '.solution_module | strings | select(length > 0)' "$config")"; then
    echo "Comparator configuration has no valid solution_module: $config" >&2
    exit 1
  fi

  config_digest="$(sha256sum -- "$config" | cut -d ' ' -f 1)"
  cache_fingerprint="$(
    printf '%s\0%s\0%s\0%s\0' \
      "$global_fingerprint" "$config_digest" "$challenge_module" "$solution_module" |
      sha256sum | cut -d ' ' -f 1
  )"

  if [[ "$config" == "$comparator_dir/"* ]]; then
    cache_relative="${config#"$comparator_dir/"}"
    cache_relative="${cache_relative%.json}.success"
  else
    cache_name="$(printf '%s' "$challenge_module" | sed 's/[^A-Za-z0-9._-]/_/g')"
    cache_relative="external/$cache_name-${config_digest:0:16}.success"
  fi
  cache_file="$cache_dir/$cache_relative"

  challenge_modules+=("$challenge_module")
  solution_modules+=("$solution_module")
  cache_files+=("$cache_file")
  cache_fingerprints+=("$cache_fingerprint")
  skip_cached+=(0)

  cached_metadata=""
  cached_challenge_artifact=""
  cached_solution_artifact=""
  if [[ -f "$cache_file" ]]; then
    read -r cached_metadata cached_challenge_artifact cached_solution_artifact < "$cache_file" || true
  fi
  cached_challenge_artifacts+=("$cached_challenge_artifact")
  cached_solution_artifacts+=("$cached_solution_artifact")

  if [[ "$force_run" != "1" && "$cached_metadata" == "$cache_fingerprint" &&
      -n "$cached_challenge_artifact" && -n "$cached_solution_artifact" ]]; then
    cache_candidates+=(1)
    freshness_targets+=("+$challenge_module:olean" "+$solution_module:olean")
  else
    cache_candidates+=(0)
  fi
done

# Usually every cached target is fresh, so query all artifact paths in one Lake process.
# If the batch is stale, the loop below checks candidates separately.
artifact_output=""
artifact_paths=()
if [[ ${#freshness_targets[@]} -ne 0 ]] &&
    artifact_output="$(lake --no-build --quiet --text query \
      "${freshness_targets[@]}" 2>/dev/null)"; then
  mapfile -t artifact_paths <<< "$artifact_output"
  if [[ ${#artifact_paths[@]} -eq ${#freshness_targets[@]} ]]; then
    artifact_index=0
    for index in "${!configs[@]}"; do
      if [[ "${cache_candidates[$index]}" == "1" ]]; then
        if artifacts_match_paths "$index" \
            "${artifact_paths[$artifact_index]}" "${artifact_paths[$((artifact_index + 1))]}"; then
          skip_cached[$index]=1
        fi
        artifact_index=$((artifact_index + 2))
      fi
    done
  fi
fi

for index in "${!configs[@]}"; do
  config="${configs[$index]}"
  challenge_module="${challenge_modules[$index]}"
  solution_module="${solution_modules[$index]}"
  cache_file="${cache_files[$index]}"
  cache_fingerprint="${cache_fingerprints[$index]}"

  if [[ "${cache_candidates[$index]}" == "1" ]] &&
      { [[ "${skip_cached[$index]}" == "1" ]] ||
        cache_artifacts_match "$index"; }; then
    echo "Skipping Comparator configuration (cached and up-to-date): ${config#"$src_root/"}"
    continue
  fi

  echo "Prebuilding Comparator challenge: $challenge_module"
  lake build "$challenge_module"

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

  if ! artifact_output="$(lake --no-build --quiet --text query \
      "+$challenge_module:olean" "+$solution_module:olean" 2>/dev/null)"; then
    echo "Comparator succeeded, but its build artifacts could not be queried for caching." >&2
    exit 1
  fi
  mapfile -t artifact_paths <<< "$artifact_output"
  if [[ ${#artifact_paths[@]} -ne 2 ]]; then
    echo "Comparator succeeded, but Lake returned unexpected artifact paths for caching." >&2
    exit 1
  fi
  if ! challenge_artifact="$(artifact_fingerprint "${artifact_paths[0]}")" ||
      ! solution_artifact="$(artifact_fingerprint "${artifact_paths[1]}")"; then
    echo "Comparator succeeded, but its build artifacts could not be fingerprinted." >&2
    exit 1
  fi

  mkdir -p "$(dirname -- "$cache_file")"
  cache_tmp="$(mktemp "$cache_file.tmp.XXXXXX")"
  printf '%s %s %s\n' \
    "$cache_fingerprint" "$challenge_artifact" "$solution_artifact" > "$cache_tmp"
  mv -- "$cache_tmp" "$cache_file"
  echo "Recorded successful Comparator run: ${cache_file#"$src_root/"}"
done
