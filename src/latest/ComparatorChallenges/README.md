# Comparator challenges

This local Lake package contains trusted theorem statements and configurations
for validation with
[leanprover/comparator](https://github.com/leanprover/comparator). Challenge
modules intentionally use `sorry`; Comparator builds them independently from
the solution modules and checks statement equality, permitted axioms, and
kernel acceptance.

Install `landrun` and ensure user-level systemd is available. From `src/latest`,
run every configuration under this directory with:

```sh
ComparatorChallenges/run.sh
```

To run one configuration, pass it explicitly. For example:

```sh
ComparatorChallenges/run.sh ComparatorChallenges/ErdosProblems/Erdos469.json
```

Comparator and its Lean version are pinned in `lakefile.toml`. The runner builds
Comparator and `lean4export` when needed. Their locations can be overridden
with `COMPARATOR_BIN`, `COMPARATOR_LANDRUN`, and `COMPARATOR_LEAN4EXPORT`.

Successful runs are cached locally under `ComparatorChallenges/.success-cache`,
with one marker file per configuration. This location is deliberately outside
`.lake`, the directory in which Comparator permits an untrusted solution to
write. Before skipping a configuration, the runner checks that its JSON and
checker tooling are unchanged and asks Lake whether both the challenge and
solution modules are up to date. Lake's build traces make this check include
transitive imports without rebuilding the solution. The marker also records
the exact module artifacts and build traces that passed Comparator, so a later
manual rebuild cannot reuse an older success.

Set `COMPARATOR_FORCE=1` to ignore cached successes and rerun the selected
configurations. Set `COMPARATOR_CACHE_DIR` to relocate the marker files, or
remove the cache directory to clear all recorded successes.
