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
