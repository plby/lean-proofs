# Erdős Problem 180

This is a formalized disproof of the
[Erdős–Simonovits compactness conjecture](https://www.erdosproblems.com/180),
even for nonempty finite families consisting entirely of graphs with cycles.

The [EPC comment](https://www.erdosproblems.com/forum/thread/180#post-8255)
links OpenAI's
[`ten-proofs` certificate](https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean).
This import uses that exact commit, recovered from the local clone, which pins
Lean and Mathlib **4.32.0**. It retains the original Apache 2.0 license.

The project credits **OpenAI**. The
[announcement](https://openai.com/index/ten-advances-in-mathematics/)
credits **Astra**, an internal OpenAI model, with the arguments and formalization,
and credits the OpenAI team with helping prepare the manuscripts and formalize
the proofs. Individual formal authors are not named in the source metadata.

The [Lean/Mathlib 4.33.0 port](../src/latest/ErdosProblems/Erdos180.lean) has
[supporting modules](../src/latest/ErdosProblems/Erdos180/) for the compactness
development, including the quantitative counterexample. The independent
Comparator challenge states `Erdos180.not_erdos_180` with the negated conjecture
and its compactness conclusion written out explicitly.

From `src/latest`:

```sh
lake build ErdosProblems.Erdos180 Erdos180
ComparatorChallenges/run.sh ComparatorChallenges/ErdosProblems/Erdos180.json
```

The standard Comparator runner requires Linux, `landrun`, and user-level systemd.
The targeted build, the Comparator library's `compareAt` and `checkAxioms` checks
on independent challenge/solution exports, and Lean kernel replay all passed.
The complete sandboxed runner and Nanoda were not run on the importing macOS host.
