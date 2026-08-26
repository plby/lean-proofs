# Erdős Problem 146

This is a formalized disproof of the
[Erdős–Simonovits degeneracy conjecture](https://www.erdosproblems.com/146).
The construction gives a bipartite, two-degenerate graph whose extremal number
grows faster than the conjectured bound.

The [EPC comment](https://www.erdosproblems.com/forum/thread/146#post-8253)
identifies `TwoDegenerateGraphs.not_erdos_146` in OpenAI's
[`ten-proofs` source](https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean).
This import uses that exact commit, recovered from the local clone, whose
`lean-toolchain` and Mathlib dependency both specify **4.32.0**.

The project credits **OpenAI**. Its
[announcement](https://openai.com/index/ten-advances-in-mathematics/)
credits **Astra**, an internal OpenAI model, with the mathematical arguments and
formalization, and says the OpenAI team helped prepare the manuscripts and
formalize the proofs. No individual formal authors are named in the source
metadata; the Git commit author is not treated as proof-author attribution.
The original Apache 2.0 license is retained in the support directory.

The [Lean/Mathlib 4.33.0 port](../src/latest/ErdosProblems/Erdos146.lean) is split
into [supporting modules](../src/latest/ErdosProblems/Erdos146/).
It imports only the degeneracy development and three required helpers from the
compactness development. The final theorem `Erdos146.not_erdos_146` spells out
the negated conjecture directly.

From `src/latest`:

```sh
lake build ErdosProblems.Erdos146 Erdos146
ComparatorChallenges/run.sh ComparatorChallenges/ErdosProblems/Erdos146.json
```

The standard Comparator runner requires Linux, `landrun`, and user-level systemd.
The targeted build, the Comparator library's `compareAt` and `checkAxioms` checks
on independent challenge/solution exports, and Lean kernel replay all passed.
The complete sandboxed runner and Nanoda were not run on the importing macOS host.
