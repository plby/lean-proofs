# Erdős Problem 183

This is a formalized solution of
[Erdős Problem 183](https://www.erdosproblems.com/183):
the `k`-th roots of the multicolor triangle Ramsey numbers tend to infinity.

The [EPC comment](https://www.erdosproblems.com/forum/thread/183#post-8250)
reports OpenAI's announcement. The
[official announcement](https://openai.com/index/ten-advances-in-mathematics/)
identifies problem 183 and links the `ten-proofs` repository. This import uses
[`MulticolorTriangleRamsey.lean` at commit `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean).
The pinned project uses Lean/Mathlib **4.32.0**. Its Ramsey proof is byte-identical
to the file in the earlier `a13547c6be4563746881d0b3b4c9fd03f72f0484` snapshot.

The source credits **Astra**, an internal OpenAI model, and the **OpenAI team**
with formalization. The project metadata names Codex as the automation framework
and does not name individual formal authors. The original Apache 2.0 license is
retained in the supporting directory.

The [Lean/Mathlib 4.33.0 port](../src/latest/ErdosProblems/Erdos183.lean) proves
`Erdos183.erdos_183`, with the
[supporting proof](../src/latest/ErdosProblems/Erdos183/Proof.lean) also retaining
the explicit quantitative lower bound and logarithmic growth estimates.

From `src/latest`:

```sh
lake build ErdosProblems.Erdos183 Erdos183
ComparatorChallenges/run.sh ComparatorChallenges/ErdosProblems/Erdos183.json
```

The standard Comparator runner requires Linux, `landrun`, and user-level systemd.
The targeted build, the Comparator library's `compareAt` and `checkAxioms` checks
on independent challenge/solution exports, and Lean kernel replay all passed.
The complete sandboxed runner and Nanoda were not run on the importing macOS host.
