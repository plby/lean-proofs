# Erdős Problem 71

This is a formalized proof of [Erdős Problem 71](https://www.erdosproblems.com/71):
every infinite arithmetic progression containing an even number contains a cycle
length forced by a sufficiently large average degree.

- Informal proof: Béla Bollobás, *Cycles modulo k* (1977).
- Formalization: Andres Gutierrez (andresg535), Aristotle, GPT-5.5, and Opus 4.7, as credited in the
  [EPC comment of 24 May 2026](https://www.erdosproblems.com/forum/thread/71#post-6635).
- Original version: Lean/Mathlib 4.28.0, explicitly selected in the linked online
  editor. The complete URL is preserved as `andresg535_71` in
  [data/urls.yaml](../data/urls.yaml).
- Port: [Lean/Mathlib 4.33.0](../src/latest/ErdosProblems/Erdos71.lean), with
  [supporting proofs](../src/latest/ErdosProblems/Erdos71/Proof.lean).

The theorem is `Erdos71.erdos_71`. Its independently stated
[Comparator challenge](../src/latest/ComparatorChallenges/ErdosProblems/Erdos71.lean)
and [configuration](../src/latest/ComparatorChallenges/ErdosProblems/Erdos71.json)
can be checked from `src/latest` using:

```sh
lake build ErdosProblems.Erdos71 Erdos71
ComparatorChallenges/run.sh ComparatorChallenges/ErdosProblems/Erdos71.json
```

The standard Comparator runner requires Linux, `landrun`, and user-level systemd.
The port was checked with the targeted Lake build, the Comparator library's
`compareAt` and `checkAxioms` functions on independent challenge/solution exports,
and Lean kernel replay of the solution export. These checks passed. The complete
sandboxed runner and Nanoda were not run on the importing macOS host.
