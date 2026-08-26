# Erdős Problem 512

[EPC](https://www.erdosproblems.com/512) ·
[announcement](https://www.erdosproblems.com/forum/thread/512#post-7140) ·
[source request](https://aristotle.harmonic.fun/dashboard/requests/b663fac0-b653-4148-8d0a-9ae5c7dbdaea)

## Scope and authorship

`Erdos512.erdos_512` states that there is an absolute positive constant `K`
such that, for every finite set `A` of integers, the integral from zero to one of
`‖∑ n ∈ A, exp (2πinθ)‖` is at least `K * log A.card`.
No positivity hypothesis on the frequencies or nonemptiness hypothesis on `A`
is required. The empty-set case uses Lean's convention `Real.log 0 = 0`.

The informal proof follows **O. Carruth McGehee, Louis Pigno, and Brent Smith**,
*Hardy's inequality and the L¹ norm of exponential sums*, Annals of Mathematics
113 (1981), 613–618, [DOI](https://doi.org/10.2307/2007000).
Their names are also given in their
[AMS announcement](https://www.ams.org/bull/1981-05-01/S0273-0979-1981-14925-9/).
JoshuaB's 22 June 2026 EPC comment identifies the formalization as produced by
**Aristotle** using that paper. Metadata credits **Aristotle and JoshuaB**;
no fuller human name was established for JoshuaB.

## Provenance and port

The user supplied these three source modules. The supplied files contain no
Lean toolchain, Mathlib pin, or license notice. The original version could not
be established from these files, and confirmation was requested from the user.
The source `version` field is therefore omitted; Lean/Mathlib 4.33.0 is the
verified port version. No original version is inferred from other Aristotle projects.
The inaccessible Aristotle dashboard was not used to retrieve any files.

| Supplied source | SHA-256 before modification |
| --- | --- |
| Hardy.lean | `f838a05628f2e9bb2a6727229f6c0d4683098e4bc251adc5143f6d4c321748ec` |
| Construction (1).lean | `d5608eb9ded3cb877750d6ff6229e468edc8c7e7b4347eb028ba39d0c2140cac` |
| Main (1).lean | `046401ff85c185b30a3edf4e1e3695c9d9b22ba891d24dcc7e53a0729dec3602` |

The port rewrites project imports, moves the declarations into `Erdos512`, marks
individual noncomputable definitions, uses proof-local classical instances,
and updates compatibility with Lean/Mathlib 4.33.0. This includes current finite-sum
integration lemmas, explicit integral and Parseval arguments, norm/cast identities,
and removing obsolete simplification arguments. The analytic machinery and
dual construction remain in `Hardy.lean` and `Construction.lean`; the final module
relates the circle integral to the interval integral and derives the lower bound.
The independent Comparator challenge imports only Mathlib and states the final
inequality directly, without any solution definitions or wrapper predicates.

## Verification

- `lake build ErdosProblems.Erdos512 Erdos512` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the independent challenge has the expected
  placeholder warning.
- `Erdos512.erdos_512` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Independent `lean4export` exports pass `Comparator.compareAt` and
  `Comparator.checkAxioms`; a fresh Lean environment accepts kernel replay of the
  exported solution.
- The full Linux sandbox/Nanoda runner was not run because this macOS environment
  lacks `landrun`. Nanoda remains enabled in the Comparator configuration.
- Metadata, registrations, challenge/configuration consistency, source hashes,
  and the absence of proof placeholders, `native_decide`, custom axioms, and
  unsafe declarations were checked.
