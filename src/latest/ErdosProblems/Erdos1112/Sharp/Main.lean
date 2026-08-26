/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Theorem 3 (SHARP), assembled: strong induction on the maximum M,
reduction to the hard core, and the six-case decision-tree routing
(D / P / L / E / T / B — exhaustive by arithmetic). Paper: the bounded subset-sum covering section.
-/
import ErdosProblems.Erdos1112.Sharp.Graham
import ErdosProblems.Erdos1112.Sharp.CaseD
import ErdosProblems.Erdos1112.Sharp.CaseP
import ErdosProblems.Erdos1112.Sharp.CaseL
import ErdosProblems.Erdos1112.Sharp.CaseE
import ErdosProblems.Erdos1112.Sharp.CaseT
import ErdosProblems.Erdos1112.Sharp.CaseB

namespace Erdos1112
namespace Proof

/-- Hard-core routing: the six cases exhaust the hard core. -/
theorem hardcore_cases {a b M : ℕ} (hc : HardCore a b M) :
    SharpTriple a b M := by
  by_cases hD : a ∣ M
  · exact caseD hc hD
  by_cases hP : a ∣ (b + M)
  · exact caseP hc hP
  by_cases hL : b - a = M - b
  · exact caseL hc hL
  by_cases hμ : M - a ≤ 11
  · exact caseT hc hD hP hL hμ
  by_cases ha : 12 ≤ a
  · exact caseE hc hD hP ha (by omega)
  · exact caseB hc hD hP hL (by omega) (by omega)

/-- **Theorem 3 (SHARP)**, by strong induction on the maximum. -/
theorem sharp (M : ℕ) : SharpAt M := by
  induction M using Nat.strong_induction_on with
  | _ M ih => exact sharpAt_of_hardcore M ih (fun a b hc => hardcore_cases hc)

end Proof
end Erdos1112
