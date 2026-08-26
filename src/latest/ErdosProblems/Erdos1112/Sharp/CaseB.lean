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
Case B: `a ≤ 11`, `μ ≥ 12` — Table B base certificates
(one per class `(a, ē, h)`, 178 classes, kernel-decided) extended to every
larger member of the class by the λ-lift (the lambda-lift lemma). Completeness of the
class table is a decidable sweep over the finite class space.
Paper: the bounded subset-sum covering section.
-/
import ErdosProblems.Erdos1112.Sharp.CaseBClasses

namespace Erdos1112
namespace Proof

/-- **Case B**: hard-core, `a ∤ M`, `a ∤ b+M`, `e ≠ h`, `a ≤ 11`,
`μ = M − a ≥ 12`. The hypotheses give the guard on `(a, h, b)` with
`h := M − b`; `rowFor` (decided sweep + descent) produces a Table-B base
row of the class `(a, b % a, h)` at or below `b`, and the λ-lift
(`sharpTriple_of_base`) transports its frame certificate to `(a, b, M)`. -/
theorem caseB {a b M : ℕ} (hc : HardCore a b M)
    (hnD : ¬ a ∣ M) (hnP : ¬ a ∣ (b + M))
    (hL : b - a ≠ M - b) (ha : a ≤ 11) (hμ : 12 ≤ M - a) :
    SharpTriple a b M := by
  have h3a := hc.three_le
  have hhb := hc.h_bounds
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  have hg : caseBGuard a (M - b) b = true := by
    rw [caseBGuard_eq_true_iff]
    refine ⟨h3a, ha, hhb.1, by omega, hab, hco, ?_, ?_, hL, by omega⟩
    · have e : b + (M - b) = M := by omega
      rw [e]
      exact fun hmod => hnD (Nat.dvd_of_mod_eq_zero hmod)
    · have e : 2 * b + (M - b) = b + M := by omega
      rw [e]
      exact fun hmod => hnP (Nat.dvd_of_mod_eq_zero hmod)
  obtain ⟨row, hrow, hmatch⟩ := rowFor b hg
  obtain ⟨hra, hrb, hrm, hrM⟩ := caseBRowMatch_eq_true_iff.mp hmatch
  exact sharpTriple_of_base hrow hra hrb hrm hrM (Nat.le_of_lt hbM)

end Proof
end Erdos1112
