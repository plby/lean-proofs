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
Case T (the Case-T lemma and the T-tail proposition): the finitely many staircase lines
`μ = e + h ≤ 11`, `e ≠ h`. Assembly:
  * `a ≤ 3000`: the kernel-decided per-line/per-block scan `T_scan_all`
    (CaseTScan, T-tail part (i)) plus its soundness `TlineGo_sound`
    (CaseTCore) — variant A / base-form staircase constructions, with the
    158 Table-A rows and the 14 supplementary rows (`tSuppT`, replacing the
    paper's variant B) discharged by frame certificates;
  * `a > 3000`: the generic linear tail `T_tail` (CaseTCore,
    T-tail part (ii)) — base form only, slope `2/μ' ≤ 2/3 < 1`.
Paper: the bounded subset-sum covering section.
-/
import ErdosProblems.Erdos1112.Sharp.Staircase
import ErdosProblems.Erdos1112.Sharp.Tables
import ErdosProblems.Erdos1112.Sharp.CaseTScan

namespace Erdos1112
namespace Proof

/-- **Case T**: hard-core, `a ∤ M`, `a ∤ b+M`, `e ≠ h`, `μ = M − a ≤ 11`. -/
theorem caseT {a b M : ℕ} (hc : HardCore a b M)
    (hnD : ¬ a ∣ M) (hnP : ¬ a ∣ (b + M))
    (hL : b - a ≠ M - b) (hμ : M - a ≤ 11) : SharpTriple a b M := by
  rcases Nat.lt_or_ge 3000 a with ha3000 | ha3000
  · exact T_tail hc hL hμ (by omega)
  · -- `a ≤ 3000`: specialize to the line `(e, h) = (b − a, M − b)`.
    have hcop := hc.coprime_a_e
    obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
    set e := b - a with hedef
    set h := M - b with hhdef
    have hbe : b = a + e := by omega
    have hMe : M = a + e + h := by omega
    have hnd1 : ¬ a ∣ (e + h) := by
      intro hd
      exact hnD (hMe ▸ (by rw [Nat.add_assoc]; exact Nat.dvd_add (dvd_refl a) hd))
    have hnd2 : ¬ a ∣ (2 * e + h) := by
      intro hd
      apply hnP
      have hbm : b + M = a + a + (2 * e + h) := by omega
      rw [hbm]
      exact Nat.dvd_add (Nat.dvd_add (dvd_refl a) (dvd_refl a)) hd
    have hgo : TlineGo e h a = true :=
      T_scan_all (by omega) (by omega) (by omega) hL ha3000
    have hs := TlineGo_sound (by omega) (by omega) (by omega) hcop hnd1 hnd2 hgo
    rw [hbe, hMe]
    exact hs

end Proof
end Erdos1112
