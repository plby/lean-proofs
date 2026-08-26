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
the frame lemma: the frame lemma — residue representatives mod ν plus
padding copies of ν cover a long run. Paper: the bounded subset-sum covering section.
-/
import ErdosProblems.Erdos1112.Sharp.TwoGen

namespace Erdos1112
namespace Proof

/-- **the frame lemma (frame lemma).** If every residue `ρ mod ν` has a
representative `j·g₁ + k·g₂` inside the box `j ≤ Y, k ≤ Z` of height `≤ S`,
and `L − 1 + S ≤ ν·x`, then the multiset `{Y×g₁, Z×g₂, x×ν}` realizes every
integer of `[S, ν·x] ⊇ [S, S+L−1]` as a subset sum. -/
theorem frame_lemma {ν g₁ g₂ Y Z x S : ℕ} (hν : 0 < ν)
    (hreps : ∀ ρ < ν, ∃ j k, j ≤ Y ∧ k ≤ Z ∧
      (j * g₁ + k * g₂) % ν = ρ ∧ j * g₁ + k * g₂ ≤ S) :
    ∀ n, S ≤ n → n ≤ ν * x →
      n ∈ subsetSums (Multiset.replicate Y g₁ + Multiset.replicate Z g₂ +
        Multiset.replicate x ν) := by
  intro n hSn hnx
  obtain ⟨j, k, hjY, hkZ, hmod, hle⟩ := hreps (n % ν) (Nat.mod_lt _ hν)
  set r : ℕ := j * g₁ + k * g₂ with hrdef
  have hrn : r ≤ n := le_trans hle hSn
  have hdvd : ν ∣ n - r := (Nat.modEq_iff_dvd' hrn).mp hmod
  set q : ℕ := (n - r) / ν with hqdef
  have hqν : q * ν = n - r := Nat.div_mul_cancel hdvd
  have hqx : q ≤ x := by
    have h1 : q * ν ≤ x * ν := by
      rw [hqν]
      calc n - r ≤ n := Nat.sub_le _ _
        _ ≤ ν * x := hnx
        _ = x * ν := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h1 hν
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate j g₁ + Multiset.replicate k g₂ +
    Multiset.replicate q ν, ?_, ?_⟩
  · exact add_le_add (add_le_add
      ((Multiset.replicate_le_replicate g₁).mpr hjY)
      ((Multiset.replicate_le_replicate g₂).mpr hkZ))
      ((Multiset.replicate_le_replicate ν).mpr hqx)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    calc j * g₁ + k * g₂ + q * ν = r + (n - r) := by rw [← hrdef, hqν]
      _ = n := by omega

end Proof
end Erdos1112
