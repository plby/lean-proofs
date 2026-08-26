/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 1189: the elementary density obstruction for covering sets.
Informal proof: count residue classes in a common period.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Core

namespace Erdos1189

open Finset

/-- A nonnegative representative of an integer residue. -/
def canonicalResidue (a : ℕ → ℤ) (d : ℕ) : ℕ :=
  (a d % (d : ℤ)).toNat

lemma canonicalResidue_cast (a : ℕ → ℤ) {d : ℕ} (hd : 0 < d) :
    (canonicalResidue a d : ℤ) = a d % (d : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd.ne'))

lemma canonicalResidue_lt (a : ℕ → ℤ) {d : ℕ} (hd : 0 < d) :
    canonicalResidue a d < d := by
  have := Int.emod_lt_of_pos (a d) (by exact_mod_cast hd : (0 : ℤ) < d)
  rw [← canonicalResidue_cast a hd] at this
  exact_mod_cast this

lemma nat_modEq_canonicalResidue_iff (a : ℕ → ℤ) {d : ℕ} (hd : 0 < d) (x : ℕ) :
    x ≡ canonicalResidue a d [MOD d] ↔ (x : ℤ) ≡ a d [ZMOD d] := by
  rw [← Int.natCast_modEq_iff, canonicalResidue_cast a hd]
  simp only [Int.ModEq, Int.emod_emod]

/-- Each class occupies exactly `N / d` positions in a period divisible by `d`. -/
lemma card_residue_class {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) (r : ℕ) :
    ((range N).filter (fun x => x ≡ r [MOD d])).card = N / d := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hd r]
  simp [Nat.mod_eq_zero_of_dvd hdN]

lemma Covers.period_le_sum_quotients {D : Finset ℕ} {a : ℕ → ℤ} {N : ℕ}
    (h : Covers D a) (hpos : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ N) :
    N ≤ ∑ d ∈ D, N / d := by
  let S : ℕ → Finset ℕ := fun d =>
    (range N).filter (fun x => x ≡ canonicalResidue a d [MOD d])
  have hsub : range N ⊆ D.biUnion S := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := h x
    exact mem_biUnion.mpr ⟨d, hd, mem_filter.mpr
      ⟨hx, (nat_modEq_canonicalResidue_iff a (hpos d hd) x).mpr hxd⟩⟩
  calc
    N = (range N).card := (card_range N).symm
    _ ≤ (D.biUnion S).card := card_le_card hsub
    _ ≤ ∑ d ∈ D, (S d).card := card_biUnion_le
    _ = ∑ d ∈ D, N / d := by
      apply sum_congr rfl
      intro d hd
      exact card_residue_class (hpos d hd) (hdiv d hd) _

/-- The reciprocal mass, using rationals so finite examples need no approximation. -/
def reciprocalSum (D : Finset ℕ) : ℚ := ∑ d ∈ D, (d : ℚ)⁻¹

lemma IsCoveringSet.one_le_reciprocalSum {D : Finset ℕ} (h : IsCoveringSet D) :
    1 ≤ reciprocalSum D := by
  obtain ⟨a, ha⟩ := h.2
  let N := ∏ d ∈ D, d
  have hpos : ∀ d ∈ D, 0 < d := fun d hd => lt_trans Nat.zero_lt_one (h.1 d hd)
  have hN : 0 < N := prod_pos hpos
  have hdiv : ∀ d ∈ D, d ∣ N := fun d hd => dvd_prod_of_mem id hd
  have hbound := ha.period_le_sum_quotients hpos hdiv
  have hcast : (N : ℚ) ≤ ∑ d ∈ D, (N : ℚ) / d := by
    calc
      (N : ℚ) ≤ ((∑ d ∈ D, N / d : ℕ) : ℚ) := by exact_mod_cast hbound
      _ = ∑ d ∈ D, (N : ℚ) / d := by
        push_cast
        apply sum_congr rfl
        intro d hd
        exact Nat.cast_div (hdiv d hd) (by exact_mod_cast (hpos d hd).ne' : (d : ℚ) ≠ 0)
  have heq : (∑ d ∈ D, (N : ℚ) / d) = N * reciprocalSum D := by
    simp only [reciprocalSum, div_eq_mul_inv, mul_sum]
  rw [heq] at hcast
  nlinarith [show (0 : ℚ) < N by exact_mod_cast hN]

lemma not_isCoveringSet_of_reciprocalSum_lt_one {D : Finset ℕ}
    (h : reciprocalSum D < 1) : ¬ IsCoveringSet D := by
  intro hD
  exact (not_le_of_gt h) hD.one_le_reciprocalSum

end Erdos1189
