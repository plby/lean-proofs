/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonWeights
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq

/-!
# Exact decomposition of the presieve indicator into residue classes

The coprimality condition is periodic on the whole integer line. Each
integer has a unique representative in `[0,W)`, so summing its allowed
residue indicators reproduces the original condition exactly.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def preSieveCondition {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ) (n : ℤ) : Prop :=
  (∏ i, (n + a i).natAbs).Coprime W

open scoped Classical in
def preSieveResidues {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ) : Finset ℕ :=
  (Finset.range W).filter (fun v => preSieveCondition W a v)

theorem natAbs_coprime_iff_of_modEq {W : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD W]) :
    a.natAbs.Coprime W ↔ b.natAbs.Coprime W := by
  change Int.gcd a W = 1 ↔ Int.gcd b W = 1
  rw [← Int.gcd_emod a W, ← Int.gcd_emod b W, h]

theorem preSieveCondition_iff_of_modEq {ι : Type*} [Fintype ι]
    {W : ℕ} (a : ι → ℤ) {n m : ℤ} (h : n ≡ m [ZMOD W]) :
    preSieveCondition W a n ↔ preSieveCondition W a m := by
  simp only [preSieveCondition, Nat.coprime_fintype_prod_left_iff]
  exact forall_congr' fun i => natAbs_coprime_iff_of_modEq (h.add_right (a i))

theorem card_preSieveResidues_le {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ) :
    (preSieveResidues W a).card ≤ W := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range W)

theorem exists_unique_natural_residue {W : ℕ} (hW : 0 < W) (n : ℤ) :
    ∃ v : ℕ, v < W ∧ n ≡ v [ZMOD W] ∧
      ∀ u : ℕ, u < W → n ≡ u [ZMOD W] → u = v := by
  obtain ⟨v, hv, hn⟩ := Int.existsUnique_equiv_nat n (by exact_mod_cast hW : (0 : ℤ) < W)
  have hvW : v < W := by exact_mod_cast hv
  refine ⟨v, hvW, hn.symm, ?_⟩
  intro u hu hnu
  have hm : u ≡ v [MOD W] := Int.natCast_modEq_iff.mp (hnu.symm.trans hn.symm)
  exact hm.eq_of_lt_of_lt hu hvW

open scoped Classical in
theorem sum_preSieve_residue_indicator {ι : Type*} [Fintype ι] {W : ℕ}
    (hW : 0 < W) (a : ι → ℤ) (n : ℤ) (b : ℝ) :
    (∑ v ∈ preSieveResidues W a, if n ≡ v [ZMOD W] then b else 0) =
      if preSieveCondition W a n then b else 0 := by
  classical
  obtain ⟨v, hv, hnv, huniq⟩ := exists_unique_natural_residue hW n
  by_cases hgood : preSieveCondition W a n
  · rw [if_pos hgood]
    have hmem : v ∈ preSieveResidues W a := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hv, (preSieveCondition_iff_of_modEq a hnv).mp hgood⟩
    rw [Finset.sum_eq_single_of_mem v hmem, if_pos hnv]
    intro u hu huv
    apply if_neg
    intro hnu
    exact huv (huniq u (Finset.mem_range.mp (Finset.mem_filter.mp hu).1) hnu)
  · rw [if_neg hgood]
    apply Finset.sum_eq_zero
    intro u hu
    apply if_neg
    intro hnu
    exact hgood ((preSieveCondition_iff_of_modEq a hnu).mpr (Finset.mem_filter.mp hu).2)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_preSieve_residue_indicator
