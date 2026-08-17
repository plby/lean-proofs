/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the density-one resolution of Erdős Problem 292.
https://www.erdosproblems.com/292

Informal source:
- Greg Martin, Denser Egyptian fractions, Acta Arith. 95 (2000), 231--260.

The formal proof uses the stronger positive-upper-density unit-fraction theorem
already proved in `UnitFractions.ErdosProblems`.
-/

import UnitFractions.ErdosProblems

namespace Erdos292

open Filter Finset Set
open UnitFractions

noncomputable section

/-- A faithful finite-set formulation of being the largest denominator in an
Egyptian-fraction representation of `1`. -/
def IsLargestDenominator (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ rec_sum S = 1

/-- The set `A` from Erdős Problem 292. -/
def largestDenominators : Set ℕ := {n | IsLargestDenominator n}

/-- The exceptional set `B = ℕ \ A`. -/
def exceptional : Set ℕ := largestDenominatorsᶜ

lemma rec_sum_erase_zero (S : Finset ℕ) : rec_sum (S.erase 0) = rec_sum S := by
  classical
  by_cases h0 : 0 ∈ S
  · simpa [rec_sum] using
      (Finset.sum_erase_add S (fun n : ℕ ↦ (1 : ℚ) / n) h0)
  · rw [Finset.erase_eq_of_notMem h0]

lemma exceptional_upper_density_eq_zero : upper_density exceptional = 0 := by
  apply le_antisymm
  · by_contra hle
    have hpos : 0 < upper_density exceptional := lt_of_not_ge hle
    obtain ⟨S, hSsub, hSsum⟩ := erdos298 exceptional hpos
    let T : Finset ℕ := S.erase 0
    have hTsum : rec_sum T = 1 := by
      simpa [T, rec_sum_erase_zero] using hSsum
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hTempty
      simp [hTempty] at hTsum
    let n : ℕ := T.max' hTne
    have hnT : n ∈ T := Finset.max'_mem T hTne
    have hTA : IsLargestDenominator n := by
      refine ⟨T, ?_, hnT, hTsum⟩
      intro m hm
      have hm0 : m ≠ 0 := by simpa [T] using Finset.ne_of_mem_erase hm
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, Finset.le_max' T m hm⟩
    have hnB : n ∈ exceptional := hSsub (Finset.erase_subset 0 S hnT)
    exact hnB hTA
  · exact upper_density_nonneg

lemma tendsto_partial_density_exceptional :
    Tendsto (partial_density exceptional) atTop (nhds 0) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · exact le_liminf_of_le
      (is_bounded_under_le_partial_density (A := exceptional)).isCoboundedUnder_ge
      (Eventually.of_forall fun N ↦ by
        unfold partial_density
        positivity)
  · exact le_of_eq exceptional_upper_density_eq_zero
  · exact is_bounded_under_le_partial_density
  · exact is_bounded_under_ge_partial_density

lemma partial_density_compl (A : Set ℕ) {N : ℕ} (hN : 0 < N) :
    partial_density A N = 1 - partial_density Aᶜ N := by
  classical
  have hNreal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [partial_density, partial_density]
  simp only [Set.mem_compl_iff]
  apply (eq_sub_iff_add_eq).2
  rw [← add_div, div_eq_one_iff_eq hNreal]
  have hcard :
      ((Finset.range N).filter fun n ↦ n ∈ A).card +
          ((Finset.range N).filter fun n ↦ ¬n ∈ A).card = N := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.range N) (p := fun n ↦ n ∈ A))
  exact_mod_cast hcard

lemma tendsto_partial_density_largestDenominators :
    Tendsto (partial_density largestDenominators) atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hsub : Tendsto (fun N : ℕ ↦ 1 - partial_density exceptional N)
      atTop (nhds 1) := by
    simpa using hconst.sub tendsto_partial_density_exceptional
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa [exceptional] using (partial_density_compl largestDenominators hN).symm

/-- Erdős Problem 292: the set of possible largest denominators has natural density `1`. -/
theorem erdos292 : has_density largestDenominators 1 := by
  exact ⟨tendsto_partial_density_largestDenominators.limsup_eq,
    tendsto_partial_density_largestDenominators.liminf_eq⟩

end

end Erdos292

#print axioms Erdos292.erdos292
