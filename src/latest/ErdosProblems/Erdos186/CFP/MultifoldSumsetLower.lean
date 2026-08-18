/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GrowthLemmas

/-!
# A linear lower bound for integer multifold sumsets

An anchored integer set containing a nonzero element contains the entire
arithmetic progression `0,a,…,h*a` in its `h`-fold sumset.  This elementary
fact supplies the global-cardinality lower bound needed by the physical
density target selector.
-/

namespace Erdos186.CFP.GrowthLemmas

/-- If both `0` and `a` belong to `W`, then every multiple `j*a` with
`j ≤ fold` belongs to the `fold`-fold sumset. -/
theorem natCast_mul_mem_multifoldSumset
    {W : Finset ℤ} {a : ℤ} (hzero : 0 ∈ W) (ha : a ∈ W) :
    ∀ {fold j : ℕ}, j ≤ fold →
      (j : ℤ) * a ∈ multifoldSumset fold W := by
  intro fold
  induction fold with
  | zero =>
      intro j hj
      have hjzero : j = 0 := by omega
      subst j
      simp [multifoldSumset]
  | succ fold ih =>
      intro j hj
      by_cases hprevious : j ≤ fold
      · exact multifoldSumset_mono_index hzero (Nat.le_succ fold)
          (ih hprevious)
      · have hjtop : j = fold + 1 := by omega
        subst j
        apply mem_multifoldSumset_succ_iff.mpr
        refine ⟨(fold : ℤ) * a, ih le_rfl, a, ha, ?_⟩
        push_cast
        ring

/-- The progression of multiples of one nonzero source element has no
collisions. -/
theorem card_image_range_natCast_mul {a : ℤ} (ha : a ≠ 0) (fold : ℕ) :
    ((Finset.range (fold + 1)).image (fun j : ℕ ↦ (j : ℤ) * a)).card =
      fold + 1 := by
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro j k hjk
  have hcast : (j : ℤ) = (k : ℤ) := by
    exact mul_right_cancel₀ ha hjk
  exact_mod_cast hcast

/-- Every anchored nontrivial integer set has at least `fold+1` elements
in its `fold`-fold sumset. -/
theorem add_one_le_card_multifoldSumset
    {W : Finset ℤ} {fold : ℕ}
    (hzero : 0 ∈ W) (hnontrivial : W ≠ {0}) :
    fold + 1 ≤ (multifoldSumset fold W).card := by
  have ha : ∃ a ∈ W, a ≠ 0 := by
    by_contra hnot
    push Not at hnot
    have hsubset : W ⊆ {0} := by
      intro a haW
      simpa [hnot a haW]
    have hsingleton : W = {0} :=
      Finset.Subset.antisymm hsubset (by simpa using hzero)
    exact hnontrivial hsingleton
  obtain ⟨a, haW, ha0⟩ := ha
  let progression :=
    (Finset.range (fold + 1)).image (fun j : ℕ ↦ (j : ℤ) * a)
  have hprogression : progression ⊆ multifoldSumset fold W := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact natCast_mul_mem_multifoldSumset hzero haW
      (by
        have hj' : j < fold + 1 := Finset.mem_range.mp hj
        omega)
  calc
    fold + 1 = progression.card := by
      symm
      exact card_image_range_natCast_mul ha0 fold
    _ ≤ (multifoldSumset fold W).card := Finset.card_le_card hprogression

/-- Any fixed comparison coefficient below `fold+1` is therefore below
the global multifold-sumset cardinality. -/
theorem coefficient_le_card_multifoldSumset
    {W : Finset ℤ} {fold coefficient : ℕ}
    (hzero : 0 ∈ W) (hnontrivial : W ≠ {0})
    (hcoefficient : coefficient ≤ fold + 1) :
    coefficient ≤ (multifoldSumset fold W).card :=
  hcoefficient.trans (add_one_le_card_multifoldSumset hzero hnontrivial)

end Erdos186.CFP.GrowthLemmas

#print axioms
  Erdos186.CFP.GrowthLemmas.add_one_le_card_multifoldSumset
