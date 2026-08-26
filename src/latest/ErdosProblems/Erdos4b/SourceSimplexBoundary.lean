/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceTensorRescale

/-!
# The simplex boundary has zero Lebesgue measure

The sum-one level set is a proper affine subspace. This proof also works
for an empty coordinate type, when the level set itself is empty.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators

def sourceSumHyperplane (ι : Type*) [Fintype ι] (c : ℝ) : AffineSubspace ℝ (ι → ℝ) where
  carrier := {t | ∑ i, t i = c}
  smul_vsub_vadd_mem' r x y z hx hy hz := by
    change (∑ i, (r * (x i - y i) + z i)) = c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx, hy, hz]
    ring

theorem sourceSumHyperplane_ne_top {ι : Type*} [Fintype ι] {c : ℝ} (hc : c ≠ 0) :
    sourceSumHyperplane ι c ≠ ⊤ := by
  intro hh
  have hz : (0 : ι → ℝ) ∈ sourceSumHyperplane ι c := by rw [hh]; trivial
  change (∑ i : ι, (0 : ℝ)) = c at hz
  simp only [Finset.sum_const_zero] at hz
  exact hc hz.symm

theorem volume_sum_eq_zero {ι : Type*} [Fintype ι] {c : ℝ} (hc : c ≠ 0) :
    volume {t : ι → ℝ | ∑ i, t i = c} = 0 :=
  Measure.addHaar_affineSubspace volume (sourceSumHyperplane ι c) (sourceSumHyperplane_ne_top hc)

theorem ae_sum_ne_one {ι : Type*} [Fintype ι] :
    ∀ᵐ t : ι → ℝ, (∑ i, t i) ≠ 1 := by
  exact compl_mem_ae_iff.mpr (volume_sum_eq_zero (by norm_num : (1 : ℝ) ≠ 0))

end

end Erdos4b
