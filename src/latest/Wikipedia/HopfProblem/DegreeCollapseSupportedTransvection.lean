import Wikipedia.HopfProblem.DegreeCollapseSupportedGermAlgebra
import Wikipedia.HopfProblem.DegreeCollapseSpecialLinearPaths
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Realizing every elementary matrix by an actual supported smooth isotopy -/

noncomputable section

open Set Function Matrix
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateSplit (i : ι) : (ι → ℝ) ≃L[ℝ] ℝ × ({j : ι // j ≠ i} → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => (x i, fun j => x j)
    invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
    left_inv := by
      intro x
      funext j
      by_cases h : j = i <;> simp [h]
    right_inv := by
      rintro ⟨a, x⟩
      apply Prod.ext
      · simp
      · funext j
        simp [j.property]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem realizes_transvection {U : Set (ι → ℝ)} (hU : IsOpen U)
    (h0 : (0 : ι → ℝ) ∈ U) {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Realizes U (SpecialLinearGroup.toLin' (SpecialLinearGroup.transvection hij a)) := by
  let c := coordinateSplit i
  let L : ({k : ι // k ≠ i} → ℝ) →L[ℝ] ℝ :=
    a • ContinuousLinearMap.proj ⟨j, Ne.symm hij⟩
  have h := (realizes_shear L (c.toHomeomorph.isOpenMap _ hU)
    (show (0 : ℝ × ({k : ι // k ≠ i} → ℝ)) ∈ c '' U from
      ⟨0, h0, map_zero c⟩)).conj c.symm
  have hset : c.symm '' (c '' U) = U := by
    rw [← image_comp]
    simp only [ContinuousLinearEquiv.symm_comp_self, image_id]
  change Realizes (c.symm '' (c '' U))
    (fun y => c.symm ((c y).1 + L (c y).2, (c y).2)) at h
  rw [hset] at h
  convert h using 1
  funext x k
  change ((SpecialLinearGroup.transvection hij a : Matrix ι ι ℝ) *ᵥ x) k =
    (c.symm ((c x).1 + L (c x).2, (c x).2)) k
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases hk : k = i
  · subst k
    simp [c, coordinateSplit, L]
  · simp [c, coordinateSplit, L, hk, Ne.symm hk]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
