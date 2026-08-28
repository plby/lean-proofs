import Wikipedia.HopfProblem.DegreeCollapseSupportedTransvection

/-!
# Supported realization of determinant-one linear germs

Elementary shears and their actual supported isotopies generate every real
special-linear map. Coordinate transport retains the original normed model.
-/

noncomputable section

open Set Function Matrix
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

theorem realizes_specialLinear {U : Set (ι → ℝ)} (hU : IsOpen U)
    (h0 : (0 : ι → ℝ) ∈ U) (A : SpecialLinearGroup ι ℝ) :
    Realizes U (SpecialLinearGroup.toLin' A) := by
  have hmul (A B : SpecialLinearGroup ι ℝ)
      (hA : Realizes U (SpecialLinearGroup.toLin' A))
      (hB : Realizes U (SpecialLinearGroup.toLin' B)) :
      Realizes U (SpecialLinearGroup.toLin' (A * B)) := by
    convert hA.comp hB using 1
    funext x
    rw [map_mul]
    rfl
  apply SpecialLinearGroup.diagonal_transvection_induction'
    (fun A => Realizes U (SpecialLinearGroup.toLin' A)) A
  · intro i j hij a ha
    rw [LinearFramePaths.diag2n_decompose hij a ha]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _
      (realizes_transvection hU h0 hij a)
      (realizes_transvection hU h0 hij.symm (-a⁻¹)))
      (realizes_transvection hU h0 hij a))
      (realizes_transvection hU h0 hij (-1)))
      (realizes_transvection hU h0 hij.symm 1))
      (realizes_transvection hU h0 hij (-1))
  · exact fun i j hij a => realizes_transvection hU h0 hij a
  · exact hmul

theorem realizes_det_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    (C : E ≃L[ℝ] E) (hdet : C.toLinearMap.det = 1)
    {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U) : Realizes U C := by
  let A : SpecialLinearGroup ι ℝ :=
    ⟨LinearMap.toMatrix b b C.toLinearMap, (LinearMap.det_toMatrix b C.toLinearMap).trans hdet⟩
  let c : (ι → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  have h := (realizes_specialLinear (c.symm.toHomeomorph.isOpenMap _ hU)
    (show (0 : ι → ℝ) ∈ c.symm '' U from ⟨0, h0, map_zero c.symm⟩) A).conj c
  change Realizes (c '' (c.symm '' U)) (fun y => c (A.toLin' (c.symm y))) at h
  have hset : c '' (c.symm '' U) = U := by
    rw [← image_comp]
    simp only [ContinuousLinearEquiv.self_comp_symm, image_id]
  rw [hset] at h
  convert h using 1
  funext x
  apply c.symm.injective
  rw [c.symm_apply_apply]
  exact (LinearMap.toMatrix_mulVec_repr b b C.toLinearMap x).symm

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
