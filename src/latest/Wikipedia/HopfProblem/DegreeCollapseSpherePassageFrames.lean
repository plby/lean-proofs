import Wikipedia.HopfProblem.DegreeCollapseBoundaryUnitCoefficient
import Wikipedia.HopfProblem.DegreeCollapsePassageNormalDeterminant

/-!
# Integral units and shared normal frames for sphere passages

Use the actual top homology of each positive-dimensional standard sphere.
The normal determinant comparison keeps both arbitrary common frames and
works in dimension four as required for three-sphere passages.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

theorem sphere_map_unit_of_homology_bijective (k : ℕ) {Y : Type} [TopologicalSpace Y]
    (e : Hemisphere.Sphere (k + 1) ≃ₜ Y) (g : C(Hemisphere.Sphere (k + 1), Y))
    (hg : Bijective (singularHomologyMap g (k + 1))) :
    ∃ u : ℤ, (u = 1 ∨ u = -1) ∧
      singularHomologyMap g (k + 1) =
        u • singularHomologyMap (e : C(Hemisphere.Sphere (k + 1), Y)) (k + 1) := by
  let H := unitSphereHomologyTopEquiv k
  let B := LinearEquiv.ofBijective (singularHomologyMap g (k + 1)) hg
  let J := homeomorphHomologyEquiv e (k + 1)
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, NoExoticSixSphere.IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := NoExoticSixSphere.IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

theorem sphere_attaching_contributions_opposite_of_relative_det_neg
    (k : ℕ) {N Y : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y]
    (a : C(sphere (0 : N) 1, Y)) (L₀ L₁ : Hemisphere.Ambient (k + 2) ≃L[ℝ] N)
    (hdet : (L₁.trans L₀.symm).toLinearMap.det < 0) :
    singularHomologyMap (a.comp
      (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)) (k + 1) =
      -singularHomologyMap (a.comp
        (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)) (k + 1) := by
  rw [singularHomologyMap_comp, singularHomologyMap_comp]
  apply LinearMap.ext
  intro u
  have h := LinearSphereAction.homology_relative_sign k L₁ L₀ k u
  rw [sign_eq_neg_one_iff.mpr hdet] at h
  simp only [SignType.coe_neg, SignType.coe_one, neg_one_zsmul] at h
  change singularHomologyMap a (k + 1)
    (singularHomologyMap (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)
      (k + 1) u) = -singularHomologyMap a (k + 1)
        (singularHomologyMap (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)
          (k + 1) u)
  rw [h, map_neg]

theorem exists_shared_sphere_passage_frames (m : ℕ)
    {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (P : Hemisphere.Ambient (m + 1) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)))
    (B : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] N)
    (Q : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)))
    (hdim : Module.finrank ℝ N = m + 1)
    (hbij : Bijective (B.comp (Q.toContinuousLinearMap.comp P))) :
    ∃ (P' : Hemisphere.Ambient (m + 1) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)))
      (B' : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] N),
      P'.toContinuousLinearMap = P ∧ B'.toContinuousLinearMap = B := by
  have hPi : Injective P := by
    intro x y hxy
    apply hbij.injective
    change B (Q (P x)) = B (Q (P y))
    rw [hxy]
  have hBs : Surjective B := by
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact ⟨Q (P x), hx⟩
  have hdimP : Module.finrank ℝ (Hemisphere.Ambient (m + 1)) =
      Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin m)) := by
    simp [Hemisphere.Ambient, Module.finrank_prod, Nat.add_comm]
  have hdimB : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin m)) = Module.finrank ℝ N := by
    simp [Module.finrank_prod, hdim, Nat.add_comm]
  have hPb : Bijective P :=
    ⟨hPi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimP).mp hPi⟩
  have hBb : Bijective B :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimB).mpr hBs, hBs⟩
  exact ⟨(LinearEquiv.ofBijective P.toLinearMap hPb).toContinuousLinearEquiv,
    (LinearEquiv.ofBijective B.toLinearMap hBb).toContinuousLinearEquiv, rfl, rfl⟩

variable {A U N : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ U] in
theorem relative_sphere_passage_frame_det
    (P : A ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    (Q₀ Q₁ : (ℝ × U) ≃L[ℝ] (ℝ × U)) :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap.det =
      Q₀.toLinearMap.det⁻¹ * Q₁.toLinearMap.det := by
  have heq : (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap =
      P.symm.toLinearMap.comp ((Q₀.symm.toLinearMap.comp Q₁.toLinearMap).comp
        P.toLinearMap) := by
    apply LinearMap.ext
    intro z
    change P.symm (Q₀.symm (B.symm (B (Q₁ (P z))))) = P.symm (Q₀.symm (Q₁ (P z)))
    rw [B.symm_apply_apply]
  rw [heq]
  have hconj := LinearMap.det_conj (Q₀.symm.toLinearMap.comp Q₁.toLinearMap) P.symm.toLinearEquiv
  calc
    _ = (Q₀.symm.toLinearMap.comp Q₁.toLinearMap).det := hconj
    _ = _ := by
      rw [LinearMap.det_comp]
      exact congrArg (fun t : ℝ => t * Q₁.toLinearMap.det)
        (LinearEquiv.det_coe_symm Q₀.toLinearEquiv)

omit [FiniteDimensional ℝ A] in
theorem sphere_passage_normal_relative_det_neg
    (P : A ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (C : U ≃L[ℝ] U) (hC : C.toLinearMap.det < 0) :
    (((P.trans (passageNormalProduct c₁ hc₁.ne' C)).trans B).trans
      ((P.trans (passageNormalProduct c₀ hc₀.ne'
        (ContinuousLinearEquiv.refl ℝ U))).trans B).symm).toLinearMap.det < 0 := by
  rw [relative_sphere_passage_frame_det, passageNormalProduct_det, passageNormalProduct_det]
  change (c₀ * (LinearMap.id : U →ₗ[ℝ] U).det)⁻¹ * (c₁ * C.toLinearMap.det) < 0
  rw [LinearMap.det_id, mul_one]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hc₀) (mul_neg_of_pos_of_neg hc₁ hC)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
