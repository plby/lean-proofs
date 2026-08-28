import Wikipedia.HopfProblem.DegreeCollapseTransverseGermInterpolation
import Wikipedia.SmoothSixDPoincare.TangentIdentityGermIsotopy
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Supported linearization retaining the unique coordinate-plane intersection

Postcompose the original coordinate change by a supported isotopy tangent
to identity, with germ equal to its derivative composed with its inverse.
The support is chosen in the image of the convex-interpolation neighborhood.
The actual scalar displacement formula then preserves uniqueness of the
intersection at every time, including throughout the support transition.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- The nonlinear part of a transverse coordinate germ can be removed by
an actual supported ambient isotopy without creating any new intersection
of the first coordinate plane with the second. -/
theorem exists_supported_transverse_germ_linearization
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (P : A ≃L[ℝ] A) (hP : ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (C : (A × B) ≃L[ℝ] (A × B)) (H : ℝ × (A × B) → A × B) (K : Set (A × B)),
      C.toContinuousLinearMap = fderiv ℝ Φ 0 ∧ IsCompact K ∧ K ⊆ Φ.target ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H ∧
      (∀ y, H (0, y) = y) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞,
        ∀ y, D y = H (t, y)) ∧
      (∀ t y, y ∉ K → H (t, y) = y) ∧ (∀ t, H (t, 0) = 0) ∧
      (∀ t x, (x, (0 : B)) ∈ Φ.source → ((H (t, Φ (x, 0))).1 = 0 ↔ x = 0)) ∧
      (∀ t, fderiv ℝ (fun x => H (t, Φ x)) 0 = fderiv ℝ Φ 0) ∧
      (fun x => H (1, Φ x)) =ᶠ[𝓝 (0 : A × B)] C := by
  have hΦ : ContDiffOn ℝ ∞ (Φ : (A × B) → A × B) Φ.source :=
    Φ.contMDiffOn_toFun.contDiffOn
  have hbij : Bijective (fderiv ℝ Φ 0) := by
    have hh := PartialChart.bijective_mfderiv Φ hzero
    change Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ 0 :
      (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ 0).toLinearMap hbij).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ Φ 0 := rfl
  obtain ⟨W, hW, hWzero, hWsource, hblend⟩ := exists_open_transverse_convex_blend
    Φ.open_source hzero hΦ hΦzero C.toContinuousLinearMap hC.symm P hP
  let U := Φ '' W
  have hU : IsOpen U := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW hWsource
  have hUzero : (0 : A × B) ∈ U := ⟨0, hWzero, hΦzero⟩
  have hUtarget : U ⊆ Φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hWsource hx)
  have htzero : (0 : A × B) ∈ Φ.target := hUtarget hUzero
  have hinvzero : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' hzero
    change Φ.symm (Φ 0) = 0 at hh
    rwa [hΦzero] at hh
  let G : (A × B) → A × B := C ∘ Φ.symm
  have hG : ContDiffOn ℝ ∞ G U := C.contDiff.comp_contDiffOn
    (Φ.contMDiffOn_invFun.contDiffOn.mono hUtarget)
  have hGzero : G 0 = 0 := by simp only [G, comp_apply, hinvzero, map_zero]
  have hdf := ((hΦ.contDiffAt (Φ.open_source.mem_nhds hzero)).differentiableAt
    (by simp)).hasFDerivAt
  have hdi := ((Φ.contMDiffOn_invFun.contDiffOn.contDiffAt
    (Φ.open_target.mem_nhds htzero)).differentiableAt (by simp)).hasFDerivAt
  have hdf' : HasFDerivAt (Φ : (A × B) → A × B) (fderiv ℝ Φ 0) (Φ.symm 0) := by
    rw [hinvzero]
    exact hdf
  have hcomp := hdf'.comp (f := Φ.symm) (0 : A × B) hdi
  have hid : (Φ ∘ Φ.symm) =ᶠ[𝓝 (0 : A × B)] id := by
    filter_upwards [Φ.open_target.mem_nhds htzero] with y hy
    exact Φ.right_inv' hy
  have hcancel : (fderiv ℝ Φ 0).comp (fderiv ℝ Φ.symm 0) =
      ContinuousLinearMap.id ℝ (A × B) :=
    hcomp.fderiv.symm.trans (hid.fderiv_eq.trans fderiv_id)
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ (A × B) := by
    have hh := C.toContinuousLinearMap.hasFDerivAt.comp (f := Φ.symm) (0 : A × B) hdi
    exact hh.fderiv.trans (by rw [hC]; exact hcancel)
  obtain ⟨H, K, hK, hKU, hH, hH0, hdiff, hfix, hscalar, hgerm⟩ :=
    SmallPerturbation.exists_supported_tangent_identity_isotopy hU hUzero hG hGzero hdG
  have hHorigin (t : ℝ) : H (t, 0) = 0 := by
    obtain ⟨α, -, hα⟩ := hscalar t 0
    simpa only [hGzero, sub_self, smul_zero, add_zero] using hα
  have hdG' : HasFDerivAt G (ContinuousLinearMap.id ℝ (A × B)) 0 := by
    rw [← hdG]
    exact ((hG.contDiffAt (hU.mem_nhds hUzero)).differentiableAt (by simp)).hasFDerivAt
  have hHder (t : ℝ) : HasFDerivAt (fun y => H (t, y))
      (ContinuousLinearMap.id ℝ (A × B)) 0 :=
    hasFDerivAt_scalar_displacement hGzero hdG' (hscalar t)
  refine ⟨C, H, K, hC, hK, hKU.trans hUtarget, hH, hH0, hdiff, hfix, hHorigin, ?_, ?_, ?_⟩
  · intro t x hx
    by_cases hxin : Φ (x, 0) ∈ K
    · obtain ⟨z, hz, hzeq⟩ := hKU hxin
      have hzx : z = (x, 0) := Φ.toOpenPartialHomeomorph.injOn (hWsource hz) hx hzeq
      have hxW : (x, (0 : B)) ∈ W := hzx ▸ hz
      obtain ⟨α, hα, he⟩ := hscalar t (Φ (x, 0))
      have hGΦ : G (Φ (x, 0)) = C (x, 0) := by
        dsimp [G]
        exact congrArg C (Φ.left_inv' hx)
      rw [he, hGΦ]
      exact hblend x hxW α hα
    · rw [hfix t _ hxin]
      exact hunique x hx
  · intro t
    have hh : HasFDerivAt (fun y => H (t, y)) (ContinuousLinearMap.id ℝ (A × B)) (Φ 0) := by
      rw [hΦzero]
      exact hHder t
    simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using
      (hh.comp (f := Φ) (0 : A × B) hdf).fderiv
  · have hΦtend : Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
      have hh := Φ.toOpenPartialHomeomorph.continuousAt hzero
      change Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
      rwa [hΦzero] at hh
    filter_upwards [hgerm.comp_tendsto hΦtend, Φ.open_source.mem_nhds hzero] with x hx hxsource
    change H (1, Φ x) = C x
    change H (1, Φ x) = G (Φ x) at hx
    rw [hx]
    dsimp [G]
    exact congrArg C (Φ.left_inv' hxsource)

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
