import Wikipedia.SmoothSixDPoincare.PlanarFrameComponentPath
import Wikipedia.SmoothSixDPoincare.OpenCurveEndpointGerms

/-!
# Smooth invertible planar-frame joins retaining complete endpoint germs

The actual endpoint determinants must have the same sign. The constructed
path in that genuine open determinant component and relative smoothing give
a globally smooth invertible join with both original local germs unchanged.
Relating this explicit sign condition to native Whitney intersection signs
is a separate geometric obligation.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.PlanarFrame

open PlaneImmersion (Plane)

/-- Same-sign endpoint determinants give a smooth invertible join preserving both entire germs. -/
theorem exists_smooth_join_of_same_determinant_sign
    {a b : ℝ → (Plane →L[ℝ] Plane)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (Plane →L[ℝ] Plane), ContDiff ℝ ∞ L ∧
      (∀ t, Bijective (L t)) ∧
      (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
      (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (a 0)
    rw [determinant_eq_det]
    exact mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (b 1)
    rw [determinant_eq_det]
    exact hsign
  obtain ⟨γ⟩ := nonempty_path_determinantComponent
    (⟨a 0, ha0⟩ : determinantComponent σ) (⟨b 1, hb1⟩ : determinantComponent σ)
  obtain ⟨L, hL, hmem, hleft, hright⟩ := exists_smooth_open_curve_with_endpoint_germs
    (determinantComponent σ) ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have h := hmem t
    change 0 < (a 0).toLinearMap.det * determinant (L t) at h
    rwa [determinant_eq_det] at h
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  apply bijective_of_determinant_ne_zero (L t)
  intro hz
  rw [determinant_eq_det] at hz
  have h := hpositive t
  rw [hz, mul_zero] at h
  exact lt_irrefl _ h

end Wikipedia.SmoothSixDPoincare.PlanarFrame

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- The joining works in any real two-dimensional normed model, with its genuine determinant. -/
theorem exists_smooth_invertible_join_of_finrank_two (hdim : Module.finrank ℝ D = 2)
    {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D), ContDiff ℝ ∞ L ∧
      (∀ t, Bijective (L t)) ∧
      (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
      (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  have hdim' : Module.finrank ℝ Plane = Module.finrank ℝ D := by
    simp [Plane, Module.finrank_prod, Module.finrank_self, hdim]
  let e : Plane ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq hdim'
  let a' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((a t).comp e.toContinuousLinearMap)
  let b' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((b t).comp e.toContinuousLinearMap)
  have ha' : ContDiffOn ℝ ∞ a' U := contDiffOn_const.clm_comp (ha.clm_comp contDiffOn_const)
  have hb' : ContDiffOn ℝ ∞ b' V := contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const)
  have hadet (t : ℝ) : (a' t).toLinearMap.det = (a t).toLinearMap.det :=
    LinearMap.det_conj (a t).toLinearMap e.symm.toLinearEquiv
  have hbdet (t : ℝ) : (b' t).toLinearMap.det = (b t).toLinearMap.det :=
    LinearMap.det_conj (b t).toLinearMap e.symm.toLinearEquiv
  have hsign' : 0 < (a' 0).toLinearMap.det * (b' 1).toLinearMap.det := by
    rw [hadet, hbdet]
    exact hsign
  obtain ⟨L', hL', hi', hdet', hleft, hright⟩ :=
    PlanarFrame.exists_smooth_join_of_same_determinant_sign ha' hb' hU hV h0U h1V hsign'
  let L (t : ℝ) := e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap)
  have hL : ContDiff ℝ ∞ L := contDiff_const.clm_comp (hL'.clm_comp contDiff_const)
  have hi (t : ℝ) : Bijective (L t) := e.bijective.comp ((hi' t).comp e.symm.bijective)
  have hdet (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have heq : (L t).toLinearMap.det = (L' t).toLinearMap.det :=
      LinearMap.det_conj (L' t).toLinearMap e.toLinearEquiv
    rw [heq, ← hadet 0]
    exact hdet' t
  refine ⟨L, hL, hi, hdet, ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = a t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (a t (e (e.symm v)))) = a t v
    simp only [e.apply_symm_apply]
  · filter_upwards [hright] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = b t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (b t (e (e.symm v)))) = b t v
    simp only [e.apply_symm_apply]

end Wikipedia.SmoothSixDPoincare.FrameField
