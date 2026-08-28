import Wikipedia.HopfProblem.DegreeCollapseMorseLinearCoordinates
import Wikipedia.SmoothSixDPoincare.NativeRegularLevelCoordinates
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Shrinking a compact birth template into an original regular chart

Affine rescaling preserves the actual Morse condition. Every compact model
set can be shrunk into any neighborhood of the origin. The original smooth
function has centered height coordinates in any prescribed open neighborhood
of a regular point, using the requested finite-dimensional model.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclidean_isMorse_affine {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hm : MorsePerturbation.IsMorse f) {c : ℝ} (hc : c ≠ 0) (b : ℝ) :
    MorsePerturbation.IsMorse (fun x => b + c * f x) := by
  have hgrad : fderiv ℝ (fun x => b + c * f x) = fun x => c • fderiv ℝ f x := by
    funext x
    rw [fderiv_const_add, fderiv_const_mul (hf.differentiable (by simp) x)]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  intro x hx
  rw [hgrad] at hx ⊢
  have hcrit : fderiv ℝ f x = 0 := (smul_eq_zero.mp hx).resolve_left hc
  change Bijective (fderiv ℝ (c • fderiv ℝ f) x)
  rw [fderiv_const_smul (hdf.differentiable (by simp) x)]
  exact (isUnit_iff_ne_zero.mpr hc).smul_bijective.comp (hm x hcrit)

theorem exists_pos_compact_smul_subset {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ (fun x : E => δ • x) '' K ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let R := max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hCR : C < R := by dsimp [R]; linarith [le_max_left C 0]
  let δ := r / (2 * R)
  have hδ : 0 < δ := div_pos hr (mul_pos (by norm_num) hR)
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hrU
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hnorm : ‖x‖ < R := (hC x hx).trans_lt hCR
  have hm : δ * ‖x‖ < δ * R := mul_lt_mul_of_pos_left hnorm hδ
  have heq : δ * R = r / 2 := by dsimp [δ]; field_simp
  rw [heq] at hm
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_centered_native_height_chart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f) {m : ℕ}
    (hdim : 1 + m = Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (0 : Model m) ∈ Φ.source ∧ Φ 0 = x ∧ Φ.target ⊆ U ∧
        ∀ p ∈ Φ.source, f (Φ p) = f x + p.1 := by
  obtain ⟨Q, hxQ, hQ, hQx⟩ := RegularLevel.exists_native_height_chart hf hx
  have hdim' : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [Module.finrank_pi, Fintype.card_fin,
      RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  let L : (Fin m → ℝ) ≃L[ℝ] RegularLevel.Model E := ContinuousLinearEquiv.ofFinrankEq hdim'
  let D : Diffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, ℝ × RegularLevel.Model E)
      (Model m) (ℝ × RegularLevel.Model E) ∞ := {
    toFun := fun p => (f x + p.1, L p.2)
    invFun := fun p => (p.1 - f x, L.symm p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp
    contMDiff_toFun := ((contDiff_const.add contDiff_fst).prodMk
      (L.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := ((contDiff_fst.sub contDiff_const).prodMk
      (L.symm.contDiff.comp contDiff_snd)).contMDiff }
  let P := D.toPartialDiffeomorph.trans Q.symm
  let Φ := PartialChart.restrictTarget P hU
  have hD0 : D 0 = Q x := by
    rw [hQx]
    change (f x + (0 : ℝ), L 0) = (f x, 0)
    simp
  have h0P : (0 : Model m) ∈ P.source := by
    change (0 : Model m) ∈ univ ∧ D 0 ∈ Q.target
    exact ⟨mem_univ _, hD0.symm ▸ Q.map_source' hxQ⟩
  have hP0 : P 0 = x := by
    change Q.symm (D 0) = x
    rw [hD0]
    exact Q.left_inv' hxQ
  have h0Φ : (0 : Model m) ∈ Φ.source := by
    change (0 : Model m) ∈ P.source ∧ P 0 ∈ U
    exact ⟨h0P, hP0.symm ▸ hxU⟩
  refine ⟨Φ, h0Φ, hP0, fun _ hy => hy.2, ?_⟩
  intro p hp
  have hpt : D p ∈ Q.target := hp.1.2
  have hh := hQ (Q.symm (D p)) (Q.map_target' hpt)
  have hright : Q (Q.symm (D p)) = D p := Q.right_inv' hpt
  rw [hright] at hh
  exact hh.symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
