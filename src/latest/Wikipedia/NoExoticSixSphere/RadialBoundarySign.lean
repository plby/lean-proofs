import Wikipedia.NoExoticSixSphere.SphereNeighborhoodAnnulus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A uniform positive inner collar from a negative radial boundary derivative

A smooth real function vanishing on the unit sphere is positive on a
uniform inner annulus if its outward radial derivative is negative there.
Compactness gives a uniform derivative neighborhood, and the one-variable
mean value theorem on each radial segment gives the strict sign.
-/

open Function Set Metric
open scoped ContDiff Topology

namespace NoExoticSixSphere.RadialBoundarySign

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem positive_of_negative_radial_derivative {h : E → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hs : ∀ x ∈ sphere (0 : E) 1, h x = 0)
    (hd : ∀ x ∈ closedBall (0 : E) 1, ρ ≤ ‖x‖ → DifferentiableAt ℝ h x)
    (hn : ∀ x ∈ closedBall (0 : E) 1, ρ ≤ ‖x‖ → fderiv ℝ h x x < 0)
    {x : E} (hx : x ∈ ball (0 : E) 1) (hrx : ρ ≤ ‖x‖) : 0 < h x := by
  have hxpos : 0 < ‖x‖ := hρ.trans_le hrx
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  let s : E := ‖x‖⁻¹ • x
  have hs1 : ‖s‖ = 1 := by
    dsimp only [s]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
  have hsx : ‖x‖ • s = x := by
    dsimp only [s]
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hpath (u : ℝ) (hu : u ∈ Icc ‖x‖ 1) :
      u • s ∈ closedBall (0 : E) 1 ∧ ρ ≤ ‖u • s‖ := by
    have hup : 0 ≤ u := hxpos.le.trans hu.1
    have hnu : ‖u • s‖ = u := by rw [norm_smul, Real.norm_of_nonneg hup, hs1, mul_one]
    exact ⟨mem_closedBall_zero_iff.mpr (hnu.trans_le hu.2),
      (hrx.trans hu.1).trans_eq hnu.symm⟩
  have hderiv (u : ℝ) (hu : u ∈ Icc ‖x‖ 1) :
      HasDerivAt (fun v : ℝ ↦ h (v • s)) (fderiv ℝ h (u • s) s) u := by
    have hline : HasDerivAt (fun v : ℝ ↦ v • s) s u := by
      simpa only [one_smul, id_eq] using! (hasDerivAt_id u).smul_const s
    exact (hd _ (hpath u hu).1 (hpath u hu).2).hasFDerivAt.comp_hasDerivAt u hline
  have hanti : StrictAntiOn (fun u : ℝ ↦ h (u • s)) (Icc ‖x‖ 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun u hu ↦ (hderiv u hu).continuousAt.continuousWithinAt)
    intro u hu
    have huc : u ∈ Icc ‖x‖ 1 := interior_subset hu
    rw [(hderiv u huc).deriv]
    have hneg := hn _ (hpath u huc).1 (hpath u huc).2
    rw [map_smul, smul_eq_mul] at hneg
    nlinarith [hxpos.trans_le huc.1]
  have hlt := hanti ⟨le_rfl, hx1.le⟩ ⟨hx1.le, le_rfl⟩ hx1
  change h (1 • s) < h (‖x‖ • s) at hlt
  rw [one_smul, hsx, hs s (mem_sphere_zero_iff_norm.mpr hs1)] at hlt
  exact hlt

theorem exists_positive_inner_annulus {h : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U) (hh : ContDiffOn ℝ ∞ h U)
    (hs : ∀ x ∈ sphere (0 : E) 1, h x = 0)
    (hn : ∀ x ∈ sphere (0 : E) 1, fderiv ℝ h x x < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      closedBall (0 : E) 1 ∩ {x | ρ ≤ ‖x‖} ⊆ U ∧
      (∀ x ∈ closedBall (0 : E) 1, ρ ≤ ‖x‖ → fderiv ℝ h x x < 0) ∧
      ∀ x ∈ ball (0 : E) 1, ρ ≤ ‖x‖ → 0 < h x := by
  let V : Set E := interior (U ∩ {x | fderiv ℝ h x x < 0})
  have hSV : sphere (0 : E) 1 ⊆ V := by
    intro x hx
    have hxc := hh.contDiffAt (hU.mem_nhds (hSU hx))
    have hc : ContinuousAt (fun y ↦ fderiv ℝ h y y) x :=
      (hxc.continuousAt_fderiv (by simp)).clm_apply continuousAt_id
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem (hU.mem_nhds (hSU hx)) (hc (Iio_mem_nhds (hn x hx))))
  obtain ⟨ρ, hρ, hρ1, hsub⟩ := exists_annulus_subset_sphere_neighborhood isOpen_interior hSV
  have hinside (x : E) (hx : x ∈ closedBall (0 : E) 1) (hrx : ρ ≤ ‖x‖) :
      x ∈ U ∧ fderiv ℝ h x x < 0 := by
    change x ∈ U ∩ {x | fderiv ℝ h x x < 0}
    exact interior_subset (hsub ⟨hx, hrx⟩)
  refine ⟨ρ, hρ, hρ1, fun x hx ↦ (hinside x hx.1 hx.2).1,
    fun x hx hrx ↦ (hinside x hx hrx).2, ?_⟩
  exact fun _ hx hrx ↦ positive_of_negative_radial_derivative hρ hs
    (fun x hx hrx ↦ (hh.contDiffAt (hU.mem_nhds (hinside x hx hrx).1)).differentiableAt
      (by simp)) (fun x hx hrx ↦ (hinside x hx hrx).2) hx hrx

end NoExoticSixSphere.RadialBoundarySign
