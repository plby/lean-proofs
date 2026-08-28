import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationAdditiveNormalFormBasic

/-!
# Holomorphic correction after removing the actual periodic Dolbeault modes

Subtracting a periodic primitive and the explicit antilinear primitive
of its constant modes gives a function with both native antiholomorphic
coordinate derivatives zero.  The actual Cauchy–Riemann criterion proves
that this corrected function is jointly holomorphic.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The explicit correction of a smooth lattice primitive. -/
def additiveHolomorphicCorrection (h u : ComplexPlane₂ → ℂ) (c : Fin 2 → ℂ)
    (z : ComplexPlane₂) : ℂ :=
  h z - u z - antiholomorphicLinear c z

theorem additiveHolomorphicCorrection_contDiff_real
    {h u : ComplexPlane₂ → ℂ} (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (c : Fin 2 → ℂ) : ContDiff ℝ ∞ (additiveHolomorphicCorrection h u c) :=
  (hh.sub hu).sub (antiholomorphicLinear c).contDiff

theorem dbarCoordinate_additiveHolomorphicCorrection
    {h u : ComplexPlane₂ → ℂ} (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (c : Fin 2 → ℂ)
    (hdu : ∀ i z, dbarCoordinate u i z = dbarCoordinate h i z - c i)
    (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (additiveHolomorphicCorrection h u c) i z = 0 := by
  have hhd : DifferentiableAt ℝ h z := hh.differentiable (by simp) z
  have hud : DifferentiableAt ℝ u z := hu.differentiable (by simp) z
  have hsub : DifferentiableAt ℝ (fun x => h x - u x) z := hhd.sub hud
  change dbarCoordinate (fun x => h x - u x - antiholomorphicLinear c x) i z = 0
  rw [dbarCoordinate_sub hsub (antiholomorphicLinear c).differentiableAt,
    dbarCoordinate_sub hhd hud, hdu i z, dbarCoordinate_antiholomorphicLinear]
  ring

/-- Vanishing of the two actual antiholomorphic derivatives proves
joint analyticity of the corrected function on the entire cover. -/
theorem additiveHolomorphicCorrection_analytic
    {h u : ComplexPlane₂ → ℂ} (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (c : Fin 2 → ℂ)
    (hdu : ∀ i z, dbarCoordinate u i z = dbarCoordinate h i z - c i) :
    AnalyticOnNhd ℂ (additiveHolomorphicCorrection h u c) univ := by
  apply analyticOnNhd_of_dbarCoordinate_zero isOpen_univ
    ((additiveHolomorphicCorrection_contDiff_real hh hu c).differentiable
      (by simp)).differentiableOn
  · intro z _
    exact dbarCoordinate_additiveHolomorphicCorrection hh hu c hdu 0 z
  · intro z _
    exact dbarCoordinate_additiveHolomorphicCorrection hh hu c hdu 1 z

theorem additiveHolomorphicCorrection_contDiff_complex
    {h u : ComplexPlane₂ → ℂ} (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (c : Fin 2 → ℂ)
    (hdu : ∀ i z, dbarCoordinate u i z = dbarCoordinate h i z - c i) :
    ContDiff ℂ ω (additiveHolomorphicCorrection h u c) :=
  (additiveHolomorphicCorrection_analytic hh hu c hdu).contDiff

/-- A periodic correction changes no lattice increment; subtracting the
antilinear primitive contributes exactly its real-linear lattice value. -/
theorem additiveHolomorphicCorrection_lattice_increment (p : PeriodDomain)
    (h u : ComplexPlane₂ → ℂ) (c : Fin 2 → ℂ)
    (hpu : ∀ z : ComplexPlane₂, ∀ l : p.lattice, u (z + l) = u z)
    (l : p.lattice) (z : ComplexPlane₂) :
    additiveHolomorphicCorrection h u c (z + l) - additiveHolomorphicCorrection h u c z +
      antiholomorphicLinear c (l : ComplexPlane₂) = h (z + l) - h z := by
  simp only [additiveHolomorphicCorrection, hpu, map_add]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
