import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlasAgreement
import Mathlib.Geometry.Manifold.Complex

/-!
# Extending a quotient function over the actual compactified cusp

The extension is the literal function on the actual one-point compactification:
it agrees with the original function on every original orbit and has the
specified value at the added cusp.  A compatible analytic germ makes this
extension holomorphic in the independently constructed compact complex atlas.
Compact complex Liouville then proves that the original function is constant.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

open Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

/-- The actual one-point extension, with prescribed value at the cusp. -/
def compactExtension (f : TriangleOrbitSpace → ℂ) (c : ℂ) :
    TriangleCompactifiedOrbitSpace → ℂ := OnePoint.rec c f

@[simp] theorem compactExtension_cusp (f : TriangleOrbitSpace → ℂ) (c : ℂ) :
    compactExtension f c triangleCuspPoint = c := rfl

@[simp] theorem compactExtension_openInclusion (f : TriangleOrbitSpace → ℂ) (c : ℂ)
    (q : TriangleOrbitSpace) : compactExtension f c (triangleOpenInclusion q) = f q := rfl

theorem compactExtension_comp_openInclusion (f : TriangleOrbitSpace → ℂ) (c : ℂ) :
    compactExtension f c ∘ triangleOpenInclusion = f := rfl

/-- Holomorphy at the old quotient points follows from the actual local
biholomorphism into the compact curve. -/
theorem compactExtension_holomorphicAt_openInclusion (f : TriangleOrbitSpace → ℂ) (c : ℂ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (q : TriangleOrbitSpace) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f c) (triangleOpenInclusion q) := by
  have hp := triangleOpenInclusion_isLocalDiffeomorph q
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (compactExtension f c ∘ triangleOpenInclusion) q := hf q
  have h := hcomp.comp_of_eq hp.localInverse_contMDiffAt
    (hp.localInverse_left_inv hp.localInverse_mem_target)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with x hx
  change compactExtension f c x =
    compactExtension f c (triangleOpenInclusion (hp.localInverse x))
  rw [show triangleOpenInclusion (hp.localInverse x) = x from hx]

/-- The cusp-image identity supplies a genuine neighbourhood identity on the
one-point compactification, including the newly added point. -/
theorem compactExtension_eventuallyEq_cuspChart
    (f : TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (h : ∀ q ∈ cuspImage Y,
      f q = g (cuspFullChart width le_rfl (triangleOpenInclusion q))) :
    compactExtension f (g 0) =ᶠ[𝓝 triangleCuspPoint]
      g ∘ cuspFullChart width le_rfl := by
  filter_upwards [cuspNeighborhood_mem_nhds Y] with x hx
  induction x using OnePoint.rec with
  | infty =>
      change g 0 = g (cuspFullChart width le_rfl triangleCuspPoint)
      rw [cuspFullChart_cuspPoint]
  | coe q =>
      change f q = g (cuspFullChart width le_rfl (triangleOpenInclusion q))
      exact h q ((openInclusion_mem_cuspNeighborhood Y q).mp hx)

/-- The actual cusp chart and the analytic germ prove holomorphy of the
explicit extension at the cusp. -/
theorem compactExtension_holomorphicAt_cusp_of_cuspImage
    (f : TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (hg : AnalyticAt ℂ g 0)
    (h : ∀ q ∈ cuspImage Y,
      f q = g (cuspFullChart width le_rfl (triangleOpenInclusion q))) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) triangleCuspPoint := by
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart width le_rfl) triangleCuspPoint :=
    triangleCompactified_cuspChart_holomorphic.contMDiffAt (cuspNeighborhood_mem_nhds width)
  have hgc := hg.contDiffAt.contMDiffAt.comp_of_eq hc (cuspFullChart_cuspPoint width le_rfl)
  exact hgc.congr_of_eventuallyEq (compactExtension_eventuallyEq_cuspChart f g Y h)

/-- The explicit extension is globally holomorphic on the actual compact
complex curve.  Analyticity of the germ is required only at zero. -/
theorem compactExtension_holomorphic_of_cuspImage
    (f : TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0)
    (h : ∀ q ∈ cuspImage Y,
      f q = g (cuspFullChart width le_rfl (triangleOpenInclusion q))) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) := by
  intro x
  induction x using OnePoint.rec with
  | infty => exact compactExtension_holomorphicAt_cusp_of_cuspImage f g Y hg h
  | coe q => exact compactExtension_holomorphicAt_openInclusion f (g 0) hf q

/-- Compact complex Liouville applies to the constructed extension, not to
an assumed compactification or a hypothesized meromorphic continuation. -/
theorem eq_const_of_cuspImage (f : TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0)
    (h : ∀ q ∈ cuspImage Y,
      f q = g (cuspFullChart width le_rfl (triangleOpenInclusion q))) :
    ∀ q, f q = g 0 := by
  let := triangleCompactifiedOrbitSpace_compact
  let := triangleCompactifiedOrbitSpace_connected
  have he := compactExtension_holomorphic_of_cuspImage f g Y hf hg h
  intro q
  exact (he.mdifferentiable (by simp)).apply_eq_of_compactSpace
    (triangleOpenInclusion q) triangleCuspPoint

theorem eq_zero_of_cuspImage (f : TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (h : ∀ q ∈ cuspImage Y,
      f q = g (cuspFullChart width le_rfl (triangleOpenInclusion q))) : f = 0 := by
  funext q
  exact (eq_const_of_cuspImage f g Y hf hg h q).trans hg0

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
