import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth radial correction with arbitrary transverse dimension

The supported radial pullback is zero on a genuine neighborhood of the
disk center. It retains the prescribed sphere-product map near the boundary
and preserves a zero core value and derivative. All transverse coordinates
are kept unchanged; no smoothness of radial retraction at zero is assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralRadialProduct

open NoExoticSixSphere GLOrthonormalization

variable {q : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pullback (b : Sphere 3) (g : Sphere 3 × Vector q → F) (p : Vector 4 × Vector q) : F :=
  g (SphereRadialRetraction.retract b p.1, p.2)

theorem contMDiffAt_radialProduct (b : Sphere 3) {x : Vector 4} (hx : x ≠ 0)
    (v : Vector q) :
    ContMDiffAt 𝓘(ℝ, Vector 4 × Vector q) ((𝓡 3).prod (𝓡 q)) ∞
      (fun p : Vector 4 × Vector q ↦ (SphereRadialRetraction.retract b p.1, p.2)) (x, v) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hfst : ContMDiffAt 𝓘(ℝ, Vector 4 × Vector q) (𝓡 4) ∞
      (Prod.fst : Vector 4 × Vector q → Vector 4) (x, v) := contDiffAt_fst.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ, Vector 4 × Vector q) (𝓡 q) ∞
      (Prod.snd : Vector 4 × Vector q → Vector q) (x, v) := contDiffAt_snd.contMDiffAt
  exact ((SphereRadialRetraction.contMDiffAt_retract (n := 3) b hx).comp (x, v)
    hfst).prodMk hsnd

theorem contDiffAt_pullback (b : Sphere 3) (g : Sphere 3 × Vector q → F)
    {x : Vector 4} (hx : x ≠ 0) (v : Vector q)
    (hg : ContMDiffAt ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) ∞ g
      (SphereRadialRetraction.retract b x, v)) :
    ContDiffAt ℝ ∞ (pullback b g) (x, v) :=
  (hg.comp (x, v) (contMDiffAt_radialProduct b hx v)).contDiffAt

theorem fderiv_pullback_eq_zero (b : Sphere 3) (g : Sphere 3 × Vector q → F)
    {x : Vector 4} (hx : x ≠ 0) (v : Vector q)
    (hg : ContMDiffAt ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) ∞ g
      (SphereRadialRetraction.retract b x, v))
    (hzero : mfderiv ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) g
      (SphereRadialRetraction.retract b x, v) = 0) :
    fderiv ℝ (pullback b g) (x, v) = 0 := by
  have hp := contMDiffAt_radialProduct b hx v
  have hc := mfderiv_comp (x, v) (hg.mdifferentiableAt (by simp))
    (hp.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Vector 4 × Vector q) 𝓘(ℝ, F) (pullback b g) (x, v) = _ at hc
  rw [mfderiv_eq_fderiv, hzero, ContinuousLinearMap.zero_comp] at hc
  exact hc

end Wikipedia.HopfProblem.DegreeCollapse.GeneralRadialProduct

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralRadialCorrection

open NoExoticSixSphere GLOrthonormalization

variable {q : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (χ : ContDiffBump (0 : Vector 4)) (b : Sphere 3) (g : Sphere 3 × Vector q → F)

def correction (p : Vector 4 × Vector q) : F :=
  (1 - χ p.1) • GeneralRadialProduct.pullback b g p

theorem correction_eq_zero {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) χ.rIn)
    (v : Vector q) : correction χ b g (x, v) = 0 := by
  simp only [correction, χ.one_of_mem_closedBall hx, sub_self, zero_smul]

theorem correction_eq_radial {x : Vector 4} (hx : χ.rOut ≤ ‖x‖) (v : Vector q) :
    correction χ b g (x, v) = g (SphereRadialRetraction.retract b x, v) := by
  have hχ : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
  simp only [correction, hχ, sub_zero, one_smul, GeneralRadialProduct.pullback]

theorem correction_eventuallyEq_zero {x : Vector 4} (hx : x ∈ ball (0 : Vector 4) χ.rIn)
    (v : Vector q) : correction χ b g =ᶠ[𝓝 (x, v)] (fun _ ↦ 0) := by
  have hf : ContinuousAt (Prod.fst : Vector 4 × Vector q → Vector 4) (x, v) :=
    continuous_fst.continuousAt
  filter_upwards [hf.eventually (χ.eventuallyEq_one_of_mem_ball hx)] with p hp
  simp only [correction, hp, Pi.one_apply, sub_self, zero_smul]

theorem correction_core (hg : ∀ s : Sphere 3, g (s, 0) = 0) (x : Vector 4) :
    correction χ b g (x, 0) = 0 := by
  simp only [correction, GeneralRadialProduct.pullback, hg, smul_zero]

theorem contDiffAt_correction (x : Vector 4) (v : Vector q)
    (hg : ContMDiffAt ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) ∞ g
      (SphereRadialRetraction.retract b x, v)) :
    ContDiffAt ℝ ∞ (correction χ b g) (x, v) := by
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (correction_eventuallyEq_zero χ b g (mem_ball_self χ.rIn_pos) v)
  · exact (contDiffAt_const.sub (χ.contDiff.contDiffAt.comp (x, v) contDiffAt_fst)).smul
      (GeneralRadialProduct.contDiffAt_pullback b g hx v hg)

end Wikipedia.HopfProblem.DegreeCollapse.GeneralRadialCorrection

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralRadialCorrection

open NoExoticSixSphere GLOrthonormalization

variable {q : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_correction_core (χ : ContDiffBump (0 : Vector 4)) (b : Sphere 3)
    (g : Sphere 3 × Vector q → F)
    (hgs : ∀ s : Sphere 3, ContMDiffAt ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) ∞ g (s, 0))
    (hg : ∀ s : Sphere 3, g (s, 0) = 0)
    (hzero : ∀ s : Sphere 3, mfderiv ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) g (s, 0) = 0)
    (x : Vector 4) : fderiv ℝ (correction χ b g) (x, 0) = 0 := by
  by_cases hx : x = 0
  · subst x
    rw [(correction_eventuallyEq_zero χ b g (mem_ball_self χ.rIn_pos) 0).fderiv_eq]
    simp
  · have hss : ContDiffAt ℝ ∞ (fun p : Vector 4 × Vector q ↦ 1 - χ p.1) (x, 0) :=
      contDiffAt_const.sub (χ.contDiff.contDiffAt.comp (x, (0 : Vector q)) contDiffAt_fst)
    have hs := hss.differentiableAt (by simp)
    have hG := (GeneralRadialProduct.contDiffAt_pullback b g hx 0
      (hgs (SphereRadialRetraction.retract b x))).differentiableAt (by simp)
    have hGj := GeneralRadialProduct.fderiv_pullback_eq_zero b g hx 0
      (hgs (SphereRadialRetraction.retract b x)) (hzero (SphereRadialRetraction.retract b x))
    have hG' := hG.hasFDerivAt
    rw [hGj] at hG'
    have he := (hs.hasFDerivAt.smul hG').fderiv
    change fderiv ℝ (correction χ b g) (x, 0) = _ at he
    simpa [GeneralRadialProduct.pullback, hg] using he

end Wikipedia.HopfProblem.DegreeCollapse.GeneralRadialCorrection
