import Wikipedia.NoExoticSixSphere.SphereRadialProduct
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A smooth supported radial correction on the disk product

An outer cutoff makes the radial pullback vanish near the disk center and
equal its prescribed sphere-product value near the boundary. Smoothness at
the center follows from an actual zero germ, not from radial retraction there.
-/

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RadialCollarCorrection

open GLOrthonormalization

variable {q : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (χ : ContDiffBump (0 : Vector 4)) (b : Sphere 3) (g : Sphere 3 × Vector q → F)

def correction (p : Vector 4 × Vector q) : F :=
  (1 - χ p.1) • SphereRadialProduct.pullback b g p

theorem correction_eq_zero {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) χ.rIn)
    (v : Vector q) : correction χ b g (x, v) = 0 := by
  simp only [correction, χ.one_of_mem_closedBall hx, sub_self, zero_smul]

theorem correction_eq_radial {x : Vector 4} (hx : χ.rOut ≤ ‖x‖) (v : Vector q) :
    correction χ b g (x, v) = g (SphereRadialRetraction.retract b x, v) := by
  have hχ : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
  simp only [correction, hχ, sub_zero, one_smul, SphereRadialProduct.pullback]

theorem correction_eventuallyEq_zero {x : Vector 4} (hx : x ∈ ball (0 : Vector 4) χ.rIn)
    (v : Vector q) : correction χ b g =ᶠ[𝓝 (x, v)] (fun _ ↦ 0) := by
  have hf : ContinuousAt (Prod.fst : Vector 4 × Vector q → Vector 4) (x, v) :=
    continuous_fst.continuousAt
  filter_upwards [hf.eventually (χ.eventuallyEq_one_of_mem_ball hx)] with p hp
  simp only [correction, hp, Pi.one_apply, sub_self, zero_smul]

theorem correction_core (hg : ∀ s : Sphere 3, g (s, 0) = 0) (x : Vector 4) :
    correction χ b g (x, 0) = 0 := by
  simp only [correction, SphereRadialProduct.pullback, hg, smul_zero]

theorem contDiffAt_correction (x : Vector 4) (v : Vector q)
    (hg : ContMDiffAt ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) ∞ g
      (SphereRadialRetraction.retract b x, v)) :
    ContDiffAt ℝ ∞ (correction χ b g) (x, v) := by
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (correction_eventuallyEq_zero χ b g (mem_ball_self χ.rIn_pos) v)
  · exact (contDiffAt_const.sub (χ.contDiff.contDiffAt.comp (x, v) contDiffAt_fst)).smul
      (SphereRadialProduct.contDiffAt_pullback b g hx v hg)

end NoExoticSixSphere.RadialCollarCorrection
