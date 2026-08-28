import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# Pulling a sphere-product map back by radial retraction

Away from the origin the pullback is smooth. A zero native derivative of the
original map gives a zero ordinary derivative of its radial pullback, using
the actual manifold chain rule and the unchanged transverse coordinate.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereRadialProduct

open GLOrthonormalization

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

end NoExoticSixSphere.SphereRadialProduct
