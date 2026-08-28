import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFramedFiber
import Wikipedia.NoExoticSixSphere.ImmersedSphereFrameParity

/-!
# The actual three-sphere factors of the framed Hopf-square fiber

The factor maps land in the original regular-fiber atlas through its
existing product diffeomorphism. Smooth retractions prove both ordinary
and native differential injectivity. Their parities use the existing
geometric frame operator, including its source twist; no value is assigned.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberFactors

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

def left (r : Sphere 3) (q : Sphere 3) : Fiber := fiberDiffeomorph (q, r)

def right (q : Sphere 3) (r : Sphere 3) : Fiber := fiberDiffeomorph (q, r)

def leftRetraction (x : Fiber) : Sphere 3 := (fiberDiffeomorph.symm x).1

def rightRetraction (x : Fiber) : Sphere 3 := (fiberDiffeomorph.symm x).2

theorem contMDiff_left (r : Sphere 3) : ContMDiff (𝓡 3) (𝓡 6) ∞ (left r) :=
  fiberDiffeomorph.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

theorem contMDiff_right (q : Sphere 3) : ContMDiff (𝓡 3) (𝓡 6) ∞ (right q) :=
  fiberDiffeomorph.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)

theorem contMDiff_leftRetraction : ContMDiff (𝓡 6) (𝓡 3) ∞ leftRetraction :=
  contMDiff_fst.comp fiberDiffeomorph.symm.contMDiff

theorem contMDiff_rightRetraction : ContMDiff (𝓡 6) (𝓡 3) ∞ rightRetraction :=
  contMDiff_snd.comp fiberDiffeomorph.symm.contMDiff

theorem leftRetraction_left (r q : Sphere 3) : leftRetraction (left r q) = q :=
  congrArg Prod.fst (fiberDiffeomorph.symm_apply_apply (q, r))

theorem rightRetraction_right (q r : Sphere 3) : rightRetraction (right q r) = r :=
  congrArg Prod.snd (fiberDiffeomorph.symm_apply_apply (q, r))

theorem left_injective (r : Sphere 3) : Function.Injective (left r) :=
  (show Function.LeftInverse leftRetraction (left r) from leftRetraction_left r).injective

theorem right_injective (q : Sphere 3) : Function.Injective (right q) :=
  (show Function.LeftInverse rightRetraction (right q) from rightRetraction_right q).injective

theorem mfderiv_injective_of_retraction (f : Sphere 3 → Fiber) (r : Fiber → Sphere 3)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hr : ContMDiff (𝓡 6) (𝓡 3) ∞ r)
    (he : r ∘ f = id) (q : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 6) f q) := by
  have h := mfderiv_comp q (hr.mdifferentiable (by simp) (f q))
    (hf.mdifferentiable (by simp) q)
  rw [he, mfderiv_id] at h
  have hl : Function.LeftInverse (mfderiv (𝓡 6) (𝓡 3) r (f q))
      (mfderiv (𝓡 3) (𝓡 6) f q) := by
    intro v
    exact (congrArg (fun L : V 3 →L[ℝ] V 3 ↦ L v) h).symm
  exact hl.injective

theorem left_mfderiv_injective (r q : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 6) (left r) q) :=
  mfderiv_injective_of_retraction (left r) leftRetraction (contMDiff_left r)
    contMDiff_leftRetraction (funext (leftRetraction_left r)) q

theorem right_mfderiv_injective (q r : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 6) (right q) r) :=
  mfderiv_injective_of_retraction (right q) rightRetraction (contMDiff_right q)
    contMDiff_rightRetraction (funext (rightRetraction_right q)) r

theorem embedding_left (r q : Sphere 3) :
    embedding.toFun (left r q) = QuaternionicHopfInducedProductFrame.ambientInclusion (q, r) := rfl

theorem embedding_right (q r : Sphere 3) :
    embedding.toFun (right q r) = QuaternionicHopfInducedProductFrame.ambientInclusion (q, r) := rfl

def leftParity (a : Sphere 16) (r : Sphere 3) : ZMod 2 :=
  embedding.immersedSphereFrameParity (framing a) (left r) (contMDiff_left r)
    (left_mfderiv_injective r)

def rightParity (a : Sphere 16) (q : Sphere 3) : ZMod 2 :=
  embedding.immersedSphereFrameParity (framing a) (right q) (contMDiff_right q)
    (right_mfderiv_injective q)

theorem leftParity_eq_sphereParity (a : Sphere 16) (r : Sphere 3) :
    leftParity a r = embedding.sphereParity (framing a) (left r)
      (contMDiff_left r) (left_injective r) (left_mfderiv_injective r) :=
  embedding.immersedSphereFrameParity_eq_sphereParity (framing a) (left r)
    (contMDiff_left r) (left_mfderiv_injective r) (left_injective r)

theorem rightParity_eq_sphereParity (a : Sphere 16) (q : Sphere 3) :
    rightParity a q = embedding.sphereParity (framing a) (right q)
      (contMDiff_right q) (right_injective q) (right_mfderiv_injective q) :=
  embedding.immersedSphereFrameParity_eq_sphereParity (framing a) (right q)
    (contMDiff_right q) (right_mfderiv_injective q) (right_injective q)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberFactors
