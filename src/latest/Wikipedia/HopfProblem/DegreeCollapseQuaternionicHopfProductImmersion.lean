import Wikipedia.HopfProblem.DegreeCollapseSphereSliceImmersion
import Wikipedia.HopfProblem.DegreeCollapseSpherePairingLocalDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfProductFiber

/-!
# The specified Hopf-square fiber is smoothly immersed in the original sphere

Compose the actual south Hopf fiber, the original suspension zero slice and
the original sphere pairing. The source is the standard product manifold
S3 × S3 with its product atlas.
-/

noncomputable section

open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductImmersion

open NoExoticSixSphere QuaternionicHopfSouthFiber SphereSliceImmersion
open SpherePairingLocalDiffeomorph

def suspendedInclusion : Sphere 3 → Sphere 8 :=
  ProductSphereFiber.slice 7 ∘ fiberPoint

theorem suspendedInclusion_ne_pole (q : Sphere 3) :
    suspendedInclusion q ≠ spherePole 8 := by
  intro h
  exact fiberPoint_ne_pole q ((ProductSphereFiber.slice_eq_pole_iff 7 (fiberPoint q)).mp h)

theorem contMDiff_suspendedInclusion :
    ContMDiff (𝓡 3) (𝓡 8) ∞ suspendedInclusion := by
  intro q
  exact (contMDiffAt_slice 7 (fiberPoint_ne_pole q)).comp q
    contMDiff_fiberPoint.contMDiffAt

theorem suspendedInclusion_mfderiv_injective (q : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 8) suspendedInclusion q) := by
  change Function.Injective (mfderiv (𝓡 3) (𝓡 8)
    (ProductSphereFiber.slice 7 ∘ fiberPoint) q)
  rw [mfderiv_comp q ((contMDiffAt_slice 7 (fiberPoint_ne_pole q)).mdifferentiableAt (by simp))
    (contMDiff_fiberPoint.mdifferentiable (by simp) q)]
  exact (slice_mfderiv_injective 7 (fiberPoint_ne_pole q)).comp
    (QuaternionicHopfSouthRegularity.fiberPoint_mfderiv_injective q)

def productInclusion : Sphere 3 × Sphere 3 → Sphere 8 × Sphere 8 :=
  Prod.map suspendedInclusion suspendedInclusion

theorem contMDiff_productInclusion :
    ContMDiff ((𝓡 3).prod (𝓡 3)) ((𝓡 8).prod (𝓡 8)) ∞ productInclusion :=
  contMDiff_suspendedInclusion.prodMap contMDiff_suspendedInclusion

theorem productInclusion_mfderiv_injective (p : Sphere 3 × Sphere 3) :
    Function.Injective (mfderiv ((𝓡 3).prod (𝓡 3)) ((𝓡 8).prod (𝓡 8))
      productInclusion p) := by
  change Function.Injective (mfderiv ((𝓡 3).prod (𝓡 3)) ((𝓡 8).prod (𝓡 8))
    (Prod.map suspendedInclusion suspendedInclusion) p)
  rw [mfderiv_prodMap (contMDiff_suspendedInclusion.mdifferentiable (by simp) p.1)
    (contMDiff_suspendedInclusion.mdifferentiable (by simp) p.2)]
  intro u v h
  exact Prod.ext (suspendedInclusion_mfderiv_injective p.1 (congrArg Prod.fst h))
    (suspendedInclusion_mfderiv_injective p.2 (congrArg Prod.snd h))

def fiberInclusion : Sphere 3 × Sphere 3 → Sphere 16 :=
  JamesSphere.pairing 8 ∘ productInclusion

theorem fiberInclusion_eq (p : Sphere 3 × Sphere 3) :
    fiberInclusion p = (QuaternionicHopfProductFiber.fiberHomeomorph p).val := rfl

theorem contMDiff_fiberInclusion :
    ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 16) ∞ fiberInclusion := by
  intro p
  exact (pairing_contMDiffAt 8 (suspendedInclusion_ne_pole p.1)
    (suspendedInclusion_ne_pole p.2)).comp p contMDiff_productInclusion.contMDiffAt

theorem fiberInclusion_mfderiv_injective (p : Sphere 3 × Sphere 3) :
    Function.Injective (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 16) fiberInclusion p) := by
  change Function.Injective (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 16)
    (JamesSphere.pairing 8 ∘ productInclusion) p)
  rw [mfderiv_comp p
    ((pairing_contMDiffAt 8 (suspendedInclusion_ne_pole p.1)
      (suspendedInclusion_ne_pole p.2)).mdifferentiableAt (by simp))
    (contMDiff_productInclusion.mdifferentiable (by simp) p)]
  exact (pairing_mfderiv_bijective 8 (suspendedInclusion_ne_pole p.1)
    (suspendedInclusion_ne_pole p.2)).injective.comp (productInclusion_mfderiv_injective p)

theorem fiberInclusion_injective : Function.Injective fiberInclusion := by
  intro p q h
  exact QuaternionicHopfProductFiber.fiberHomeomorph.injective (Subtype.ext h)

theorem fiberInclusion_range (x : Sphere 16) :
    SphereSmash.squareMap QuaternionicHopf.suspendedMap x = QuaternionicHopfProductFiber.point ↔
      ∃ p, fiberInclusion p = x :=
  QuaternionicHopfProductFiber.square_fiber_range x

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductImmersion

