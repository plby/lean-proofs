import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardBaseIdealLinear

/-!
# The genuine native base-line section sheaf is the negative-one ideal sheaf

On every original sphere open the proved section equivalence is linear
over its actual holomorphic function ring.  Its compatibility with
literal restriction gives an isomorphism of the actual additive sheaves.
The source remains the holomorphic-section sheaf of the independently
constructed original native base-twist bundle, with its original charts.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal

open HolomorphicFunctionSheaf.SphereH1

/-- The actual section-module identifications assemble naturally on
all original sphere opens, not only on the two large affine charts. -/
def presheafIso :
    NativeBundleSections.presheaf CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ) ≅
      negativeOnePresheaf :=
  NatIso.ofComponents
    (fun U => (sectionLinearEquiv U.unop).toAddEquiv.toAddCommGrpIso)
    (by
      intro U V h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (sectionLinearEquiv_restrict (leOfHom h.unop) s).symm)

/-- The original native base-twist holomorphic section sheaf is
genuinely isomorphic to the actual ideal sheaf of infinity. -/
def sheafIso :
    NativeBundleSections.sheaf CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ) ≅
      negativeOneSheaf :=
  ObjectProperty.isoMk _ presheafIso

@[simp] theorem sheafIso_hom_app (U : Opens RiemannSphere) (s : BundleSection U) :
    sheafIso.hom.hom.app (op U) s = sectionLinearEquiv U s := rfl

@[simp] theorem sheafIso_inv_app (U : Opens RiemannSphere) (f : NegativeOneSection U) :
    sheafIso.inv.hom.app (op U) f = (sectionLinearEquiv U).symm f := rfl

/-- The sheaf comparison has the exact original native-chart formula. -/
theorem sheafIso_hom_app_value (U : Opens RiemannSphere) (s : BundleSection U)
    (b : Bool) (p : U) (hp : (p : RiemannSphere) ∈ NegativeOneFrames.frameChart b) :
    (sheafIso.hom.hom.app (op U) s : NegativeOneSection U).val p =
      (CanonicalGlobal.BaseTwist.bundle.localTriv b ⟨(p : RiemannSphere), s p⟩).2 *
        CanonicalGlobal.BaseTwist.idealFrameValue b p :=
  sectionLinearEquiv_value U s b p hp

/-- Every forward component is linear over the actual holomorphic
functions on that original open set. -/
theorem sheafIso_hom_app_smul (U : Opens RiemannSphere)
    (r : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (s : BundleSection U) :
    id (α := NegativeOneSection U) (sheafIso.hom.hom.app (op U) (r • s)) =
      r • id (α := NegativeOneSection U) (sheafIso.hom.hom.app (op U) s) :=
  (sectionLinearEquiv U).map_smul r s

theorem sheafIso_inv_app_smul (U : Opens RiemannSphere)
    (r : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (f : NegativeOneSection U) :
    id (α := BundleSection U) (sheafIso.inv.hom.app (op U) (r • f)) =
      r • id (α := BundleSection U) (sheafIso.inv.hom.app (op U) f) :=
  (sectionLinearEquiv U).symm.map_smul r f

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal
