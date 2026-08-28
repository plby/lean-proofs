import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardIdentification
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFrames

/-!
# The genuine canonical direct image is O(-infinity)

The actual O(U)-linear equivalences on every base open commute with the
literal restrictions, so they form an isomorphism of genuine sheaves.
The source is Mathlib's pushforward of sections of the original native
alternating-cotangent canonical bundle. The target is the previously
constructed literal ideal sheaf of holomorphic functions vanishing at
infinity, not a line carrying only a prescribed degree label.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The actual ideal-sheaf section object has the original ideal's
module structure over holomorphic functions on its open domain. -/
instance negativeOneSheaf_obj_baseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (negativeOneSheaf.obj.obj (op U)) :=
  inferInstanceAs (Module (Threefold.BaseSection U) (NegativeOneSection U))

/-- Native canonical descent as an isomorphism of actual presheaves. -/
def canonicalDirectImagePresheafIso :
    canonicalDirectImage.presheaf ≅ negativeOneSheaf.presheaf :=
  NatIso.ofComponents
    (fun U => (canonicalSectionIdealEquiv U.unop).toAddEquiv.toAddCommGrpIso)
    (by
      intro U V h
      ext s
      exact canonicalSectionIdealEquiv_restrict (leOfHom h.unop) s)

/-- The actual sheaf identity `f_* K_X ≃ O(-∞)`. Its component maps are
the proved O(U)-linear native descent and native reconstruction maps. -/
def canonicalDirectImageIso : canonicalDirectImage ≅ negativeOneSheaf :=
  ObjectProperty.isoMk _ canonicalDirectImagePresheafIso

@[simp] theorem canonicalDirectImageIso_hom_app (U : Opens RiemannSphere)
    (s : PreimageSection U) :
    canonicalDirectImageIso.hom.hom.app (op U) s = canonicalSectionIdealEquiv U s := rfl

@[simp] theorem canonicalDirectImageIso_inv_app (U : Opens RiemannSphere)
    (h : NegativeOneSection U) :
    canonicalDirectImageIso.inv.hom.app (op U) h = (canonicalSectionIdealEquiv U).symm h := rfl

/-- The categorical forward map preserves the actual structure-sheaf action. -/
theorem canonicalDirectImageIso_hom_app_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    canonicalDirectImageIso.hom.hom.app (op U) (f • s) =
      f • canonicalDirectImageIso.hom.hom.app (op U) s :=
  (canonicalSectionIdealEquiv U).map_smul f s

/-- The categorical inverse is O(U)-linear for actual native scalar multiplication. -/
theorem canonicalDirectImageIso_inv_app_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (h : NegativeOneSection U) :
    canonicalDirectImageIso.inv.hom.app (op U) (f • h) =
      f • canonicalDirectImageIso.inv.hom.app (op U) h :=
  (canonicalSectionIdealEquiv U).symm.map_smul f h

/-- Actual rank-one local trivializations of the canonical direct image
on every subopen of either fixed affine sphere chart. -/
def canonicalDirectImageLocalTrivialization (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    Threefold.BaseSection U ≃ₗ[Threefold.BaseSection U]
      canonicalDirectImage.obj.obj (op U) :=
  (NegativeOneFrames.chartTrivialization b U hU).trans (canonicalSectionIdealEquiv U).symm

/-- Every point has an actual neighborhood on all of whose subopens the
actual direct image is a free rank-one module over holomorphic functions. -/
theorem canonicalDirectImage_locally_free_rank_one (p : RiemannSphere) :
    ∃ b : Bool, p ∈ NegativeOneFrames.frameChart b ∧
      ∀ (U : Opens RiemannSphere) (_hU : U ≤ NegativeOneFrames.frameChart b),
        Nonempty (Threefold.BaseSection U ≃ₗ[Threefold.BaseSection U]
          canonicalDirectImage.obj.obj (op U)) := by
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact ⟨b, hb, fun U hU => ⟨canonicalDirectImageLocalTrivialization b U hU⟩⟩

/-- Unconditional canonical pushforward for the actual constructed threefold. -/
theorem directImage_canonical_bundle : Nonempty (canonicalDirectImage ≅ negativeOneSheaf) :=
  ⟨canonicalDirectImageIso⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward
