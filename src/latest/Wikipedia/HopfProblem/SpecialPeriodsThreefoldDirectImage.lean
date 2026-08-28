import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDescentHolomorphic
import Mathlib.Topology.Sheaves.Functors

/-!
# The actual direct image of the holomorphic function sheaf

For the constructed sphere projection, actual holomorphic pullback is
an isomorphism on every open-set section algebra and commutes with
restrictions. It therefore identifies the genuine sheaf `f_* O_X` with
`O_{P¹}`. The inverse is the uniquely determined holomorphic descent
proved using actual fibres, the regular zero section, and removability.

No Stein factorization, Grauert theorem, higher-direct-image formula,
or sheaf-cohomology vanishing is assumed in this result.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual continuous sphere projection as a morphism of spaces. -/
def sphereProjectionMap : TopCat.of Space ⟶ TopCat.of RiemannSphere :=
  TopCat.ofHom ⟨projectionSphere, projectionSphere_continuous⟩

abbrev sphereHolomorphicSheaf := HolomorphicFunctionSheaf.sheaf 𝓘(ℂ) RiemannSphere

abbrev totalHolomorphicSheaf := HolomorphicFunctionSheaf.sheaf IF Space

/-- Mathlib's actual sheaf pushforward along the constructed map. -/
def holomorphicDirectImage : TopCat.Sheaf CommRingCat (TopCat.of RiemannSphere) :=
  (TopCat.Sheaf.pushforward CommRingCat sphereProjectionMap).obj totalHolomorphicSheaf

/-- The component isomorphisms are actual pullback of holomorphic
functions, and their naturality is literal restriction compatibility. -/
def holomorphicDirectImagePresheafIso :
    sphereHolomorphicSheaf.presheaf ≅ holomorphicDirectImage.presheaf :=
  NatIso.ofComponents
    (fun U => (pullbackSectionEquiv U.unop).toRingEquiv.toCommRingCatIso)
    (by
      intro U V h
      ext f
      rfl)

/-- The actual sheaf identity `O_{P¹} ≅ f_* O_X`. Its forward map is
the genuine holomorphic pullback, not an abstract section marking. -/
def holomorphicDirectImageIso : sphereHolomorphicSheaf ≅ holomorphicDirectImage :=
  ObjectProperty.isoMk _ holomorphicDirectImagePresheafIso

@[simp] theorem holomorphicDirectImageIso_hom_app (U : Opens RiemannSphere)
    (f : BaseSection U) :
    holomorphicDirectImageIso.hom.hom.app (op U) f = pullbackSection U f := rfl

@[simp] theorem holomorphicDirectImageIso_inv_app (U : Opens RiemannSphere)
    (f : PreimageSection U) (b : U) :
    holomorphicDirectImageIso.inv.hom.app (op U) f b = descendedFunction U f b := by
  change (pullbackSectionEquiv U).symm f b = descendedFunction U f b
  rw [pullbackSectionEquiv_symm_apply]
  rfl

/-- The source's direct-image assertion for the actual constructed
threefold and actual holomorphic sheaves, with no existence inputs. -/
theorem directImage_holomorphic_functions :
    Nonempty (holomorphicDirectImage ≅ sphereHolomorphicSheaf) :=
  ⟨holomorphicDirectImageIso.symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
