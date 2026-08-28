import Wikipedia.HopfProblem.CuspNormalizationSheafReducedSheaf
import Mathlib.Topology.Sheaves.Functors

/-!
# Actual ambient restriction to the reduced holomorphic-function sheaf

The subset inclusion is the actual continuous inclusion. Pulling back
an ambient holomorphic section means restricting its actual function
to the inverse-image open set. This gives a genuine morphism from the
ambient holomorphic-function sheaf to the pushforward of the reduced
holomorphic-function sheaf of the subset.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- The actual continuous inclusion of the subset in its ambient space. -/
def subsetInclusion : TopCat.of S ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem subsetInclusion_apply (x : S) : subsetInclusion S x = x.val := rfl

/-- The actual inverse-image relative open set. -/
def ambientOpen (V : Opens M) : Opens S := (Opens.map (subsetInclusion S)).obj V

@[simp] theorem mem_ambientOpen (V : Opens M) (x : S) :
    x ∈ ambientOpen S V ↔ x.val ∈ V := Iff.rfl

/-- Literal restriction of an actual ambient holomorphic section. -/
def ambientRestriction (V : Opens M) :
    HolomorphicFunctionSheaf.Section I M V →+* Section I S (ambientOpen S V) where
  toFun g :=
    ⟨fun x => g ⟨x.val.val, x.property⟩,
      IsLocallyAmbient.of_ambient I S (ambientOpen S V) V g (fun x => x.property)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem ambientRestriction_apply (V : Opens M)
    (g : HolomorphicFunctionSheaf.Section I M V) (x : ambientOpen S V) :
    ambientRestriction I S V g x = g ⟨x.val.val, x.property⟩ := rfl

@[simp] theorem ambientRestriction_constant (V : Opens M) (c : ℂ) :
    ambientRestriction I S V (algebraMap ℂ
      (HolomorphicFunctionSheaf.Section I M V) c) = constant I S (ambientOpen S V) c := rfl

/-- Ambient restriction is a homomorphism of the actual complex algebras. -/
def ambientRestrictionAlgHom (V : Opens M) :
    HolomorphicFunctionSheaf.Section I M V →ₐ[ℂ] Section I S (ambientOpen S V) where
  __ := ambientRestriction I S V
  commutes' _ := rfl

/-- The actual restriction maps form a morphism of presheaves. -/
def ambientPullbackPresheaf : HolomorphicFunctionSheaf.presheaf I M ⟶
    (TopCat.Presheaf.pushforward CommRingCat (subsetInclusion S)).obj (presheaf I S) where
  app V := CommRingCat.ofHom (ambientRestriction I S V.unop)
  naturality _ _ _ := rfl

/-- The genuine ambient-to-reduced restriction morphism of sheaves. -/
def ambientPullback : HolomorphicFunctionSheaf.sheaf I M ⟶
    (TopCat.Sheaf.pushforward CommRingCat (subsetInclusion S)).obj (sheaf I S) :=
  ObjectProperty.homMk (ambientPullbackPresheaf I S)

@[simp] theorem ambientPullback_apply (V : Opens M)
    (g : HolomorphicFunctionSheaf.Section I M V) (x : ambientOpen S V) :
    (((ambientPullback I S).hom.app (op V) g :
      Section I S (ambientOpen S V)).val x) = g ⟨x.val.val, x.property⟩ := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
