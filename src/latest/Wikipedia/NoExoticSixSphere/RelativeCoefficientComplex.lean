import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps
import Wikipedia.HopfProblem.SphereHomologyCoefficientsChainsFunctor
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Actual relative singular complexes with arbitrary integral coefficient objects

The subspace inclusion is sent to a monomorphism by Mathlib's singular-chain
functor for every coefficient object. We take its actual cokernel and
construct coefficient-change maps. At the integral coefficient object this
is exactly the previously constructed relative complex.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.RelativeCoefficients

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual coefficient singular-chain map of a continuous map. -/
abbrev spaceMap (A : ModuleCat.{0} ℤ) (f : C(X, Y)) :
    coefficientComplex A X ⟶ coefficientComplex A Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj A).map (TopCat.ofHom f)

/-- The original inclusion of the actual subspace, with the specified coefficients. -/
abbrev inclusion (A : ModuleCat.{0} ℤ) (U : Set X) :
    coefficientComplex A U ⟶ coefficientComplex A X :=
  spaceMap A (subtypeInclusion U)

instance inclusion_mono (A : ModuleCat.{0} ℤ) (U : Set X) : Mono (inclusion A U) := by
  have : Mono (TopCat.ofHom (subtypeInclusion U)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact inferInstanceAs (Mono
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj A).map
      (TopCat.ofHom (subtypeInclusion U))))

/-- The genuine relative singular-chain complex with this coefficient object. -/
abbrev complex (A : ModuleCat.{0} ℤ) (U : Set X) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (inclusion A U)

def projection (A : ModuleCat.{0} ℤ) (U : Set X) : coefficientComplex A X ⟶ complex A U :=
  cokernel.π (inclusion A U)

def sequence (A : ModuleCat.{0} ℤ) (U : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (inclusion A U) (projection A U) (cokernel.condition _)

theorem sequence_shortExact (A : ModuleCat.{0} ℤ) (U : Set X) :
    (sequence A U).ShortExact where
  exact := ShortComplex.exact_cokernel (inclusion A U)
  mono_f := inclusion_mono A U
  epi_g := inferInstanceAs (Epi (cokernel.π (inclusion A U)))

/-- This is literally the previously constructed relative integral complex. -/
theorem complex_int (U : Set X) :
    complex (ModuleCat.of ℤ ℤ) U = RelativeSingularHomology.complex U := rfl

/-- Native coefficient change commutes with the original subspace inclusion. -/
theorem inclusion_change {A B : ModuleCat.{0} ℤ} (r : A ⟶ B) (U : Set X) :
    inclusion A U ≫ coefficientComplexMap r X = coefficientComplexMap r U ≫ inclusion B U :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).map r).naturality
    (TopCat.ofHom (subtypeInclusion U))

/-- Change of coefficients on the actual relative singular complex. -/
def change {A B : ModuleCat.{0} ℤ} (r : A ⟶ B) (U : Set X) : complex A U ⟶ complex B U :=
  cokernel.map (inclusion A U) (inclusion B U) (coefficientComplexMap r U)
    (coefficientComplexMap r X) (inclusion_change r U)

@[reassoc]
theorem projection_change {A B : ModuleCat.{0} ℤ} (r : A ⟶ B) (U : Set X) :
    projection A U ≫ change r U = coefficientComplexMap r X ≫ projection B U :=
  cokernel.π_desc _ _ _

theorem coefficientMap_id (A : ModuleCat.{0} ℤ) :
    coefficientComplexMap (𝟙 A) X = 𝟙 (coefficientComplex A X) :=
  (nativeCoefficientFunctor X).map_id A

theorem coefficientMap_comp {A B D : ModuleCat.{0} ℤ} (r : A ⟶ B) (s : B ⟶ D) :
    coefficientComplexMap (r ≫ s) X = coefficientComplexMap r X ≫ coefficientComplexMap s X :=
  (nativeCoefficientFunctor X).map_comp r s

theorem coefficientMap_add {A B : ModuleCat.{0} ℤ} (r s : A ⟶ B) :
    coefficientComplexMap (r + s) X = coefficientComplexMap r X + coefficientComplexMap s X :=
  (nativeCoefficientFunctor X).map_add

theorem change_id (A : ModuleCat.{0} ℤ) (U : Set X) : change (𝟙 A) U = 𝟙 (complex A U) := by
  apply (cancel_epi (cokernel.π (inclusion A U))).mp
  change projection A U ≫ _ = projection A U ≫ _
  rw [projection_change, Category.comp_id, coefficientMap_id, Category.id_comp]

theorem change_comp {A B D : ModuleCat.{0} ℤ} (r : A ⟶ B) (s : B ⟶ D) (U : Set X) :
    change (r ≫ s) U = change r U ≫ change s U := by
  apply (cancel_epi (cokernel.π (inclusion A U))).mp
  change projection A U ≫ _ = projection A U ≫ _
  rw [projection_change, ← Category.assoc, projection_change, Category.assoc, projection_change]
  rw [coefficientMap_comp, Category.assoc]

/-- Coefficient change is a functor on the original relative complexes. -/
def functor (U : Set X) : ModuleCat.{0} ℤ ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ where
  obj A := complex A U
  map r := change r U
  map_id A := change_id A U
  map_comp r s := change_comp r s U

theorem change_add {A B : ModuleCat.{0} ℤ} (r s : A ⟶ B) (U : Set X) :
    change (r + s) U = change r U + change s U := by
  apply (cancel_epi (cokernel.π (inclusion A U))).mp
  change projection A U ≫ _ = projection A U ≫ _
  rw [projection_change, Preadditive.comp_add, projection_change, projection_change]
  rw [coefficientMap_add, Preadditive.add_comp]

instance functor_additive (U : Set X) : (functor U).Additive where
  map_add := by intros; exact change_add _ _ U

/-- The map of native coefficient sequences obtained from the actual subspace inclusion. -/
abbrev inclusionSequenceMap (S : ShortComplex (ModuleCat.{0} ℤ)) (U : Set X) :
    S.map (nativeCoefficientFunctor U) ⟶ S.map (nativeCoefficientFunctor X) where
  τ₁ := inclusion S.X₁ U
  τ₂ := inclusion S.X₂ U
  τ₃ := inclusion S.X₃ U
  comm₁₂ := inclusion_change S.f U
  comm₂₃ := inclusion_change S.g U

end NoExoticSixSphere.RelativeCoefficients
