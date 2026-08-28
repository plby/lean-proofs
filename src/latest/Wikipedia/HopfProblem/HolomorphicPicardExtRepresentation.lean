import Wikipedia.HopfProblem.HolomorphicPicardExtPullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Every degree-one Ext class is represented by an actual extension

Choose an injective presentation `A ⟶ I`.  The cokernel sequence gives a
surjective connecting map `Hom(B, cokernel(A ⟶ I)) ⟶ Ext(B,A,1)`, since
positive-degree Ext into `I` vanishes.  Pulling the actual cokernel sequence
back along a preimage represents the given class.  No Yoneda classification
or extension-representability hypothesis is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The actual cokernel sequence of the chosen injective presentation. -/
abbrev injectivePresentationComplex (A : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A))
    (cokernel.condition (Injective.ι A))

/-- The monomorphism into the chosen injective and its actual cokernel form
a genuine short exact sequence. -/
theorem injectivePresentationComplex_shortExact (A : C) :
    (injectivePresentationComplex A).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι A)) }

variable [HasExt.{w} C] {A B : C}

/-- Surjectivity of the actual degree-zero connecting homomorphism from an
injective presentation, proved by the long exact Ext sequence. -/
theorem exists_injectivePresentation_connecting_morphism (ξ : Ext.{w} B A 1) :
    ∃ a : B ⟶ cokernel (Injective.ι A),
      (Ext.mk₀ a).comp (injectivePresentationComplex_shortExact A).extClass (zero_add 1) =
        ξ := by
  have hz : ξ.comp (Ext.mk₀ (injectivePresentationComplex A).f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨η, hη⟩ := Ext.covariant_sequence_exact₁ B
    (injectivePresentationComplex_shortExact A) ξ hz (rfl : 0 + 1 = 1)
  refine ⟨Ext.homEquiv₀ η, ?_⟩
  rw [Ext.mk₀_homEquiv₀_apply]
  exact hη

/-- A genuine morphism whose connecting class is the prescribed Ext class. -/
def injectivePresentationConnectingMorphism (ξ : Ext.{w} B A 1) :
    B ⟶ cokernel (Injective.ι A) :=
  (exists_injectivePresentation_connecting_morphism ξ).choose

theorem injectivePresentationConnectingMorphism_spec (ξ : Ext.{w} B A 1) :
    (Ext.mk₀ (injectivePresentationConnectingMorphism ξ)).comp
      (injectivePresentationComplex_shortExact A).extClass (zero_add 1) = ξ :=
  (exists_injectivePresentation_connecting_morphism ξ).choose_spec

/-- An actual short complex with literal endpoints `A` and `B` representing
the prescribed class. Its middle object is a categorical pullback. -/
abbrev representativeComplex (ξ : Ext.{w} B A 1) : ShortComplex C :=
  pullbackComplex (injectivePresentationComplex A) (injectivePresentationConnectingMorphism ξ)

/-- The representative is genuinely short exact. -/
theorem representativeComplex_shortExact (ξ : Ext.{w} B A 1) :
    (representativeComplex ξ).ShortExact :=
  pullbackComplex_shortExact (injectivePresentationComplex_shortExact A)
    (injectivePresentationConnectingMorphism ξ)

/-- Its actual derived-category extension class is precisely the given class. -/
theorem representativeComplex_extClass (ξ : Ext.{w} B A 1) :
    (representativeComplex_shortExact ξ).extClass = ξ :=
  (pullbackComplex_extClass (injectivePresentationComplex_shortExact A)
    (injectivePresentationConnectingMorphism ξ)).trans
      (injectivePresentationConnectingMorphism_spec ξ)

/-- Every degree-one Ext class is the class of an actual short exact sequence
whose endpoints are literally the prescribed objects. -/
theorem exists_shortExact_extClass (ξ : Ext.{w} B A 1) :
    ∃ (E : C) (i : A ⟶ E) (p : E ⟶ B) (hzero : i ≫ p = 0),
      ∃ hS : (ShortComplex.mk i p hzero).ShortExact, hS.extClass = ξ := by
  refine ⟨(representativeComplex ξ).X₂, (representativeComplex ξ).f,
    (representativeComplex ξ).g, (representativeComplex ξ).zero,
    representativeComplex_shortExact ξ, ?_⟩
  exact representativeComplex_extClass ξ

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
