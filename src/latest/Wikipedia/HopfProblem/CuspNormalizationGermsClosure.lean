import Wikipedia.HopfProblem.CuspNormalizationGermsFinite
import Wikipedia.HopfProblem.CuspNormalizationGermsFractionsMaps
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closure inside the actual product of branch fraction rings

An integral element in the product of branch fraction rings is integral
in each coordinate after mapping its monic equation to that branch ring.
If the branch rings are integrally closed, every coordinate is therefore
the canonical image of a branch-ring element. Conversely, surjectivity
onto the finitely many coordinates makes the product integral over the
actual image subring, by the proved finite-module result.

Thus the product of the branch rings is the actual integral closure in
the product of their fraction rings, with its canonical inclusion. The
normality hypotheses remain explicit here. Separating elements are not
needed for this statement; they enter the separate proof identifying the
ambient product with the genuine total fraction ring of the image.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.CuspNormalization.GermsClosure

open GermsFractions

universe u v

variable {I : Type u} (B : I → Type v) [∀ i, CommRing (B i)]
  (A : Subring (∀ i, B i))

attribute [local instance] productFractionAlgebra

/-- Mapping an actual monic equation through a coordinate projection
gives integrality over that branch ring. -/
theorem isIntegral_coordinate {x : ∀ i, FractionRing (B i)}
    (hx : IsIntegral A x) (i : I) : IsIntegral (B i) (x i) :=
  IsIntegral.map_of_comp_eq ((Pi.evalRingHom B i).comp A.subtype)
    (Pi.evalRingHom (fun i => FractionRing (B i)) i) (by ext a; rfl) hx

/-- Every canonical product element is integral over the actual subring
when its finitely many coordinate restrictions are surjective. -/
theorem productFractionMap_isIntegral [Finite I]
    (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i)) (b : ∀ i, B i) :
    IsIntegral A (productFractionMap B b) := by
  let := GermsFinite.subring_moduleFinite B A hsurj
  exact IsIntegral.map_of_comp_eq (RingHom.id A) (productFractionMap B)
    (by ext a; rfl) (IsIntegral.of_finite A b)

/-- The canonical product map lands in the literal integral-closure
subalgebra, before any normality hypothesis is imposed. -/
def productToIntegralClosure [Finite I]
    (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i)) :
    (∀ i, B i) →ₐ[A] integralClosure A (∀ i, FractionRing (B i)) where
  toFun b := ⟨productFractionMap B b, productFractionMap_isIntegral B A hsurj b⟩
  map_one' := Subtype.ext (map_one (productFractionMap B))
  map_mul' b c := Subtype.ext (map_mul (productFractionMap B) b c)
  map_zero' := Subtype.ext (map_zero (productFractionMap B))
  map_add' b c := Subtype.ext (map_add (productFractionMap B) b c)
  commutes' _ := Subtype.ext rfl

variable [∀ i, IsIntegrallyClosed (B i)]

/-- Branch integral closedness puts every coordinate of an integral
element back in its original ring, without a finite-index assumption. -/
theorem exists_product_of_isIntegral {x : ∀ i, FractionRing (B i)} (hx : IsIntegral A x) :
    ∃ b : ∀ i, B i, productFractionMap B b = x := by
  choose b hb using fun i =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_coordinate B A hx i)
  exact ⟨b, funext hb⟩

variable [Finite I]
  (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i))

include hsurj

/-- The actual integral elements are exactly the canonical images of
the product of the original integrally closed branch rings. -/
theorem isIntegral_iff_exists_product (x : ∀ i, FractionRing (B i)) :
    IsIntegral A x ↔ ∃ b : ∀ i, B i, productFractionMap B b = x :=
  ⟨exists_product_of_isIntegral B A,
    by rintro ⟨b, rfl⟩; exact productFractionMap_isIntegral B A hsurj b⟩

/-- Coordinatewise membership characterizes the actual integral closure. -/
theorem isIntegral_iff_coordinate_mem (x : ∀ i, FractionRing (B i)) :
    IsIntegral A x ↔ ∀ i, x i ∈ range (algebraMap (B i) (FractionRing (B i))) := by
  rw [isIntegral_iff_exists_product B A hsurj]
  constructor
  · rintro ⟨b, rfl⟩ i
    exact ⟨b i, rfl⟩
  · intro hx
    choose b hb using hx
    exact ⟨b, funext hb⟩

/-- The actual product, with the actual coordinatewise fraction map,
satisfies mathlib's integral-closure predicate. -/
theorem product_isIntegralClosure :
    IsIntegralClosure (∀ i, B i) A (∀ i, FractionRing (B i)) where
  algebraMap_injective := productFractionMap_injective B
  isIntegral_iff {x} := isIntegral_iff_exists_product B A hsurj x

omit [∀ i, IsIntegrallyClosed (B i)] in
theorem productToIntegralClosure_injective :
    Injective (productToIntegralClosure B A hsurj) := by
  intro b c h
  exact productFractionMap_injective B (congrArg Subtype.val h)

theorem productToIntegralClosure_surjective :
    Surjective (productToIntegralClosure B A hsurj) := by
  intro x
  obtain ⟨b, hb⟩ := exists_product_of_isIntegral B A x.property
  exact ⟨b, Subtype.ext hb⟩

/-- The product is canonically the literal integral-closure subalgebra,
as an algebra over the actual image subring. -/
def productIntegralClosureEquiv :
    (∀ i, B i) ≃ₐ[A] integralClosure A (∀ i, FractionRing (B i)) :=
  AlgEquiv.ofBijective (productToIntegralClosure B A hsurj)
    ⟨productToIntegralClosure_injective B A hsurj,
      productToIntegralClosure_surjective B A hsurj⟩

/-- The integral-closure comparison is the actual coordinatewise
canonical fraction map after inclusion in the ambient product. -/
@[simp] theorem productIntegralClosureEquiv_coe (b : ∀ i, B i) :
    (productIntegralClosureEquiv B A hsurj b : ∀ i, FractionRing (B i)) =
      productFractionMap B b := rfl

@[simp] theorem productIntegralClosureEquiv_apply (b : ∀ i, B i) (i : I) :
    (productIntegralClosureEquiv B A hsurj b : ∀ i, FractionRing (B i)) i =
      algebraMap (B i) (FractionRing (B i)) (b i) :=
  congrFun (productIntegralClosureEquiv_coe B A hsurj b) i

end Wikipedia.HopfProblem.CuspNormalization.GermsClosure
