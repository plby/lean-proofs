import Wikipedia.HopfProblem.CuspNormalizationGermsFractionsMaps
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Integral closure inside the source's actual total fraction ring

Suppose a finite ring map to a product of integrally closed rings extends
to a compatible isomorphism of actual total fraction rings.  The product
then is the integral closure inside the original source's fraction ring.
The embedding is explicitly the coordinatewise fraction map followed by
the inverse of the given fraction-ring isomorphism.

Both directions map actual monic equations through compatible ring maps.
There are no domain or finite-index assumptions: the finite ring map is
exactly what the integrality direction requires.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.CuspNormalization.GermsClosure

open GermsFractions

universe u v w

variable {I : Type u} (B : I → Type v) [∀ i, CommRing (B i)]
  {R : Type w} [CommRing R]

/-- The actual product of branch rings embedded in the original total
fraction ring through the given compatible fraction-ring comparison. -/
def totalProductMap (e : FractionRing R ≃+* ∀ i, FractionRing (B i)) :
    (∀ i, B i) →+* FractionRing R :=
  e.symm.toRingHom.comp (productFractionMap B)

@[simp] theorem totalProductMap_apply
    (e : FractionRing R ≃+* ∀ i, FractionRing (B i)) (b : ∀ i, B i) :
    totalProductMap B e b = e.symm (productFractionMap B b) := rfl

@[simp] theorem totalProductMap_e
    (e : FractionRing R ≃+* ∀ i, FractionRing (B i)) (b : ∀ i, B i) :
    e (totalProductMap B e b) = productFractionMap B b :=
  e.apply_symm_apply _

theorem totalProductMap_injective
    (e : FractionRing R ≃+* ∀ i, FractionRing (B i)) :
    Injective (totalProductMap B e) :=
  e.symm.injective.comp (productFractionMap_injective B)

section Comparison

variable (σ : R →+* ∀ i, B i)
  (e : FractionRing R ≃+* ∀ i, FractionRing (B i))
  (he : ∀ r, e (algebraMap R (FractionRing R) r) = productFractionMap B (σ r))

include he

@[simp] theorem totalProductMap_sigma (r : R) :
    totalProductMap B e (σ r) = algebraMap R (FractionRing R) r := by
  change e.symm (productFractionMap B (σ r)) = algebraMap R (FractionRing R) r
  rw [← he r]
  exact e.symm_apply_apply _

/-- The embedding extends the actual original ring map. -/
theorem totalProductMap_comp_sigma :
    (totalProductMap B e).comp σ = algebraMap R (FractionRing R) := by
  ext r
  exact totalProductMap_sigma B σ e he r

/-- Coordinate projection carries an actual monic equation over the
source ring to one over the corresponding branch ring. -/
theorem total_isIntegral_coordinate {x : FractionRing R} (hx : IsIntegral R x) (i : I) :
    IsIntegral (B i) (e x i) :=
  IsIntegral.map_of_comp_eq ((Pi.evalRingHom B i).comp σ)
    ((Pi.evalRingHom (fun i => FractionRing (B i)) i).comp e.toRingHom)
    (by ext r; exact (congrFun (he r) i).symm) hx

/-- Integral closedness in each actual branch fraction ring reconstructs
an element of the original product. -/
theorem total_exists_product_of_isIntegral [∀ i, IsIntegrallyClosed (B i)]
    {x : FractionRing R} (hx : IsIntegral R x) :
    ∃ b : ∀ i, B i, totalProductMap B e b = x := by
  choose b hb using fun i =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (total_isIntegral_coordinate B σ e he hx i)
  refine ⟨b, e.injective ?_⟩
  rw [totalProductMap_e]
  exact funext hb

end Comparison

section Finite

variable (σ : R →+* ∀ i, B i) (hσ : σ.Finite)
  (e : FractionRing R ≃+* ∀ i, FractionRing (B i))
  (he : ∀ r, e (algebraMap R (FractionRing R) r) = productFractionMap B (σ r))

include hσ he

/-- Every product element is integral in the original total fraction
ring, since the actual product ring map is finite. -/
theorem totalProductMap_isIntegral (b : ∀ i, B i) :
    IsIntegral R (totalProductMap B e b) := by
  let : Algebra R (∀ i, B i) := σ.toAlgebra
  let : Module.Finite R (∀ i, B i) := hσ
  exact IsIntegral.map_of_comp_eq (RingHom.id R) (totalProductMap B e)
    (by ext r; exact (totalProductMap_sigma B σ e he r).symm) (IsIntegral.of_finite R b)

/-- The literal embedding into the integral-closure subalgebra. -/
def totalProductToIntegralClosure :
    (∀ i, B i) →+* integralClosure R (FractionRing R) where
  toFun b := ⟨totalProductMap B e b, totalProductMap_isIntegral B σ hσ e he b⟩
  map_one' := Subtype.ext (map_one (totalProductMap B e))
  map_mul' b c := Subtype.ext (map_mul (totalProductMap B e) b c)
  map_zero' := Subtype.ext (map_zero (totalProductMap B e))
  map_add' b c := Subtype.ext (map_add (totalProductMap B e) b c)

@[simp] theorem totalProductToIntegralClosure_coe (b : ∀ i, B i) :
    (totalProductToIntegralClosure B σ hσ e he b : FractionRing R) =
      totalProductMap B e b := rfl

theorem totalProductToIntegralClosure_injective :
    Injective (totalProductToIntegralClosure B σ hσ e he) := by
  intro b c h
  exact totalProductMap_injective B e (congrArg Subtype.val h)

variable [∀ i, IsIntegrallyClosed (B i)]

/-- The integral elements in the source's actual total fraction ring
are exactly the images of the original branch-ring product. -/
theorem totalProduct_isIntegral_iff (x : FractionRing R) :
    IsIntegral R x ↔ ∃ b : ∀ i, B i, totalProductMap B e b = x :=
  ⟨total_exists_product_of_isIntegral B σ e he,
    by rintro ⟨b, rfl⟩; exact totalProductMap_isIntegral B σ hσ e he b⟩

/-- Mathlib's integral-closure predicate for the explicit embedding in
the original total fraction ring. -/
theorem totalProduct_isIntegralClosure :
    letI : Algebra (∀ i, B i) (FractionRing R) := (totalProductMap B e).toAlgebra
    IsIntegralClosure (∀ i, B i) R (FractionRing R) := by
  let : Algebra (∀ i, B i) (FractionRing R) := (totalProductMap B e).toAlgebra
  exact {
    algebraMap_injective := totalProductMap_injective B e
    isIntegral_iff := totalProduct_isIntegral_iff B σ hσ e he _ }

theorem totalProductToIntegralClosure_surjective :
    Surjective (totalProductToIntegralClosure B σ hσ e he) := by
  intro x
  obtain ⟨b, hb⟩ := total_exists_product_of_isIntegral B σ e he x.property
  exact ⟨b, Subtype.ext hb⟩

/-- The actual product is ring-isomorphic to the literal integral
closure inside the original total fraction ring. -/
def totalProductIntegralClosureEquiv :
    (∀ i, B i) ≃+* integralClosure R (FractionRing R) :=
  RingEquiv.ofBijective (totalProductToIntegralClosure B σ hσ e he)
    ⟨totalProductToIntegralClosure_injective B σ hσ e he,
      totalProductToIntegralClosure_surjective B σ hσ e he⟩

@[simp] theorem totalProductIntegralClosureEquiv_coe (b : ∀ i, B i) :
    (totalProductIntegralClosureEquiv B σ hσ e he b : FractionRing R) =
      totalProductMap B e b := rfl

/-- After the fraction-ring comparison, the integral-closure
isomorphism is exactly the coordinatewise canonical map. -/
@[simp] theorem totalProductIntegralClosureEquiv_coordinate (b : ∀ i, B i) (i : I) :
    e (totalProductIntegralClosureEquiv B σ hσ e he b : FractionRing R) i =
      algebraMap (B i) (FractionRing (B i)) (b i) :=
  congrFun (totalProductMap_e B e b) i

@[simp] theorem totalProductIntegralClosureEquiv_sigma (r : R) :
    (totalProductIntegralClosureEquiv B σ hσ e he (σ r) : FractionRing R) =
      algebraMap R (FractionRing R) r :=
  totalProductMap_sigma B σ e he r

/-- Restricting an actual source element agrees with its canonical
inclusion into its integral closure. -/
@[simp] theorem totalProductIntegralClosureEquiv_restriction (r : R) :
    totalProductIntegralClosureEquiv B σ hσ e he (σ r) =
      algebraMap R (integralClosure R (FractionRing R)) r :=
  Subtype.ext (totalProductMap_sigma B σ e he r)

/-- The comparison also respects the original source algebra structure,
with that structure explicitly induced by the actual map `σ`. -/
def totalProductIntegralClosureAlgEquiv :
    letI : Algebra R (∀ i, B i) := σ.toAlgebra
    (∀ i, B i) ≃ₐ[R] integralClosure R (FractionRing R) := by
  letI : Algebra R (∀ i, B i) := σ.toAlgebra
  exact {
    toRingEquiv := totalProductIntegralClosureEquiv B σ hσ e he
    commutes' := fun r => Subtype.ext (totalProductMap_sigma B σ e he r) }

@[simp] theorem totalProductIntegralClosureAlgEquiv_coe (b : ∀ i, B i) :
    (totalProductIntegralClosureAlgEquiv B σ hσ e he b : FractionRing R) =
      totalProductMap B e b := rfl

end Finite

end Wikipedia.HopfProblem.CuspNormalization.GermsClosure
