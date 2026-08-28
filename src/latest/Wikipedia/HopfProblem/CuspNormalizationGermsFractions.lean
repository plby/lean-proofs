import Wikipedia.HopfProblem.CuspNormalizationGermsFractionsMaps
import Wikipedia.HopfProblem.CuspNormalizationGermsFractionsSeparators

/-!
# The total fraction ring of the actual branch-restriction image

Suppose a subring of a finite product of domains surjects onto every
coordinate and contains a separating family supported on the individual
coordinates. Its non-zero-divisors are exactly the elements whose every
coordinate is nonzero. The product of the branch fraction fields is the
localization at those actual non-zero-divisors.

The localization property is proved by explicit denominator clearing:
lift each numerator and denominator coordinate, multiply the lifts by
the supported separating elements, and sum. In particular no birational
identification is assumed. The resulting equivalence is from the genuine
total fraction ring `FractionRing A`, including when `A` has zero divisors.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.CuspNormalization.GermsFractions

universe u v

variable {I : Type u} {B : I → Type v} [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]

attribute [local instance] productFractionAlgebra

variable [Finite I] (A : Subring (∀ i, B i)) (s : SeparatingFamily A)
  (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i))

include s hsurj

/-- The product of the actual branch fraction fields has the localization
universal property for the actual non-zero-divisors of the image subring. -/
theorem product_isFractionRing : IsFractionRing A (∀ i, FractionRing (B i)) := by
  classical
  let := Fintype.ofFinite I
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro y
    apply Pi.isUnit_iff.mpr
    intro i
    change IsUnit (algebraMap (B i) (FractionRing (B i)) ((y.val : ∀ j, B j) i))
    exact IsLocalization.map_units (FractionRing (B i))
      ⟨(y.val : ∀ j, B j) i,
        mem_nonZeroDivisors_iff_ne_zero.mpr ((s.mem_nonZeroDivisors_iff y.val).mp y.prop i)⟩
  · intro z
    choose nd hnd using fun i => IsLocalization.surj (nonZeroDivisors (B i)) (z i)
    choose n hn using fun i => hsurj i (nd i).1
    choose d hd using fun i => hsurj i ((nd i).2 : B i)
    change ∀ i, (n i : ∀ j, B j) i = (nd i).1 at hn
    change ∀ i, (d i : ∀ j, B j) i = ((nd i).2 : B i) at hd
    have hD : s.weightedSum d ∈ nonZeroDivisors A :=
      s.weightedSum_mem_nonZeroDivisors d (fun i => by
        rw [hd i]
        exact mem_nonZeroDivisors_iff_ne_zero.mp (nd i).2.prop)
    refine ⟨(s.weightedSum n, ⟨s.weightedSum d, hD⟩), ?_⟩
    ext i
    change z i * algebraMap (B i) (FractionRing (B i))
      ((s.weightedSum d : ∀ j, B j) i) =
        algebraMap (B i) (FractionRing (B i)) ((s.weightedSum n : ∀ j, B j) i)
    rw [s.weightedSum_apply, s.weightedSum_apply, hd i, hn i, map_mul, map_mul]
    rw [mul_left_comm, hnd i]
  · intro x y hxy
    exact ⟨1, by simpa using subring_algebraMap_injective B A hxy⟩

/-- The actual total fraction ring is canonically the product of the
branch fraction fields, as an algebra over the original image subring. -/
def totalFractionAlgEquiv : FractionRing A ≃ₐ[A] ∀ i, FractionRing (B i) := by
  let := product_isFractionRing A s hsurj
  exact IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) (∀ i, FractionRing (B i))

/-- The same identification as a ring equivalence, independent of local
instance notation for the explicitly defined product algebra. -/
def totalFractionEquiv : FractionRing A ≃+* ∀ i, FractionRing (B i) :=
  (totalFractionAlgEquiv A s hsurj).toRingEquiv

/-- On the actual image ring the equivalence is the canonical coordinate
fraction map, so it is not an unrelated abstract product isomorphism. -/
@[simp] theorem totalFractionEquiv_algebraMap_apply (a : A) (i : I) :
    totalFractionEquiv A s hsurj (algebraMap A (FractionRing A) a) i =
      algebraMap (B i) (FractionRing (B i)) ((a : ∀ j, B j) i) :=
  congrFun ((totalFractionAlgEquiv A s hsurj).commutes a) i

/-- An actual fraction is sent to the coordinatewise fraction of its
actual numerator and non-zero-divisor denominator. -/
theorem totalFractionEquiv_mk'_apply (a : A) (d : nonZeroDivisors A) (i : I) :
    totalFractionEquiv A s hsurj (IsLocalization.mk' (FractionRing A) a d) i =
      algebraMap (B i) (FractionRing (B i)) ((a : ∀ j, B j) i) /
        algebraMap (B i) (FractionRing (B i)) ((d.val : ∀ j, B j) i) := by
  have hd : algebraMap (B i) (FractionRing (B i)) ((d.val : ∀ j, B j) i) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (B i) (FractionRing (B i)))
      (IsFractionRing.injective (B i) (FractionRing (B i)))).mpr
        ((s.mem_nonZeroDivisors_iff d.val).mp d.prop i)
  apply (eq_div_iff hd).mpr
  have h := congrArg (fun x : FractionRing A => totalFractionEquiv A s hsurj x i)
    (IsLocalization.mk'_spec (FractionRing A) a d)
  simpa only [map_mul, Pi.mul_apply, totalFractionEquiv_algebraMap_apply] using h

end Wikipedia.HopfProblem.CuspNormalization.GermsFractions
