import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral

/-!
# Transcendence degree of a rational meromorphic-function field

This file uses Mathlib's actual `Algebra.trdeg` and `IsTranscendenceBasis`.
It applies to an independently constructed algebra equivalence with the
rational-function field; it does not define a meromorphic-function field or
its transcendence degree by the desired answer.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.Transcendence

universe u v

open Function

/-- The single rational coordinate is a transcendence basis.  Passing from
the polynomial ring to its field of fractions is algebraic over the
polynomial ring, so it preserves the original polynomial basis. -/
theorem ratFunc_isTranscendenceBasis (K : Type u) [Field K] :
    IsTranscendenceBasis K (fun _ : Unit => (RatFunc.X : RatFunc K)) := by
  let : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := Polynomial K) (K := RatFunc K) (C := RatFunc K)).2 inferInstance
  simpa only [Function.comp_def, RatFunc.algebraMap_X] using
    (IsTranscendenceBasis.polynomial Unit K).algebraMap_comp (A := RatFunc K)

/-- The actual cardinal-valued transcendence degree of the rational-function
field in one variable is one. -/
theorem ratFunc_trdeg_eq_one (K : Type u) [Field K] :
    Algebra.trdeg K (RatFunc K) = 1 := by
  simpa using (ratFunc_isTranscendenceBasis K).lift_cardinalMk_eq_trdeg.symm

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- An algebra equivalence transports the rational coordinate to a genuine
one-element transcendence basis of the given field. -/
theorem isTranscendenceBasis_of_algEquiv_ratFunc (e : F ≃ₐ[K] RatFunc K) :
    IsTranscendenceBasis K (fun _ : Unit => e.symm RatFunc.X) := by
  simpa only [Function.comp_def] using
    e.symm.isTranscendenceBasis (ratFunc_isTranscendenceBasis K)

/-- Any genuine field algebra-equivalent to `RatFunc K` has transcendence
degree one.  The universes of the two fields need not agree. -/
theorem trdeg_eq_one_of_algEquiv_ratFunc (e : F ≃ₐ[K] RatFunc K) :
    Algebra.trdeg K F = 1 := by
  simpa using
    (isTranscendenceBasis_of_algEquiv_ratFunc e).lift_cardinalMk_eq_trdeg.symm

/-- The natural-number-valued version of the same finite transcendence degree. -/
theorem trdeg_toNat_eq_one_of_algEquiv_ratFunc (e : F ≃ₐ[K] RatFunc K) :
    Cardinal.toNat (Algebra.trdeg K F) = 1 := by
  rw [trdeg_eq_one_of_algEquiv_ratFunc e]
  simp

/-- The coordinate obtained from the rational coordinate is transcendental
over the original coefficient field. -/
theorem coordinate_transcendental_of_algEquiv_ratFunc (e : F ≃ₐ[K] RatFunc K) :
    Transcendental K (e.symm RatFunc.X) :=
  (isTranscendenceBasis_of_algEquiv_ratFunc e).1.transcendental ()

/-- A version for a previously defined coordinate whose image has been
identified with the rational indeterminate. -/
theorem transcendental_of_algEquiv_ratFunc_eq_X (e : F ≃ₐ[K] RatFunc K)
    {x : F} (hx : e x = RatFunc.X) : Transcendental K x := by
  have hcoord : x = e.symm RatFunc.X := e.injective (by simpa using hx)
  rw [hcoord]
  exact coordinate_transcendental_of_algEquiv_ratFunc e

/-- In particular, polynomial evaluation in this genuine coordinate is
injective; no nonzero polynomial relation can vanish in the field. -/
theorem aeval_coordinate_injective_of_algEquiv_ratFunc (e : F ≃ₐ[K] RatFunc K) :
    Function.Injective (Polynomial.aeval (e.symm RatFunc.X) : Polynomial K →ₐ[K] F) :=
  transcendental_iff_injective.1 (coordinate_transcendental_of_algEquiv_ratFunc e)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.Transcendence
