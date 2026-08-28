import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarAlgebraBasic

/-!
# Unit factors preserve the actual denominator ideal

Multiplication by the image of a ring unit does not change which ring
elements clear a fraction. Consequently, unit factors in a displayed
numerator and denominator leave its denominator ideal unchanged. These
statements require neither a domain nor a fraction-ring or factoriality
hypothesis on the original ring.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial

open PolarAlgebra

variable (B : Type*) [CommRing B] {K : Type*} [Field K] [Algebra B K]

/-- Multiplying by a ring-unit image preserves the actual clearing ideal. -/
theorem denominatorIdeal_mul_unit (x : K) (u : Bˣ) :
    denominatorIdeal B (x * algebraMap B K (u : B)) = denominatorIdeal B x := by
  ext a
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b * (↑u⁻¹ : B), ?_⟩
    have hu : algebraMap B K (u : B) * algebraMap B K (↑u⁻¹ : B) = 1 := by
      rw [← map_mul, u.mul_inv, map_one]
    have he := congrArg (fun y : K => y * algebraMap B K (↑u⁻¹ : B)) hb
    simpa only [mul_assoc, hu, map_mul, mul_one] using he
  · rintro ⟨b, hb⟩
    refine ⟨b * (u : B), ?_⟩
    simpa only [map_mul, mul_assoc] using
      congrArg (fun y : K => y * algebraMap B K (u : B)) hb

/-- The same invariance with the unit image on the left. -/
theorem denominatorIdeal_unit_mul (x : K) (u : Bˣ) :
    denominatorIdeal B (algebraMap B K (u : B) * x) = denominatorIdeal B x := by
  simpa only [mul_comm] using denominatorIdeal_mul_unit B x u

/-- Both unit factors can be removed from a quotient without changing its
denominator ideal, including when the displayed denominator maps to zero. -/
theorem denominatorIdeal_unit_mul_div_unit_mul (p q : B) (u v : Bˣ) :
    denominatorIdeal B
        (algebraMap B K ((u : B) * p) / algebraMap B K ((v : B) * q)) =
      denominatorIdeal B (algebraMap B K p / algebraMap B K q) := by
  have he :
      algebraMap B K ((u : B) * p) / algebraMap B K ((v : B) * q) =
        (algebraMap B K p / algebraMap B K q) *
          algebraMap B K ((u * v⁻¹ : Bˣ) : B) := by
    simp only [Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv,
      mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
  exact (congrArg (denominatorIdeal B) he).trans
    (denominatorIdeal_mul_unit B (algebraMap B K p / algebraMap B K q) (u * v⁻¹))

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial
