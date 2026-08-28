import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyZero
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyOne
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyTwo

/-!
# All genuine holomorphic cohomology groups of every period torus

The original Ext-defined cohomology, with the original sheaf-induced
complex scalars, is ℂ, ℂ², ℂ in degrees zero, one, and two. It vanishes
in every higher degree. The finite-dimensionality and dimension formulas
below follow from those actual comparisons and the proved native acyclic
resolution; no fibre-cohomology or generic-period hypothesis is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

/-- The actual cohomology group is trivial in every degree greater than two. -/
theorem higher_subsingleton (p : PeriodDomain) (n : ℕ) : Subsingleton (H p (n + 3)) :=
  Dolbeault.higher_subsingleton p n

theorem higher_eq_zero (p : PeriodDomain) (n : ℕ) (a : H p (n + 3)) : a = 0 :=
  (higher_subsingleton p n).elim a 0

/-- No actual higher Ext class survives past the native resolution's final term. -/
theorem cohomology_subsingleton_of_two_lt (p : PeriodDomain) (q : ℕ) (hq : 2 < q) :
    Subsingleton (H p q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 3 := ⟨q - 3, by omega⟩
  exact higher_subsingleton p n

/-- Every original holomorphic cohomology group is finite-dimensional over its actual scalars. -/
instance cohomology_finite (p : PeriodDomain) (q : ℕ) : FiniteDimensional ℂ (H p q) := by
  cases q with
  | zero => exact (h0Equiv p).symm.finiteDimensional
  | succ q =>
    cases q with
    | zero => exact (h1Equiv p).symm.finiteDimensional
    | succ q =>
      cases q with
      | zero => exact (h2Equiv p).symm.finiteDimensional
      | succ n =>
        let := higher_subsingleton p n
        infer_instance

theorem higher_finrank (p : PeriodDomain) (n : ℕ) :
    Module.finrank ℂ (H p (n + 3)) = 0 := by
  let := higher_subsingleton p n
  exact Module.finrank_zero_of_subsingleton

/-- The complete dimension formula for the actual sheaf cohomology of every period torus. -/
theorem cohomology_finrank (p : PeriodDomain) (q : ℕ) :
    Module.finrank ℂ (H p q) =
      if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 1 else 0 := by
  cases q with
  | zero => simpa using h0_finrank p
  | succ q =>
    cases q with
    | zero => simpa using h1_finrank p
    | succ q =>
      cases q with
      | zero => simpa using h2_finrank p
      | succ n => simpa using higher_finrank p n

/-- Equivalently, the genuine dimensions are the binomial coefficients for complex dimension two. -/
theorem cohomology_finrank_choose (p : PeriodDomain) (q : ℕ) :
    Module.finrank ℂ (H p q) = Nat.choose 2 q := by
  cases q with
  | zero => simpa using h0_finrank p
  | succ q =>
    cases q with
    | zero => simpa using h1_finrank p
    | succ q =>
      cases q with
      | zero => simpa using h2_finrank p
      | succ n =>
        rw [higher_finrank, Nat.choose_eq_zero_of_lt (by omega)]

/-- The Euler characteristic of the original, finitely supported holomorphic cohomology is zero. -/
theorem eulerCharacteristic (p : PeriodDomain) :
    (Module.finrank ℂ (H p 0) : ℤ) - (Module.finrank ℂ (H p 1) : ℤ) +
      (Module.finrank ℂ (H p 2) : ℤ) = 0 := by
  rw [h0_finrank, h1_finrank, h2_finrank]
  norm_num

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
