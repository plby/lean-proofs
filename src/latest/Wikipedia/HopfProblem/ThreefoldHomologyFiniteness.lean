import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEuler

/-!
# Unconditional homological finiteness of the constructed threefold

All the groups below are genuine singular homology of the original
glued space.  Finite generation, the degree bound, and Euler characteristic
are proved from its actual star cover.  The finer boundary-matrix
computations in degrees two through five are not assumed here.
-/

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open SingularMayerVietoris

/-- The original compact complex threefold has finite integral homology,
no homology above degree six, and Euler characteristic two. -/
theorem global_homology_finiteness :
    (∀ n, Module.Finite ℤ (SingularHomology Space n)) ∧
      (∀ n, 6 < n → IsZero (SingularHomology Space n)) ∧
        eulerCharacteristic = 2 :=
  ⟨homology_finite, fun _ hn => homology_isZero_of_lt hn, eulerCharacteristic_eq_two⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
