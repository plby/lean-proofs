import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessPieces
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebraRank
import Wikipedia.HopfProblem.ThreefoldHomologyStar

/-!
# Finitely generated, bounded homology of the actual compact threefold

The star Mayer--Vietoris sequence has the original regular family and
three filling pieces in its middle, and the actual three overlaps on
its left.  Their proved finite generation and dimension bounds imply
finite generation in every degree and vanishing above degree six for
the constructed threefold itself.  No matrix for an attachment map,
global homology splitting, or global torsion-freeness is assumed.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open SingularMayerVietoris ThreefoldHomologyFinitenessAlgebra

/-- Genuine integral singular homology of the constructed threefold is
finitely generated in every degree. -/
theorem homology_finite (n : ℕ) : Module.Finite ℤ (SingularHomology Space n) := by
  cases n with
  | zero => exact LowDegrees.singularH0_finite
  | succ n =>
    have := starPairHomology_finite (n + 1)
    have := starOverlapHomology_finite n
    exact finite_of_exact (starRightHomologyMap (n + 1))
      (starConnectingHomomorphism n) (star_exact_at_ambient n)

/-- All integral homology groups are Noetherian, without a freeness premise. -/
theorem homology_noetherian (n : ℕ) : IsNoetherian ℤ (SingularHomology Space n) := by
  have := homology_finite n
  infer_instance

/-- Above degree six both actual neighboring terms in the star sequence
vanish, so the actual global homology group vanishes. -/
theorem homology_subsingleton_of_lt {n : ℕ} (hn : 6 < n) :
    Subsingleton (SingularHomology Space n) := by
  cases n with
  | zero => omega
  | succ n =>
    have := starPairHomology_subsingleton (by omega : 5 < n + 1)
    have := starOverlapHomology_subsingleton (by omega : 5 < n)
    exact subsingleton_of_exact (starRightHomologyMap (n + 1))
      (starConnectingHomomorphism n) (star_exact_at_ambient n)

theorem homology_eq_zero_of_lt {n : ℕ} (hn : 6 < n)
    (a : SingularHomology Space n) : a = 0 := by
  have := homology_subsingleton_of_lt hn
  exact Subsingleton.elim _ _

theorem homology_isZero_of_lt {n : ℕ} (hn : 6 < n) :
    IsZero (SingularHomology Space n) := by
  have := homology_subsingleton_of_lt hn
  exact ModuleCat.isZero_of_subsingleton _

/-- Rationalization of the original integral homology, not a substitute
complex with an assumed rank table. -/
abbrev RationalHomology (n : ℕ) := ℚ ⊗[ℤ] SingularHomology Space n

theorem rational_homology_finite (n : ℕ) : Module.Finite ℚ (RationalHomology n) := by
  have := homology_finite n
  exact rationalization_finite (SingularHomology Space n)

theorem rational_homology_subsingleton_of_lt {n : ℕ} (hn : 6 < n) :
    Subsingleton (RationalHomology n) := by
  have := homology_subsingleton_of_lt hn
  infer_instance

/-- The actual rational Betti number; global torsion-freeness is not used. -/
def rationalBetti (n : ℕ) : ℕ := Module.finrank ℚ (RationalHomology n)

theorem rationalBetti_zero : rationalBetti 0 = 1 := by
  have := LowDegrees.singularH0_free
  change Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology Space 0) = 1
  rw [Module.finrank_baseChange]
  exact LowDegrees.singularH0_finrank

theorem rationalBetti_one : rationalBetti 1 = 0 := by
  have := LowDegrees.singularH1_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem rationalBetti_eq_zero_of_lt {n : ℕ} (hn : 6 < n) : rationalBetti n = 0 := by
  have := rational_homology_subsingleton_of_lt hn
  exact Module.finrank_zero_of_subsingleton

/-- Both assertions refer to the original, unconditional threefold. -/
theorem finite_and_bounded_homology :
    (∀ n, Module.Finite ℤ (SingularHomology Space n)) ∧
      ∀ n, 6 < n → IsZero (SingularHomology Space n) :=
  ⟨homology_finite, fun _ hn => homology_isZero_of_lt hn⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
