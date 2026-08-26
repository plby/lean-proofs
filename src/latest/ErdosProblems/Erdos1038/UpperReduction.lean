import ErdosProblems.Erdos1038.EndpointEquality
import ErdosProblems.Erdos1038.ExtremumOrder

/-!
# Reduction of the sharp upper theorem to Tao's potential inequality

The difficult analytic content is isolated as a proposition about positive
sets of empirical logarithmic potentials.  This file proves that content
implies all three upper-extremum clauses of `MainTheorem`, including the
polynomial equality classification.
-/

open scoped ENNReal
open MeasureTheory Polynomial

namespace Erdos1038

noncomputable section

/-- The empirical specialization of Tao's sharp probability-measure
inequality and its equality statement.  This is a proposition to be proved,
not an assumption or axiom. -/
def TaoSharpUpperEmpirical : Prop :=
  ∀ f : Polynomial ℝ, ∀ hf : IsAdmissible f,
    volume {x | 0 < taoEmpiricalPotential f hf x} ≤
        ENNReal.ofReal (2 * Real.sqrt 2) ∧
      (volume {x | 0 < taoEmpiricalPotential f hf x} =
          ENNReal.ofReal (2 * Real.sqrt 2) →
        empiricalRootProbability f hf = endpointRootProbability)

theorem polynomial_upper_bound_of_taoSharpUpperEmpirical
    (hTao : TaoSharpUpperEmpirical) (f : Polynomial ℝ)
    (hf : IsAdmissible f) :
    sublevelVolume f ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  rw [sublevelVolume_eq_volume_taoEmpiricalPotential_pos hf]
  exact (hTao f hf).1

theorem polynomial_upper_equality_iff_of_taoSharpUpperEmpirical
    (hTao : TaoSharpUpperEmpirical) (f : Polynomial ℝ)
    (hf : IsAdmissible f) :
    sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
      ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m := by
  constructor
  · intro hvolume
    have hpotential :
        volume {x | 0 < taoEmpiricalPotential f hf x} =
          ENNReal.ofReal (2 * Real.sqrt 2) := by
      rw [← sublevelVolume_eq_volume_taoEmpiricalPotential_pos hf]
      exact hvolume
    exact empiricalRootProbability_eq_endpoint_imp_extremal hf
      ((hTao f hf).2 hpotential)
  · rintro ⟨m, hm, rfl⟩
    exact sublevelVolume_extremal hm

/-- Once Tao's analytic proposition is available, all target clauses for
the supremum follow at once. -/
theorem mainTheorem_upper_clauses_of_taoSharpUpperEmpirical
    (hTao : TaoSharpUpperEmpirical) :
    supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) ∧
    (∀ m : ℕ, 0 < m →
      IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
      sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
        ENNReal.ofReal (2 * Real.sqrt 2)) ∧
    (∀ f : Polynomial ℝ, IsAdmissible f →
      (sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
        ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m)) := by
  refine ⟨supremumLength_eq_proposed
    (polynomial_upper_bound_of_taoSharpUpperEmpirical hTao), ?_, ?_⟩
  · exact extremalPolynomial_attains
  · exact polynomial_upper_equality_iff_of_taoSharpUpperEmpirical hTao

end

end Erdos1038
