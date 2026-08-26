import ErdosProblems.Erdos67b.MRAuxiliaryBlockSeparation
import ErdosProblems.Erdos67b.MRAuxiliarySourceDensity

/-!
# The exact auxiliary Ramaré factorization at the original source schedule

All interval separation and finite prime partition hypotheses are
discharged. The original typical support is preserved in the cofactors;
the boundary, prime-square, and missing-prime polynomials remain explicit.
-/

open Filter
open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSourceAuxiliarySubblocks (X : ℕ) : Finset ℕ :=
  mrLogBlockIndices (mrAuxiliaryResolution (Real.log (X : ℝ)))
    (mrAuxiliaryLogLower (Real.log (X : ℝ))) (mrAuxiliaryLogUpper (Real.log (X : ℝ)))

theorem mrSourceAuxiliary_prime_partition (X : ℕ)
    (hH : 0 ≤ mrAuxiliaryResolution (Real.log (X : ℝ))) :
    Set.PairwiseDisjoint (↑(mrSourceAuxiliarySubblocks X) : Set ℕ)
      (mrPrimeSubblock (mrAuxiliaryResolution (Real.log (X : ℝ)))
        (primesInBlock (mrSourceAuxiliaryInterval X))) ∧
    (mrSourceAuxiliarySubblocks X).biUnion
      (mrPrimeSubblock (mrAuxiliaryResolution (Real.log (X : ℝ)))
        (primesInBlock (mrSourceAuxiliaryInterval X))) =
      primesInBlock (mrSourceAuxiliaryInterval X) := by
  constructor
  · exact mrPrimeSubblock_pairwiseDisjoint _ _ _
  · exact mrPrimeSubblock_biUnion_eq hH _
      (fun p hp ↦ mem_primesInBlock_mrLogPrimeInterval_bounds hp)

theorem mrExists_sourceAuxiliary_factorization :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        p₁ ≤ q₁ → 1 ≤ Real.log q₁ → 4096 * Real.log q₁ ≤ eta * p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
        mrSourceAuxiliaryInterval X ∉ mrScheduledBlocks p₁ q₁ J ∧
        ∀ (f : ℕ → ℂ) (t : ℝ),
          let blocks := mrScheduledBlocks p₁ q₁ J
          let I := mrSourceAuxiliaryInterval X
          let H := mrAuxiliaryResolution (Real.log (X : ℝ))
          mrTypicalDyadicPolynomial blocks f X t =
            (∑ r ∈ mrSourceAuxiliarySubblocks X,
              (logarithmicDirichletPolynomial (mrPrimeSubblock H (primesInBlock I) r)
                  (mrFinitePrimeLineCoefficient f) t *
                logarithmicDirichletPolynomial
                  (mrTypicalCofactorRectangle blocks I (mrNarrowPrimeInterval H r) X)
                  (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t -
                mrTypicalRamareBoundaryPolynomial blocks I (mrNarrowPrimeInterval H r)
                  (mrPrimeSubblock H (primesInBlock I) r) f X t)) +
              mrPrimeSquareErrorPolynomial (insert I blocks) I f X t +
              mrAuxiliaryMissingPolynomial blocks I f X t := by
  have heventual := EulerSubpower.tendsto_log_nat_atTop.eventually mrEventually_auxiliary_schedule
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 heventual
  refine ⟨max X₁ 1, le_max_right _ _, ?_⟩
  intro X hX eta p₁ q₁ heta hp hq hpq hlogq hbudget J hupper
  obtain ⟨_, hH, ha, hab, hgap, _⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hdisj := mrAuxiliaryInterval_disjoint_scheduled (b := mrAuxiliaryLogUpper (Real.log (X : ℝ)))
    heta hp hq hpq hlogq hbudget hupper hgap
  have hnot := mrAuxiliaryInterval_not_mem_scheduled heta hp hq hpq hlogq hbudget
    hupper hgap (by linarith : 2 ≤ mrAuxiliaryLogLower (Real.log (X : ℝ))) hab
  refine ⟨hnot, ?_⟩
  intro f t
  dsimp only
  have hpartition := mrSourceAuxiliary_prime_partition X (by linarith)
  exact mrTypicalDyadicPolynomial_eq_auxiliary_products_add_errors hpartition.1 hpartition.2
    (fun r _ ↦ mrNarrowPrimeInterval_lower_pos _ r)
    (fun r _ p hpI ↦ mrPrimeSubblock_integer_bounds
      (by linarith : 0 < mrAuxiliaryResolution (Real.log (X : ℝ)))
      (fun p hpI ↦ (mem_primesInBlock.mp hpI).1) hpI)
    (fun K hK _ ↦ hdisj K hK) f X t

end

end Erdos67b
