import ErdosProblems.Erdos67b.MRPrimeSquareEnergy

/-!
# Exact additional Ramaré factorization with both arithmetic errors

Insert the auxiliary interval in the typical family to reuse the proved
prime-square correction. Removing it in the cofactor restores the original
remaining family. The difference of the two typical polynomials is kept as
an explicit missing-prime polynomial.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mem_typicalFactorizationSet_insert
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (Z n : ℕ) :
    n ∈ typicalFactorizationSet (insert I blocks) Z ↔
      n ∈ typicalFactorizationSet blocks Z ∧ HasPrimeFactorInBlock I n := by
  classical
  simp only [mem_typicalFactorizationSet, HasTypicalFactorization, Finset.forall_mem_insert]
  tauto

def mrAuxiliaryMissingCoefficient
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (Z : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (mrTypicalValueCoefficient blocks Z f n -
    mrTypicalValueCoefficient (insert I blocks) Z f n) / (n : ℂ)

open Classical in
theorem mrAuxiliaryMissingCoefficient_eq
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (Z : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    mrAuxiliaryMissingCoefficient blocks I Z f n =
      if n ∈ typicalFactorizationSet blocks Z ∧ ¬HasPrimeFactorInBlock I n
      then f n / (n : ℂ) else 0 := by
  unfold mrAuxiliaryMissingCoefficient mrTypicalValueCoefficient
  simp only [mem_typicalFactorizationSet_insert]
  by_cases htyp : n ∈ typicalFactorizationSet blocks Z <;>
    by_cases hprime : HasPrimeFactorInBlock I n <;> simp [htyp, hprime]

def mrAuxiliaryMissingPolynomial
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
    (mrAuxiliaryMissingCoefficient blocks I (2 * X) f) t

theorem mrTypicalDyadicPolynomial_eq_insert_add_missing
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    mrTypicalDyadicPolynomial blocks f X t =
      mrTypicalDyadicPolynomial (insert I blocks) f X t +
        mrAuxiliaryMissingPolynomial blocks I f X t := by
  unfold mrTypicalDyadicPolynomial mrAuxiliaryMissingPolynomial logarithmicDirichletPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  unfold mrAuxiliaryMissingCoefficient
  ring

theorem mrTypicalCofactorRectangle_insert
    (blocks : Finset (ℕ × ℕ)) (I K : ℕ × ℕ) (X : ℕ) :
    mrTypicalCofactorRectangle (insert I blocks) I K X =
      mrTypicalCofactorRectangle blocks I K X := by
  classical
  simp only [mrTypicalCofactorRectangle, Finset.erase_insert_eq_erase]

theorem mrTypicalRamareBoundaryPolynomial_insert
    (blocks : Finset (ℕ × ℕ)) (I K : ℕ × ℕ) (D : Finset ℕ)
    (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    mrTypicalRamareBoundaryPolynomial (insert I blocks) I K D f X t =
      mrTypicalRamareBoundaryPolynomial blocks I K D f X t := by
  unfold mrTypicalRamareBoundaryPolynomial mrTypicalRamareBoundarySupport
  rw [mrTypicalCofactorRectangle_insert]

theorem mrTypicalDyadicPolynomial_eq_auxiliary_products_add_errors
    {ι : Type*} {V : Finset ι}
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {D : ι → Finset ℕ} {K : ι → ℕ × ℕ}
    (hpartition : Set.PairwiseDisjoint (↑V) D) (hcover : V.biUnion D = primesInBlock I)
    (hK : ∀ v ∈ V, 0 < (K v).1)
    (hDK : ∀ v ∈ V, ∀ p ∈ D v, (K v).1 ≤ p ∧ p ≤ (K v).2)
    (hdisj : ∀ B ∈ blocks, B ≠ I → Disjoint (primesInBlock I) (primesInBlock B))
    (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    mrTypicalDyadicPolynomial blocks f X t =
      (∑ v ∈ V,
        (logarithmicDirichletPolynomial (D v) (mrFinitePrimeLineCoefficient f) t *
            logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I (K v) X)
              (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t -
          mrTypicalRamareBoundaryPolynomial blocks I (K v) (D v) f X t)) +
        mrPrimeSquareErrorPolynomial (insert I blocks) I f X t +
        mrAuxiliaryMissingPolynomial blocks I f X t := by
  classical
  have hdisj' : ∀ B ∈ insert I blocks, B ≠ I →
      Disjoint (primesInBlock I) (primesInBlock B) := by
    intro B hB hBI
    rcases Finset.mem_insert.mp hB with heq | hmem
    · exact False.elim (hBI heq)
    · exact hdisj B hmem hBI
  rw [mrTypicalDyadicPolynomial_eq_insert_add_missing blocks I f X t,
    mrTypicalDyadicPolynomial_eq_common_add_error,
    mrTypicalCommonPolynomial_eq_products_sub_boundary hpartition hcover hK hDK hdisj']
  simp only [mrTypicalCofactorRectangle_insert, mrTypicalRamareBoundaryPolynomial_insert]

end

end Erdos67b
