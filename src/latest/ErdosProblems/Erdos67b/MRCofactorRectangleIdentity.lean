import ErdosProblems.Erdos67b.MRTypicalCofactorEuler
import ErdosProblems.Erdos67b.MRTypicalLowHigh
import ErdosProblems.Erdos67b.MRFiniteTypicalRamare

/-!
# The actual rounded typical rectangle as an indexed cofactor polynomial

Filtering the index set removes every preimage of the distinguished block.
No injectivity assumption is needed for the exact erased-image identity.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrScheduledRemainingIndices (p₁ q₁ : ℝ) (J : ℕ) (I : ℕ × ℕ) : Finset ℕ :=
  (Finset.Icc 1 J).filter (fun j ↦ mrScheduledPrimeInterval p₁ q₁ j ≠ I)

theorem mrScheduledRemainingIndices_subset (p₁ q₁ : ℝ) (J : ℕ) (I : ℕ × ℕ) :
    mrScheduledRemainingIndices p₁ q₁ J I ⊆ Finset.Icc 1 J := Finset.filter_subset _ _

theorem mrScheduledRemainingIndices_image (p₁ q₁ : ℝ) (J : ℕ) (I : ℕ × ℕ) :
    (mrScheduledRemainingIndices p₁ q₁ J I).image (mrScheduledPrimeInterval p₁ q₁) =
      (mrScheduledBlocks p₁ q₁ J).erase I := by
  ext K
  simp only [mrScheduledRemainingIndices, mrScheduledBlocks, Finset.mem_image,
    Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨j, ⟨hj, hne⟩, rfl⟩
    exact ⟨hne, j, hj, rfl⟩
  · rintro ⟨hne, j, hj, rfl⟩
    exact ⟨j, ⟨hj, hne⟩, rfl⟩

open Classical in
theorem mrIndexedTypicalCoefficient_image_eq (J : Finset ℕ)
    (B : ℕ → ℕ × ℕ) (f : ℕ → ℂ) :
    mrIndexedTypicalCoefficient J (fun j ↦ primesInBlock (B j)) f =
      fun n ↦ if HasTypicalFactorization (J.image B) n then f n else 0 := by
  funext n
  unfold mrIndexedTypicalCoefficient HasTypicalFactorization
  simp only [Finset.forall_mem_image, HasPrimeFactorInBlock, mrPrimeBlockHit]
  exact (ite_eq_ite _ _ _).mpr trivial

open Classical in
theorem mrIndexedTypicalCoefficient_schedule_remaining_eq
    (p₁ q₁ : ℝ) (J : ℕ) (I : ℕ × ℕ) (f : ℕ → ℂ) :
    mrIndexedTypicalCoefficient (mrScheduledRemainingIndices p₁ q₁ J I)
        (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f =
      fun n ↦ if HasTypicalFactorization ((mrScheduledBlocks p₁ q₁ J).erase I) n
        then f n else 0 := by
  rw [mrIndexedTypicalCoefficient_image_eq, mrScheduledRemainingIndices_image]

theorem mrTypicalCofactorRectangle_polynomial_eq_indexed
    (p₁ q₁ : ℝ) (J : ℕ) (I K : ℕ × ℕ) (X : ℕ)
    (A : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) :
    logarithmicDirichletPolynomial
        (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I K X)
        (mrFiniteCofactorLineCoefficient A f) t =
      logarithmicDirichletPolynomial (mrDyadicCofactorRectangle K X)
        (fun n ↦ mrIndexedTypicalCofactorCoefficient A (mrScheduledRemainingIndices p₁ q₁ J I)
          (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f n / (n : ℂ)) t := by
  classical
  unfold mrTypicalCofactorRectangle logarithmicDirichletPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [mrIndexedTypicalCofactorCoefficient, mrIndexedTypicalCoefficient_schedule_remaining_eq]
  unfold mrFiniteCofactorLineCoefficient
  split_ifs <;> simp [div_div]

end

end Erdos67b
