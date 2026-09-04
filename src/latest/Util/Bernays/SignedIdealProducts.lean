import Util.Bernays.QuadraticFactorData
import Util.Bernays.SignedProducts

/-!
# Realizing sign choices by ideals of unchanged norm
-/

namespace Bernays

theorem exists_ideal_of_signed_goodMaximals {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ {k : ℕ} (P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      (∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
        IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b)) →
      ∀ σ : Fin k → Bool, ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        J.idealClass = signedProduct σ (fun i => (P i).idealClass) ∧
          (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
            ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) :
              Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  let := quadraticOrderIsDomain hD
  intro k P hP σ
  choose Q hQc hQN using fun i => goodMaximal_inverseClass_sameNorm hD (P i) (hP i).1 (hP i).2
  let T : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b) := fun i => if σ i then Q i else P i
  refine ⟨∏ i, T i, ?_, ?_⟩
  · rw [InvertibleIdeal.idealClass_prod, signedProduct]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : σ i
    · simp only [T, hi, Bool.false_eq_true, if_false]
    · simpa only [T, hi, if_true] using hQc i
  · rw [InvertibleIdeal.cardQuot_prod, InvertibleIdeal.cardQuot_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : σ i
    · simp only [T, hi, Bool.false_eq_true, if_false]
    · simpa only [T, hi, if_true] using hQN i

theorem exists_goodMaximal_tuple {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ k : ℕ, ∃ P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (∏ i, P i) = I ∧ ∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
          IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) := by
  let := quadraticOrderIsDomain hD
  intro I hI
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hI
  refine ⟨l.length, l.get, ?_, fun i => hP _ (List.get_mem l i)⟩
  rw [← Fin.prod_ofFn, List.ofFn_get, hl]

theorem exists_squareSubgroup_of_missing_ideal_class {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ {k : ℕ} (P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      (∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
        IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b)) →
      ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))))
          (∏ i, (P i).idealClass) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) C →
      (∀ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
          ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Ideal (QuadraticAlgebra ℤ d b)).cardQuot →
        J.idealClass ≠ C) →
      ∃ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))), H ≠ ⊤ ∧
        countOutsideSubgroup H (List.ofFn fun i => classSquareElement (P i).idealClass) <
          Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))) := by
  classical
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro k P hP C hgenus hmiss
  apply exists_proper_squareSubgroup_with_few_coordinates_of_no_signedProduct
    (fun i => (P i).idealClass) C hgenus
  intro σ hσ
  obtain ⟨J, hJc, hJn⟩ := exists_ideal_of_signed_goodMaximals hD P hP σ
  exact hmiss J hJn (hJc.trans hσ)

end Bernays
