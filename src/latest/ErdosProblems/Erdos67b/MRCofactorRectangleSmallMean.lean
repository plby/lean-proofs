import ErdosProblems.Erdos67b.MRCofactorIntervalSmallMean
import ErdosProblems.Erdos67b.MRCofactorRectangleRounding
import ErdosProblems.Erdos67b.MRCofactorRectangleIdentity

/-!
# Uniform smallness of the actual rounded scheduled cofactor rectangle

The actual typical support, erased distinguished block, natural endpoints,
and original denominator are retained. All scale conditions are imposed
at the lower cofactor endpoint; subsequent schedule estimates discharge them.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_uniform_small_scheduled_cofactor_rectangle
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X P Q : ℕ}, M₀ ≤ M → Y₀ ≤ X / Q →
        4 ≤ P → P ≤ Q → Q ≤ 2 * P → 2 * Q ^ 2 ≤ X →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (p₁ q₁ : ℝ) (J : ℕ) (I : ℕ × ℕ),
        (∀ j ∈ Finset.Icc 1 J,
          primesInBlock (mrScheduledPrimeInterval p₁ q₁ j) ⊆ primesUpTo (X / Q)) →
        Set.PairwiseDisjoint (↑(Finset.Icc 1 J) : Set ℕ)
          (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) →
        (∀ j ∈ Finset.Icc 1 J, ∀ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j),
          Real.log (p : ℝ) ≤ Real.log (X / Q : ℕ) / 16) →
        (∀ j ∈ Finset.Icc 1 J, 2 * Real.log (j : ℝ) ≤
          ∑ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j), 1 / (p : ℝ)) →
        (∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta (X / Q)) →
        (∀ j ∈ Finset.Icc 1 J, ∀ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j),
          p ≤ mrCofactorPowerCutoff delta (X / Q)) →
        (∀ j ∈ Finset.Icc 1 J, ∀ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j), 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
          (mrFiniteCofactorLineCoefficient A f) (-t)‖ ≤ epsilon := by
  obtain ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, hinterval⟩ :=
    mrExists_uniform_small_interval_cofactor_polynomial 8 (by norm_num) hepsilon
  refine ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, ?_⟩
  intro M X P Q hM hY hP hPQ hQP hsize A hA p₁ q₁ J I
    hB hdisj hsmall hmass hAy hBy hlarge f hmul hbound hnonpret t ht
  have hPpos : 0 < P := by omega
  have hQpos : 0 < Q := hPpos.trans_le hPQ
  have hQX : Q ≤ X := by
    calc
      Q = 1 * Q := by omega
      _ ≤ (2 * Q) * Q := Nat.mul_le_mul_right Q (by omega)
      _ = 2 * Q ^ 2 := by ring
      _ ≤ X := hsize
  have horder := mrCofactor_rectangle_endpoints_order (X := X) hPpos hPQ
  have hratio := mrCofactor_rectangle_upper_le_eight_lower hPpos hPQ hQP hQX
  have hUX : (2 * X) / P ≤ X := by
    have h := mrCofactor_rectangle_upper_twice_le (X := X) hP
    omega
  have hlog := mrCofactor_rectangle_log_lower hQpos hsize
  have hwindow := mrCofactor_rectangle_frequency_window hP ht
  let J' := mrScheduledRemainingIndices p₁ q₁ J I
  let B : ℕ → Finset ℕ := fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)
  have hsub : J' ⊆ Finset.Icc 1 J := mrScheduledRemainingIndices_subset p₁ q₁ J I
  rw [mrTypicalCofactorRectangle_polynomial_eq_indexed]
  change ‖logarithmicDirichletPolynomial (Finset.Ioc (X / Q) ((2 * X) / P))
    (fun n ↦ mrIndexedTypicalCofactorCoefficient A J' B f n / (n : ℂ)) (-t)‖ ≤ epsilon
  apply hinterval hM hY horder hratio hUX hlog A hA J' B
  · intro j hj
    exact (Finset.mem_Icc.1 (hsub hj)).1
  · intro j hj
    exact hB j (hsub hj)
  · intro i hi j hj hij
    exact hdisj (hsub hi) (hsub hj) hij
  · intro j hj p hp
    exact hsmall j (hsub hj) p hp
  · intro j hj
    exact hmass j (hsub hj)
  · exact hAy
  · intro j hj p hp
    exact hBy j (hsub hj) p hp
  · intro j hj p hp
    exact hlarge j (hsub hj) p hp
  · exact hmul
  · exact hbound
  · exact hnonpret
  · exact hwindow

end

end Erdos67b
