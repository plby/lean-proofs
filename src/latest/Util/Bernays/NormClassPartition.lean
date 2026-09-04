import Util.Bernays.ClassLSeries
import Util.Bernays.GoodIdealNormFibers
import Util.Bernays.GenusNorms

/-!
# The genus-character weight is constant on an ideal norm fiber
-/

open scoped Classical

namespace Bernays

def idealNormClassFiberEquiv {R : Type*} [CommRing R] [IsDomain R]
    (F : Ideal R) (n : ℕ) (C : ClassGroup R) :
    {I : GoodIdealNormFiber F n // I.1.idealClass = C} ≃
      {I : CoprimeIdealsInClass R C F // (I.1 : Ideal R).cardQuot = n} where
  toFun I := ⟨⟨I.1.1, I.2, I.1.2.2⟩, I.1.2.1⟩
  invFun I := ⟨⟨I.1.1, I.2, I.1.2.2⟩, I.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem idealClassNormCount_sum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (n : ℕ) :
    letI := quadraticOrderIsDomain hD
    letI := quadraticOrderClassGroupFintype hD
    (∑ C, idealClassNormCount C F n) = Nat.card (GoodIdealNormFiber F n) := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  let := finite_goodIdealNormFiber hD F n
  have hsum : (∑ C, idealClassNormCount C F n) =
      ∑ C, Nat.card {I : GoodIdealNormFiber F n // I.1.idealClass = C} := by
    apply Finset.sum_congr rfl
    intro C _
    exact (Nat.card_congr (idealNormClassFiberEquiv F n C)).symm
  rw [hsum, ← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun I : GoodIdealNormFiber F n => I.1.idealClass))

theorem weightedIdealNormCoeff_eq_const {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (n : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (a : ℂ),
      (∀ I : GoodIdealNormFiber F n, w I.1.idealClass = a) →
      weightedIdealNormCoeff hD F w n = a * (Nat.card (GoodIdealNormFiber F n) : ℂ) := by
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  intro w a hw
  unfold weightedIdealNormCoeff
  rw [← idealClassNormCount_sum hD F n, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  by_cases h : Nonempty {I : CoprimeIdealsInClass (QuadraticAlgebra ℤ d b) C F //
      (I.1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n}
  · obtain ⟨I⟩ := h
    have hwa := hw ⟨I.1.1, I.2, I.1.2.2⟩
    rw [I.1.2.1] at hwa
    rw [hwa]
  · have : IsEmpty {I : CoprimeIdealsInClass (QuadraticAlgebra ℤ d b) C F //
        (I.1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n} := not_nonempty_iff.mp h
    have hz : idealClassNormCount C F n = 0 := by simp [idealClassNormCount]
    simp only [hz, Nat.cast_zero, mul_zero]

theorem genusWeightedIdealNormCoeff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (n : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      weightedIdealNormCoeff hD (quadraticBadIdeal d b)
        (fun C => ψ (Additive.ofMul (genusMap C))) n =
      ψ (Additive.ofMul (genusValue hD n)) *
        (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) : ℂ) := by
  let := quadraticOrderIsDomain hD
  intro ψ
  apply weightedIdealNormCoeff_eq_const hD
  intro I
  rw [← genusValue_goodIdeal_norm hD I.1 I.2.2, I.2.1]

end Bernays
