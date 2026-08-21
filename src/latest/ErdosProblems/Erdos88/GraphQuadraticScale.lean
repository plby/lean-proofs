import ErdosProblems.Erdos88.GraphQuadraticMoments
import ErdosProblems.Erdos88.SwitchingLemma136

open scoped BigOperators

namespace Erdos88
namespace GraphQuadratic

open Classical

/-- The standard deviation of the perturbed induced-edge count under the
uniform Boolean-cube law. -/
noncomputable def graphPerturbedSigma {n : ℕ} (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) : ℝ :=
  Real.sqrt (Probability.variance (1 / 2 : ℝ)
    (Probability.perturbedEdgePolynomial G e₀ c))

lemma variance_half_perturbedEdgePolynomial_nonneg {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) :
    0 ≤ Probability.variance (1 / 2 : ℝ)
      (Probability.perturbedEdgePolynomial G e₀ c) := by
  rw [variance_half_perturbedEdgePolynomial]
  positivity

lemma graphPerturbedSigma_nonneg {n : ℕ} (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) :
    0 ≤ graphPerturbedSigma G e₀ c :=
  Real.sqrt_nonneg _

lemma graphPerturbedSigma_sq {n : ℕ} (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) :
    graphPerturbedSigma G e₀ c ^ 2 =
      Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) := by
  exact Real.sq_sqrt (variance_half_perturbedEdgePolynomial_nonneg G e₀ c)

lemma n_rpow_three_halves_sq (n : ℕ) :
    ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- Positive edge density and nonnegative perturbations give the lower
`n^(3/2)` standard-deviation scale. -/
theorem graphPerturbedSigma_lower {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    {a : ℝ} (hn : 0 < n) (ha : 0 ≤ a)
    (hc : ∀ i, 0 ≤ c i)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
    (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
      graphPerturbedSigma G e₀ c := by
  have hlhs : 0 ≤ (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  rw [graphPerturbedSigma]
  apply (Real.le_sqrt hlhs
    (variance_half_perturbedEdgePolynomial_nonneg G e₀ c)).2
  calc
      ((a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 =
        (a ^ 2 / 4) * (n : ℝ) ^ 3 := by
        rw [mul_pow]
        rw [n_rpow_three_halves_sq n]
        ring
    _ ≤ Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) :=
      variance_half_perturbedEdgePolynomial_lower G e₀ c hn ha hc hedge

lemma graphPerturbedSigma_pos {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    {a : ℝ} (hn : 0 < n) (ha : 0 < a)
    (hc : ∀ i, 0 ≤ c i)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
    0 < graphPerturbedSigma G e₀ c := by
  rw [graphPerturbedSigma]
  apply Real.sqrt_pos.2
  refine lt_of_lt_of_le ?_
    (variance_half_perturbedEdgePolynomial_lower G e₀ c hn ha.le hc hedge)
  positivity

/-- A linear perturbation bounded by `R n` gives the upper `n^(3/2)`
standard-deviation scale. -/
theorem graphPerturbedSigma_upper {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n) :
    graphPerturbedSigma G e₀ c ≤
      R * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have hrhs : 0 ≤ R * (n : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  rw [graphPerturbedSigma]
  apply (Real.sqrt_le_left hrhs).2
  calc
    Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) ≤
        R ^ 2 * (n : ℝ) ^ 3 :=
      Switching.variance_perturbedEdgePolynomial_half_le G e₀ c R hR hc
    _ = (R * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
      rw [mul_pow]
      rw [n_rpow_three_halves_sq n]

/-- The graph hypotheses used in the analytic branches place the standard
deviation between two explicit constant multiples of `n^(3/2)`. -/
theorem graphPerturbedSigma_scale {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    {a R : ℝ} (hn : 0 < n) (ha : 0 ≤ a)
    (hcNonneg : ∀ i, 0 ≤ c i)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    (hR : 1 ≤ R) (hcBound : ∀ v, |c v| ≤ R * n) :
    (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
        graphPerturbedSigma G e₀ c ∧
      graphPerturbedSigma G e₀ c ≤
        R * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  exact ⟨graphPerturbedSigma_lower G e₀ c hn ha hcNonneg hedge,
    graphPerturbedSigma_upper G e₀ c R hR hcBound⟩

end GraphQuadratic
end Erdos88
