import ErdosProblems.Erdos4.LabelResidueClass
import ErdosProblems.Erdos4.IndicatorProducts

/-!
# Finite normalization of the actual affine weights

The main term is the full orthonormal coefficient energy. Each compatible
pair of divisor labels has interval-count error at most `φ(W)`, and the
total error is bounded by this constant times the square of the absolute
divisor-coefficient mass.
-/

open scoped BigOperators

namespace Erdos4.AffineNormalization

open DivisorCoefficients DivisibilityExpansion IndicatorProducts

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def pairCount (Y W : ℕ) (h : Fin k → ℕ) (p : ℕ)
    (a b : P → Option (Fin k)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, if n.Coprime W then
    evaluation (AffineWeights.residueState ell h n p) a *
      evaluation (AffineWeights.residueState ell h n p) b else 0

theorem pairCount_error_le (Y W : ℕ) (hW : 0 < W) (hWcop : ∀ l, W.Coprime (ell l))
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell))
    (a b : P → Option (Fin k)) :
    |pairCount ell Y W h p a b -
      BoundedGaps.Maynard.coprimeHarmonicDensity W * Y * jointDensity ell a b| ≤ Nat.totient W := by
  classical
  unfold pairCount
  simp_rw [evaluation_mul, jointDensity_eq]
  by_cases hab : CompatibleLabels a b
  · simp only [if_pos hab]
    simpa only [div_eq_mul_inv] using
      LabelResidueClass.count_error_le ell Y W hW hWcop hcop h hh p hp (joinLabels a b)
  · simp [hab]

theorem amplitude_sq_expansion (m : ℝ) (R : ℕ) (h : Fin k → ℕ) (p n : ℕ) :
    AffineWeights.amplitude ell m R h p n ^ 2 =
      ∑ a : P → Option (Fin k), ∑ b : P → Option (Fin k),
        (divisorCoefficient m R ell a * divisorCoefficient m R ell b) *
          (evaluation (AffineWeights.residueState ell h n p) a *
            evaluation (AffineWeights.residueState ell h n p) b) := by
  unfold AffineWeights.amplitude
  rw [← expansion_eq, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _hb => by ring)

noncomputable def normalizer (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, AffineWeights.weight ell m R Y W h p n

theorem normalizer_nonneg (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p : ℕ) :
    0 ≤ normalizer ell m R Y W h p :=
  Finset.sum_nonneg (fun n _hn => AffineWeights.weight_nonneg ell m R Y W h p n)

theorem normalizer_eq_pairs (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p : ℕ) :
    normalizer ell m R Y W h p =
      ∑ a : P → Option (Fin k), ∑ b : P → Option (Fin k),
        (divisorCoefficient m R ell a * divisorCoefficient m R ell b) * pairCount ell Y W h p a b := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 Y) :
      AffineWeights.weight ell m R Y W h p n =
        ∑ a : P → Option (Fin k), ∑ b : P → Option (Fin k),
          (divisorCoefficient m R ell a * divisorCoefficient m R ell b) *
            (if n.Coprime W then evaluation (AffineWeights.residueState ell h n p) a *
              evaluation (AffineWeights.residueState ell h n p) b else 0) := by
    by_cases hc : n.Coprime W
    · rw [AffineWeights.weight, if_pos ⟨hn, hc⟩]
      simp only [if_pos hc]
      exact amplitude_sq_expansion ell m R h p n
    · simp [AffineWeights.weight, hc]
  unfold normalizer
  calc
    _ = ∑ n ∈ Finset.Icc 1 Y, ∑ a : P → Option (Fin k), ∑ b : P → Option (Fin k),
          (divisorCoefficient m R ell a * divisorCoefficient m R ell b) *
            (if n.Coprime W then evaluation (AffineWeights.residueState ell h n p) a *
              evaluation (AffineWeights.residueState ell h n p) b else 0) :=
      Finset.sum_congr rfl hpoint
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _hb
      exact (Finset.mul_sum _ _ _).symm

section FiniteError

variable {I : Type*} [Fintype I]

/-- Uniform entrywise errors control a finite quadratic form by the square
of the absolute coefficient mass. -/
theorem quadratic_error_le (c : I → ℝ) (E : I → I → ℝ) {B : ℝ}
    (hE : ∀ a b, |E a b| ≤ B) :
    |∑ a, ∑ b, (c a * c b) * E a b| ≤ B * (∑ a, |c a|) ^ 2 := by
  calc
    _ ≤ ∑ a, |∑ b, (c a * c b) * E a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, |(c a * c b) * E a b| :=
      Finset.sum_le_sum (fun a _ha => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, (|c a| * |c b|) * B := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hE a b) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

end FiniteError

theorem normalizer_error_le (m : ℝ) (R Y W : ℕ) (hW : 0 < W)
    (hWcop : ∀ l, W.Coprime (ell l))
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (hell : ∀ l, (k : ℝ) < ell l)
    (h : Fin k → ℕ) (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell)) :
    |normalizer ell m R Y W h p -
      BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
        RestrictedProductNorm.energy (coefficient (k := k) m R ell)| ≤
      Nat.totient W * (∑ b : P → Option (Fin k), |divisorCoefficient m R ell b|) ^ 2 := by
  classical
  have hid : normalizer ell m R Y W h p -
      BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
        RestrictedProductNorm.energy (coefficient (k := k) m R ell) =
      ∑ a : P → Option (Fin k), ∑ b : P → Option (Fin k),
        (divisorCoefficient m R ell a * divisorCoefficient m R ell b) *
          (pairCount ell Y W h p a b -
            BoundedGaps.Maynard.coprimeHarmonicDensity W * Y * jointDensity ell a b) := by
    rw [normalizer_eq_pairs, ← coefficient_joint_sum_eq_energy m R ell hell]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  rw [hid]
  exact quadratic_error_le (divisorCoefficient m R ell) _
    (pairCount_error_le ell Y W hW hWcop hcop h hh p hp)

end Erdos4.AffineNormalization
