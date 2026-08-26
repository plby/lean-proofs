import ErdosProblems.Erdos4.DivisibilityExpansion
import ErdosProblems.Erdos4.ProductOrthogonality

/-!
# Products of divisibility indicators and the exact main term

Two occupied labels at one prime are compatible precisely when they are
equal. Compatible labels merge into one divisibility condition; an
incompatible pair contributes zero. The product of the local densities
is the reciprocal merged divisor, and its quadratic form in the actual
divisor coefficients equals the original orthonormal coefficient energy.
-/

open scoped BigOperators

namespace Erdos4.IndicatorProducts

open LocalIndicatorExpansion DivisibilityExpansion DivisorCoefficients

variable {k : ℕ}

def Compatible (a b : Option (Fin k)) : Prop := a = none ∨ b = none ∨ a = b

def join (a b : Option (Fin k)) : Option (Fin k) := if a = none then b else a

open Classical in
theorem indicator_mul (s a b : Option (Fin k)) :
    indicator s a * indicator s b = if Compatible a b then indicator s (join a b) else 0 := by
  cases a with
  | none => simp [Compatible, join, indicator]
  | some i =>
    cases b with
    | none => simp [Compatible, join, indicator]
    | some j =>
      by_cases hij : i = j
      · subst j
        by_cases hs : s = some i <;> simp [Compatible, join, indicator, hs]
      · by_cases hsi : s = some i
        · subst s
          simp [Compatible, join, indicator, hij]
        · simp [Compatible, join, indicator, hsi, hij]

noncomputable def localDensity (ell : ℝ) (a b : Option (Fin k)) : ℝ := by
  classical
  exact if Compatible a b then (if join a b = none then 1 else 1 / ell) else 0

theorem mean_indicator {ell : ℝ} (hell : (k : ℝ) < ell) (b : Option (Fin k)) :
    LocalOrthogonality.mean ell (fun s => indicator s b) = if b = none then 1 else 1 / ell := by
  classical
  cases b with
  | none => simpa [indicator] using LocalOrthogonality.mean_one hell
  | some i => simp [LocalOrthogonality.mean, indicator]

theorem mean_indicator_mul {ell : ℝ} (hell : (k : ℝ) < ell) (a b : Option (Fin k)) :
    LocalOrthogonality.mean ell (fun s => indicator s a * indicator s b) = localDensity ell a b := by
  classical
  simp_rw [indicator_mul]
  by_cases hab : Compatible a b
  · simp only [if_pos hab, localDensity]
    exact mean_indicator hell (join a b)
  · simp [hab, localDensity, LocalOrthogonality.mean]

variable {P : Type*} [Fintype P] [DecidableEq P]

def CompatibleLabels (a b : P → Option (Fin k)) : Prop := ∀ p, Compatible (a p) (b p)

def joinLabels (a b : P → Option (Fin k)) : P → Option (Fin k) := fun p => join (a p) (b p)

noncomputable def jointDensity (ell : P → ℕ) (a b : P → Option (Fin k)) : ℝ :=
  ∏ p, localDensity (ell p : ℝ) (a p) (b p)

open Classical in
theorem evaluation_mul (s a b : P → Option (Fin k)) :
    evaluation s a * evaluation s b =
      if CompatibleLabels a b then evaluation s (joinLabels a b) else 0 := by
  unfold evaluation
  rw [← Finset.prod_mul_distrib]
  simp_rw [indicator_mul]
  by_cases hab : CompatibleLabels a b
  · rw [if_pos hab]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [if_pos (hab p)]
    rfl
  · rw [if_neg hab]
    obtain ⟨p, hp⟩ := not_forall.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

open Classical in
theorem jointDensity_eq (ell : P → ℕ) (a b : P → Option (Fin k)) :
    jointDensity ell a b =
      if CompatibleLabels a b then (totalDivisor ell (joinLabels a b) : ℝ)⁻¹ else 0 := by
  unfold jointDensity
  by_cases hab : CompatibleLabels a b
  · rw [if_pos hab]
    unfold totalDivisor
    rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p _hp
    simp only [localDensity, if_pos (hab p), joinLabels]
    by_cases hj : join (a p) (b p) = none <;> simp [hj, one_div]
  · rw [if_neg hab]
    obtain ⟨p, hp⟩ := not_forall.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [localDensity, hp])

theorem mean_evaluation_mul (ell : P → ℕ) (hell : ∀ p, (k : ℝ) < ell p)
    (a b : P → Option (Fin k)) :
    ProductOrthogonality.mean (fun p => (ell p : ℝ))
      (fun s => evaluation s a * evaluation s b) = jointDensity ell a b := by
  classical
  have hfactor : ∀ s : P → Option (Fin k),
      ProductOrthogonality.stateWeight (fun p => (ell p : ℝ)) s * (evaluation s a * evaluation s b) =
        ∏ p, LocalOrthogonality.stateWeight (ell p : ℝ) k (s p) *
          (indicator (s p) (a p) * indicator (s p) (b p)) := by
    intro s
    simp only [ProductOrthogonality.stateWeight, evaluation, Finset.prod_mul_distrib]
  unfold ProductOrthogonality.mean
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun p (s : Option (Fin k)) =>
    LocalOrthogonality.stateWeight (ell p : ℝ) k s * (indicator s (a p) * indicator s (b p)))]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [← LocalOrthogonality.mean_eq_sum]
  exact mean_indicator_mul (hell p) (a p) (b p)

/-- The divisor-expansion main term is exactly the original coefficient
energy, with no approximation or diagonal-only replacement. -/
theorem coefficient_joint_sum_eq_energy (m : ℝ) (R : ℕ) (ell : P → ℕ)
    (hell : ∀ p, (k : ℝ) < ell p) :
    (∑ a : P → Option (Fin k), ∑ b : P → Option (Fin k),
      (divisorCoefficient m R ell a * divisorCoefficient m R ell b) * jointDensity ell a b) =
      RestrictedProductNorm.energy (coefficient (k := k) m R ell) := by
  classical
  have hbase := ProductOrthogonality.mean_expansion_sq (fun p => (ell p : ℝ)) hell
    (coefficient (k := k) m R ell)
  have hexpand : ∀ s : P → Option (Fin k),
      ProductOrthogonality.expansion (fun p => (ell p : ℝ)) (coefficient m R ell) s =
        ∑ b, divisorCoefficient m R ell b * evaluation s b := by
    intro s
    exact (expansion_eq m R ell s).symm
  have hpoint : ∀ s : P → Option (Fin k),
      (∑ a, divisorCoefficient m R ell a * evaluation s a) ^ 2 =
        ∑ a, ∑ b, (divisorCoefficient m R ell a * divisorCoefficient m R ell b) *
          (evaluation s a * evaluation s b) := by
    intro s
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _hb => by ring)
  simp_rw [hexpand, hpoint, ProductOrthogonality.mean_sum,
    ProductOrthogonality.mean_const_mul, mean_evaluation_mul ell hell] at hbase
  exact hbase

end Erdos4.IndicatorProducts
