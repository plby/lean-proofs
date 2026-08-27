import ErdosProblems.Erdos4.FGKMTSieveEnergy
import ErdosProblems.Erdos4.IdealAction

/-! Exact positive ideal-kernel contributions for pairs with a common divisor core. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients IdealProjection IdealAction Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem freeze_ne_anchor (j : Fin k) (a : Option (Fin k)) : freeze j a ≠ some j := by
  unfold freeze
  split_ifs with h
  · simp
  · exact h

theorem compatible_of_coordinateDivisor_eq (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a c : P → Option (Fin k))
    (hcore : ∀ i, i ≠ j → coordinateDivisor ell a i = coordinateDivisor ell c i) :
    Compatible j a c := by
  intro p
  apply Option.ext
  intro i
  by_cases hij : i = j
  · subst i
    simp only [freeze_ne_anchor, iff_self]
  · rw [freeze_eq_some_iff j i hij, freeze_eq_some_iff j i hij,
      ← prime_dvd_coordinateDivisor_iff ell hprime hinj a p i,
      ← prime_dvd_coordinateDivisor_iff ell hprime hinj c p i, hcore i hij]

theorem fiberWeight_eq_anchor_totient (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a c : P → Option (Fin k)) (hac : Compatible j a c) :
    fiberWeight ell j a c = ((coordinateDivisor ell c j).totient : ℝ)⁻¹ := by
  rw [totient_coordinateDivisor ell hprime hinj, Nat.cast_prod, ← Finset.prod_inv_distrib]
  unfold fiberWeight
  apply Finset.prod_congr rfl
  intro p _
  cases hc : c p with
  | none => simp [localWeight]
  | some i =>
    by_cases hij : i = j
    · subst i
      have hfr : freeze j (a p) = none := by rw [hac p, hc]; simp [freeze]
      simp only [hfr, if_true, Nat.cast_sub (hprime p).one_le, Nat.cast_one]
      exact CoefficientMass.localWeight_some_sq (hprime p).one_le j
    · have hfr : freeze j (a p) = some i := by rw [hac p, hc]; simp [freeze, hij]
      simp [hfr, hij]

noncomputable def sieveWindowDensity (ell : P → ℕ) : ℝ :=
  ∏ p, ((ell p : ℝ) - 1) / ell p

theorem sieveWindowDensity_nonneg (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) :
    0 ≤ sieveWindowDensity ell := by
  apply Finset.prod_nonneg
  intro p _
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hp : (1 : ℝ) ≤ ell p := by exact_mod_cast hell p
  linarith

noncomputable def rationalIdealPair (b : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k)
    (a c : P → Option (Fin k)) : ℝ :=
  rationalCoefficient b R ell a * rationalCoefficient b R ell c *
    ∏ p, kernel (ell p : ℝ) j (a p) (c p)

noncomputable def rationalIdealForm (b : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k) : ℝ :=
  ∑ a : P → Option (Fin k), ∑ c : P → Option (Fin k), rationalIdealPair b R ell j a c

theorem rationalIdealPair_nonneg {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p) (j : Fin k) (a c : P → Option (Fin k)) :
    0 ≤ rationalIdealPair b R ell j a c := by
  apply mul_nonneg
  · exact mul_nonneg (rationalCoefficient_nonneg hb R ell a) (rationalCoefficient_nonneg hb R ell c)
  · exact Finset.prod_nonneg (fun p _ => kernel_nonneg (by exact_mod_cast hell p) j (a p) (c p))

theorem rationalIdealPair_eq (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a c : P → Option (Fin k)) (hac : Compatible j a c)
    (ha : totalDivisor ell a ≤ R) (hc : totalDivisor ell c ≤ R) :
    rationalIdealPair b R ell j a c = activeDensity ell j a *
      (rationalProfileProduct b ell a * rationalProfileProduct b ell c *
        normalization ell a ^ 2 * ((coordinateDivisor ell c j).totient : ℝ)⁻¹) := by
  unfold rationalIdealPair
  rw [rationalCoefficient, if_pos ha, rationalCoefficient, if_pos hc]
  calc
    _ = (rationalProfileProduct b ell a * rationalProfileProduct b ell c * normalization ell a) *
        ((∏ p, kernel (ell p : ℝ) j (a p) (c p)) * normalization ell c) := by ring
    _ = (rationalProfileProduct b ell a * rationalProfileProduct b ell c * normalization ell a) *
        (normalization ell a * activeDensity ell j a *
          ((coordinateDivisor ell c j).totient : ℝ)⁻¹) := by
      rw [kernelProduct_mul_normalization ell (fun p => (hprime p).two_le) j a c hac,
        fiberWeight_eq_anchor_totient ell hprime hinj j a c hac]
    _ = _ := by ring

theorem rationalIdealPair_lower {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a c : P → Option (Fin k)) (hac : Compatible j a c)
    (ha : totalDivisor ell a ≤ R) (hc : totalDivisor ell c ≤ R) :
    sieveWindowDensity ell *
      (rationalProfileProduct b ell a * rationalProfileProduct b ell c *
        normalization ell a ^ 2 * ((coordinateDivisor ell c j).totient : ℝ)⁻¹) ≤
      rationalIdealPair b R ell j a c := by
  rw [rationalIdealPair_eq b R ell hprime hinj j a c hac ha hc]
  apply mul_le_mul_of_nonneg_right (density_product_le_active ell (fun p => (hprime p).two_le) j a)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (rationalProfileProduct_nonneg hb ell a)
      (rationalProfileProduct_nonneg hb ell c)) (sq_nonneg _))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end Erdos4.FGKMT
