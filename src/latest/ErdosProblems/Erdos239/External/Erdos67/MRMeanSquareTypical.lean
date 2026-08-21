import ErdosProblems.Erdos239.External.Erdos67.MRTTypicalReduction
import ErdosProblems.Erdos239.External.Erdos67.MRMeanSquareProof

/-!
# The typical-factorisation reduction for the complex MR mean square

The corrected complex Matomäki--Radziwiłł input concerns merely
multiplicative functions, whereas the convenient bilinear identity in
`MRTTypicalReduction` was stated for completely multiplicative functions.
This file supplies the two finite reductions needed before applying the
Dirichlet-polynomial estimates:

* an `L²` typical/atypical decomposition whose left-hand side is exactly
  `uncenteredShortIntervalMeanSquare`; and
* the corrected Ramaré expansion for a merely multiplicative function.  The
  latter keeps the terms `p ∣ n / p` as a separate prime-square error and
  factors `f (p * k)` only on the coprime main terms.

Both results are unconditional finite identities/inequalities.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-! ## The `L²` exceptional-set reduction -/

theorem normSq_add_le_two_mul (z w : ℂ) :
    Complex.normSq (z + w) ≤
      2 * Complex.normSq z + 2 * Complex.normSq w := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  have htri := norm_add_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hsquare : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg hz hw)).2 htri
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

@[simp]
theorem modulatedShortSum_zero (f : ℕ → ℂ) (n H : ℕ) :
    modulatedShortSum f n H 0 =
      ∑ j ∈ Finset.Icc 1 H, f (n + j) := by
  simp [modulatedShortSum, additivePhase]

/-- The difference between a short sum and its typical part has norm at
most the length of the interval. -/
theorem norm_modulatedShortSum_sub_typical_le_length
    {blocks : Finset (ℕ × ℕ)} {Z : ℕ} {f : ℕ → ℂ}
    {n H : ℕ} {alpha : ℝ}
    (hrange : ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ‖modulatedShortSum f n H alpha -
        typicalModulatedShortSum blocks Z f n H alpha‖ ≤ H := by
  calc
    ‖modulatedShortSum f n H alpha -
        typicalModulatedShortSum blocks Z f n H alpha‖ ≤
        ∑ j ∈ Finset.Icc 1 H,
          if n + j ∈ atypicalFactorizationSet blocks Z then (1 : ℝ) else 0 :=
      norm_modulatedShortSum_sub_typical_le hrange hf
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs <;> norm_num
    _ = H := by simp

/-- Squaring the exceptional part costs one further factor `H`.
The formulation is pointwise so it can also be used with weighted or
restricted sets of starting points. -/
theorem normSq_modulatedShortSum_sub_typical_le_length_mul_norm
    {blocks : Finset (ℕ × ℕ)} {Z : ℕ} {f : ℕ → ℂ}
    {n H : ℕ} {alpha : ℝ}
    (hrange : ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    Complex.normSq
        (modulatedShortSum f n H alpha -
          typicalModulatedShortSum blocks Z f n H alpha) ≤
      H * ‖modulatedShortSum f n H alpha -
        typicalModulatedShortSum blocks Z f n H alpha‖ := by
  rw [Complex.normSq_eq_norm_sq]
  let E := ‖modulatedShortSum f n H alpha -
    typicalModulatedShortSum blocks Z f n H alpha‖
  have hE : E ≤ (H : ℝ) := by
    exact norm_modulatedShortSum_sub_typical_le_length hrange hf
  have hE0 : 0 ≤ E := norm_nonneg _
  change E ^ 2 ≤ (H : ℝ) * E
  nlinarith

/-- The square mass of the exceptional part, averaged over `(X,2X]`, is
at most `H²` times the total number of atypical integers in the ambient
range. -/
theorem sum_Ioc_normSq_modulatedShortSum_sub_typical_le
    {blocks : Finset (ℕ × ℕ)} {Z X : ℕ} {f : ℕ → ℂ}
    {H : ℕ} {alpha : ℝ}
    (hrange : ∀ n ∈ Finset.Icc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (modulatedShortSum f n H alpha -
          typicalModulatedShortSum blocks Z f n H alpha)) ≤
      H ^ 2 * (atypicalFactorizationSet blocks Z).card := by
  let E : ℕ → ℂ := fun n ↦
    modulatedShortSum f n H alpha -
      typicalModulatedShortSum blocks Z f n H alpha
  have hsubset : Finset.Ioc X (2 * X) ⊆ Finset.Icc X (2 * X) := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  calc
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n)) ≤
        ∑ n ∈ Finset.Icc X (2 * X), Complex.normSq (E n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn hnot
      exact Complex.normSq_nonneg _
    _ ≤ ∑ n ∈ Finset.Icc X (2 * X), (H : ℝ) * ‖E n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact normSq_modulatedShortSum_sub_typical_le_length_mul_norm
        (hrange n hn) hf
    _ = (H : ℝ) * ∑ n ∈ Finset.Icc X (2 * X), ‖E n‖ := by
      rw [Finset.mul_sum]
    _ ≤ (H : ℝ) *
        ((H : ℝ) * (atypicalFactorizationSet blocks Z).card) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg H)
      exact sum_norm_modulatedShortSum_sub_typical_le hrange hf
    _ = (H : ℝ) ^ 2 * (atypicalFactorizationSet blocks Z).card := by ring

/-- Exact finite typical/atypical reduction for the left-hand side of
`MRComplexNonpretentiousMeanSquareInput`. -/
theorem uncenteredShortIntervalMeanSquare_le_typical_add_atypical
    (blocks : Finset (ℕ × ℕ)) (f : ℕ → ℂ) (X H : ℕ)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    uncenteredShortIntervalMeanSquare f X H ≤
      2 * (∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks (2 * X + H) f n H 0)) +
      2 * (H : ℝ) ^ 2 *
        (atypicalFactorizationSet blocks (2 * X + H)).card := by
  let T : ℕ → ℂ := fun n ↦
    typicalModulatedShortSum blocks (2 * X + H) f n H 0
  let E : ℕ → ℂ := fun n ↦ modulatedShortSum f n H 0 - T n
  have hrange : ∀ n ∈ Finset.Icc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ 2 * X + H := by
    intro n hn j hj
    have hn' := (Finset.mem_Icc.mp hn).2
    have hj' := (Finset.mem_Icc.mp hj).2
    omega
  have herr :
      (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n)) ≤
        (H : ℝ) ^ 2 *
          (atypicalFactorizationSet blocks (2 * X + H)).card := by
    exact sum_Ioc_normSq_modulatedShortSum_sub_typical_le hrange hf
  unfold uncenteredShortIntervalMeanSquare
  simp_rw [← modulatedShortSum_zero]
  calc
    (∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq (modulatedShortSum f n H 0)) =
        ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n + T n) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      dsimp [E, T]
      ring
    _ ≤ ∑ n ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (E n) + 2 * Complex.normSq (T n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact normSq_add_le_two_mul (E n) (T n)
    _ = 2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (T n)) +
        2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ 2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (T n)) +
        2 * ((H : ℝ) ^ 2 *
          (atypicalFactorizationSet blocks (2 * X + H)).card) := by
      gcongr
    _ = 2 * (∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (typicalModulatedShortSum blocks (2 * X + H) f n H 0)) +
        2 * (H : ℝ) ^ 2 *
          (atypicalFactorizationSet blocks (2 * X + H)).card := by
      simp only [T]
      ring

/-- Quantitative endpoint of the preceding reduction.  Thus it suffices
to prove square-mean cancellation for the typical part and a density bound
for the atypical set. -/
theorem uncenteredShortIntervalMeanSquare_le_of_typical_of_density
    {blocks : Finset (ℕ × ℕ)} {f : ℕ → ℂ} {X H : ℕ}
    {eta rho : ℝ}
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (htypical :
      (∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks (2 * X + H) f n H 0)) ≤
        eta ^ 2 * H ^ 2 * X)
    (hbad : ((atypicalFactorizationSet blocks (2 * X + H)).card : ℝ) ≤
      rho * X) :
    uncenteredShortIntervalMeanSquare f X H ≤
      2 * (eta ^ 2 + rho) * H ^ 2 * X := by
  have hbase :=
    uncenteredShortIntervalMeanSquare_le_typical_add_atypical blocks f X H hf
  have hHsq : 0 ≤ (H : ℝ) ^ 2 := sq_nonneg _
  calc
    uncenteredShortIntervalMeanSquare f X H ≤
        2 * (∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (typicalModulatedShortSum blocks (2 * X + H) f n H 0)) +
        2 * (H : ℝ) ^ 2 *
          (atypicalFactorizationSet blocks (2 * X + H)).card := hbase
    _ ≤ 2 * (eta ^ 2 * (H : ℝ) ^ 2 * X) +
        2 * (H : ℝ) ^ 2 * (rho * X) := by
      gcongr
    _ = 2 * (eta ^ 2 + rho) * (H : ℝ) ^ 2 * X := by ring

/-! ## Corrected Ramaré factorisation for multiplicative functions -/

/-- For a merely multiplicative function, the Ramaré expansion factors on
the terms for which `p` does not divide the cofactor.  The complementary
terms are retained verbatim; these are precisely the prime-square error.
-/
theorem multiplicative_ramare_bilinear_split
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (hSpos : ∀ n ∈ S, 0 < n)
    (g w : ℕ → ℂ) (hg : IsMultiplicativeOnPositiveNat g) :
    (∑ n ∈ S, w n * g n) =
      ∑ p ∈ P, ∑ n ∈ S,
        if p ∣ n then
          if p ∣ n / p then
            w n * g n / (ramareDenominator P p (n / p) : ℂ)
          else
            w n * (g p * g (n / p)) /
              (ramareDenominator P p (n / p) : ℂ)
        else 0 := by
  rw [sum_eq_ramare_expansion_commuted hP hS (fun n ↦ w n * g n)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hpn hsq
  · rfl
  · have hp0 : 0 < p := (hP p hp).pos
    have hn0 : 0 < n := hSpos n hn
    have hk0 : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp0
    have hcop : Nat.Coprime p (n / p) :=
      (hP p hp).coprime_iff_not_dvd.mpr hsq
    rw [← hg.2 p (n / p) hp0 hk0 hcop, Nat.mul_div_cancel' hpn]
  · rfl

/-- Cofactor-indexed version of the corrected multiplicative Ramaré
split.  This is the form in which the main term becomes a prime Dirichlet
polynomial and the `p ∣ k` term is estimated as a prime-square error. -/
theorem multiplicative_ramare_cofactor_split
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (hSpos : ∀ n ∈ S, 0 < n)
    (g w : ℕ → ℂ) (hg : IsMultiplicativeOnPositiveNat g) :
    (∑ n ∈ S, w n * g n) =
      ∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
        if p ∣ k then
          w (p * k) * g (p * k) /
            (ramareDenominator P p k : ℂ)
        else
          w (p * k) * (g p * g k) /
            (ramareDenominator P p k : ℂ) := by
  rw [multiplicative_ramare_bilinear_split hP hS hSpos g w hg]
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_dvd_eq_sum_divisorCofactorImage S (hP p hp).pos
    (fun n k ↦
      if p ∣ k then
        w n * g n / (ramareDenominator P p k : ℂ)
      else
        w n * (g p * g k) / (ramareDenominator P p k : ℂ))

/-- The typical short sum has an exact cofactor expansion for merely
multiplicative `f`, with the prime-square obstruction displayed explicitly.
-/
theorem typicalModulatedShortSum_eq_multiplicative_ramare_cofactors
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (Z : ℕ) (f : ℕ → ℂ) (n H : ℕ) (alpha : ℝ)
    (hf : IsMultiplicativeOnPositiveNat f) :
    typicalModulatedShortSum blocks Z f n H alpha =
      ∑ p ∈ primesInBlock I,
        ∑ k ∈ divisorCofactorImage (typicalShortSupport blocks Z n H) p,
          if p ∣ k then
            additivePhase alpha (p * k - n) * f (p * k) /
              (ramareDenominator (primesInBlock I) p k : ℂ)
          else
            additivePhase alpha (p * k - n) * (f p * f k) /
              (ramareDenominator (primesInBlock I) p k : ℂ) := by
  rw [typicalModulatedShortSum_eq_support_sum]
  apply multiplicative_ramare_cofactor_split
  · intro p hp
    exact (mem_primesInBlock.mp hp).1
  · intro m hm
    have htyp := (mem_typicalShortSupport.mp hm).1
    exact (mem_typicalFactorizationSet.mp htyp).2.2 I hI
  · intro m hm
    have htyp := (mem_typicalShortSupport.mp hm).1
    exact (mem_typicalFactorizationSet.mp htyp).1
  · exact hf

/-! ## The prime-square error is sparse -/

/-- Number of selected primes whose square divides `n`.  This is exactly
the combinatorial support of the `p ∣ k` branch in the corrected Ramaré
split. -/
def primeSquareDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  (P.filter fun p ↦ p * p ∣ n).card

theorem dvd_div_iff_sq_dvd {p n : ℕ} (hp : 0 < p) (hpn : p ∣ n) :
    p ∣ n / p ↔ p * p ∣ n := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
      _ = p * (p * k) := by rw [hk]
      _ = p * p * k := by ring
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [show p * p * k = p * (p * k) by ring,
      Nat.mul_div_cancel_left _ hp]

/-- The branch condition in the corrected Ramaré split is exactly
square divisibility. -/
theorem card_ramare_square_branch_eq
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (P.filter fun p ↦ p ∣ n ∧ p ∣ n / p).card =
      primeSquareDivisorCount P n := by
  unfold primeSquareDivisorCount
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpP, hpn, hpq⟩
    exact ⟨hpP, (dvd_div_iff_sq_dvd (hP p hpP).pos hpn).mp hpq⟩
  · rintro ⟨hpP, hsq⟩
    have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hsq
    exact ⟨hpP, hpn,
      (dvd_div_iff_sq_dvd (hP p hpP).pos hpn).mpr hsq⟩

/-- Exact average size of the prime-square obstruction on `[1,Z]`.
No primality hypothesis is needed for this counting identity. -/
theorem sum_primeSquareDivisorCount_Icc (P : Finset ℕ) (Z : ℕ) :
    ∑ n ∈ Finset.Icc 1 Z, primeSquareDivisorCount P n =
      ∑ p ∈ P, Z / (p * p) := by
  classical
  calc
    ∑ n ∈ Finset.Icc 1 Z, primeSquareDivisorCount P n =
        ∑ n ∈ Finset.Icc 1 Z,
          ∑ p ∈ P, if p * p ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold primeSquareDivisorCount
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ P,
          ∑ n ∈ Finset.Icc 1 Z, if p * p ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P, Z / (p * p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      have hsets :
          (Finset.Icc 1 Z).filter (fun n ↦ p * p ∣ n) =
            (Finset.Ioc 0 Z).filter (fun n ↦ p * p ∣ n) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hsets]
      exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div Z (p * p)

end

end Erdos67
