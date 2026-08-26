import ErdosProblems.Erdos69.LargePrimeAverages
import ErdosProblems.Erdos69.RationalPhase

/-! # Separating fixed, small free, and large prime contributions -/

open scoped BigOperators

namespace Erdos69.Elementary

def freePrimes (Q y : ℕ) : Finset ℕ := (Nat.primesLE y).filter (fun p ↦ ¬p ∣ Q)

noncomputable def fixedPrimeCount (Q y b : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE y).filter (fun p ↦ p ∣ Q), if p ∣ b then (1 : ℝ) else 0

theorem smallPrimeCount_affine_split (Q y b t : ℕ) :
    smallPrimeCount (b + Q * t) y = fixedPrimeCount Q y b +
      ∑ p ∈ freePrimes Q y, if p ∣ b + Q * t then (1 : ℝ) else 0 := by
  classical
  have hsum := Finset.sum_filter_add_sum_filter_not (Nat.primesLE y) (fun p ↦ p ∣ Q)
    (fun p ↦ if p ∣ b + Q * t then (1 : ℝ) else 0)
  have hfixed : (∑ p ∈ (Nat.primesLE y).filter (fun p ↦ p ∣ Q),
      if p ∣ b + Q * t then (1 : ℝ) else 0) = fixedPrimeCount Q y b := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpQ := (Finset.mem_filter.mp hp).2
    simp only [← Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpQ t)]
  rw [hfixed] at hsum
  exact hsum.symm

theorem weighted_omega_affine_decomposition {ι : Type*} [Fintype ι]
    (Q y b t : ℕ) (s : ι → ℕ) (c : ι → ℝ)
    (hpos : ∀ i, 0 < b + Q * t + s i) :
    (∑ i, c i * (omegaCount (b + Q * t + s i) : ℝ)) =
      (∑ i, c i * fixedPrimeCount Q y (b + s i)) +
      (∑ p ∈ freePrimes Q y, ∑ i, c i *
        (if p ∣ b + Q * t + s i then (1 : ℝ) else 0)) +
      ∑ i, c i * (largePrimeCount (b + Q * t + s i) y : ℝ) := by
  have hsmall (i : ι) : smallPrimeCount (b + Q * t + s i) y =
      fixedPrimeCount Q y (b + s i) +
        ∑ p ∈ freePrimes Q y, if p ∣ b + Q * t + s i then (1 : ℝ) else 0 := by
    simpa only [Nat.add_right_comm] using smallPrimeCount_affine_split Q y (b + s i) t
  simp_rw [omegaCount_eq_small_add_large _ y (hpos _), hsmall, mul_add]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := freePrimes Q y)]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem norm_mean_fourierPhase_add_const (μ : FiniteLaw Ω) (X : Ω → ℝ) (c : ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (c + X x))‖ =
      ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ := by
  simp only [fourierPhase_add, complexMean_const_mul, norm_mul, norm_fourierPhase, one_mul]

theorem norm_mean_fourierPhase_compare_shift (μ : FiniteLaw Ω) (W Z : Ω → ℝ) (c : ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (W x))‖ ≤
      ‖μ.complexMean (fun x ↦ fourierPhase (Z x))‖ +
        2 * Real.pi * μ.mean (fun x ↦ |W x - (c + Z x)|) := by
  have h := norm_mean_fourierPhase_sub_le μ W (fun x ↦ c + Z x)
  have ht := norm_le_norm_add_norm_sub
    (μ.complexMean (fun x ↦ fourierPhase (c + Z x)))
    (μ.complexMean (fun x ↦ fourierPhase (W x)))
  rw [norm_sub_rev] at ht
  rw [norm_mean_fourierPhase_add_const] at ht
  linarith

theorem weighted_largePrime_mean_le {ι : Type*} [Fintype ι]
    (T Q b y R X : ℕ) (hT : 0 < T) (hQ : 0 < Q) (hQy : Q ≤ y)
    (hyR : y ≤ R) (hR : 1 < R) (s : ι → ℕ) (c : ι → ℝ)
    (hpos : ∀ (t : Fin T) i, 0 < b + Q * t.val + s i)
    (hupper : ∀ (t : Fin T) i, b + Q * t.val + s i ≤ X) :
    (uniform T hT).mean (fun t ↦
      |∑ i, c i * (largePrimeCount (b + Q * t.val + s i) y : ℝ)|) ≤
        (∑ i, |c i|) * (primeReciprocalSum R - primeReciprocalSum y +
          ((primeWindow y R).card : ℝ) / T + Real.log X / Real.log R) := by
  have habs (t : Fin T) : |∑ i, c i * (largePrimeCount (b + Q * t.val + s i) y : ℝ)| ≤
      ∑ i, |c i| * (largePrimeCount (b + Q * t.val + s i) y : ℝ) := by
    calc
      _ ≤ ∑ i, |c i * (largePrimeCount (b + Q * t.val + s i) y : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, Nat.abs_cast]
  apply ((uniform T hT).mean_mono habs).trans
  rw [mean_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [mean_const_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (c i))
  have h := uniform_largePrimeCount_le T Q (b + s i) y R X hT hQ hQy hyR hR
    (fun t ↦ by simpa only [Nat.add_right_comm] using hpos t i)
    (fun t ↦ by simpa only [Nat.add_right_comm] using hupper t i)
  simpa only [Nat.add_right_comm] using h

theorem affine_omega_fourier_compare_small {ι : Type*} [Fintype ι]
    (T Q b y R X : ℕ) (hT : 0 < T) (hQ : 0 < Q) (hQy : Q ≤ y)
    (hyR : y ≤ R) (hR : 1 < R) (s : ι → ℕ) (c : ι → ℝ)
    (hpos : ∀ (t : Fin T) i, 0 < b + Q * t.val + s i)
    (hupper : ∀ (t : Fin T) i, b + Q * t.val + s i ≤ X) :
    ‖(uniform T hT).complexMean (fun t ↦ fourierPhase
      (∑ i, c i * (omegaCount (b + Q * t.val + s i) : ℝ)))‖ ≤
        ‖(uniform T hT).complexMean (fun t ↦ fourierPhase
          (∑ p ∈ freePrimes Q y, ∑ i, c i *
            (if p ∣ b + Q * t.val + s i then (1 : ℝ) else 0)))‖ +
        2 * Real.pi * (∑ i, |c i|) *
          (primeReciprocalSum R - primeReciprocalSum y + ((primeWindow y R).card : ℝ) / T +
            Real.log X / Real.log R) := by
  have hcompare := norm_mean_fourierPhase_compare_shift (uniform T hT)
    (fun t ↦ ∑ i, c i * (omegaCount (b + Q * t.val + s i) : ℝ))
    (fun t ↦ ∑ p ∈ freePrimes Q y, ∑ i, c i *
      (if p ∣ b + Q * t.val + s i then (1 : ℝ) else 0))
    (∑ i, c i * fixedPrimeCount Q y (b + s i))
  simp_rw [weighted_omega_affine_decomposition Q y b _ s c (hpos _),
    add_sub_cancel_left] at hcompare ⊢
  have hlarge := weighted_largePrime_mean_le T Q b y R X hT hQ hQy hyR hR s c hpos hupper
  have hmul := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ 2 * Real.pi)
  calc
    _ ≤ _ := hcompare
    _ ≤ _ := by linarith

end FiniteLaw

end Erdos69.Elementary
