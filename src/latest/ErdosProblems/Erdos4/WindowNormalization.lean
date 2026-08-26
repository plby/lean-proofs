import ErdosProblems.Erdos4.AffineNormalization
import ErdosProblems.Erdos4.WindowWeightBound

/-!
# Normalization and probability weights on a prime window

A fixed lower prime cutoff gives an error of at most `φ(W) exp(1)² R⁴`
for every source prime larger than `R`. The same cutoff bounds every raw
weight. Once the error is smaller than half the main term, division by
the actual normalizer gives a probability distribution and a uniform
atom bound.
-/

open scoped BigOperators

namespace Erdos4.WindowNormalization

open ArithmeticFibers DivisorCoefficients DivisibilityExpansion AffineNormalization

theorem window_coprime_small (K R : ℕ) (l : primeWindow K R) :
    (primorial K).Coprime (l : ℕ) := by
  have hl := (mem_primeWindow.mp l.property).1
  apply Nat.Coprime.symm
  apply (hl.coprime_iff_not_dvd).mpr
  intro hd
  exact (not_le_of_gt (mem_primeWindow.mp l.property).2.1) (hl.dvd_primorial_iff.mp hd)

theorem window_pairwise_coprime (K R : ℕ) :
    Pairwise (fun l r : primeWindow K R => (l : ℕ).Coprime (r : ℕ)) :=
  ProductCharacterEncoding.pairwise_coprime_of_prime (fun l : primeWindow K R => (l : ℕ))
    (fun l => (mem_primeWindow.mp l.property).1) Subtype.val_injective

/-- Finite uniform bounds with all small-prime conditions discharged by
one fixed lower cutoff. The cutoff can subsequently be enlarged. -/
theorem exists_uniform_normalization {m : ℝ} (hm : 1 ≤ m) (k : ℕ) :
    ∃ K₀ : ℕ, k + 2 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ R : ℕ, 2 ≤ R →
      ∀ Y p : ℕ, p.Prime → R < p →
        |normalizer (fun l : primeWindow K R => (l : ℕ)) m R Y (primorial K)
            (AffineWeights.shift K : Fin k → ℕ) p -
          BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Y *
            RestrictedProductNorm.energy (coefficient (k := k) m R
              (fun l : primeWindow K R => (l : ℕ)))| ≤
          Nat.totient (primorial K) * Real.exp 1 ^ 2 * (R : ℝ) ^ 4 ∧
        ∀ n : ℕ, AffineWeights.weight (fun l : primeWindow K R => (l : ℕ)) m R Y
          (primorial K) (AffineWeights.shift K : Fin k → ℕ) p n ≤ Real.exp 1 ^ 2 * (R : ℝ) ^ 4 := by
  obtain ⟨K₀, hK₀, hbounds⟩ := WindowWeightBound.exists_uniform_bounds hm k
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK R hR Y p hp hpR
  let ell : primeWindow K R → ℕ := fun l => l
  have hell (l : primeWindow K R) : (k : ℝ) < ell l := by
    have hl := (mem_primeWindow.mp l.property).2.1
    have hkK := hK₀.trans hK
    exact_mod_cast (show k < ell l by dsimp [ell]; omega)
  have hh : ∀ l, Function.Injective
      (fun i : Fin k => (AffineWeights.shift K i : ZMod (ell l))) := by
    intro l
    exact AffineWeights.shift_mod_injective K (ell l)
      (mem_primeWindow.mp l.property).1 (mem_primeWindow.mp l.property).2.1
      (by have := hK₀.trans hK; omega)
  have hpmod := ProductPrimeMeanSquare.coprime_modulus_of_prime_gt ell hp
    (fun l => (mem_primeWindow.mp l.property).2.2.trans_lt hpR)
  have herror := normalizer_error_le ell m R Y (primorial K) (primorial_pos K)
    (window_coprime_small K R) (window_pairwise_coprime K R) hell
    (AffineWeights.shift K) hh p hpmod
  have hmass := (hbounds K hK R hR).1
  have hmass0 : 0 ≤ ∑ b : primeWindow K R → Option (Fin k),
      |divisorCoefficient m R ell b| := Finset.sum_nonneg (fun b _hb => abs_nonneg _)
  have hsq := (sq_le_sq₀ hmass0 (by positivity : 0 ≤ Real.exp 1 * (R : ℝ) ^ 2)).mpr hmass
  constructor
  · calc
      _ ≤ Nat.totient (primorial K) *
          (∑ b : primeWindow K R → Option (Fin k), |divisorCoefficient m R ell b|) ^ 2 := herror
      _ ≤ Nat.totient (primorial K) * (Real.exp 1 * (R : ℝ) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
      _ = _ := by ring
  · exact (hbounds K hK R hR).2 Y (primorial K) (AffineWeights.shift K) p

section Probability

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def probability (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p n : ℕ) : ℝ :=
  AffineWeights.weight ell m R Y W h p n / normalizer ell m R Y W h p

theorem probability_nonneg (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p n : ℕ) :
    0 ≤ probability ell m R Y W h p n :=
  div_nonneg (AffineWeights.weight_nonneg ell m R Y W h p n)
    (normalizer_nonneg ell m R Y W h p)

theorem sum_probability (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p : ℕ)
    (hZ : normalizer ell m R Y W h p ≠ 0) :
    (∑ n ∈ Finset.Icc 1 Y, probability ell m R Y W h p n) = 1 := by
  unfold probability
  rw [← Finset.sum_div]
  exact div_self hZ

theorem normalizer_bounds {m : ℝ} {R Y W : ℕ} (hW : 0 < W) (hY : 0 < Y)
    (hR : 1 ≤ R) (h : Fin k → ℕ) (p : ℕ)
    (herr : |normalizer ell m R Y W h p -
      BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
        RestrictedProductNorm.energy (coefficient (k := k) m R ell)| ≤
          BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / 2) :
    BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / 2 ≤ normalizer ell m R Y W h p ∧
    0 < normalizer ell m R Y W h p ∧
    normalizer ell m R Y W h p ≤ 2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
      RestrictedProductNorm.energy (coefficient (k := k) m R ell) := by
  have hρ := FiberAsymptotic.density_pos hW
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hmain : 0 < BoundedGaps.Maynard.coprimeHarmonicDensity W * Y := mul_pos hρ hYreal
  have hN := one_le_coefficient_energy (k := k) m hR ell
  have hmainN := mul_le_mul_of_nonneg_left hN hmain.le
  have he := abs_le.mp herr
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem probability_le {m : ℝ} {R Y W : ℕ} (hW : 0 < W) (hY : 0 < Y)
    (h : Fin k → ℕ) (p n : ℕ)
    (hZ : BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / 2 ≤ normalizer ell m R Y W h p)
    {B : ℝ} (hw : AffineWeights.weight ell m R Y W h p n ≤ B) :
    probability ell m R Y W h p n ≤ 2 * B /
      (BoundedGaps.Maynard.coprimeHarmonicDensity W * Y) := by
  have hρ := FiberAsymptotic.density_pos hW
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hden : 0 < BoundedGaps.Maynard.coprimeHarmonicDensity W * Y := mul_pos hρ hYreal
  have hhalf : 0 < BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / 2 := by positivity
  unfold probability
  calc
    _ ≤ AffineWeights.weight ell m R Y W h p n /
        (BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / 2) :=
      div_le_div_of_nonneg_left (AffineWeights.weight_nonneg ell m R Y W h p n) hhalf hZ
    _ ≤ B / (BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / 2) :=
      div_le_div_of_nonneg_right hw hhalf.le
    _ = _ := by ring

end Probability

end Erdos4.WindowNormalization
