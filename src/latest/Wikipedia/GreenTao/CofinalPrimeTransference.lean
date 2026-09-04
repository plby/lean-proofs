import Wikipedia.GreenTao.CofinalPrimeModulusAssembly
import Wikipedia.GreenTao.Transference.RelativeSzemeredi
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Order.Filter.Finite

/-!
# Quantitative transference on cofinal prime moduli

This file is the assembly bridge between the three deep inputs:

* uniform dense weighted Szemerédi;
* the relative AP comparison;
* the cyclic majorant linear-forms estimate.

All constants are fixed first.  Once majorization, the linear-forms
condition, and relative comparison hold eventually and uniformly for the
finitely many residues below `W`, an arbitrarily large prime modulus is
chosen beyond their common threshold.  Primality supplies the factorial
coprimality required by the AP cut model.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped Polynomial

/-! ## Uniform eventual majorization over a fixed primorial -/

/-- For fixed `W`, the pointwise majorization theorem has one eventual
threshold valid for every standard representative `b<W`. -/
theorem eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant
    (χ : SmoothSieveCutoff)
    {k W : ℕ} (hk : 3 ≤ k) (hW : 0 < W) :
    ∀ᶠ M : ℕ in atTop,
      ∀ b, b < W →
        ∀ x : ZMod (M + 1),
          wTrickedPrimeWeight
              (primeScale k χ.normalizer) W b x ≤
            χ.cyclicMajorant
              (sieveLevel k (M + 1)) W b x := by
  have hb :
      ∀ b : Fin W,
        ∀ᶠ M : ℕ in atTop,
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight
                (primeScale k χ.normalizer) W b x ≤
              χ.cyclicMajorant
                (sieveLevel k (M + 1)) W b x := by
    intro b
    obtain ⟨N₀, hmajor⟩ :=
      exists_threshold_wTrickedPrimeWeight_le_cyclicMajorant
        χ hk hW b
    filter_upwards [eventually_ge_atTop N₀] with M hM
    exact
      hmajor (M + 1) (hM.trans (Nat.le_succ M))
        (Nat.succ_pos M)
  have hall :
      ∀ᶠ M : ℕ in atTop,
        ∀ b : Fin W,
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight
                (primeScale k χ.normalizer) W b x ≤
              χ.cyclicMajorant
                (sieveLevel k (M + 1)) W b x :=
    Filter.eventually_all.mpr hb
  filter_upwards [hall] with M hM
  intro b hbW
  exact hM ⟨b, hbW⟩

/-! ## Generic cofinal-prime transference assembly -/

/-- **Cofinal prime quantitative transference.**  Suppose the majorant is
eventually valid, satisfies the CFZ linear-forms condition, and has the
required relative counting comparison, uniformly over `b<W`.  A uniform
dense weighted AP lower bound then gives the corresponding cofinal-prime
W-tricked count lower bound.

The density requested of the sparse weight is exactly
`δ + polynomialDenseModelError`; the output count is exactly
`denseCount - countError`. -/
theorem cofinalPrimeUniformWTrickedPrimeProgressionCount_of_eventually
    {r W : ℕ} {α : ℝ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (hα : 0 ≤ α)
    (happroximationError : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1)))
    (hweighted :
      HasUniformWeightedAPCount
        (r + 2) δ denseCount)
    (hν0 :
      ∀ M b (x : ZMod (M + 1)), 0 ≤ ν M b x)
    (hmajor :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b < W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight α W b x ≤ ν M b x)
    (hLF :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b < W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              linearFormsError)
    (hcomparison :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b < W →
          RelativeAPComparisonLe
            r (M + 1) (ν M b)
            (polynomialDenseModelError
              p cutError approximationError)
            countError) :
    CofinalPrimeUniformWTrickedPrimeProgressionCount
      (r + 2) α W
      (δ + polynomialDenseModelError
        p cutError approximationError)
      (denseCount - countError) := by
  have hall :
      ∀ᶠ M : ℕ in atTop,
        (∀ b, b < W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight α W b x ≤ ν M b x) ∧
        (∀ b, b < W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              linearFormsError) ∧
        (∀ b, b < W →
          RelativeAPComparisonLe
            r (M + 1) (ν M b)
            (polynomialDenseModelError
              p cutError approximationError)
            countError) :=
    hmajor.and (hLF.and hcomparison)
  rw [eventually_atTop] at hall
  obtain ⟨Mthreshold, hfrom⟩ := hall
  intro M₀
  obtain ⟨q, hqLarge, hqPrime⟩ :=
    Nat.exists_infinite_primes
      (max (max M₀ Mthreshold) (r + 1) + 1)
  let M := q - 1
  have hqPos : 0 < q := hqPrime.pos
  have hMsucc : M + 1 = q := by
    dsimp [M]
    omega
  have hM₀ : M₀ ≤ M := by
    dsimp [M]
    omega
  have hMthreshold : Mthreshold ≤ M := by
    dsimp [M]
    omega
  have hrank : r + 1 < M + 1 := by
    dsimp [M]
    omega
  obtain ⟨hmajorM, hLFM, hcomparisonM⟩ :=
    hfrom M hMthreshold
  refine
    ⟨M, hM₀, by simpa only [hMsucc] using hqPrime, ?_⟩
  intro b hb hmean
  let : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  exact
    relativeAPCount_lower_bound_of_linearFormsCondition
      happroximationError hcutError
      (wTrickedPrimeWeight_nonneg hα W b)
      (hmajorM b hb)
      (hν0 M b)
      hp
      (hLFM b hb)
      (by
        have hrankq : r + 1 < q := by
          simpa only [← hMsucc] using hrank
        have hcoprime :
            Nat.Coprime q (Nat.factorial (r + 1)) :=
          hqPrime.coprime_factorial_of_lt hrankq
        simpa only [hMsucc] using hcoprime)
      hconvert
      (hweighted (M + 1))
      hmean
      (hcomparisonM b hb)

end Wikipedia.SzemeredisTheorem
