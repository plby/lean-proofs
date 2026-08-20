import ErdosProblems.Erdos980.ElliottTail.OddAuxiliaryScaleCore
import ErdosProblems.Erdos980.ElliottTail.OddRosserParameters

/-!
# Norm-sieve adapters for the odd auxiliary scale

This module transports the uniform subpower estimate to the natural ceiling
used by the norm sieve and absorbs its fixed lower-endpoint contributions.
-/

open Filter
open scoped NumberField Topology nonZeroDivisors

namespace Erdos980.ElliottTail.OddAuxiliaryScale

open NumberField OddMediumParameters OddRosserParameters

noncomputable section

/-- Natural-ceiling form of the uniform subpower bound. -/
theorem eventually_uniform_auxiliaryModulus_le_normSieveUpper
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      (t + 1) ^ oddTensorDepth t ≤ normSieveUpper δ x := by
  filter_upwards [eventually_uniform_auxiliaryModulus_le_rpow hδ]
    with x hx
  intro t ht
  have hreal := hx t ht
  have hceil : (x : ℝ) ^ δ ≤ (normSieveUpper δ x : ℝ) := by
    simpa only [normSieveUpper] using Nat.le_ceil ((x : ℝ) ^ δ)
  exact_mod_cast hreal.trans hceil

/-- The natural upper endpoint tends to infinity for every positive power. -/
theorem tendsto_normSieveUpper_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (normSieveUpper δ) atTop atTop := by
  unfold normSieveUpper
  exact tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop)

/-- The moving upper endpoint eventually dominates the complete norm-sieve
lower endpoint, uniformly in every layer below `smoothParameterY x` and in
every ray modulus bounded by the auxiliary modulus. -/
theorem eventually_normSieveLower_le_normSieveUpper_of_auxiliaryModulus
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ∀ f : ℕ, f ≤ (t + 1) ^ oddTensorDepth t →
        normSieveLower K J f ≤ normSieveUpper δ x := by
  let fixedLower : ℕ :=
    max (2 * normSieveDimension K)
      (Ideal.absNorm (J : Ideal (RingOfIntegers K)))
  have hfixed : ∀ᶠ x : ℕ in atTop,
      fixedLower ≤ normSieveUpper δ x :=
    (tendsto_normSieveUpper_atTop hδ).eventually
      (eventually_ge_atTop fixedLower)
  filter_upwards
      [eventually_uniform_auxiliaryModulus_le_normSieveUpper hδ, hfixed]
      with x hmod hfixedX
  intro t ht f hf
  have hfUpper : f ≤ normSieveUpper δ x := hf.trans (hmod t ht)
  unfold normSieveLower
  apply max_le
  · exact (le_max_left _ _).trans hfixedX
  · apply max_le
    · exact hfUpper
    · exact (le_max_right _ _).trans hfixedX

/-- Product form for consumers that keep the auxiliary-prime family rather
than its scalar modulus. -/
theorem eventually_uniform_auxiliaryProduct_le_normSieveUpper
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ∀ Q : Finset ℕ, Q.card ≤ oddTensorDepth t →
        (∀ q ∈ Q, q ≤ t + 1) → Q.prod id ≤ normSieveUpper δ x := by
  filter_upwards [eventually_uniform_auxiliaryModulus_le_normSieveUpper hδ]
    with x hx
  intro t ht Q hcard hQ
  calc
    Q.prod id ≤ Q.prod (fun _ ↦ t + 1) :=
      Finset.prod_le_prod' fun q hq ↦ hQ q hq
    _ = (t + 1) ^ Q.card := by simp
    _ ≤ (t + 1) ^ oddTensorDepth t := by
      exact Nat.pow_le_pow_right (by omega) hcard
    _ ≤ normSieveUpper δ x := hx t ht

end

end Erdos980.ElliottTail.OddAuxiliaryScale
