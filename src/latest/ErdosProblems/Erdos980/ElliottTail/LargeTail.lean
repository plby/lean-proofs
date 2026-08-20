import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The large-value part of Elliott's tail argument

This file contains the order-theoretic and asymptotic step that combines a
rarity bound for exceptional primes with a pointwise Pólya--Vinogradov bound
for the least power nonresidue.  The number-theoretic inputs are deliberately
arguments of the lemmas below; their concrete proofs live in the sibling
character and large-sieve modules.
-/

namespace Erdos980.ElliottTail

open Filter
open scoped BigOperators Topology

/-- A finite collection of nonnegative weights, each at most `B`, has total
mass at most its cardinality times `B`. -/
lemma sum_le_card_mul_of_nonneg_of_le
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ) (B : ℝ)
    (_hw : ∀ a ∈ s, 0 ≤ w a) (hB : ∀ a ∈ s, w a ≤ B) :
    ∑ a ∈ s, w a ≤ (s.card : ℝ) * B := by
  simpa [nsmul_eq_mul] using
    Finset.sum_le_card_nsmul s w B hB

/-- Cardinality times a pointwise bound controls the weighted exceptional
mass.  This is the finite inequality used on the range
`n_k(p) > (log x)^A`. -/
theorem exceptionalWeightedMass_le
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ)
    (C D X : ℝ) (a b : ℝ)
    (hw : ∀ p ∈ s, 0 ≤ w p)
    (hcard : (s.card : ℝ) ≤ C * X ^ a)
    (hpoint : ∀ p ∈ s, w p ≤ D * X ^ b)
    (hbound : 0 ≤ D * X ^ b) :
    ∑ p ∈ s, w p ≤ C * D * X ^ a * X ^ b := by
  calc
    ∑ p ∈ s, w p ≤ (s.card : ℝ) * (D * X ^ b) :=
      sum_le_card_mul_of_nonneg_of_le s w _ hw hpoint
    _ ≤ (C * X ^ a) * (D * X ^ b) :=
      mul_le_mul_of_nonneg_right hcard hbound
    _ = C * D * X ^ a * X ^ b := by ring

/-- The same finite bound with the two real powers combined. -/
theorem exceptionalWeightedMass_le_rpow_add
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ)
    (C D X : ℝ) (a b : ℝ)
    (hw : ∀ p ∈ s, 0 ≤ w p)
    (hcard : (s.card : ℝ) ≤ C * X ^ a)
    (hpoint : ∀ p ∈ s, w p ≤ D * X ^ b)
    (hD : 0 ≤ D) (hX : 0 < X) :
    ∑ p ∈ s, w p ≤ C * D * X ^ (a + b) := by
  rw [Real.rpow_add hX]
  simpa [mul_assoc] using
    exceptionalWeightedMass_le s w C D X a b hw hcard hpoint
      (mul_nonneg hD (Real.rpow_nonneg hX.le _))

/-- A real power `x^γ`, multiplied by one logarithm and normalized by `x`,
tends to zero whenever `γ < 1`. -/
theorem tendsto_natCast_rpow_mul_log_div_natCast_zero
    {γ : ℝ} (hγ : γ < 1) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) ^ γ * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x ^ (1 - γ)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hγ)).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (1 - γ) * (n : ℝ) ^ γ = (n : ℝ) := by
    rw [← Real.rpow_add hnpos, show 1 - γ + γ = 1 by ring,
      Real.rpow_one]
  change
    Real.log (n : ℝ) / (n : ℝ) ^ (1 - γ) =
      (n : ℝ) ^ γ * Real.log (n : ℝ) / (n : ℝ)
  symm
  conv_lhs => rhs; rw [← hpow]
  field_simp [(Real.rpow_pos_of_pos hnpos γ).ne',
    (Real.rpow_pos_of_pos hnpos (1 - γ)).ne']

/-- The power-saving form used after multiplying a rarity exponent by a
pointwise character-sum exponent. -/
theorem tendsto_largeTail_majorant_zero
    {C γ : ℝ} (hγ : γ < 1) :
    Tendsto
      (fun n : ℕ =>
        C * ((n : ℝ) ^ γ * Real.log (n : ℝ) / (n : ℝ)))
      atTop (nhds 0) :=
  by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_natCast_rpow_mul_log_div_natCast_zero hγ) :
        Tendsto
          (fun n : ℕ =>
            C * ((n : ℝ) ^ γ * Real.log (n : ℝ) / (n : ℝ)))
          atTop (nhds (C * 0)))

/-- An eventually nonnegative normalized tail tends to zero as soon as it is
eventually dominated by the power-saving majorant above. -/
theorem tendsto_zero_of_eventually_le_largeTail_majorant
    (f : ℕ → ℝ) {C γ : ℝ} (hγ : γ < 1)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (hf : ∀ᶠ n in atTop,
      f n ≤ C * ((n : ℝ) ^ γ * Real.log (n : ℝ) / (n : ℝ))) :
    Tendsto f atTop (nhds 0) :=
  squeeze_zero' hf0 hf (tendsto_largeTail_majorant_zero hγ)

end Erdos980.ElliottTail
