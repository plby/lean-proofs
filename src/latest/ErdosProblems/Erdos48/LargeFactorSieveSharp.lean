/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.LargeFactorSieve
import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalTotientComparison

/-!
# A fixed-product form of the FLP large-factor sieve

The interval aggregation in `LargeFactorSieve` is convenient for controlling
Bombieri--Vinogradov remainders, but enlarging the multiples of `q*r` to all
cofactors loses the principal factor `1 / phi(q*r)`.  FLP Lemma 2.6 needs
that factor.  This file instead sums the pointwise residual-fibre estimate
only over the actual cofactors `q*r*b`.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

open BoundedGaps.Maynard

/-- The prime-pair residual fibre is contained in the residual prime fibre
obtained by forgetting that `m*s-1` is prime. -/
theorem residualPrimePairFiber_subset_residualPrimeFiber
    (U y z m : ℕ) :
    residualPrimePairFiber U y z m ⊆ Erdos4.residualPrimeFiber U y z m := by
  exact Finset.filter_subset _ _

/-- Pointwise beta-sieve aggregation over the actual cofactors `q*r*b`.
Unlike the interval aggregation, the displayed principal terms retain their
full reciprocal-totient dependence on `q*r*b`. -/
theorem exists_representedLargeFactorPrimes_pointwise_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta Bexp CBV : ℝ}
        {X₀ x u q r B y z S : ℕ},
        2 ≤ z → z ≤ u → 1 < y → y + 1 < q * r → 1 ≤ B →
        101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        PrimeLevelWitness theta Bexp CBV X₀ →
        X₀ ≤ z →
        y ^ S ≤ modulusCutoff theta z →
        (∀ b ∈ Finset.Icc 1 B,
          z ≤ (x + 1) / (q * r * b) ∧
          X₀ ≤ (x + 1) / (q * r * b) ∧
          y ^ S ≤ modulusCutoff theta ((x + 1) / (q * r * b)) ∧
          2 ≤ (x + 1) / (q * r * b)) →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((representedLargeFactorPrimes x u q r B).card : ℝ) ≤
          ∑ b ∈ Finset.Icc 1 B,
            ((Cπ * (((x + 1) / (q * r * b) : ℕ) : ℝ) /
                Real.log (((x + 1) / (q * r * b) : ℕ) : ℝ) *
              ((1 + eta) *
                (CV * ((q * r * b : ℕ) : ℝ) /
                    (Nat.totient (q * r * b) : ℝ) /
                  Real.log (y : ℝ)))) +
              CBV * (((x + 1) / (q * r * b) : ℕ) : ℝ) /
                Real.rpow
                  (Real.log (((x + 1) / (q * r * b) : ℕ) : ℝ)) Bexp +
              CBV * (z : ℝ) /
                Real.rpow (Real.log (z : ℝ)) Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hpoint⟩ :=
    Erdos4.exists_residualPrimeFiber_beta_mertens_upper_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta Bexp CBV X₀ x u q r B y z S hz hzu hy hqr hB hS
    hlogAβ hw hXz hDz hparams
  dsimp only
  have hcardNat :=
    card_representedLargeFactorPrimes_le_sum_residualPrimeFiber
      (x := x) (u := u) (q := q) (r := r) (B := B) (y := y) (z := z)
      hzu hqr
  have hcard :
      ((representedLargeFactorPrimes x u q r B).card : ℝ) ≤
        ∑ b ∈ Finset.Icc 1 B,
          ((residualPrimePairFiber (x + 1) y z (q * r * b)).card : ℝ) := by
    exact_mod_cast hcardNat
  let F : ℕ → ℝ := fun b ↦
    ((Cπ * (((x + 1) / (q * r * b) : ℕ) : ℝ) /
        Real.log (((x + 1) / (q * r * b) : ℕ) : ℝ) *
      ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        (CV * ((q * r * b : ℕ) : ℝ) /
            (Nat.totient (q * r * b) : ℝ) /
          Real.log (y : ℝ)))) +
      CBV * (((x + 1) / (q * r * b) : ℕ) : ℝ) /
        Real.rpow
          (Real.log (((x + 1) / (q * r * b) : ℕ) : ℝ)) Bexp +
      CBV * (z : ℝ) /
        Real.rpow (Real.log (z : ℝ)) Bexp)
  apply hcard.trans
  change (∑ b ∈ Finset.Icc 1 B,
      ((residualPrimePairFiber (x + 1) y z (q * r * b)).card : ℝ)) ≤
    ∑ b ∈ Finset.Icc 1 B, F b
  apply Finset.sum_le_sum
  intro b hb
  have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
  have hqrPos : 0 < q * r := by omega
  have hmPos : 0 < q * r * b := Nat.mul_pos hqrPos hbPos
  have hp := hparams b hb
  by_cases hmEven : Even (q * r * b)
  · have hres := hpoint hmPos hmEven hp.1 hy hS hlogAβ hw hp.2.1 hXz
      hp.2.2.1 hDz hp.2.2.2
    have hsubset := residualPrimePairFiber_subset_residualPrimeFiber
      (x + 1) y z (q * r * b)
    have hpair :
        ((residualPrimePairFiber (x + 1) y z (q * r * b)).card : ℝ) ≤
          ((Erdos4.residualPrimeFiber
            (x + 1) y z (q * r * b)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    change ((residualPrimePairFiber
      (x + 1) y z (q * r * b)).card : ℝ) ≤ F b
    dsimp only [F]
    simpa only [div_eq_mul_inv, mul_assoc] using hpair.trans hres
  ·
    have hempty : residualPrimePairFiber (x + 1) y z (q * r * b) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      exact hmEven (cofactor_even_of_mem_residualPrimePairFiber hz
        (by
          have hle : q * r ≤ q * r * b :=
            Nat.le_mul_of_pos_right (q * r) hbPos
          omega)
        hs)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    change 0 ≤ F b
    dsimp only [F]
    have hlogU : 0 < Real.log
        (((x + 1) / (q * r * b) : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < (x + 1) / (q * r * b) by
        omega))
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast hy)
    have hlogz : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z by omega))
    have hphi : (0 : ℝ) < Nat.totient (q * r * b) := by
      exact_mod_cast Nat.totient_pos.mpr hmPos
    have hCBV : 0 ≤ CBV := hw.1
    have hAβnonneg : 0 ≤ Aβ := zero_le_one.trans hAβ
    have heta : 0 ≤
        (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      positivity
    have hmain : 0 ≤
        Cπ * (((x + 1) / (q * r * b) : ℕ) : ℝ) /
          Real.log (((x + 1) / (q * r * b) : ℕ) : ℝ) *
            ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (CV * ((q * r * b : ℕ) : ℝ) /
                (Nat.totient (q * r * b) : ℝ) /
                  Real.log (y : ℝ))) := by
      positivity
    have herrU : 0 ≤
        CBV * (((x + 1) / (q * r * b) : ℕ) : ℝ) /
          Real.rpow
            (Real.log (((x + 1) / (q * r * b) : ℕ) : ℝ)) Bexp := by
      exact div_nonneg (mul_nonneg hCBV (by positivity))
        (Real.rpow_nonneg hlogU.le _)
    have herrz : 0 ≤ CBV * (z : ℝ) /
        Real.rpow (Real.log (z : ℝ)) Bexp := by
      exact div_nonneg (mul_nonneg hCBV (by positivity))
        (Real.rpow_nonneg hlogz.le _)
    exact add_nonneg (add_nonneg hmain herrU) herrz

/-- Reciprocal totients factor over the fixed positive product `q*r`.
This is the precise inequality which recovers FLP's `1/(qr)` scale after
summing over `b`. -/
theorem sum_inv_totient_fixed_product_le
    {d B : ℕ} (hd : 0 < d) :
    (∑ b ∈ Finset.Icc 1 B, ((Nat.totient (d * b) : ℝ))⁻¹) ≤
      ((Nat.totient d : ℝ))⁻¹ * reciprocalTotientPrefix B := by
  unfold reciprocalTotientPrefix
  have hIcc : Finset.Icc 1 B = Finset.Ioc 0 B := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc]
  calc
    (∑ b ∈ Finset.Ioc 0 B, ((Nat.totient (d * b) : ℝ))⁻¹) ≤
        ∑ b ∈ Finset.Ioc 0 B,
          ((Nat.totient d : ℝ))⁻¹ *
            ((Nat.totient b : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro b hb
      exact inv_totient_mul_le_mul_inv_totient hd
        (Finset.mem_Ioc.mp hb).1
    _ = ((Nat.totient d : ℝ))⁻¹ *
        ∑ b ∈ Finset.Ioc 0 B, ((Nat.totient b : ℝ))⁻¹ := by
      rw [Finset.mul_sum]

/-- A logarithmic version of the preceding fixed-product bound. -/
theorem sum_inv_totient_fixed_product_le_log
    {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    (∑ b ∈ Finset.Icc 1 B, ((Nat.totient (d * b) : ℝ))⁻¹) ≤
      ((Nat.totient d : ℝ))⁻¹ *
        (4 * (1 + Real.log (B : ℝ))) := by
  exact (sum_inv_totient_fixed_product_le hd).trans
    (mul_le_mul_of_nonneg_left
      (reciprocalTotientPrefix_le_four_mul_one_add_log hB) (by positivity))

end

end Erdos48
