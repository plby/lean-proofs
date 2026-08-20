/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveParameters
import ErdosProblems.Erdos48.BadRootIncidence
import ErdosProblems.Erdos48.EndpointMass
import ErdosProblems.Erdos48.ProductPairEndpointMass

/-!
# Vaughan bounds for power-sieve bad roots

This file packages the finite last step of the power-scale bad-root
argument.  A lower bound for the number of endpoint-bad auxiliary partners
is combined with the endpoint Vaughan mean, separately for bad auxiliary
conductors and bad product conductors.
-/

namespace Erdos48

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- The Vaughan endpoint budget used for one conductor range. -/
def primitiveEndpointVaughanBudget (x M : ℕ) : ℝ :=
  vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
    vaughanPrimitiveMeanEquationOneOnePolynomial x M *
      vaughanPrimitiveMeanEquationOneOneLogPower x

/-- Markov's inequality and Vaughan's endpoint mean bound the number of bad
auxiliary conductors in an arbitrary finite prime set below `M`. -/
theorem badAuxiliaryConductors_card_mul_le_vaughan
    {x M : ℕ} {R : Finset ℕ}
    (hx : 4 ≤ x) (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ))
    (hR : ∀ r ∈ R, r.Prime) (hupper : ∀ r ∈ R, r ≤ M) :
    ((((R.filter fun r ↦
          (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) *
        ((x : ℝ) / 10)) ≤
      primitiveEndpointVaughanBudget x M := by
  have hRsub : R ⊆ Finset.Icc 1 M := by
    intro r hr
    exact Finset.mem_Icc.mpr ⟨(hR r hr).one_le, hupper r hr⟩
  calc
    ((((R.filter fun r ↦
          (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) *
        ((x : ℝ) / 10)) ≤
        ∑ r ∈ R, primitiveEndpointMass x r :=
      card_filter_mul_le_sum_of_nonneg R
        (fun r ↦ primitiveEndpointMass x r) (by positivity)
        (fun r _ ↦ primitiveEndpointMass_nonneg x r)
    _ ≤ ∑ r ∈ Finset.Icc 1 M, primitiveEndpointMass x r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hRsub
      intro r hrM hrR
      exact primitiveEndpointMass_nonneg x r
    _ ≤ primitiveEndpointVaughanBudget x M := by
      simpa only [primitiveEndpointVaughanBudget] using
        sum_primitiveEndpointMass_le_vaughan hx hM

/-- The clean reusable dyadic bad-root estimate.  The first Vaughan budget
controls endpoint-bad auxiliaries, with multiplicity `Q.card`; the second
controls endpoint-bad products, whose multiplication fibers have size at
most two. -/
theorem badRoots_card_mul_mul_threshold_le_vaughan
    {x M A : ℕ} {E Q R : Finset ℕ}
    (hx : 4 ≤ x) (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ))
    (hE : E ⊆ Q)
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hRupper : ∀ r ∈ R, r ≤ M)
    (hprodUpper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ M)
    (hpartners : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners x q R).card) :
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
      ((Q.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x M +
        2 * primitiveEndpointVaughanBudget x M := by
  have hincidence := badRoots_card_mul_le_auxiliary_add_product
    hE hpartners
  have haux := badAuxiliaryConductors_card_mul_le_vaughan
    hx hM hR hRupper
  have hproducts := badPrimePairs_card_mul_le_two_mul_vaughan
    hx hM hQ hR hprodUpper
  change ((((Q.product R).filter fun qr ↦
      (x : ℝ) / 10 <
        primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ) *
      ((x : ℝ) / 10) ≤
        2 * primitiveEndpointVaughanBudget x M at hproducts
  have hcast : ((E.card * A : ℕ) : ℝ) ≤
      (((Q.card *
          (R.filter fun r ↦
            (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) +
        ((((Q.product R).filter fun qr ↦
          (x : ℝ) / 10 <
            primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ)) := by
    exact_mod_cast hincidence
  calc
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
        ((((Q.card *
            (R.filter fun r ↦
              (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) +
          ((((Q.product R).filter fun qr ↦
            (x : ℝ) / 10 <
              primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ)) *
            ((x : ℝ) / 10)) := by
      exact mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ((Q.card : ℕ) : ℝ) *
          (((R.filter fun r ↦
            (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) *
              ((x : ℝ) / 10) +
        ((((Q.product R).filter fun qr ↦
          (x : ℝ) / 10 <
            primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ) *
              ((x : ℝ) / 10) := by
      push_cast
      ring
    _ ≤ ((Q.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x M +
          2 * primitiveEndpointVaughanBudget x M := by
      apply add_le_add _ hproducts
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left haux (Nat.cast_nonneg Q.card)

/-- A slightly more compact form of the same estimate. -/
theorem badRoots_card_mul_mul_threshold_le_card_add_two_mul_vaughan
    {x M A : ℕ} {E Q R : Finset ℕ}
    (hx : 4 ≤ x) (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ))
    (hE : E ⊆ Q)
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hRupper : ∀ r ∈ R, r ≤ M)
    (hprodUpper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ M)
    (hpartners : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners x q R).card) :
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
      (((Q.card : ℕ) : ℝ) + 2) *
        primitiveEndpointVaughanBudget x M := by
  have h := badRoots_card_mul_mul_threshold_le_vaughan
    hx hM hE hQ hR hRupper hprodUpper hpartners
  calc
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
        ((Q.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x M +
          2 * primitiveEndpointVaughanBudget x M := h
    _ = (((Q.card : ℕ) : ℝ) + 2) *
          primitiveEndpointVaughanBudget x M := by ring

/-! ## Integer-power specialization -/

/-- Natural cutoff equal to the square root of the power-sieve endpoint. -/
def powerSieveVaughanCutoff (n L : ℕ) : ℕ := n ^ (120 * L)

theorem powerSieveVaughanCutoff_sq (n L : ℕ) :
    (powerSieveVaughanCutoff n L) ^ 2 = powerSieveX n L := by
  simp only [powerSieveVaughanCutoff, powerSieveX, ← pow_mul]
  congr 1
  omega

theorem powerSieveVaughanCutoff_le_sqrt (n L : ℕ) :
    (powerSieveVaughanCutoff n L : ℝ) ≤
      Real.sqrt (powerSieveX n L : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast (powerSieveVaughanCutoff_sq n L).le

/-- Every auxiliary prime lies below the Vaughan cutoff. -/
theorem powerSieveAuxPrime_le_vaughanCutoff
    {n L Q r : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    r ≤ powerSieveVaughanCutoff n L := by
  have hrUpper : r ≤ powerSieveAuxUpper n L Q :=
    (mem_powerSieveAuxPrimes.mp hr).2.1
  calc
    r ≤ powerSieveAuxUpper n L Q := hrUpper
    _ ≤ powerSieveSmoothBound n L :=
      powerSieveAuxUpper_le_smoothBound hn hL hQ
    _ ≤ n ^ (120 * L) := by
      simp only [powerSieveSmoothBound]
      exact pow_le_pow_right' hn (by omega)
    _ = powerSieveVaughanCutoff n L := rfl

/-- A root in the dyadic block `(Q,2Q]` times an auxiliary prime still lies
below the square-root Vaughan cutoff.  This uses the block-dependent term
`n^(120L-7)/Q` in the auxiliary core; bounding the two factors separately by
the smoothness cutoff would be much too weak. -/
theorem powerSieve_root_mul_auxPrime_le_vaughanCutoff
    {n L Q q r : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L)
    (hq : q ≤ 2 * Q)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    q * r ≤ powerSieveVaughanCutoff n L := by
  let A := powerSieveAuxScale n L
  let B := powerSieveProductBase n L
  let U := powerSieveSmoothBound n L
  let C := powerSieveAuxCore n L Q
  have hn1 : 1 ≤ n := by omega
  have hrUpper : r ≤ C * A := by
    simpa only [C, A, powerSieveAuxUpper] using
      (mem_powerSieveAuxPrimes.mp hr).2.1
  have hcore : C ≤ B / Q + A := by
    dsimp only [C, B, A, powerSieveAuxCore]
    apply max_le
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _
  have hdiv : Q * (B / Q) ≤ B := Nat.mul_div_le B Q
  have hBA : B * A = U := by
    simpa only [B, A, U] using
      powerSieveProductBase_mul_auxScale (n := n) hL
  have hUAA : U * A * A = n ^ (120 * L - 4) := by
    dsimp only [U, A, powerSieveSmoothBound, powerSieveAuxScale]
    simp only [← pow_succ]
    congr 1
    omega
  have hUle : U ≤ n ^ (120 * L - 4) := by
    dsimp only [U, powerSieveSmoothBound]
    exact pow_le_pow_right' hn1 (by omega)
  have hpowers :
      2 * B * A + 2 * U * A * A ≤ n ^ (120 * L) := by
    have hfour : 4 ≤ n ^ 4 := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
        _ ≤ n ^ 4 := pow_le_pow_right' hn1 (by omega)
    calc
      2 * B * A + 2 * U * A * A =
          2 * U + 2 * n ^ (120 * L - 4) := by
        calc
          2 * B * A + 2 * U * A * A =
              2 * (B * A) + 2 * (U * A * A) := by ring
          _ = _ := by rw [hBA, hUAA]
      _ ≤ 4 * n ^ (120 * L - 4) := by omega
      _ ≤ n ^ (120 * L - 4) * n ^ 4 := by
        simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left (n ^ (120 * L - 4)) hfour
      _ = n ^ (120 * L) := by
        rw [← pow_add]
        congr 1
        omega
  calc
    q * r ≤ (2 * Q) * (C * A) := Nat.mul_le_mul hq hrUpper
    _ ≤ (2 * Q) * ((B / Q + A) * A) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right A hcore)
    _ = 2 * (Q * (B / Q)) * A + 2 * Q * A * A := by ring
    _ ≤ 2 * B * A + 2 * U * A * A := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right A (Nat.mul_le_mul_left 2 hdiv)
      · exact Nat.mul_le_mul_right A
          (Nat.mul_le_mul_right A
            (Nat.mul_le_mul_left 2 (by simpa only [U] using hQupper)))
    _ ≤ n ^ (120 * L) := hpowers
    _ = powerSieveVaughanCutoff n L := rfl

/-- Power-parameter instance of the dyadic bad-root cardinal estimate. -/
theorem powerSieve_badRoots_card_mul_mul_threshold_le_vaughan
    {n L Q0 A : ℕ} {E Q : Finset ℕ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ0 : 1 ≤ Q0)
    (hQ0upper : Q0 ≤ powerSieveSmoothBound n L)
    (hE : E ⊆ Q)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQblock : ∀ q ∈ Q, q ≤ 2 * Q0)
    (hpartners : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners (powerSieveX n L) q
        (powerSieveAuxPrimes n L Q0)).card) :
    (((E.card * A : ℕ) : ℝ) *
        ((powerSieveX n L : ℝ) / 10)) ≤
      (((Q.card : ℕ) : ℝ) + 2) *
        primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveVaughanCutoff n L) := by
  have hn1 : 1 ≤ n := by omega
  have hx : 4 ≤ powerSieveX n L := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ (240 * L) := pow_le_pow_right' hn1 (by omega)
      _ = powerSieveX n L := rfl
  apply badRoots_card_mul_mul_threshold_le_card_add_two_mul_vaughan
    (R := powerSieveAuxPrimes n L Q0)
    hx (powerSieveVaughanCutoff_le_sqrt n L) hE hQprime
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.2
  · intro r hr
    exact powerSieveAuxPrime_le_vaughanCutoff hn1 hL hQ0 hr
  · intro q hq r hr
    exact powerSieve_root_mul_auxPrime_le_vaughanCutoff hn hL
      hQ0upper (hQblock q hq) hr
  · exact hpartners

end

end Erdos48
