/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveBadRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Two-scale Vaughan budgets for the power sieve

The auxiliary-conductor error and the product-conductor error in the
bad-root incidence count live on different conductor scales.  This file
keeps their Vaughan cutoffs separate.  It then supplies the block-dependent
product cutoff used by the integer-power sieve and a quantitative assembly
lemma whose hypotheses are exactly the two analytic budget estimates needed
for a square-root saving in the dyadic bad-root count.
-/

namespace Erdos48

open Filter
open scoped BigOperators Topology
open BoundedGaps.Maynard

noncomputable section

/-- Bad-root incidence with independent Vaughan cutoffs for auxiliary
conductors and product conductors. -/
theorem badRoots_card_mul_mul_threshold_le_two_vaughanCutoffs
    {x Maux Mprod A : ℕ} {E Q R : Finset ℕ}
    (hx : 4 ≤ x)
    (hMaux : (Maux : ℝ) ≤ Real.sqrt (x : ℝ))
    (hMprod : (Mprod : ℝ) ≤ Real.sqrt (x : ℝ))
    (hE : E ⊆ Q)
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hRupper : ∀ r ∈ R, r ≤ Maux)
    (hprodUpper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ Mprod)
    (hpartners : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners x q R).card) :
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
      ((Q.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x Maux +
        2 * primitiveEndpointVaughanBudget x Mprod := by
  have hincidence := badRoots_card_mul_le_auxiliary_add_product
    hE hpartners
  have haux := badAuxiliaryConductors_card_mul_le_vaughan
    hx hMaux hR hRupper
  have hproducts := badPrimePairs_card_mul_le_two_mul_vaughan
    hx hMprod hQ hR hprodUpper
  change ((((Q.product R).filter fun qr ↦
      (x : ℝ) / 10 <
        primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ) *
      ((x : ℝ) / 10) ≤
        2 * primitiveEndpointVaughanBudget x Mprod at hproducts
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
    _ ≤ ((Q.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x Maux +
          2 * primitiveEndpointVaughanBudget x Mprod := by
      apply add_le_add _ hproducts
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left haux (Nat.cast_nonneg Q.card)

/-! ## Block-dependent integer-power cutoffs -/

/-- A product-conductor cutoff retaining the dyadic block parameter.
The term `powerSieveProductBase + Q*n` bounds `Q * powerSieveAuxCore`,
and the two remaining factors account for the dyadic width and auxiliary
scale. -/
def powerSieveProductVaughanCutoff (n L Q : ℕ) : ℕ :=
  2 * (powerSieveProductBase n L + Q * n) * n

/-- The defining auxiliary interval already supplies its sharp Vaughan
cutoff. -/
theorem powerSieveAuxPrime_le_auxUpper
    {n L Q r : ℕ} (hr : r ∈ powerSieveAuxPrimes n L Q) :
    r ≤ powerSieveAuxUpper n L Q :=
  (mem_powerSieveAuxPrimes.mp hr).2.1

/-- A root in `(Q,2Q]` times an auxiliary prime is bounded by the
block-dependent product cutoff. -/
theorem powerSieve_root_mul_auxPrime_le_productVaughanCutoff
    {n L Q q r : ℕ} (hq : q ≤ 2 * Q)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    q * r ≤ powerSieveProductVaughanCutoff n L Q := by
  let P : ℕ := powerSieveProductBase n L
  let C : ℕ := powerSieveAuxCore n L Q
  have hrUpper : r ≤ C * n := by
    simpa only [C, powerSieveAuxUpper, powerSieveAuxScale] using
      (mem_powerSieveAuxPrimes.mp hr).2.1
  have hcore : C ≤ P / Q + n := by
    dsimp only [C, P, powerSieveAuxCore, powerSieveAuxScale]
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hdiv : Q * (P / Q) ≤ P := Nat.mul_div_le P Q
  calc
    q * r ≤ (2 * Q) * (C * n) := Nat.mul_le_mul hq hrUpper
    _ ≤ (2 * Q) * ((P / Q + n) * n) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right n hcore)
    _ = 2 * (Q * (P / Q) + Q * n) * n := by ring
    _ ≤ 2 * (P + Q * n) * n := by
      exact Nat.mul_le_mul_right n
        (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hdiv (Q * n)))
    _ = powerSieveProductVaughanCutoff n L Q := rfl

/-- The sharp auxiliary cutoff remains below the square-root range of
Vaughan's theorem. -/
theorem powerSieveAuxUpper_le_vaughanCutoff
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    powerSieveAuxUpper n L Q ≤ powerSieveVaughanCutoff n L := by
  exact (powerSieveAuxUpper_le_smoothBound hn hL hQ).trans (by
    unfold powerSieveSmoothBound powerSieveVaughanCutoff
    exact pow_le_pow_right' hn (by omega))

/-- The block-dependent product cutoff also lies below `sqrt x`; it saves
four powers of `n` relative to that square-root scale. -/
theorem powerSieveProductVaughanCutoff_le_vaughanCutoff
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    powerSieveProductVaughanCutoff n L Q ≤
      powerSieveVaughanCutoff n L := by
  let U : ℕ := powerSieveSmoothBound n L
  let P : ℕ := powerSieveProductBase n L
  have hn1 : 1 ≤ n := by omega
  have hP : P ≤ U := by
    dsimp only [P, U, powerSieveProductBase, powerSieveSmoothBound]
    exact pow_le_pow_right' hn1 (by omega)
  have hfactor : 2 * (1 + n) * n ≤ n ^ 6 := by
    have hone : 1 + n ≤ 2 * n := by omega
    have hfour : 4 ≤ n ^ 4 := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
        _ ≤ n ^ 4 := pow_le_pow_right' hn1 (by omega)
    calc
      2 * (1 + n) * n ≤ 4 * n ^ 2 := by nlinarith
      _ ≤ n ^ 4 * n ^ 2 := Nat.mul_le_mul_right _ hfour
      _ = n ^ 6 := by ring
  calc
    powerSieveProductVaughanCutoff n L Q = 2 * (P + Q * n) * n := rfl
    _ ≤ 2 * (U + U * n) * n := by gcongr
    _ = U * (2 * (1 + n) * n) := by ring
    _ ≤ U * n ^ 6 := Nat.mul_le_mul_left U hfactor
    _ = n ^ (120 * L - 6) * n ^ 6 := rfl
    _ = n ^ (120 * L) := by
      rw [← pow_add]
      congr 1
      omega
    _ = powerSieveVaughanCutoff n L := rfl

/-- The two-cutoff Vaughan incidence inequality at the actual power-sieve
scales. -/
theorem powerSieve_badRoots_card_mul_mul_threshold_le_twoVaughanBudgets
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
      ((Q.card : ℕ) : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveAuxUpper n L Q0) +
        2 * primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveProductVaughanCutoff n L Q0) := by
  have hn1 : 1 ≤ n := by omega
  have hx : 4 ≤ powerSieveX n L := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ (240 * L) := pow_le_pow_right' hn1 (by omega)
      _ = powerSieveX n L := rfl
  apply badRoots_card_mul_mul_threshold_le_two_vaughanCutoffs
    (R := powerSieveAuxPrimes n L Q0)
    (Maux := powerSieveAuxUpper n L Q0)
    (Mprod := powerSieveProductVaughanCutoff n L Q0)
    hx
  · exact (show (powerSieveAuxUpper n L Q0 : ℝ) ≤
        (powerSieveVaughanCutoff n L : ℝ) by
          exact_mod_cast powerSieveAuxUpper_le_vaughanCutoff hn1 hL hQ0).trans
      (powerSieveVaughanCutoff_le_sqrt n L)
  · exact (show (powerSieveProductVaughanCutoff n L Q0 : ℝ) ≤
        (powerSieveVaughanCutoff n L : ℝ) by
          exact_mod_cast powerSieveProductVaughanCutoff_le_vaughanCutoff
            hn hL hQ0upper).trans
      (powerSieveVaughanCutoff_le_sqrt n L)
  · exact hE
  · exact hQprime
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.2
  · intro r hr
    exact powerSieveAuxPrime_le_auxUpper hr
  · intro q hq r hr
    exact powerSieve_root_mul_auxPrime_le_productVaughanCutoff
      (hQblock q hq) hr
  · exact hpartners

/-! ## Quantitative square-root-saving assembly -/

/-- The natural partner threshold at a block is the auxiliary core divided
by a fixed dilution and by the exponent parameter. -/
def powerSieveVaughanPartnerThreshold (n L Q D : ℕ) : ℕ :=
  powerSieveAuxCore n L Q / (D * L)

theorem powerSieveVaughanPartnerThreshold_pos
    {n L Q D : ℕ} (hD : 0 < D) (hL : 0 < L)
    (hscale : D * L ≤ powerSieveAuxCore n L Q) :
    0 < powerSieveVaughanPartnerThreshold n L Q D := by
  exact Nat.div_pos hscale (Nat.mul_pos hD hL)

/-- Two explicit Vaughan-budget inequalities imply the desired dyadic
square-root saving.  The constants `20` and `40` are chosen so that after
multiplying the incidence estimate by `20*sqrt n`, the auxiliary and
product errors each consume one copy of `Q.card * A * x`.

This theorem deliberately exposes the two analytic threshold hypotheses:
they can be discharged by an independent asymptotic module without
reopening the finite incidence proof. -/
theorem badRoots_card_mul_sqrt_le_card_of_twoVaughanBudgets
    {n x Maux Mprod A : ℕ} {E Q R : Finset ℕ}
    (hx : 4 ≤ x) (hA : 0 < A)
    (hMaux : (Maux : ℝ) ≤ Real.sqrt (x : ℝ))
    (hMprod : (Mprod : ℝ) ≤ Real.sqrt (x : ℝ))
    (hE : E ⊆ Q)
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hRupper : ∀ r ∈ R, r ≤ Maux)
    (hprodUpper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ Mprod)
    (hpartners : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners x q R).card)
    (hauxBudget :
      20 * Real.sqrt (n : ℝ) * primitiveEndpointVaughanBudget x Maux ≤
        (A : ℝ) * (x : ℝ))
    (hprodBudget :
      40 * Real.sqrt (n : ℝ) * primitiveEndpointVaughanBudget x Mprod ≤
        ((Q.card : ℕ) : ℝ) * (A : ℝ) * (x : ℝ)) :
    ((E.card : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤
      ((Q.card : ℕ) : ℝ) := by
  have hmain := badRoots_card_mul_mul_threshold_le_two_vaughanCutoffs
    hx hMaux hMprod hE hQ hR hRupper hprodUpper hpartners
  let s : ℝ := Real.sqrt (n : ℝ)
  let e : ℝ := E.card
  let q : ℝ := Q.card
  let a : ℝ := A
  let X : ℝ := x
  let Vaux : ℝ := primitiveEndpointVaughanBudget x Maux
  let Vprod : ℝ := primitiveEndpointVaughanBudget x Mprod
  have hmain' : (e * a) * (X / 10) ≤ q * Vaux + 2 * Vprod := by
    simpa only [e, q, a, X, Vaux, Vprod, Nat.cast_mul] using hmain
  have hscaled := mul_le_mul_of_nonneg_left hmain'
    (show 0 ≤ 20 * s by dsimp [s]; positivity)
  have hauxBudget' : 20 * s * Vaux ≤ a * X := by
    simpa only [s, Vaux, a, X] using hauxBudget
  have hprodBudget' : 40 * s * Vprod ≤ q * a * X := by
    simpa only [s, Vprod, q, a, X] using hprodBudget
  have hcombined : (e * s) * (2 * a * X) ≤ q * (2 * a * X) := by
    calc
      (e * s) * (2 * a * X) =
          (20 * s) * ((e * a) * (X / 10)) := by ring
      _ ≤ (20 * s) * (q * Vaux + 2 * Vprod) := hscaled
      _ = q * (20 * s * Vaux) + 40 * s * Vprod := by ring
      _ ≤ q * (a * X) + q * a * X := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hauxBudget' (by positivity))
          hprodBudget'
      _ = q * (2 * a * X) := by ring
  have hfactor : 0 < 2 * a * X := by
    dsimp [a, X]
    positivity
  have := le_of_mul_le_mul_right hcombined hfactor
  simpa only [e, q, s] using this

/-- Power-sieve specialization of the quantitative assembly theorem.  Its
two remaining hypotheses are explicit bounds on the sharp auxiliary and
block-dependent product Vaughan budgets. -/
theorem powerSieve_badRoots_card_mul_sqrt_le_card
    {n L Q0 D : ℕ} {E Q : Finset ℕ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ0 : 1 ≤ Q0) (hD : 0 < D)
    (hQ0upper : Q0 ≤ powerSieveSmoothBound n L)
    (hthreshold :
      D * L ≤ powerSieveAuxCore n L Q0)
    (hE : E ⊆ Q)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQblock : ∀ q ∈ Q, q ≤ 2 * Q0)
    (hpartners : ∀ q ∈ E,
      powerSieveVaughanPartnerThreshold n L Q0 D ≤
        (endpointBadAuxiliaryPartners (powerSieveX n L) q
          (powerSieveAuxPrimes n L Q0)).card)
    (hauxBudget :
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveAuxUpper n L Q0) ≤
        (powerSieveVaughanPartnerThreshold n L Q0 D : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget :
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveProductVaughanCutoff n L Q0) ≤
        ((Q.card : ℕ) : ℝ) *
          (powerSieveVaughanPartnerThreshold n L Q0 D : ℝ) *
            (powerSieveX n L : ℝ)) :
    ((E.card : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤
      ((Q.card : ℕ) : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hx : 4 ≤ powerSieveX n L := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ (240 * L) := pow_le_pow_right' hn1 (by omega)
      _ = powerSieveX n L := rfl
  apply badRoots_card_mul_sqrt_le_card_of_twoVaughanBudgets
    (x := powerSieveX n L)
    (Maux := powerSieveAuxUpper n L Q0)
    (Mprod := powerSieveProductVaughanCutoff n L Q0)
    (A := powerSieveVaughanPartnerThreshold n L Q0 D)
    (R := powerSieveAuxPrimes n L Q0)
    hx (powerSieveVaughanPartnerThreshold_pos hD (by omega) hthreshold)
  · exact (show (powerSieveAuxUpper n L Q0 : ℝ) ≤
        (powerSieveVaughanCutoff n L : ℝ) by
          exact_mod_cast powerSieveAuxUpper_le_vaughanCutoff hn1 hL hQ0).trans
      (powerSieveVaughanCutoff_le_sqrt n L)
  · exact (show (powerSieveProductVaughanCutoff n L Q0 : ℝ) ≤
        (powerSieveVaughanCutoff n L : ℝ) by
          exact_mod_cast powerSieveProductVaughanCutoff_le_vaughanCutoff
            hn hL hQ0upper).trans
      (powerSieveVaughanCutoff_le_sqrt n L)
  · exact hE
  · exact hQprime
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.2
  · intro r hr
    exact powerSieveAuxPrime_le_auxUpper hr
  · intro q hq r hr
    exact powerSieve_root_mul_auxPrime_le_productVaughanCutoff
      (hQblock q hq) hr
  · exact hpartners
  · exact hauxBudget
  · exact hprodBudget

end

end Erdos48
