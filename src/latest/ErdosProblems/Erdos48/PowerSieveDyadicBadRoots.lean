/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveGoodRoot
import ErdosProblems.Erdos48.PowerSieveBadRoots
import ErdosProblems.Erdos48.ShiftedSmoothBadRoots

/-!
# Dyadic power-sieve bad roots

This file turns failure of the shifted-smooth lower bound at an endpoint-good
root into many endpoint-bad auxiliary partners.  It then performs the dyadic
incidence count with *separate* Vaughan cutoffs for auxiliary conductors and
product conductors.  Keeping these cutoffs separate is important: the
auxiliary contribution is multiplied by the number of roots, whereas the
product contribution is not.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Prime roots in the dyadic interval `(Q, 2Q]`. -/
def powerSieveDyadicPrimeBlock (Q : ℕ) : Finset ℕ :=
  (Finset.Ioc Q (2 * Q)).filter Nat.Prime

@[simp] theorem mem_powerSieveDyadicPrimeBlock {Q q : ℕ} :
    q ∈ powerSieveDyadicPrimeBlock Q ↔ Q < q ∧ q ≤ 2 * Q ∧ q.Prime := by
  simp only [powerSieveDyadicPrimeBlock, Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- The literal bad-root set for the power sieve.  A root is bad precisely
when its shifted-smooth fiber has cardinality strictly below
`W(q)/(240000 L^2)`. -/
def powerSieveShiftedSmoothBadRoots
    (n L : ℕ) (W : ℕ → ℝ) : Finset ℕ :=
  shiftedSmoothBadRoots (powerSieveX n L) (powerSieveSmoothBound n L)
    (fun q ↦ W q / (240000 * (L : ℝ) ^ 2))

@[simp] theorem mem_powerSieveShiftedSmoothBadRoots
    {n L q : ℕ} {W : ℕ → ℝ} :
    q ∈ powerSieveShiftedSmoothBadRoots n L W ↔
      q.Prime ∧ q ≤ powerSieveSmoothBound n L ∧
        (((smoothShiftedPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L)).filter
            fun p ↦ q ∣ p + 1).card : ℝ) <
          W q / (240000 * (L : ℝ) ^ 2) := by
  simp only [powerSieveShiftedSmoothBadRoots,
    mem_shiftedSmoothBadRoots]
  tauto

/-- The roots to which the endpoint incidence argument applies: literal bad
roots in `(Q,2Q]`, above the deletion threshold `2000L`, whose own endpoint
mass is good. -/
def powerSieveEndpointGoodDyadicBadRoots
    (n L Q : ℕ) (W : ℕ → ℝ) : Finset ℕ :=
  (powerSieveShiftedSmoothBadRoots n L W).filter fun q ↦
    q ∈ powerSieveDyadicPrimeBlock Q ∧ 2000 * L ≤ q ∧
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10

@[simp] theorem mem_powerSieveEndpointGoodDyadicBadRoots
    {n L Q q : ℕ} {W : ℕ → ℝ} :
    q ∈ powerSieveEndpointGoodDyadicBadRoots n L Q W ↔
      q ∈ powerSieveShiftedSmoothBadRoots n L W ∧
      q ∈ powerSieveDyadicPrimeBlock Q ∧ 2000 * L ≤ q ∧
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10 := by
  simp only [powerSieveEndpointGoodDyadicBadRoots, Finset.mem_filter]

/-- If `q ≥ 2000L`, deleting `q` from an auxiliary family of reciprocal mass
at least `1/(500L)` leaves reciprocal mass at least `3/(2000L)`. -/
theorem three_div_two_thousand_le_sum_inv_powerSieveAuxPrimesAway
    {n L Q q : ℕ} (hL : 1 ≤ L) (hq : 2000 * L ≤ q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹) :
    (3 / (2000 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ := by
  have hqInv : (q : ℝ)⁻¹ ≤ (1 / (2000 * (L : ℝ)) : ℝ) := by
    have hcast : (2000 : ℝ) * (L : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    calc
      (q : ℝ)⁻¹ ≤ ((2000 : ℝ) * (L : ℝ))⁻¹ :=
        inv_anti₀ (by positivity) hcast
      _ = 1 / (2000 * (L : ℝ)) := by rw [one_div]
  have hsplit := sum_inv_powerSieveAuxPrimes_le_root_add_away n L Q q
  have hscale :
      (1 / (500 * (L : ℝ)) : ℝ) =
        4 / (2000 * (L : ℝ)) := by
    have hL0 : (L : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  rw [hscale] at hmass
  calc
    (3 / (2000 * (L : ℝ)) : ℝ) =
        4 / (2000 * (L : ℝ)) - 1 / (2000 * (L : ℝ)) := by ring
    _ ≤ (∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹) -
          (q : ℝ)⁻¹ := sub_le_sub hmass hqInv
    _ ≤ ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ := by
      linarith

/-- The endpoint-good auxiliary partners remaining after deleting the root. -/
def powerSieveEndpointGoodAuxiliaryPartnersAway
    (n L Q q : ℕ) : Finset ℕ :=
  endpointGoodAuxiliaryPartners (powerSieveX n L) q
    (powerSieveAuxPrimesAway n L Q q)

/-- At a literal bad root, the endpoint-good auxiliary partners have
reciprocal mass strictly below `1/(1000L)`.  The cofactor and numerical
progression estimates are left explicit, since these are the analytic
inputs furnished by the beta-sieve part of the argument. -/
theorem sum_inv_powerSieveEndpointGoodAuxiliaryPartnersAway_lt
    {n L Q q B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hW : 0 < W q)
    (hqBad : q ∈ powerSieveShiftedSmoothBadRoots n L W)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    (∑ r ∈ powerSieveEndpointGoodAuxiliaryPartnersAway n L Q q,
      (r : ℝ)⁻¹) < 1 / (1000 * (L : ℝ)) := by
  let G := powerSieveEndpointGoodAuxiliaryPartnersAway n L Q q
  have hqData := mem_powerSieveShiftedSmoothBadRoots.mp hqBad
  have hbridge :
      W q * ∑ r ∈ G, (r : ℝ)⁻¹ ≤
        ((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ) := by
    apply mul_sum_inv_le_mul_card_smoothShiftedFiber_of_endpoint_good_of_ne
      (x := powerSieveX n L) (u := powerSieveSmoothBound n L)
      (q := q) (B := B) (D := 240 * L)
      (R0 := powerSieveAuxLower n L Q) (R := G) (W := W q)
    · rw [powerSieveX_eq_auxScale_pow]
      have hscale : 2 ≤ powerSieveAuxScale n L := by
        simpa only [powerSieveAuxScale] using hn
      exact hscale.trans (Nat.le_pow (by omega : 0 < 240 * L))
    · exact hW.le
    · exact hqData.1
    · intro r hr
      exact (mem_powerSieveAuxPrimes.mp
        (mem_powerSieveAuxPrimesAway.mp
          (mem_endpointGoodAuxiliaryPartners.mp hr).1).1).2.2
    · exact hqData.2.1
    · intro r hr
      have hrAux := (mem_powerSieveAuxPrimesAway.mp
        (mem_endpointGoodAuxiliaryPartners.mp hr).1).1
      exact ((mem_powerSieveAuxPrimes.mp hrAux).2.1).trans
        (powerSieveAuxUpper_le_smoothBound (by omega) hL hQ)
    · intro r hr
      exact (mem_powerSieveAuxPrimes.mp
        (mem_powerSieveAuxPrimesAway.mp
          (mem_endpointGoodAuxiliaryPartners.mp hr).1).1).1
    · exact powerSieveX_add_one_lt_auxLower_pow hn hL
    · intro r hr
      exact (mem_powerSieveAuxPrimesAway.mp
        (mem_endpointGoodAuxiliaryPartners.mp hr).1).2.symm
    · exact hqGood
    · intro r hr
      exact (mem_endpointGoodAuxiliaryPartners.mp hr).2.1
    · intro r hr
      exact (mem_endpointGoodAuxiliaryPartners.mp hr).2.2
    · intro r hr
      exact hcofactor r
        (mem_powerSieveAuxPrimesAway.mp
          (mem_endpointGoodAuxiliaryPartners.mp hr).1).1
    · intro r hr
      exact hnumeric r
        (mem_powerSieveAuxPrimesAway.mp
          (mem_endpointGoodAuxiliaryPartners.mp hr).1).1
  have hcardBad := hqData.2.2
  have hscaled :
      ((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ) <
        W q * (1 / (1000 * (L : ℝ))) := by
    calc
      ((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ) <
          ((240 * L : ℕ) : ℝ) *
            (W q / (240000 * (L : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hcardBad (by positivity)
      _ = W q * (1 / (1000 * (L : ℝ))) := by
        push_cast
        field_simp
        ring
  have hmul : W q * ∑ r ∈ G, (r : ℝ)⁻¹ <
      W q * (1 / (1000 * (L : ℝ))) := hbridge.trans_lt hscaled
  nlinarith

/-- The natural-number partner threshold supplied by the reciprocal-mass
gap. -/
def powerSieveDyadicPartnerLower (n L Q : ℕ) : ℕ :=
  (powerSieveAuxLower n L Q + 1) / (2000 * L)

/-- Every endpoint-good literal bad root above `2000L` has at least the
uniform dyadic number of endpoint-bad auxiliary partners. -/
theorem powerSieveDyadicPartnerLower_le_card_endpointBadAuxiliaryPartners
    {n L Q q B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hW : 0 < W q)
    (hqBad : q ∈ powerSieveShiftedSmoothBadRoots n L W)
    (hqLarge : 2000 * L ≤ q)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    powerSieveDyadicPartnerLower n L Q ≤
      (endpointBadAuxiliaryPartners (powerSieveX n L) q
        (powerSieveAuxPrimes n L Q)).card := by
  let Raway := powerSieveAuxPrimesAway n L Q q
  have haway : (3 / (2000 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ Raway, (r : ℝ)⁻¹ :=
    three_div_two_thousand_le_sum_inv_powerSieveAuxPrimesAway
      hL hqLarge hmass
  have hgood :
      (∑ r ∈ endpointGoodAuxiliaryPartners (powerSieveX n L) q Raway,
        (r : ℝ)⁻¹) < 1 / (1000 * (L : ℝ)) := by
    simpa only [powerSieveEndpointGoodAuxiliaryPartnersAway] using
      sum_inv_powerSieveEndpointGoodAuxiliaryPartnersAway_lt
        hn hL hQ hW hqBad hqGood hcofactor hnumeric
  have hgap : (((2000 * L : ℕ) : ℝ)⁻¹) ≤
      (3 / (2000 * (L : ℝ)) : ℝ) -
        1 / (1000 * (L : ℝ)) := by
    push_cast
    field_simp
    norm_num
  have hawayCount :
      (powerSieveAuxLower n L Q + 1) / (2000 * L) ≤
        (endpointBadAuxiliaryPartners (powerSieveX n L) q Raway).card := by
    apply div_le_card_endpointBadAuxiliaryPartners
      (R0 := powerSieveAuxLower n L Q + 1) (D := 2000 * L)
      (S := 3 / (2000 * (L : ℝ)))
      (G := 1 / (1000 * (L : ℝ)))
    · omega
    · omega
    · intro r hr
      have hrAux := (mem_powerSieveAuxPrimesAway.mp hr).1
      have := (mem_powerSieveAuxPrimes.mp hrAux).1
      omega
    · exact haway
    · exact hgood
    · exact hgap
  have hsubset :
      endpointBadAuxiliaryPartners (powerSieveX n L) q Raway ⊆
        endpointBadAuxiliaryPartners (powerSieveX n L) q
          (powerSieveAuxPrimes n L Q) := by
    intro r hr
    have hrData := mem_endpointBadAuxiliaryPartners.mp hr
    exact mem_endpointBadAuxiliaryPartners.mpr
      ⟨(mem_powerSieveAuxPrimesAway.mp hrData.1).1, hrData.2⟩
  exact hawayCount.trans (Finset.card_le_card hsubset)

/-- The dyadic auxiliary-conductor cutoff. -/
def powerSieveDyadicAuxCutoff (n L Q : ℕ) : ℕ :=
  powerSieveAuxUpper n L Q

/-- The dyadic product-conductor cutoff obtained from `q ≤ 2Q` and the
auxiliary upper endpoint. -/
def powerSieveDyadicProductCutoff (n L Q : ℕ) : ℕ :=
  2 * Q * powerSieveAuxUpper n L Q

/-- The sharp auxiliary cutoff remains below the square root of the endpoint. -/
theorem powerSieveDyadicAuxCutoff_le_sqrt
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    (powerSieveDyadicAuxCutoff n L Q : ℝ) ≤
      Real.sqrt (powerSieveX n L : ℝ) := by
  have hnat : powerSieveDyadicAuxCutoff n L Q ≤
      powerSieveVaughanCutoff n L := by
    dsimp only [powerSieveDyadicAuxCutoff]
    exact (powerSieveAuxUpper_le_smoothBound (by omega) hL hQ).trans
      (by
        simp only [powerSieveSmoothBound, powerSieveVaughanCutoff]
        exact pow_le_pow_right' (by omega : 1 ≤ n) (by omega))
  have hcast : (powerSieveDyadicAuxCutoff n L Q : ℝ) ≤
      (powerSieveVaughanCutoff n L : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (powerSieveVaughanCutoff_le_sqrt n L)

/-- The exact block-dependent product cutoff also remains below the square
root of the endpoint. -/
theorem powerSieveDyadicProductCutoff_le_sqrt
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    (powerSieveDyadicProductCutoff n L Q : ℝ) ≤
      Real.sqrt (powerSieveX n L : ℝ) := by
  let A := powerSieveAuxScale n L
  let B := powerSieveProductBase n L
  let U := powerSieveSmoothBound n L
  let C := powerSieveAuxCore n L Q
  have hn1 : 1 ≤ n := by omega
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
  have hnat : powerSieveDyadicProductCutoff n L Q ≤
      powerSieveVaughanCutoff n L := by
    calc
      powerSieveDyadicProductCutoff n L Q = 2 * Q * (C * A) := by
        rfl
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
  have hcast : (powerSieveDyadicProductCutoff n L Q : ℝ) ≤
      (powerSieveVaughanCutoff n L : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (powerSieveVaughanCutoff_le_sqrt n L)

/-- The incidence/Vaughan estimate with separate conductor cutoffs. -/
theorem badRoots_card_mul_mul_threshold_le_two_vaughan_cutoffs
    {x Maux Mprod A : ℕ} {E Roots R : Finset ℕ}
    (hx : 4 ≤ x)
    (hMaux : (Maux : ℝ) ≤ Real.sqrt (x : ℝ))
    (hMprod : (Mprod : ℝ) ≤ Real.sqrt (x : ℝ))
    (hE : E ⊆ Roots)
    (hRoots : ∀ q ∈ Roots, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hRupper : ∀ r ∈ R, r ≤ Maux)
    (hprodUpper : ∀ q ∈ Roots, ∀ r ∈ R, q * r ≤ Mprod)
    (hpartners : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners x q R).card) :
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
      ((Roots.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x Maux +
        2 * primitiveEndpointVaughanBudget x Mprod := by
  have hincidence := badRoots_card_mul_le_auxiliary_add_product hE hpartners
  have haux := badAuxiliaryConductors_card_mul_le_vaughan
    hx hMaux hR hRupper
  have hproducts := badPrimePairs_card_mul_le_two_mul_vaughan
    hx hMprod hRoots hR hprodUpper
  change ((((Roots.product R).filter fun qr ↦
      (x : ℝ) / 10 <
        primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ) *
      ((x : ℝ) / 10) ≤
        2 * primitiveEndpointVaughanBudget x Mprod at hproducts
  have hcast : ((E.card * A : ℕ) : ℝ) ≤
      (((Roots.card *
          (R.filter fun r ↦
            (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) +
        ((((Roots.product R).filter fun qr ↦
          (x : ℝ) / 10 <
            primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ)) := by
    exact_mod_cast hincidence
  calc
    (((E.card * A : ℕ) : ℝ) * ((x : ℝ) / 10)) ≤
        ((((Roots.card *
            (R.filter fun r ↦
              (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) +
          ((((Roots.product R).filter fun qr ↦
            (x : ℝ) / 10 <
              primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ)) *
            ((x : ℝ) / 10)) :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ((Roots.card : ℕ) : ℝ) *
          (((R.filter fun r ↦
            (x : ℝ) / 10 < primitiveEndpointMass x r).card : ℕ) : ℝ) *
              ((x : ℝ) / 10) +
        ((((Roots.product R).filter fun qr ↦
          (x : ℝ) / 10 <
            primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ) *
              ((x : ℝ) / 10) := by
      push_cast
      ring
    _ ≤ ((Roots.card : ℕ) : ℝ) * primitiveEndpointVaughanBudget x Maux +
          2 * primitiveEndpointVaughanBudget x Mprod := by
      apply add_le_add _ hproducts
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left haux (Nat.cast_nonneg Roots.card)

/-- A reusable dyadic prefix-sparsity estimate.  The two square-root
hypotheses retain the sharp block-dependent auxiliary and product Vaughan
budgets. -/
theorem powerSieveEndpointGoodDyadicBadRoots_card_bound
    {n L Q B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hW : ∀ q ∈ powerSieveEndpointGoodDyadicBadRoots n L Q W,
      0 < W q)
    (hcofactor : ∀ q ∈ powerSieveEndpointGoodDyadicBadRoots n L Q W,
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ q ∈ powerSieveEndpointGoodDyadicBadRoots n L Q W,
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    ((((powerSieveEndpointGoodDyadicBadRoots n L Q W).card *
        powerSieveDyadicPartnerLower n L Q : ℕ) : ℝ) *
        ((powerSieveX n L : ℝ) / 10)) ≤
      ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) +
        2 * primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveDyadicProductCutoff n L Q) := by
  apply badRoots_card_mul_mul_threshold_le_two_vaughan_cutoffs
    (Maux := powerSieveDyadicAuxCutoff n L Q)
    (Mprod := powerSieveDyadicProductCutoff n L Q)
    (E := powerSieveEndpointGoodDyadicBadRoots n L Q W)
    (Roots := powerSieveDyadicPrimeBlock Q)
    (R := powerSieveAuxPrimes n L Q)
  · rw [powerSieveX_eq_auxScale_pow]
    have hscale : 2 ≤ powerSieveAuxScale n L := by
      simpa only [powerSieveAuxScale] using hn
    exact (by norm_num : 4 ≤ 2 ^ 2) |>.trans
      (Nat.pow_le_pow_left hscale 2) |>.trans
      (pow_le_pow_right' (by omega : 1 ≤ powerSieveAuxScale n L)
        (by omega : 2 ≤ 240 * L))
  · exact powerSieveDyadicAuxCutoff_le_sqrt hn hL hQ
  · exact powerSieveDyadicProductCutoff_le_sqrt hn hL hQupper
  · intro q hqBad
    exact (mem_powerSieveEndpointGoodDyadicBadRoots.mp hqBad).2.1
  · intro q hq
    exact (mem_powerSieveDyadicPrimeBlock.mp hq).2.2
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.2
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.1
  · intro q hqBlock r hr
    have hqUpper := (mem_powerSieveDyadicPrimeBlock.mp hqBlock).2.1
    have hrUpper := (mem_powerSieveAuxPrimes.mp hr).2.1
    dsimp only [powerSieveDyadicProductCutoff]
    exact Nat.mul_le_mul hqUpper hrUpper
  · intro q hqBad
    have hqData := mem_powerSieveEndpointGoodDyadicBadRoots.mp hqBad
    exact powerSieveDyadicPartnerLower_le_card_endpointBadAuxiliaryPartners
      hn hL hQ hmass (hW q hqBad) hqData.1 hqData.2.2.1
      hqData.2.2.2 (hcofactor q hqBad) (hnumeric q hqBad)

end

end Erdos48
