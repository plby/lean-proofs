/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveDyadicBadRoots
import ErdosProblems.Erdos48.PowerSieveVaughanAsymptotic
import ErdosProblems.Erdos48.PowerSieveDyadicAggregation
import ErdosProblems.Erdos48.PowerSieveVaughanBudgetAbsorption

/-!
# Prefix sparsity for the literal power-sieve bad-root set

This file joins the finite bad-partner construction, the two-cutoff Vaughan
assembly, and dyadic aggregation.  One Page-excluded conductor is erased
explicitly.  A final corollary restores the literal bad-root set when that
conductor is not itself a bad prime root.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- A dyadic prime block contains at most `Q` elements. -/
theorem card_powerSieveDyadicPrimeBlock_le (Q : ℕ) :
    (powerSieveDyadicPrimeBlock Q).card ≤ Q := by
  calc
    (powerSieveDyadicPrimeBlock Q).card ≤
        (Finset.Ioc Q (2 * Q)).card := Finset.card_filter_le _ _
    _ = 2 * Q - Q := by rw [Nat.card_Ioc]
    _ = Q := by omega

/-- A possible exceptional root at the retargeted base `n` has prefix
density at most `1/n`. -/
theorem card_filter_singleton_le_one_div_mul
    {n y : ℕ} (hn : 1 ≤ n) :
    (((({n} : Finset ℕ).filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
      (1 / (n : ℝ)) * (y : ℝ) := by
  classical
  by_cases hny : n ≤ y
  · simp only [Finset.filter_singleton, hny, ↓reduceIte,
      Finset.card_singleton, Nat.cast_one]
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      (1 : ℝ) ≤ (y : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ hnR]
        simpa only [one_mul] using (show (n : ℝ) ≤ y by exact_mod_cast hny)
      _ = (1 / (n : ℝ)) * (y : ℝ) := by ring
  · simp only [Finset.filter_singleton, hny, ↓reduceIte,
      Finset.card_empty, Nat.cast_zero]
    positivity

/-- Since `sqrt n ≤ n` for `n ≥ 1`, the exceptional singleton costs at
most `y/sqrt n` in every prefix. -/
theorem card_filter_singleton_le_one_div_sqrt_mul
    {n y : ℕ} (hn : 1 ≤ n) :
    (((({n} : Finset ℕ).filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
      (1 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  refine (card_filter_singleton_le_one_div_mul hn).trans ?_
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtLe : Real.sqrt (n : ℝ) ≤ (n : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hnR)
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hinv : (n : ℝ)⁻¹ ≤ (Real.sqrt (n : ℝ))⁻¹ :=
    inv_anti₀ hsqrtPos hsqrtLe
  rw [one_div, one_div]
  exact mul_le_mul_of_nonneg_right hinv (by positivity)

/-- Adding a possible exceptional root at the base changes a
`2/sqrt n` prefix estimate for `E.erase n` into a `3/sqrt n` estimate for
the full set `E`. -/
theorem card_filter_le_three_div_sqrt_of_erase_base
    {n : ℕ} {E : Finset ℕ} (hn : 1 ≤ n)
    (herased : ∀ y : ℕ,
      ((((E.erase n).filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (2 / Real.sqrt (n : ℝ)) * (y : ℝ)) :
    ∀ y : ℕ,
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (3 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  classical
  intro y
  let Eordinary := (E.erase n).filter fun q ↦ q ≤ y
  let Eexceptional := ({n} : Finset ℕ).filter fun q ↦ q ≤ y
  have hsubset : E.filter (fun q ↦ q ≤ y) ⊆
      Eordinary ∪ Eexceptional := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    by_cases hqn : q = n
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨by simp only [hqn, Finset.mem_singleton],
        hqData.2⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hqn, hqData.1⟩, hqData.2⟩
  have hcard :
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (Eordinary.card : ℝ) + (Eexceptional.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsubset).trans
      (Finset.card_union_le Eordinary Eexceptional)
  calc
    (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (Eordinary.card : ℝ) + (Eexceptional.card : ℝ) := hcard
    _ ≤ (2 / Real.sqrt (n : ℝ)) * (y : ℝ) +
          (1 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
      exact add_le_add (by simpa only [Eordinary] using herased y)
        (by simpa only [Eexceptional] using
          card_filter_singleton_le_one_div_sqrt_mul (y := y) hn)
    _ = (3 / Real.sqrt (n : ℝ)) * (y : ℝ) := by ring

/-- Retargeted-base form for the literal power-sieve bad-root set.  The
ordinary roots are supplied by the erased-set theorem below; the only
remaining possible endpoint exception is the singleton `{n}`. -/
theorem powerSieveBadRoots_prefix_bound_with_base_exception
    {n L : ℕ} {W : ℕ → ℝ} (hn : 1 ≤ n)
    (herased : ∀ y : ℕ,
      (((((powerSieveShiftedSmoothBadRoots n L W).erase n).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (2 / Real.sqrt (n : ℝ)) * (y : ℝ)) :
    ∀ y : ℕ,
      ((((powerSieveShiftedSmoothBadRoots n L W).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (3 / Real.sqrt (n : ℝ)) * (y : ℝ) :=
  card_filter_le_three_div_sqrt_of_erase_base hn herased

/-- General coefficient form of the base-singleton argument. -/
theorem card_filter_le_add_one_div_sqrt_of_erase_base
    {n : ℕ} {E : Finset ℕ} {A : ℝ} (hn : 1 ≤ n)
    (herased : ∀ y : ℕ,
      ((((E.erase n).filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (A / Real.sqrt (n : ℝ)) * (y : ℝ)) :
    ∀ y : ℕ,
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        ((A + 1) / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  classical
  intro y
  let Eordinary := (E.erase n).filter fun q ↦ q ≤ y
  let Eexceptional := ({n} : Finset ℕ).filter fun q ↦ q ≤ y
  have hsubset : E.filter (fun q ↦ q ≤ y) ⊆
      Eordinary ∪ Eexceptional := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    by_cases hqn : q = n
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨by simp only [hqn, Finset.mem_singleton], hqData.2⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hqn, hqData.1⟩, hqData.2⟩
  have hcard :
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (Eordinary.card : ℝ) + (Eexceptional.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsubset).trans
      (Finset.card_union_le Eordinary Eexceptional)
  calc
    (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (Eordinary.card : ℝ) + (Eexceptional.card : ℝ) := hcard
    _ ≤ (A / Real.sqrt (n : ℝ)) * (y : ℝ) +
          (1 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
      exact add_le_add (by simpa only [Eordinary] using herased y)
        (by simpa only [Eexceptional] using
          card_filter_singleton_le_one_div_sqrt_mul (y := y) hn)
    _ = ((A + 1) / Real.sqrt (n : ℝ)) * (y : ℝ) := by ring

/-- For fixed positive `L`, the natural bad-partner threshold is eventually
positive, uniformly in every dyadic parameter `Q`. -/
theorem eventually_powerSieveDyadicPartnerLower_pos
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q : ℕ, 1 ≤ Q →
      0 < powerSieveDyadicPartnerLower n L Q := by
  filter_upwards [Filter.eventually_ge_atTop (2000 * L)] with n hn
  intro Q _hQ
  unfold powerSieveDyadicPartnerLower
  apply Nat.div_pos
  · have hcore : n ≤ powerSieveAuxCore n L Q := by
      unfold powerSieveAuxCore powerSieveAuxScale
      exact le_max_right _ _
    unfold powerSieveAuxLower
    omega
  · exact Nat.mul_pos (by norm_num) (by omega)

/-- Any selected family of endpoint-good literal bad roots in `(Q,2Q]`
has square-root-sparse cardinality, provided the two sharp Vaughan budgets
hold.  The represented-large-factor and numerical progression estimates
remain explicit inputs. -/
theorem powerSieveDyadicBadRoots_card_mul_sqrt_le_block
    {n L Q B : ℕ} {W : ℕ → ℝ} {E : Finset ℕ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L)
    (hE : E ⊆ powerSieveEndpointGoodDyadicBadRoots n L Q W)
    (hpartnerPos : 0 < powerSieveDyadicPartnerLower n L Q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hW : ∀ q ∈ E, 0 < W q)
    (hcofactor : ∀ q ∈ E,
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ q ∈ E,
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hauxBudget :
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget :
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ)) :
    ((E.card : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤
      ((powerSieveDyadicPrimeBlock Q).card : ℝ) := by
  have hx : 4 ≤ powerSieveX n L := by
    rw [powerSieveX_eq_auxScale_pow]
    have hscale : 2 ≤ powerSieveAuxScale n L := by
      simpa only [powerSieveAuxScale] using hn
    exact (by norm_num : 4 ≤ 2 ^ 2) |>.trans
      (Nat.pow_le_pow_left hscale 2) |>.trans
      (pow_le_pow_right' (by omega : 1 ≤ powerSieveAuxScale n L)
        (by omega : 2 ≤ 240 * L))
  apply badRoots_card_mul_sqrt_le_card_of_twoVaughanBudgets
    (x := powerSieveX n L)
    (Maux := powerSieveDyadicAuxCutoff n L Q)
    (Mprod := powerSieveDyadicProductCutoff n L Q)
    (A := powerSieveDyadicPartnerLower n L Q)
    (Q := powerSieveDyadicPrimeBlock Q)
    (R := powerSieveAuxPrimes n L Q)
    hx hpartnerPos
  · exact powerSieveDyadicAuxCutoff_le_sqrt hn hL hQ
  · exact powerSieveDyadicProductCutoff_le_sqrt hn hL hQupper
  · intro q hqE
    exact (mem_powerSieveEndpointGoodDyadicBadRoots.mp (hE hqE)).2.1
  · intro q hqBlock
    exact (mem_powerSieveDyadicPrimeBlock.mp hqBlock).2.2
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.2
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp hr).2.1
  · intro q hqBlock r hr
    exact Nat.mul_le_mul
      (mem_powerSieveDyadicPrimeBlock.mp hqBlock).2.1
      (mem_powerSieveAuxPrimes.mp hr).2.1
  · intro q hqE
    have hqData := mem_powerSieveEndpointGoodDyadicBadRoots.mp (hE hqE)
    exact powerSieveDyadicPartnerLower_le_card_endpointBadAuxiliaryPartners
      hn hL hQ hmass (hW q hqE) hqData.1 hqData.2.2.1
      hqData.2.2.2 (hcofactor q hqE) (hnumeric q hqE)
  · exact hauxBudget
  · exact hprodBudget

/-- Twice a dyadic base below the smoothness cutoff is still in Vaughan's
square-root conductor range. -/
theorem powerSieve_two_mul_blockBase_le_sqrt
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L) :
    ((2 * Q : ℕ) : ℝ) ≤ Real.sqrt (powerSieveX n L : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hsix : 2 ≤ n ^ 6 := by
    calc
      2 ≤ 2 ^ 6 := by norm_num
      _ ≤ n ^ 6 := Nat.pow_le_pow_left hn 6
  have hnat : 2 * Q ≤ powerSieveVaughanCutoff n L := by
    calc
      2 * Q ≤ 2 * powerSieveSmoothBound n L :=
        Nat.mul_le_mul_left 2 hQupper
      _ ≤ n ^ 6 * powerSieveSmoothBound n L :=
        Nat.mul_le_mul_right _ hsix
      _ = n ^ (120 * L) := by
        unfold powerSieveSmoothBound
        rw [← pow_add]
        congr 1
        omega
      _ = powerSieveVaughanCutoff n L := rfl
  have hcast : ((2 * Q : ℕ) : ℝ) ≤
      (powerSieveVaughanCutoff n L : ℝ) := by exact_mod_cast hnat
  exact hcast.trans (powerSieveVaughanCutoff_le_sqrt n L)

/-- Roots in a dyadic block whose own endpoint mass is bad. -/
def powerSieveEndpointBadDyadicRoots (n L Q : ℕ) : Finset ℕ :=
  (powerSieveDyadicPrimeBlock Q).filter fun q ↦
    (powerSieveX n L : ℝ) / 10 <
      primitiveEndpointMass (powerSieveX n L) q

@[simp] theorem mem_powerSieveEndpointBadDyadicRoots
    {n L Q q : ℕ} :
    q ∈ powerSieveEndpointBadDyadicRoots n L Q ↔
      q ∈ powerSieveDyadicPrimeBlock Q ∧
        (powerSieveX n L : ℝ) / 10 <
          primitiveEndpointMass (powerSieveX n L) q := by
  simp only [powerSieveEndpointBadDyadicRoots, Finset.mem_filter]

/-- A direct Vaughan budget bounds roots whose own endpoint mass is bad.
This is the part required above the range controlled by Page exclusion. -/
theorem powerSieveEndpointBadDyadicRoots_card_mul_sqrt_le_base
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hQupper : Q ≤ powerSieveSmoothBound n L)
    (hrootBudget :
      10 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
        (Q : ℝ) * (powerSieveX n L : ℝ)) :
    ((powerSieveEndpointBadDyadicRoots n L Q).card : ℝ) *
        Real.sqrt (n : ℝ) ≤ (Q : ℝ) := by
  have hx : 4 ≤ powerSieveX n L := by
    rw [powerSieveX_eq_auxScale_pow]
    have hscale : 2 ≤ powerSieveAuxScale n L := by
      simpa only [powerSieveAuxScale] using hn
    exact (by norm_num : 4 ≤ 2 ^ 2) |>.trans
      (Nat.pow_le_pow_left hscale 2) |>.trans
      (pow_le_pow_right' (by omega : 1 ≤ powerSieveAuxScale n L)
        (by omega : 2 ≤ 240 * L))
  have hmain := badAuxiliaryConductors_card_mul_le_vaughan
    (x := powerSieveX n L) (M := 2 * Q)
    (R := powerSieveDyadicPrimeBlock Q) hx
    (powerSieve_two_mul_blockBase_le_sqrt hn hL hQupper)
    (fun q hq ↦ (mem_powerSieveDyadicPrimeBlock.mp hq).2.2)
    (fun q hq ↦ (mem_powerSieveDyadicPrimeBlock.mp hq).2.1)
  have hmain' :
      ((powerSieveEndpointBadDyadicRoots n L Q).card : ℝ) *
          ((powerSieveX n L : ℝ) / 10) ≤
        primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) := by
    simpa only [powerSieveEndpointBadDyadicRoots] using hmain
  have hscaled := mul_le_mul_of_nonneg_left hmain'
    (show 0 ≤ 10 * Real.sqrt (n : ℝ) by positivity)
  have hcombined :
      (((powerSieveEndpointBadDyadicRoots n L Q).card : ℝ) *
          Real.sqrt (n : ℝ)) * (powerSieveX n L : ℝ) ≤
        (Q : ℝ) * (powerSieveX n L : ℝ) := by
    calc
      (((powerSieveEndpointBadDyadicRoots n L Q).card : ℝ) *
          Real.sqrt (n : ℝ)) * (powerSieveX n L : ℝ) =
          (10 * Real.sqrt (n : ℝ)) *
            (((powerSieveEndpointBadDyadicRoots n L Q).card : ℝ) *
              ((powerSieveX n L : ℝ) / 10)) := by ring
      _ ≤ (10 * Real.sqrt (n : ℝ)) *
          primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) :=
        hscaled
      _ ≤ (Q : ℝ) * (powerSieveX n L : ℝ) := hrootBudget
  exact le_of_mul_le_mul_right hcombined (by positivity)

/-- Splitting a literal bad-root block by whether the root endpoint itself
is good gives two `1/sqrt n` contributions: partner incidence for the good
part and direct Vaughan for the bad part. -/
theorem powerSieveDyadicBadRoots_card_mul_sqrt_le_two_mul_base
    {n L Q B : ℕ} {W : ℕ → ℝ} {E : Finset ℕ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hQupper : Q ≤ powerSieveSmoothBound n L)
    (hEbad : E ⊆ powerSieveShiftedSmoothBadRoots n L W)
    (hEblock : E ⊆ powerSieveDyadicPrimeBlock Q)
    (hlarge : ∀ q ∈ E, 2000 * L ≤ q)
    (hPageGood : ∀ q ∈ E, q ≤ n →
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10)
    (hpartnerPos : 0 < powerSieveDyadicPartnerLower n L Q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hW : ∀ q ∈ E, 0 < W q)
    (hcofactor : ∀ q ∈ E,
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ q ∈ E,
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hauxBudget :
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget :
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ))
    (hrootBudget : n < 2 * Q →
      10 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
        (Q : ℝ) * (powerSieveX n L : ℝ)) :
    ((E.card : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤ 2 * (Q : ℝ) := by
  let Good := E.filter fun q ↦
    primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10
  let Bad := E.filter fun q ↦ ¬
    primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10
  have hGoodSubset : Good ⊆
      powerSieveEndpointGoodDyadicBadRoots n L Q W := by
    intro q hqGood
    have hqData := Finset.mem_filter.mp hqGood
    exact mem_powerSieveEndpointGoodDyadicBadRoots.mpr
      ⟨hEbad hqData.1, hEblock hqData.1, hlarge q hqData.1, hqData.2⟩
  have hGood := powerSieveDyadicBadRoots_card_mul_sqrt_le_block
    hn hL hQ hQupper hGoodSubset hpartnerPos hmass
    (fun q hq ↦ hW q (Finset.mem_filter.mp hq).1)
    (fun q hq ↦ hcofactor q (Finset.mem_filter.mp hq).1)
    (fun q hq ↦ hnumeric q (Finset.mem_filter.mp hq).1)
    hauxBudget hprodBudget
  have hGoodQ : (Good.card : ℝ) * Real.sqrt (n : ℝ) ≤ (Q : ℝ) :=
    hGood.trans (by exact_mod_cast card_powerSieveDyadicPrimeBlock_le Q)
  have hBadSubset : Bad ⊆ powerSieveEndpointBadDyadicRoots n L Q := by
    intro q hqBad
    have hqData := Finset.mem_filter.mp hqBad
    exact mem_powerSieveEndpointBadDyadicRoots.mpr
      ⟨hEblock hqData.1, lt_of_not_ge hqData.2⟩
  have hBadQ : (Bad.card : ℝ) * Real.sqrt (n : ℝ) ≤ (Q : ℝ) := by
    by_cases hsmall : 2 * Q ≤ n
    · have hBadEmpty : Bad = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨q, hqBad⟩
        have hqData := Finset.mem_filter.mp hqBad
        have hqUpper := (mem_powerSieveDyadicPrimeBlock.mp
          (hEblock hqData.1)).2.1
        exact hqData.2 (hPageGood q hqData.1 (hqUpper.trans hsmall))
      rw [hBadEmpty]
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
    · have hBadAll :=
        powerSieveEndpointBadDyadicRoots_card_mul_sqrt_le_base
          hn hL hQupper (hrootBudget (lt_of_not_ge hsmall))
      have hBadCast : (Bad.card : ℝ) ≤
          ((powerSieveEndpointBadDyadicRoots n L Q).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hBadSubset
      exact (mul_le_mul_of_nonneg_right hBadCast (by positivity)).trans hBadAll
  have hpartition : Good.card + Bad.card = E.card := by
    simpa only [Good, Bad] using
      (Finset.card_filter_add_card_filter_not
        (s := E) (p := fun q ↦
          primitiveEndpointMass (powerSieveX n L) q ≤
            (powerSieveX n L : ℝ) / 10))
  calc
    ((E.card : ℕ) : ℝ) * Real.sqrt (n : ℝ) =
        (Good.card : ℝ) * Real.sqrt (n : ℝ) +
          (Bad.card : ℝ) * Real.sqrt (n : ℝ) := by
      rw [← hpartition]
      push_cast
      ring
    _ ≤ (Q : ℝ) + (Q : ℝ) := add_le_add hGoodQ hBadQ
    _ = 2 * (Q : ℝ) := by ring

/-- Prefix sparsity after erasing the one Page-excluded conductor.

The low-root hypothesis says the erased bad set is empty through `2^J₀`.
All scale-dependent analytic hypotheses are required only for dyadic bases
`Q ≤ powerSieveSmoothBound`; higher shells are automatically empty. -/
theorem powerSieveBadRootsErase_prefix_bound
    {n L J₀ m₀ B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hJlarge : 2000 * L ≤ 2 ^ J₀)
    (hbelow : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → q ≤ 2 ^ J₀ → False)
    (hendpoint : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ →
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10)
    (hmass : ∀ Q : ℕ, 1 ≤ Q → Q ≤ powerSieveSmoothBound n L →
      (1 / (500 * (L : ℝ)) : ℝ) ≤
        ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hpartnerPos : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      0 < powerSieveDyadicPartnerLower n L Q)
    (hW : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → 0 < W q)
    (hcofactor : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
      q ∈ powerSieveDyadicPrimeBlock Q →
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
      q ∈ powerSieveDyadicPrimeBlock Q →
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hauxBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ)) :
    ∀ y : ℕ,
      (((((powerSieveShiftedSmoothBadRoots n L W).erase m₀).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (2 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  let E := (powerSieveShiftedSmoothBadRoots n L W).erase m₀
  have hlowE : ∀ q ∈ E, q ≤ 2 ^ J₀ → False := by
    intro q hqE hqLow
    have hmem := Finset.mem_erase.mp hqE
    exact hbelow q hmem.2 hmem.1 hqLow
  have hblocks : ∀ j : ℕ, J₀ ≤ j →
      ((powerSieveDyadicShell E j).card : ℝ) ≤
        (1 / Real.sqrt (n : ℝ)) * ((2 ^ j : ℕ) : ℝ) := by
    intro j hj
    let Q := 2 ^ j
    have hQ : 1 ≤ Q := by
      have hQpos : 0 < Q := by dsimp [Q]; positivity
      omega
    by_cases hQupper : Q ≤ powerSieveSmoothBound n L
    · have hshellSubset : powerSieveDyadicShell E j ⊆
          powerSieveEndpointGoodDyadicBadRoots n L Q W := by
        intro q hqShell
        have hqShellData := mem_powerSieveDyadicShell.mp hqShell
        have hqErase := Finset.mem_erase.mp hqShellData.1
        have hqBlock : q ∈ powerSieveDyadicPrimeBlock Q := by
          rw [mem_powerSieveDyadicPrimeBlock]
          refine ⟨hqShellData.2.1, ?_,
            (mem_powerSieveShiftedSmoothBadRoots.mp hqErase.2).1⟩
          simpa only [Q, pow_succ, Nat.mul_comm] using hqShellData.2.2
        have hqLarge : 2000 * L ≤ q := by
          have hpow : 2 ^ J₀ ≤ 2 ^ j := pow_le_pow_right' (by omega) hj
          dsimp only [Q] at hqBlock
          exact (hJlarge.trans hpow).trans hqShellData.2.1.le
        exact mem_powerSieveEndpointGoodDyadicBadRoots.mpr
          ⟨hqErase.2, hqBlock, hqLarge,
            hendpoint q hqErase.2 hqErase.1⟩
      have hsquare := powerSieveDyadicBadRoots_card_mul_sqrt_le_block
        hn hL hQ hQupper hshellSubset
        (hpartnerPos Q hQ hQupper) (hmass Q hQ hQupper)
        (fun q hq ↦ by
          have hmem := Finset.mem_erase.mp
            (mem_powerSieveDyadicShell.mp hq).1
          exact hW q hmem.2 hmem.1)
        (fun q hq ↦ by
          have hmem := Finset.mem_erase.mp
            (mem_powerSieveDyadicShell.mp hq).1
          exact hcofactor Q hQ hQupper q hmem.2 hmem.1
            (mem_powerSieveEndpointGoodDyadicBadRoots.mp
              (hshellSubset hq)).2.1)
        (fun q hq ↦ by
          have hmem := Finset.mem_erase.mp
            (mem_powerSieveDyadicShell.mp hq).1
          exact hnumeric Q hQ hQupper q hmem.2 hmem.1
            (mem_powerSieveEndpointGoodDyadicBadRoots.mp
              (hshellSubset hq)).2.1)
        (hauxBudget Q hQ hQupper) (hprodBudget Q hQ hQupper)
      have hblockCard :
          ((powerSieveDyadicPrimeBlock Q).card : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast card_powerSieveDyadicPrimeBlock_le Q
      have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
      calc
        ((powerSieveDyadicShell E j).card : ℝ) ≤
            (Q : ℝ) / Real.sqrt (n : ℝ) := by
          rw [le_div_iff₀ hsqrtPos]
          exact hsquare.trans hblockCard
        _ = (1 / Real.sqrt (n : ℝ)) * ((2 ^ j : ℕ) : ℝ) := by
          dsimp only [Q]
          ring
    · have hempty : powerSieveDyadicShell E j = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨q, hqShell⟩
        have hqData := mem_powerSieveDyadicShell.mp hqShell
        have hqBad := (Finset.mem_erase.mp hqData.1).2
        have hqu := (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).2.1
        have hQq : Q < q := by simpa only [Q] using hqData.2.1
        omega
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hpref := card_filter_le_two_mul_of_dyadicShell_bounds
    (E := E) (J₀ := J₀) (c := 1 / Real.sqrt (n : ℝ))
    (by positivity) hlowE hblocks
  intro y
  simpa only [E, div_eq_mul_inv, one_mul] using hpref y

/-- Source-audited prefix theorem.  It does not assume Page endpoint
goodness beyond the Page base: each shell is split into endpoint-good roots,
handled by partner incidence, and endpoint-bad roots, handled directly by
Vaughan at cutoff `2Q`. -/
theorem powerSieveBadRootsErase_prefix_bound_of_endpoint_split
    {n L J₀ m₀ B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hJlarge : 2000 * L ≤ 2 ^ J₀)
    (hbelow : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → q ≤ 2 ^ J₀ → False)
    (hPageGood : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → q ≤ n →
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10)
    (hmass : ∀ Q : ℕ, 1 ≤ Q → Q ≤ powerSieveSmoothBound n L →
      (1 / (500 * (L : ℝ)) : ℝ) ≤
        ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hpartnerPos : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      0 < powerSieveDyadicPartnerLower n L Q)
    (hW : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → 0 < W q)
    (hcofactor : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
      q ∈ powerSieveDyadicPrimeBlock Q →
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
      q ∈ powerSieveDyadicPrimeBlock Q →
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hauxBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ))
    (hrootBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L → n < 2 * Q →
      10 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
        (Q : ℝ) * (powerSieveX n L : ℝ)) :
    ∀ y : ℕ,
      (((((powerSieveShiftedSmoothBadRoots n L W).erase m₀).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (4 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  let E := (powerSieveShiftedSmoothBadRoots n L W).erase m₀
  have hlowE : ∀ q ∈ E, q ≤ 2 ^ J₀ → False := by
    intro q hqE hqLow
    have hmem := Finset.mem_erase.mp hqE
    exact hbelow q hmem.2 hmem.1 hqLow
  have hblocks : ∀ j : ℕ, J₀ ≤ j →
      ((powerSieveDyadicShell E j).card : ℝ) ≤
        (2 / Real.sqrt (n : ℝ)) * ((2 ^ j : ℕ) : ℝ) := by
    intro j hj
    let Q := 2 ^ j
    have hQ : 1 ≤ Q := by
      have hQpos : 0 < Q := by dsimp [Q]; positivity
      omega
    by_cases hQupper : Q ≤ powerSieveSmoothBound n L
    · have hShellBad : powerSieveDyadicShell E j ⊆
          powerSieveShiftedSmoothBadRoots n L W := by
        intro q hq
        exact (Finset.mem_erase.mp
          (mem_powerSieveDyadicShell.mp hq).1).2
      have hShellBlock : powerSieveDyadicShell E j ⊆
          powerSieveDyadicPrimeBlock Q := by
        intro q hq
        have hqData := mem_powerSieveDyadicShell.mp hq
        have hqBad := (Finset.mem_erase.mp hqData.1).2
        rw [mem_powerSieveDyadicPrimeBlock]
        refine ⟨hqData.2.1, ?_,
          (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).1⟩
        simpa only [Q, pow_succ, Nat.mul_comm] using hqData.2.2
      have hShellLarge : ∀ q ∈ powerSieveDyadicShell E j,
          2000 * L ≤ q := by
        intro q hq
        have hqData := mem_powerSieveDyadicShell.mp hq
        have hpow : 2 ^ J₀ ≤ 2 ^ j := pow_le_pow_right' (by omega) hj
        exact (hJlarge.trans hpow).trans hqData.2.1.le
      have hsquare :=
        powerSieveDyadicBadRoots_card_mul_sqrt_le_two_mul_base
          hn hL hQ hQupper hShellBad hShellBlock hShellLarge
          (fun q hq hqn ↦ by
            have hmem := Finset.mem_erase.mp
              (mem_powerSieveDyadicShell.mp hq).1
            exact hPageGood q hmem.2 hmem.1 hqn)
          (hpartnerPos Q hQ hQupper) (hmass Q hQ hQupper)
          (fun q hq ↦ by
            have hmem := Finset.mem_erase.mp
              (mem_powerSieveDyadicShell.mp hq).1
            exact hW q hmem.2 hmem.1)
          (fun q hq ↦ by
            have hmem := Finset.mem_erase.mp
              (mem_powerSieveDyadicShell.mp hq).1
            exact hcofactor Q hQ hQupper q hmem.2 hmem.1
              (hShellBlock hq))
          (fun q hq ↦ by
            have hmem := Finset.mem_erase.mp
              (mem_powerSieveDyadicShell.mp hq).1
            exact hnumeric Q hQ hQupper q hmem.2 hmem.1
              (hShellBlock hq))
          (hauxBudget Q hQ hQupper) (hprodBudget Q hQ hQupper)
          (hrootBudget Q hQ hQupper)
      have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
      calc
        ((powerSieveDyadicShell E j).card : ℝ) ≤
            (2 * (Q : ℝ)) / Real.sqrt (n : ℝ) := by
          rw [le_div_iff₀ hsqrtPos]
          exact hsquare
        _ = (2 / Real.sqrt (n : ℝ)) * ((2 ^ j : ℕ) : ℝ) := by
          dsimp only [Q]
          ring
    · have hempty : powerSieveDyadicShell E j = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨q, hqShell⟩
        have hqData := mem_powerSieveDyadicShell.mp hqShell
        have hqBad := (Finset.mem_erase.mp hqData.1).2
        have hqu := (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).2.1
        have hQq : Q < q := by simpa only [Q] using hqData.2.1
        omega
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hpref := card_filter_le_two_mul_of_dyadicShell_bounds
    (E := E) (J₀ := J₀) (c := 2 / Real.sqrt (n : ℝ))
    (by positivity) hlowE hblocks
  intro y
  dsimp only [E] at hpref
  convert hpref y using 1 <;> ring

/-- The exact finite hypotheses consumed by the source-audited prefix
theorem.  Packaging them makes the eventual all-good and retargeted branches
directly usable by `PowerSieveAnalyticAssembly`. -/
structure PowerSieveEndpointSplitPrefixInput
    (n L J₀ m₀ B : ℕ) (W : ℕ → ℝ) : Prop where
  hn : 2 ≤ n
  hL : 1 ≤ L
  hJlarge : 2000 * L ≤ 2 ^ J₀
  hbelow : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
    q ≠ m₀ → q ≤ 2 ^ J₀ → False
  hPageGood : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
    q ≠ m₀ → q ≤ n →
    primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10
  hmass : ∀ Q : ℕ, 1 ≤ Q → Q ≤ powerSieveSmoothBound n L →
    (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹
  hpartnerPos : ∀ Q : ℕ, 1 ≤ Q →
    Q ≤ powerSieveSmoothBound n L →
    0 < powerSieveDyadicPartnerLower n L Q
  hW : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
    q ≠ m₀ → 0 < W q
  hcofactor : ∀ Q : ℕ, 1 ≤ Q →
    Q ≤ powerSieveSmoothBound n L →
    ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
    q ∈ powerSieveDyadicPrimeBlock Q →
    ∀ r ∈ powerSieveAuxPrimes n L Q,
    ∀ p ∈ primesInProgression
      (powerSieveX n L) (q * r) (q * r - 1),
      ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
        s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B
  hnumeric : ∀ Q : ℕ, 1 ≤ Q →
    Q ≤ powerSieveSmoothBound n L →
    ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
    q ∈ powerSieveDyadicPrimeBlock Q →
    ∀ r ∈ powerSieveAuxPrimes n L Q,
    ((representedLargeFactorPrimes
      (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
        W q * (r : ℝ)⁻¹ ≤
      powerSieveProgressionBudget (powerSieveX n L) q r
  hauxBudget : ∀ Q : ℕ, 1 ≤ Q →
    Q ≤ powerSieveSmoothBound n L →
    20 * Real.sqrt (n : ℝ) *
        primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveDyadicAuxCutoff n L Q) ≤
      (powerSieveDyadicPartnerLower n L Q : ℝ) *
        (powerSieveX n L : ℝ)
  hprodBudget : ∀ Q : ℕ, 1 ≤ Q →
    Q ≤ powerSieveSmoothBound n L →
    40 * Real.sqrt (n : ℝ) *
        primitiveEndpointVaughanBudget (powerSieveX n L)
          (powerSieveDyadicProductCutoff n L Q) ≤
      ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ)
  hrootBudget : ∀ Q : ℕ, 1 ≤ Q →
    Q ≤ powerSieveSmoothBound n L → n < 2 * Q →
    10 * Real.sqrt (n : ℝ) *
        primitiveEndpointVaughanBudget (powerSieveX n L) (2 * Q) ≤
      (Q : ℝ) * (powerSieveX n L : ℝ)

theorem PowerSieveEndpointSplitPrefixInput.erase_prefix_bound
    {n L J₀ m₀ B : ℕ} {W : ℕ → ℝ}
    (h : PowerSieveEndpointSplitPrefixInput n L J₀ m₀ B W) :
    ∀ y : ℕ,
      (((((powerSieveShiftedSmoothBadRoots n L W).erase m₀).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (4 / Real.sqrt (n : ℝ)) * (y : ℝ) :=
  powerSieveBadRootsErase_prefix_bound_of_endpoint_split
    h.hn h.hL h.hJlarge h.hbelow h.hPageGood h.hmass h.hpartnerPos h.hW
      h.hcofactor h.hnumeric h.hauxBudget h.hprodBudget h.hrootBudget

theorem zero_not_mem_powerSieveShiftedSmoothBadRoots
    (n L : ℕ) (W : ℕ → ℝ) :
    0 ∉ powerSieveShiftedSmoothBadRoots n L W := by
  intro hzero
  exact Nat.not_prime_zero
    (mem_powerSieveShiftedSmoothBadRoots.mp hzero).1

/-- All-good branch: using the harmless sentinel exception `m₀=0`, the
full literal bad-root set has coefficient `4`. -/
theorem PowerSieveEndpointSplitPrefixInput.full_prefix_bound_of_zero
    {n L J₀ B : ℕ} {W : ℕ → ℝ}
    (h : PowerSieveEndpointSplitPrefixInput n L J₀ 0 B W) :
    ∀ y : ℕ,
      ((((powerSieveShiftedSmoothBadRoots n L W).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (4 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  simpa only [Finset.erase_eq_of_notMem
    (zero_not_mem_powerSieveShiftedSmoothBadRoots n L W)] using
      h.erase_prefix_bound

/-- Retarget branch: the sole remaining endpoint exception is the base
itself, and its singleton cost raises the coefficient from `4` to `5`. -/
theorem PowerSieveEndpointSplitPrefixInput.full_prefix_bound_of_base
    {n L J₀ B : ℕ} {W : ℕ → ℝ}
    (h : PowerSieveEndpointSplitPrefixInput n L J₀ n B W) :
    ∀ y : ℕ,
      ((((powerSieveShiftedSmoothBadRoots n L W).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (5 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  have hfull := card_filter_le_add_one_div_sqrt_of_erase_base
    (E := powerSieveShiftedSmoothBadRoots n L W) (A := 4)
    ((by omega : 1 ≤ 2).trans h.hn) h.erase_prefix_bound
  convert hfull using 1 <;> norm_num

/-- Eventual coefficient-`4` prefix sparsity for the all-good branch,
ready to be passed as `hprefix` to `PowerSieveAnalyticAssembly`. -/
theorem eventually_powerSieveBadRoots_prefix_bound_allGood
    {L J₀ B : ℕ} {rawLower : ℕ → ℕ → ℝ}
    (hinput : ∀ᶠ n : ℕ in Filter.atTop,
      PowerSieveEndpointSplitPrefixInput n L J₀ 0 B (rawLower n)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ y : ℕ,
      ((((powerSieveShiftedSmoothBadRoots n L (rawLower n)).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (4 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  filter_upwards [hinput] with n hn
  exact hn.full_prefix_bound_of_zero

/-- Eventual coefficient-`5` prefix sparsity for the branch retargeted at
the base `n`, again in the exact shape consumed by analytic assembly. -/
theorem eventually_powerSieveBadRoots_prefix_bound_retarget
    {L J₀ B : ℕ} {rawLower : ℕ → ℕ → ℝ}
    (hinput : ∀ᶠ n : ℕ in Filter.atTop,
      PowerSieveEndpointSplitPrefixInput n L J₀ n B (rawLower n)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ y : ℕ,
      ((((powerSieveShiftedSmoothBadRoots n L (rawLower n)).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (5 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  filter_upwards [hinput] with n hn
  exact hn.full_prefix_bound_of_base

/-- If the Page-excluded conductor is not a literal bad prime root, the
preceding erased-set estimate is exactly the required prefix estimate for
the full literal bad-root set. -/
theorem powerSieveBadRoots_prefix_bound
    {n L J₀ m₀ B : ℕ} {W : ℕ → ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hm₀ : m₀ ∉ powerSieveShiftedSmoothBadRoots n L W)
    (hJlarge : 2000 * L ≤ 2 ^ J₀)
    (hbelow : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → q ≤ 2 ^ J₀ → False)
    (hendpoint : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ →
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10)
    (hmass : ∀ Q : ℕ, 1 ≤ Q → Q ≤ powerSieveSmoothBound n L →
      (1 / (500 * (L : ℝ)) : ℝ) ≤
        ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hpartnerPos : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      0 < powerSieveDyadicPartnerLower n L Q)
    (hW : ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W,
      q ≠ m₀ → 0 < W q)
    (hcofactor : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
      q ∈ powerSieveDyadicPrimeBlock Q →
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      ∀ q ∈ powerSieveShiftedSmoothBadRoots n L W, q ≠ m₀ →
      q ∈ powerSieveDyadicPrimeBlock Q →
      ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r)
    (hauxBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      20 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicAuxCutoff n L Q) ≤
        (powerSieveDyadicPartnerLower n L Q : ℝ) *
          (powerSieveX n L : ℝ))
    (hprodBudget : ∀ Q : ℕ, 1 ≤ Q →
      Q ≤ powerSieveSmoothBound n L →
      40 * Real.sqrt (n : ℝ) *
          primitiveEndpointVaughanBudget (powerSieveX n L)
            (powerSieveDyadicProductCutoff n L Q) ≤
        ((powerSieveDyadicPrimeBlock Q).card : ℝ) *
          (powerSieveDyadicPartnerLower n L Q : ℝ) *
            (powerSieveX n L : ℝ)) :
    ∀ y : ℕ,
      ((((powerSieveShiftedSmoothBadRoots n L W).filter
        fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
        (2 / Real.sqrt (n : ℝ)) * (y : ℝ) := by
  have h := powerSieveBadRootsErase_prefix_bound
    hn hL hJlarge hbelow hendpoint hmass hpartnerPos hW
      hcofactor hnumeric hauxBudget hprodBudget
  simpa only [Finset.erase_eq_of_notMem hm₀] using h

end

end Erdos48
