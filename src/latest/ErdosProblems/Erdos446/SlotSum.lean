/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BitMasks

/-!
# Erdős Problem 446: summing close ordered slot configurations

This file combines the distinguished-prime fiber estimate with the sharp
last-difference bit-mask count.  It first bounds the prime-array sum for one
fixed mask, then aggregates diagonal and non-diagonal masks.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def configurationCloseWeightSum (M k : ℕ) (b : ℕ → ℕ)
    (c : BlockSlot k b → Bool × Bool) : ℝ := by
  classical
  exact ∑ a : SlotPrimeArray M k b,
    if SlotClose (a, c) then slotConfigurationWeight (a, c) else 0

theorem sum_blockPrimeSubtype (j : ℕ) :
    (∑ p : ↥(primeBlock j), 1 / (p.1 : ℝ)) = primeBlockMass j := by
  rw [← Finset.sum_subtype (primeBlock j) (fun p ↦ Iff.rfl)
    (fun p ↦ 1 / (p : ℝ))]
  rfl

theorem sum_piAway_primeWeight {M k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b) :
    (∑ v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
        ∏ t, 1 / ((v t).1 : ℝ)) =
      ∏ t : {t : BlockSlot k b // t ≠ s},
        primeBlockMass (M + t.1.1) := by
  let A := fun t : {t : BlockSlot k b // t ≠ s} ↦
    ↥(primeBlock (M + t.1.1))
  let w : ∀ t, A t → ℝ := fun _ p ↦ 1 / (p.1 : ℝ)
  have hprod := Finset.prod_univ_sum
    (t := fun t : {t : BlockSlot k b // t ≠ s} ↦
      (Finset.univ : Finset (A t))) w
  calc
    (∑ v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
        ∏ t, 1 / ((v t).1 : ℝ)) =
        ∏ t : {t : BlockSlot k b // t ≠ s},
          ∑ p : A t, w t p := by
      simpa only [A, w, Fintype.piFinset_univ, Finset.mem_univ,
        Finset.sum_const_zero] using hprod.symm
    _ = ∏ t : {t : BlockSlot k b // t ≠ s},
        primeBlockMass (M + t.1.1) := by
      apply Finset.prod_congr rfl
      intro t ht
      exact sum_blockPrimeSubtype (M + t.1.1)

theorem card_slotAway {k : ℕ} {b : ℕ → ℕ} (s : BlockSlot k b) :
    Fintype.card {t : BlockSlot k b // t ≠ s} = slotCount k b - 1 := by
  rw [Fintype.card_subtype_compl (fun t : BlockSlot k b ↦ t = s),
    card_blockSlot]
  simp

theorem piAway_primeWeight_upper {M k : ℕ} {b : ℕ → ℕ}
    {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H)
    (s : BlockSlot k b) :
    (∑ v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
        ∏ t, 1 / ((v t).1 : ℝ)) ≤ H ^ (slotCount k b - 1) := by
  rw [sum_piAway_primeWeight]
  calc
    (∏ t : {t : BlockSlot k b // t ≠ s},
        primeBlockMass (M + t.1.1)) ≤
        ∏ _t : {t : BlockSlot k b // t ≠ s}, H := by
      apply Finset.prod_le_prod
      · intro t ht
        rw [primeBlockMass]
        exact Finset.sum_nonneg fun p hp ↦ by positivity
      · intro t ht
        exact hmass t.1.1
    _ = H ^ (slotCount k b - 1) := by
      rw [Finset.prod_const, Finset.card_univ, card_slotAway]

theorem configurationCloseWeightSum_le_fibers
    {M k : ℕ} {b : ℕ → ℕ} (s : BlockSlot k b)
    (c : BlockSlot k b → Bool × Bool) (C : ℝ)
    (hfiber : ∀ v : PiAway
      (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
      (∑ q : ↥(primeBlock (M + s.1)),
        distinguishedFiberWeight s v c q) ≤ C) :
    configurationCloseWeightSum M k b c ≤
      ∑ v : PiAway
          (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
        (∏ t, 1 / ((v t).1 : ℝ)) * C := by
  classical
  let A := fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))
  let w : ∀ t, A t → ℝ := fun _ p ↦ 1 / (p.1 : ℝ)
  have hfiber' (v : PiAway A s) :
      (∑ q : A s,
        if SlotClose (piInsert s q v, c) then w s q else 0) ≤ C := by
    simpa only [A, w, distinguishedFiberWeight] using hfiber v
  have hsplit := sum_pi_event_weight_le_fiber
    (I := BlockSlot k b) (A := A) w
    (fun _ p ↦ by dsimp [w]; positivity) s
    (fun a ↦ SlotClose (a, c)) C hfiber'
  simpa only [configurationCloseWeightSum, slotConfigurationWeight,
    A, w] using hsplit

theorem configurationCloseWeightSum_le_of_lastDifference
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H)
    (s : BlockSlot k b) (c : BlockSlot k b → Bool × Bool)
    (hlast : LastDifferenceAt s c) :
    configurationCloseWeightSum M k b c ≤
      H ^ (slotCount k b - 1) *
        (7 / Real.log (blockEndpoint (M + s.1) : ℝ)) := by
  classical
  let C : ℝ := 7 / Real.log (blockEndpoint (M + s.1) : ℝ)
  have hfiber (v : PiAway
      (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s) :
      (∑ q : ↥(primeBlock (M + s.1)),
        distinguishedFiberWeight s v c q) ≤ C := by
    simpa only [C] using
      distinguishedPrime_fiber_mass_upper hN hendpoint hprime s v c hlast.1
  calc
    configurationCloseWeightSum M k b c ≤
        ∑ v : PiAway
            (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
          (∏ t, 1 / ((v t).1 : ℝ)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ)) := by
      simpa only [C] using
        configurationCloseWeightSum_le_fibers s c C hfiber
    _ = (∑ v : PiAway
            (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
          ∏ t, 1 / ((v t).1 : ℝ)) *
          (7 / Real.log (blockEndpoint (M + s.1) : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ H ^ (slotCount k b - 1) *
          (7 / Real.log (blockEndpoint (M + s.1) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (piAway_primeWeight_upper hH hmass s)
      have hlog : 0 < Real.log (blockEndpoint (M + s.1) : ℝ) :=
        Real.log_pos (by
          exact_mod_cast (show 1 < blockEndpoint (M + s.1) by
            exact lt_of_lt_of_le (by omega : 1 < N) (hendpoint s.1)))
      positivity

theorem sum_slotPrimeArray_weight (M k : ℕ) (b : ℕ → ℕ) :
    (∑ a : SlotPrimeArray M k b,
        ∏ s, 1 / ((a s).1 : ℝ)) =
      ∏ s : BlockSlot k b, primeBlockMass (M + s.1) := by
  let A := fun s : BlockSlot k b ↦ ↥(primeBlock (M + s.1))
  let w : ∀ s, A s → ℝ := fun _ p ↦ 1 / (p.1 : ℝ)
  have hprod := Finset.prod_univ_sum
    (t := fun s : BlockSlot k b ↦ (Finset.univ : Finset (A s))) w
  calc
    (∑ a : SlotPrimeArray M k b,
        ∏ s, 1 / ((a s).1 : ℝ)) =
        ∏ s : BlockSlot k b, ∑ p : A s, w s p := by
      simpa only [A, w, Fintype.piFinset_univ] using hprod.symm
    _ = ∏ s : BlockSlot k b, primeBlockMass (M + s.1) := by
      apply Finset.prod_congr rfl
      intro s hs
      exact sum_blockPrimeSubtype (M + s.1)

theorem slotPrimeArray_weight_upper {M k : ℕ} {b : ℕ → ℕ}
    {H : ℝ} (_hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H) :
    (∑ a : SlotPrimeArray M k b,
        ∏ s, 1 / ((a s).1 : ℝ)) ≤ H ^ slotCount k b := by
  rw [sum_slotPrimeArray_weight]
  calc
    (∏ s : BlockSlot k b, primeBlockMass (M + s.1)) ≤
        ∏ _s : BlockSlot k b, H := by
      apply Finset.prod_le_prod
      · intro s hs
        rw [primeBlockMass]
        exact Finset.sum_nonneg fun p hp ↦ by positivity
      · intro s hs
        exact hmass s.1
    _ = H ^ slotCount k b := by
      rw [Finset.prod_const, Finset.card_univ, card_blockSlot]

theorem slotClose_of_diagonal {M k : ℕ} {b : ℕ → ℕ}
    {c : BlockSlot k b → Bool × Bool} (hc : DiagonalBits c)
    (a : SlotPrimeArray M k b) : SlotClose (a, c) := by
  have hprod : slotBitProduct (a, c) true = slotBitProduct (a, c) false := by
    unfold slotBitProduct
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hc s]
  rw [SlotClose, hprod, sub_self, abs_zero]
  exact Real.log_nonneg (by norm_num)

theorem configurationCloseWeightSum_le_of_diagonal
    {M k : ℕ} {b : ℕ → ℕ} {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H)
    {c : BlockSlot k b → Bool × Bool} (hc : DiagonalBits c) :
    configurationCloseWeightSum M k b c ≤ H ^ slotCount k b := by
  calc
    configurationCloseWeightSum M k b c =
        ∑ a : SlotPrimeArray M k b,
          ∏ s, 1 / ((a s).1 : ℝ) := by
      classical
      rw [configurationCloseWeightSum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_pos (slotClose_of_diagonal hc a)]
      rfl
    _ ≤ H ^ slotCount k b := slotPrimeArray_weight_upper hH hmass

theorem closeSlotSum_eq_sum_configuration (M k : ℕ) (b : ℕ → ℕ) :
    (∑ z ∈ closeSlotConfigurations M k b, slotConfigurationWeight z) =
      ∑ c : BlockSlot k b → Bool × Bool,
        configurationCloseWeightSum M k b c := by
  classical
  rw [closeSlotConfigurations, Finset.sum_filter]
  change (∑ z : SlotConfiguration M k b,
      if SlotClose z then slotConfigurationWeight z else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

private theorem sum_union_le_add {α : Type*} [DecidableEq α]
    (A B : Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ A ∪ B, f x) ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  have hdisj : Disjoint A (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hx
    exact (Finset.mem_sdiff.mp hx).2 hxA
  have hunion : A ∪ (B \ A) = A ∪ B := by
    ext x
    simp
  rw [← hunion, Finset.sum_union hdisj]
  have hdiff : (∑ x ∈ B \ A, f x) ≤ ∑ x ∈ B, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x hxB hxnot ↦ hf x)
  exact add_le_add le_rfl hdiff

private theorem sum_biUnion_le_sum_sum {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (S : Finset ι) (T : ι → Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ S.biUnion T, f x) ≤ ∑ i ∈ S, ∑ x ∈ T i, f x := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (sum_union_le_add (T i) (S.biUnion T) f hf).trans
        (add_le_add le_rfl ih)

theorem configurationCloseWeightSum_nonneg (M k : ℕ) (b : ℕ → ℕ)
    (c : BlockSlot k b → Bool × Bool) :
    0 ≤ configurationCloseWeightSum M k b c := by
  rw [configurationCloseWeightSum]
  exact Finset.sum_nonneg fun a ha ↦ by
    split_ifs
    · exact Finset.prod_nonneg fun s hs ↦ by positivity
    · positivity

theorem diagonal_configuration_sum_upper
    {M k : ℕ} {b : ℕ → ℕ} {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H) :
    (∑ c ∈ diagonalBitMasks k b, configurationCloseWeightSum M k b c) ≤
      (2 : ℝ) ^ slotCount k b * H ^ slotCount k b := by
  classical
  calc
    (∑ c ∈ diagonalBitMasks k b, configurationCloseWeightSum M k b c) ≤
        ∑ _c ∈ diagonalBitMasks k b, H ^ slotCount k b := by
      apply Finset.sum_le_sum
      intro c hc
      exact configurationCloseWeightSum_le_of_diagonal hH hmass
        (Finset.mem_filter.mp hc).2
    _ = ((diagonalBitMasks k b).card : ℝ) * H ^ slotCount k b := by
      simp
    _ ≤ (2 : ℝ) ^ slotCount k b * H ^ slotCount k b := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hH _)
      exact_mod_cast card_diagonalBitMasks_le k b

theorem nondiagonal_configuration_sum_upper
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H) :
    (∑ c ∈ nondiagonalBitMasks k b,
        configurationCloseWeightSum M k b c) ≤
      ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          (H ^ (slotCount k b - 1) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
  classical
  let f := configurationCloseWeightSum M k b
  let U := (Finset.univ : Finset (BlockSlot k b)).biUnion
    lastDifferenceBitMasks
  have hsubset : nondiagonalBitMasks k b ⊆ U :=
    nondiagonalBitMasks_subset_biUnion_last k b
  have hnonneg : ∀ c, 0 ≤ f c := configurationCloseWeightSum_nonneg M k b
  calc
    (∑ c ∈ nondiagonalBitMasks k b, f c) ≤ ∑ c ∈ U, f c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun c hcU hcnot ↦ hnonneg c)
    _ ≤ ∑ s : BlockSlot k b,
        ∑ c ∈ lastDifferenceBitMasks s, f c := by
      simpa only [U] using sum_biUnion_le_sum_sum
        (Finset.univ : Finset (BlockSlot k b))
        lastDifferenceBitMasks f hnonneg
    _ ≤ ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          (H ^ (slotCount k b - 1) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
      apply Finset.sum_le_sum
      intro s hs
      have hlog : 0 < Real.log (blockEndpoint (M + s.1) : ℝ) :=
        Real.log_pos (by
          exact_mod_cast (show 1 < blockEndpoint (M + s.1) by
            exact lt_of_lt_of_le (by omega : 1 < N) (hendpoint s.1)))
      let K := H ^ (slotCount k b - 1) *
        (7 / Real.log (blockEndpoint (M + s.1) : ℝ))
      calc
        (∑ c ∈ lastDifferenceBitMasks s, f c) ≤
            ∑ _c ∈ lastDifferenceBitMasks s, K := by
          apply Finset.sum_le_sum
          intro c hc
          exact configurationCloseWeightSum_le_of_lastDifference
            hN hendpoint hprime hH hmass s c (Finset.mem_filter.mp hc).2
        _ = ((lastDifferenceBitMasks s).card : ℝ) * K := by simp
        _ ≤ (2 : ℝ) ^ (slotCount k b +
              ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) * K := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_lastDifferenceBitMasks_le s
          · dsimp [K]
            positivity

theorem closeSlotSum_upper
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H) :
    (∑ z ∈ closeSlotConfigurations M k b, slotConfigurationWeight z) ≤
      (2 : ℝ) ^ slotCount k b * H ^ slotCount k b +
      ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          (H ^ (slotCount k b - 1) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
  classical
  rw [closeSlotSum_eq_sum_configuration]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (BlockSlot k b → Bool × Bool)) DiagonalBits
    (configurationCloseWeightSum M k b)
  calc
    (∑ c : BlockSlot k b → Bool × Bool,
        configurationCloseWeightSum M k b c) =
        (∑ c ∈ diagonalBitMasks k b,
          configurationCloseWeightSum M k b c) +
        ∑ c ∈ nondiagonalBitMasks k b,
          configurationCloseWeightSum M k b c := by
      simpa [diagonalBitMasks, nondiagonalBitMasks] using hsplit.symm
    _ ≤ _ := add_le_add
      (diagonal_configuration_sum_upper hH hmass)
      (nondiagonal_configuration_sum_upper hN hendpoint hprime hH hmass)

/-! ## Exact block-mass form

The preceding convenient uniform form is not sharp enough for the final
exponent if `H` is a fixed enlargement of `log 2`.  We therefore retain the
full product of the reciprocal masses of all nondistinguished slots. -/

theorem configurationCloseWeightSum_le_of_lastDifference_exact
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    (s : BlockSlot k b) (c : BlockSlot k b → Bool × Bool)
    (hlast : LastDifferenceAt s c) :
    configurationCloseWeightSum M k b c ≤
      (∏ t : {t : BlockSlot k b // t ≠ s},
        primeBlockMass (M + t.1.1)) *
        (7 / Real.log (blockEndpoint (M + s.1) : ℝ)) := by
  classical
  let C : ℝ := 7 / Real.log (blockEndpoint (M + s.1) : ℝ)
  have hfiber (v : PiAway
      (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s) :
      (∑ q : ↥(primeBlock (M + s.1)),
        distinguishedFiberWeight s v c q) ≤ C := by
    simpa only [C] using
      distinguishedPrime_fiber_mass_upper hN hendpoint hprime s v c hlast.1
  calc
    configurationCloseWeightSum M k b c ≤
        ∑ v : PiAway
            (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
          (∏ t, 1 / ((v t).1 : ℝ)) * C :=
      configurationCloseWeightSum_le_fibers s c C hfiber
    _ = (∑ v : PiAway
            (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s,
          ∏ t, 1 / ((v t).1 : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ = _ := by rw [sum_piAway_primeWeight]

theorem configurationCloseWeightSum_eq_of_diagonal_exact
    {M k : ℕ} {b : ℕ → ℕ}
    {c : BlockSlot k b → Bool × Bool} (hc : DiagonalBits c) :
    configurationCloseWeightSum M k b c =
      ∏ s : BlockSlot k b, primeBlockMass (M + s.1) := by
  calc
    configurationCloseWeightSum M k b c =
        ∑ a : SlotPrimeArray M k b,
          ∏ s, 1 / ((a s).1 : ℝ) := by
      classical
      rw [configurationCloseWeightSum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_pos (slotClose_of_diagonal hc a)]
      rfl
    _ = _ := sum_slotPrimeArray_weight M k b

theorem primeBlockMass_nonneg (j : ℕ) : 0 ≤ primeBlockMass j := by
  rw [primeBlockMass]
  exact Finset.sum_nonneg fun p hp ↦ by positivity

theorem slotMassProduct_nonneg (M k : ℕ) (b : ℕ → ℕ) :
    0 ≤ ∏ s : BlockSlot k b, primeBlockMass (M + s.1) :=
  Finset.prod_nonneg fun s hs ↦ primeBlockMass_nonneg _

theorem diagonal_configuration_sum_upper_exact
    {M k : ℕ} {b : ℕ → ℕ} :
    (∑ c ∈ diagonalBitMasks k b,
        configurationCloseWeightSum M k b c) ≤
      (2 : ℝ) ^ slotCount k b *
        ∏ s : BlockSlot k b, primeBlockMass (M + s.1) := by
  classical
  let P : ℝ := ∏ s : BlockSlot k b, primeBlockMass (M + s.1)
  calc
    (∑ c ∈ diagonalBitMasks k b,
        configurationCloseWeightSum M k b c) =
        ∑ _c ∈ diagonalBitMasks k b, P := by
      apply Finset.sum_congr rfl
      intro c hc
      exact configurationCloseWeightSum_eq_of_diagonal_exact
        (Finset.mem_filter.mp hc).2
    _ = ((diagonalBitMasks k b).card : ℝ) * P := by simp
    _ ≤ (2 : ℝ) ^ slotCount k b * P := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_diagonalBitMasks_le k b
      · exact slotMassProduct_nonneg M k b

theorem nondiagonal_configuration_sum_upper_exact
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    (∑ c ∈ nondiagonalBitMasks k b,
        configurationCloseWeightSum M k b c) ≤
      ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          ((∏ t : {t : BlockSlot k b // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
  classical
  let f := configurationCloseWeightSum M k b
  let U := (Finset.univ : Finset (BlockSlot k b)).biUnion
    lastDifferenceBitMasks
  have hsubset : nondiagonalBitMasks k b ⊆ U :=
    nondiagonalBitMasks_subset_biUnion_last k b
  have hnonneg : ∀ c, 0 ≤ f c := configurationCloseWeightSum_nonneg M k b
  calc
    (∑ c ∈ nondiagonalBitMasks k b, f c) ≤ ∑ c ∈ U, f c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun c hcU hcnot ↦ hnonneg c)
    _ ≤ ∑ s : BlockSlot k b,
        ∑ c ∈ lastDifferenceBitMasks s, f c := by
      simpa only [U] using sum_biUnion_le_sum_sum
        (Finset.univ : Finset (BlockSlot k b))
        lastDifferenceBitMasks f hnonneg
    _ ≤ ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          ((∏ t : {t : BlockSlot k b // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
      apply Finset.sum_le_sum
      intro s hs
      let K : ℝ :=
        (∏ t : {t : BlockSlot k b // t ≠ s},
          primeBlockMass (M + t.1.1)) *
          (7 / Real.log (blockEndpoint (M + s.1) : ℝ))
      calc
        (∑ c ∈ lastDifferenceBitMasks s, f c) ≤
            ∑ _c ∈ lastDifferenceBitMasks s, K := by
          apply Finset.sum_le_sum
          intro c hc
          exact configurationCloseWeightSum_le_of_lastDifference_exact
            hN hendpoint hprime s c (Finset.mem_filter.mp hc).2
        _ = ((lastDifferenceBitMasks s).card : ℝ) * K := by simp
        _ ≤ (2 : ℝ) ^ (slotCount k b +
              ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) * K := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_lastDifferenceBitMasks_le s
          · dsimp [K]
            apply mul_nonneg
            · exact Finset.prod_nonneg fun t ht ↦ primeBlockMass_nonneg _
            · have hlog : 0 < Real.log (blockEndpoint (M + s.1) : ℝ) :=
                Real.log_pos (by
                  exact_mod_cast (show 1 < blockEndpoint (M + s.1) by
                    exact lt_of_lt_of_le (by omega : 1 < N) (hendpoint s.1)))
              positivity

theorem closeSlotSum_upper_exact
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    (∑ z ∈ closeSlotConfigurations M k b, slotConfigurationWeight z) ≤
      (2 : ℝ) ^ slotCount k b *
        (∏ s : BlockSlot k b, primeBlockMass (M + s.1)) +
      ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          ((∏ t : {t : BlockSlot k b // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
  classical
  rw [closeSlotSum_eq_sum_configuration]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (BlockSlot k b → Bool × Bool)) DiagonalBits
    (configurationCloseWeightSum M k b)
  calc
    (∑ c : BlockSlot k b → Bool × Bool,
        configurationCloseWeightSum M k b c) =
        (∑ c ∈ diagonalBitMasks k b,
          configurationCloseWeightSum M k b c) +
        ∑ c ∈ nondiagonalBitMasks k b,
          configurationCloseWeightSum M k b c := by
      simpa [diagonalBitMasks, nondiagonalBitMasks] using hsplit.symm
    _ ≤ _ := add_le_add diagonal_configuration_sum_upper_exact
      (nondiagonal_configuration_sum_upper_exact hN hendpoint hprime)

end Erdos446
