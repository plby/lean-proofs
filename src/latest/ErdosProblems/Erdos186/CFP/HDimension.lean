/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.BiluFreiman
import ErdosProblems.Erdos186.CFP.BoundingBox
import ErdosProblems.Erdos186.CFP.Centering
import ErdosProblems.Erdos186.CFP.Corollary217
import ErdosProblems.Erdos186.CFP.DilateVolume
import ErdosProblems.Erdos186.CFP.GAPBuilders
import ErdosProblems.Erdos186.CFP.GrowthLemmas
import ErdosProblems.Erdos186.CFP.NonproperBound
import ErdosProblems.Erdos186.CFP.SymmetricGAP

/-!
# Finite h-dimension and bounding-box estimates

This file gives the exact finite interface to the output of Conlon--Fox--
Pham, Lemma 2.22, and proves the deductions made in Corollary 2.24 and the
cardinality part of Lemma 2.26.

The paper writes its constant-scale conclusion as follows: for a constant
`c > 0`, the `h`-fold sumset of `A` contains a translate of the proper GAP
`c h P`.  `HApproximation` records this without real dilations.  Its natural
scale `k` satisfies the division-free estimate

`scaleNum * h <= scaleDen * k`.

Thus `scaleNum / scaleDen` is the paper's constant `c`.  All constants and
thresholds are explicit natural numbers.  The definition also records the
nondegeneracy which is established in the proof of Lemma 2.22 by deleting
directions shorter than the contraction scale.

The deep existence assertion is deliberately not postulated here.  It
requires the Bilu--Freiman inverse theorem represented by
`BiluFreimanStatement`, together with the dense-box argument.  In particular,
none of the theorems below takes an arbitrary proposition standing in for
the conclusion: they are unconditional consequences of an actual finite
`HApproximation` object.
-/

namespace Erdos186.CFP.HDimension

open scoped BigOperators Pointwise
open GrowthLemmas

/-! ## Boundary growth for nonproper dilates -/

/-- A product changes by at most the sum of its one-coordinate changes,
with all unchanged coordinates evaluated at the larger endpoint. -/
theorem prod_le_prod_add_sum_erase {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℕ)
    (hba : ∀ i ∈ s, b i ≤ a i) :
    (∏ i ∈ s, a i) ≤ (∏ i ∈ s, b i) +
      ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, a j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hxba : b x ≤ a x := hba x (Finset.mem_insert_self x s)
      have hsba : ∀ i ∈ s, b i ≤ a i := fun i hi ↦
        hba i (Finset.mem_insert_of_mem hi)
      have hih := ih hsba
      have hprod : (∏ i ∈ s, b i) ≤ ∏ i ∈ s, a i :=
        Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) hsba
      have hxsplit : a x = b x + (a x - b x) :=
        (Nat.add_sub_of_le hxba).symm
      have hsum :
          (∑ i ∈ insert x s,
              (a i - b i) * ∏ j ∈ (insert x s).erase i, a j) =
            (a x - b x) * (∏ i ∈ s, a i) +
              a x * ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, a j := by
        rw [Finset.sum_insert hx]
        apply congrArg₂ (· + ·)
        · simp [hx]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hix : i ≠ x := fun h ↦ hx (h ▸ hi)
          have herase : (insert x s).erase i = insert x (s.erase i) := by
            ext z
            simp only [Finset.mem_erase, Finset.mem_insert]
            constructor
            · rintro ⟨hzi, hzx | hzs⟩
              · exact Or.inl hzx
              · exact Or.inr ⟨hzi, hzs⟩
            · rintro (hzx | ⟨hzi, hzs⟩)
              · subst z
                exact ⟨Ne.symm hix, Or.inl rfl⟩
              · exact ⟨hzi, Or.inr hzs⟩
          rw [herase, Finset.prod_insert]
          · ring
          · simp [hx]
      calc
        (∏ i ∈ insert x s, a i) = a x * ∏ i ∈ s, a i := by simp [hx]
        _ ≤ a x * ((∏ i ∈ s, b i) +
              ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, a j) :=
          Nat.mul_le_mul_left _ hih
        _ = a x * (∏ i ∈ s, b i) +
              a x * ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, a j := by
          rw [Nat.mul_add]
        _ = (b x * (∏ i ∈ s, b i) +
              (a x - b x) * (∏ i ∈ s, b i)) +
              a x * ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, a j := by
          rw [hxsplit, Nat.add_sub_cancel_left, Nat.add_mul]
        _ ≤ (b x * (∏ i ∈ s, b i) +
              (a x - b x) * (∏ i ∈ s, a i)) +
              a x * ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, a j := by
          gcongr
        _ = (∏ i ∈ insert x s, b i) +
              ∑ i ∈ insert x s,
                (a i - b i) * ∏ j ∈ (insert x s).erase i, a j := by
          rw [Finset.prod_insert hx, hsum]
          ring

/-- The finite slow-growth pigeonhole argument used in CFP Lemma 2.22.
If the total growth across `steps` consecutive scales is at most `K^steps`,
then one adjacent pair grows by at most `K`.  Keeping this lemma over `ℝ`
allows the source's factor `2^(d + 1/2)` to be used literally. -/
theorem exists_slow_step_of_end_le_pow_mul (f : ℕ → ℝ)
    {start steps : ℕ} {K : ℝ} (hsteps : 0 < steps) (hK : 0 ≤ K)
    (hend : f (start + steps) ≤ K ^ steps * f start) :
    ∃ i < steps, f (start + i + 1) ≤ K * f (start + i) := by
  by_contra hnone
  push Not at hnone
  have hstrict : ∀ i, i < steps →
      K ^ (i + 1) * f start < f (start + (i + 1)) := by
    intro i hi
    induction i with
    | zero =>
        simpa using hnone 0 hsteps
    | succ i ih =>
        have hi' : i < steps := (Nat.lt_succ_self i).trans hi
        have hmul :
            K * (K ^ (i + 1) * f start) ≤
              K * f (start + (i + 1)) :=
          mul_le_mul_of_nonneg_left (le_of_lt (ih hi')) hK
        calc
          K ^ (i + 1 + 1) * f start =
              K * (K ^ (i + 1) * f start) := by ring
          _ ≤ K * f (start + (i + 1)) := hmul
          _ < f (start + (i + 1) + 1) := hnone (i + 1) hi
          _ = f (start + (Nat.succ i + 1)) := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc]
  obtain ⟨last, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsteps)
  have hlast := hstrict last (Nat.lt_succ_self last)
  exact (not_lt_of_ge hend) (by simpa [Nat.add_assoc] using hlast)

/-- The literal half-exponent specialization occurring in CFP Lemma 2.22.
This avoids replacing `2^(d+1/2)` by an inexact natural threshold. -/
theorem exists_dyadic_slow_step (f : ℕ → ℝ) (d : ℕ)
    {start steps : ℕ} (hsteps : 0 < steps)
    (hend : f (start + steps) ≤
      (Real.rpow 2 ((d : ℝ) + 1 / 2)) ^ steps * f start) :
    ∃ i < steps,
      f (start + i + 1) ≤
        Real.rpow 2 ((d : ℝ) + 1 / 2) * f (start + i) := by
  apply exists_slow_step_of_end_le_pow_mul f hsteps
  · exact (Real.rpow_pos_of_pos (by norm_num) _).le
  · exact hend

end Erdos186.CFP.HDimension

namespace Erdos186.GAP

variable {ambient rank : ℕ}
open Module

/-- Two GAP presentations are equal when their data fields agree. -/
theorem ext {P Q : Erdos186.GAP ambient rank}
    (hoffset : P.offset = Q.offset) (hsteps : P.steps = Q.steps)
    (hwidths : P.widths = Q.widths) : P = Q := by
  cases P
  cases Q
  rw [Erdos186.GAP.mk.injEq]
  exact ⟨hoffset, hsteps, hwidths⟩

/-- Add a coefficient of an `s`-dilate to a coefficient of the residual
`(k-s)`-dilate.  The result is a coefficient of the `k`-dilate. -/
def addDilateCoord (P : Erdos186.GAP ambient rank) {s k : ℕ}
    (hsk : s ≤ k) (a : (P.dilate s).Coord)
    (n : (P.dilate (k - s)).Coord) : (P.dilate k).Coord :=
  fun i ↦ ⟨(n i : ℕ) + (a i : ℕ), by
    have hn : (n i : ℕ) ≤ (k - s) * (P.widths i - 1) := by
      have := (n i).isLt
      simpa only [Erdos186.GAP.dilate_widths, Nat.lt_add_one_iff] using this
    have ha : (a i : ℕ) ≤ s * (P.widths i - 1) := by
      have := (a i).isLt
      simpa only [Erdos186.GAP.dilate_widths, Nat.lt_add_one_iff] using this
    have hsum := Nat.add_le_add hn ha
    rw [← Nat.add_mul, Nat.sub_add_cancel hsk] at hsum
    exact hsum.trans_lt (Nat.lt_succ_self _)⟩

/-- Translation by a fixed coefficient vector embeds the residual box into
the larger dilation box. -/
theorem addDilateCoord_injective (P : Erdos186.GAP ambient rank)
    {s k : ℕ} (hsk : s ≤ k) (a : (P.dilate s).Coord) :
    Function.Injective (addDilateCoord P hsk a) := by
  intro n m hnm
  funext i
  apply Fin.ext
  have hi := congrArg Fin.val (congrFun hnm i)
  simpa only [addDilateCoord] using Nat.add_right_cancel hi

/-- Two colliding coefficients of an `s`-dilate give equal translated
points in every larger dilation. -/
theorem coordPoint_addDilateCoord_eq_of_coordPoint_eq
    (P : Erdos186.GAP ambient rank) {s k : ℕ} (hsk : s ≤ k)
    {a b : (P.dilate s).Coord}
    (hab : (P.dilate s).coordPoint a = (P.dilate s).coordPoint b)
    (n : (P.dilate (k - s)).Coord) :
    (P.dilate k).coordPoint (addDilateCoord P hsk a n) =
      (P.dilate k).coordPoint (addDilateCoord P hsk b n) := by
  funext j
  have habj := congrFun hab j
  have hsums :
      (∑ i, (a i : ℤ) * P.steps i j) =
        ∑ i, (b i : ℤ) * P.steps i j := by
    change (s : ℤ) * P.offset j + (∑ i, (a i : ℤ) * P.steps i j) =
      (s : ℤ) * P.offset j + ∑ i, (b i : ℤ) * P.steps i j at habj
    exact add_left_cancel habj
  change
    (k : ℤ) * P.offset j +
          ∑ i, (((n i : ℕ) + (a i : ℕ) : ℕ) : ℤ) * P.steps i j =
      (k : ℤ) * P.offset j +
          ∑ i, (((n i : ℕ) + (b i : ℕ) : ℕ) : ℤ) * P.steps i j
  simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [hsums]

/-- Exact boundary loss caused by a collision at scale `s`. -/
theorem card_dilate_add_residual_volume_le_of_not_proper
    (P : Erdos186.GAP ambient rank) {s k : ℕ} (hsk : s ≤ k)
    (hnp : ¬ (P.dilate s).Proper) :
    (P.dilate k).carrier.card + (P.dilate (k - s)).volume ≤
      (P.dilate k).volume := by
  classical
  rw [Erdos186.GAP.Proper, Function.Injective] at hnp
  push Not at hnp
  obtain ⟨a, b, hab, hne⟩ := hnp
  have hdiff : ∃ i, a i ≠ b i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hdiff
  have hval : (a i : ℕ) ≠ (b i : ℕ) := fun h ↦ hi (Fin.ext h)
  have oriented (u v : (P.dilate s).Coord)
      (huv : (P.dilate s).coordPoint u = (P.dilate s).coordPoint v)
      (hlt : (u i : ℕ) < (v i : ℕ)) :
      (P.dilate k).carrier.card + (P.dilate (k - s)).volume ≤
        (P.dilate k).volume := by
    let outer : Finset (P.dilate k).Coord := Finset.univ
    let omitted : Finset (P.dilate k).Coord :=
      Finset.univ.image (addDilateCoord P hsk v)
    have homitted_outer : omitted ⊆ outer := by simp [outer]
    have hdesc : ∀ x ∈ omitted, ∃ y ∈ outer,
        (P.dilate k).coordPoint y = (P.dilate k).coordPoint x ∧
          (y i : ℕ) < (x i : ℕ) := by
      intro x hx
      obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨addDilateCoord P hsk u n, by simp [outer], ?_, ?_⟩
      · exact coordPoint_addDilateCoord_eq_of_coordPoint_eq P hsk huv n
      · change (n i : ℕ) + (u i : ℕ) < (n i : ℕ) + (v i : ℕ)
        omega
    have hcount := card_image_add_card_le_of_fiber_descent
      outer omitted (P.dilate k).coordPoint (fun n ↦ (n i : ℕ))
      homitted_outer hdesc
    have homitted_card : omitted.card = (P.dilate (k - s)).volume := by
      change (Finset.univ.image (addDilateCoord P hsk v)).card = _
      rw [Finset.card_image_of_injective _ (addDilateCoord_injective P hsk v)]
      rw [Finset.card_univ, Fintype.card_pi]
      simp only [Fintype.card_fin]
      change (P.dilate (k - s)).volume = _
      exact P.volume_dilate (k - s)
    have houter_card : outer.card = (P.dilate k).volume := by
      change Fintype.card (P.dilate k).Coord = (P.dilate k).volume
      rw [Fintype.card_pi]
      simp only [Fintype.card_fin]
      change (P.dilate k).volume = _
      exact P.volume_dilate k
    simpa only [outer, Erdos186.GAP.carrier, homitted_card, houter_card] using hcount
  rcases lt_or_gt_of_ne hval with hablt | hbalt
  · exact oriented a b hab hablt
  · exact oriented b a hab.symm hbalt

/-- Quantitative boundary estimate at an arbitrary collision scale.  It is
the coefficient-box form underlying CFP Corollary 2.21. -/
theorem card_dilate_le_rank_mul_scale_mul_pow_of_not_proper
    (P : Erdos186.GAP ambient rank) {s k : ℕ} (hsk : s ≤ k)
    (hnp : ¬ (P.dilate s).Proper) :
    (P.dilate k).carrier.card ≤
      rank * s * (k + 1) ^ (rank - 1) * P.volume := by
  classical
  let a : Fin rank → ℕ := fun i ↦ k * (P.widths i - 1) + 1
  let b : Fin rank → ℕ := fun i ↦ (k - s) * (P.widths i - 1) + 1
  have hba (i : Fin rank) : b i ≤ a i := by
    dsimp [a, b]
    gcongr
    exact Nat.sub_le k s
  have hprod := Erdos186.CFP.HDimension.prod_le_prod_add_sum_erase
    (Finset.univ : Finset (Fin rank)) a b (fun i _ ↦ hba i)
  have hboundary : (P.dilate k).carrier.card ≤
      ∑ i : Fin rank, (a i - b i) *
        ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i, a j := by
    have hcollision :=
      card_dilate_add_residual_volume_le_of_not_proper P hsk hnp
    change (P.dilate k).carrier.card + (∏ i, b i) ≤ ∏ i, a i at hcollision
    have hupper : (∏ i, a i) ≤ (∏ i, b i) +
        ∑ i : Fin rank, (a i - b i) *
          ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i, a j := by
      simpa using hprod
    omega
  have hterm (i : Fin rank) :
      (a i - b i) *
          ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i, a j ≤
        s * (k + 1) ^ (rank - 1) * P.volume := by
    have hdiff : a i - b i = s * (P.widths i - 1) := by
      dsimp [a, b]
      have hexpand : k * (P.widths i - 1) + 1 =
          ((k - s) * (P.widths i - 1) + 1) +
            s * (P.widths i - 1) := by
        calc
          k * (P.widths i - 1) + 1 =
              ((k - s) + s) * (P.widths i - 1) + 1 := by
            rw [Nat.sub_add_cancel hsk]
          _ = ((k - s) * (P.widths i - 1) + 1) +
              s * (P.widths i - 1) := by ring
      rw [hexpand]
      omega
    have hfactor (j : Fin rank) : a j ≤ (k + 1) * P.widths j := by
      exact P.dilate_width_le k j
    calc
      (a i - b i) *
          ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i, a j =
          (s * (P.widths i - 1)) *
            ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i, a j := by rw [hdiff]
      _ ≤ (s * P.widths i) *
            ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i,
              ((k + 1) * P.widths j) := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left s (Nat.sub_le _ _))
          (Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
            (fun j _ ↦ hfactor j))
      _ = s * (k + 1) ^ (rank - 1) * P.volume := by
        rw [Finset.prod_mul_distrib]
        have hcard : ((Finset.univ : Finset (Fin rank)).erase i).card = rank - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
        simp only [Finset.prod_const, hcard]
        rw [Erdos186.GAP.volume, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        ring
  calc
    (P.dilate k).carrier.card ≤
        ∑ i : Fin rank, (a i - b i) *
          ∏ j ∈ (Finset.univ : Finset (Fin rank)).erase i, a j := hboundary
    _ ≤ ∑ _i : Fin rank, s * (k + 1) ^ (rank - 1) * P.volume :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    _ = rank * s * (k + 1) ^ (rank - 1) * P.volume := by
      simp [mul_assoc]

/-- **CFP Corollary 2.21**, with an explicit dimension-only constant.
If the double of a rank-`rank` GAP is nonproper, every positive dilation has
degree at most `rank - 1` growth.  The paper only asserts an unspecified
constant `C_rank`; the direct boundary proof gives `rank * 2^rank`. -/
theorem card_dilate_le_pow_sub_one_mul_volume_of_two_not_proper
    (P : Erdos186.GAP ambient rank) {k : ℕ} (hk : 1 ≤ k)
    (hnp : ¬ (P.dilate 2).Proper) :
    (P.dilate k).carrier.card ≤
      (rank * 2 ^ rank) * k ^ (rank - 1) * P.volume := by
  by_cases hk2 : 2 ≤ k
  · have hmain :=
      card_dilate_le_rank_mul_scale_mul_pow_of_not_proper P hk2 hnp
    have hbase : k + 1 ≤ 2 * k := by omega
    have hpow : (k + 1) ^ (rank - 1) ≤
        (2 * k) ^ (rank - 1) := Nat.pow_le_pow_left hbase _
    calc
      (P.dilate k).carrier.card ≤
          rank * 2 * (k + 1) ^ (rank - 1) * P.volume := hmain
      _ ≤ rank * 2 * (2 * k) ^ (rank - 1) * P.volume := by gcongr
      _ = (rank * 2 ^ rank) * k ^ (rank - 1) * P.volume := by
        cases rank with
        | zero => simp
        | succ r => simp only [Nat.succ_sub_one, mul_pow]
                    ring
  · have hk1 : k = 1 := by omega
    subst k
    calc
      (P.dilate 1).carrier.card ≤ (P.dilate 1).volume :=
        (P.dilate 1).card_carrier_le_volume
      _ = P.volume := by
        rw [P.volume_dilate 1, Erdos186.GAP.volume]
        apply Finset.prod_congr rfl
        intro i _hi
        have hw := P.width_pos i
        omega
      _ ≤ (rank * 2 ^ rank) * 1 ^ (rank - 1) * P.volume := by
        have hrank : 1 ≤ rank := by
          by_contra hr
          have hr0 : rank = 0 := by omega
          subst rank
          exact hnp (by
            intro x y _hxy
            exact Subsingleton.elim x y)
        have hp : 0 < 2 ^ rank := by positivity
        have hc : 1 ≤ rank * 2 ^ rank := Nat.mul_pos hrank hp
        simpa using Nat.mul_le_mul_right P.volume hc

/-- Source-form CFP Corollary 2.21.  Properness identifies the displayed
volume of the original GAP with its actual cardinality. -/
theorem card_dilate_le_pow_sub_one_mul_card_of_proper_of_two_not_proper
    (P : Erdos186.GAP ambient rank) {k : ℕ} (hk : 1 ≤ k)
    (hproper : P.Proper) (hnp : ¬ (P.dilate 2).Proper) :
    (P.dilate k).carrier.card ≤
      (rank * 2 ^ rank) * k ^ (rank - 1) * P.carrier.card := by
  rw [P.card_carrier_eq_volume hproper]
  exact card_dilate_le_pow_sub_one_mul_volume_of_two_not_proper P hk hnp

/-- Embed the coefficient box of a smaller dilation in that of a larger
dilation. -/
def castDilateCoord (P : Erdos186.GAP ambient rank) {a b : ℕ}
    (hab : a ≤ b) (n : (P.dilate a).Coord) : (P.dilate b).Coord :=
  fun i ↦ ⟨n i, (n i).isLt.trans_le (by
    simp only [Erdos186.GAP.dilate_widths]
    gcongr)⟩

/-- Properness of GAP dilations is downward monotone in the integral scale. -/
theorem dilate_proper_mono (P : Erdos186.GAP ambient rank) {a b : ℕ}
    (hab : a ≤ b) (hproper : (P.dilate b).Proper) :
    (P.dilate a).Proper := by
  intro n m hnm
  have hsums (j : Fin ambient) :
      (∑ i, (n i : ℤ) * P.steps i j) =
        ∑ i, (m i : ℤ) * P.steps i j := by
    have hj := congrFun hnm j
    change (a : ℤ) * P.offset j + (∑ i, (n i : ℤ) * P.steps i j) =
      (a : ℤ) * P.offset j + ∑ i, (m i : ℤ) * P.steps i j at hj
    exact add_left_cancel hj
  have hembed :
      (P.dilate b).coordPoint (castDilateCoord P hab n) =
        (P.dilate b).coordPoint (castDilateCoord P hab m) := by
    funext j
    change (b : ℤ) * P.offset j + (∑ i, (n i : ℤ) * P.steps i j) =
      (b : ℤ) * P.offset j + ∑ i, (m i : ℤ) * P.steps i j
    exact congrArg ((b : ℤ) * P.offset j + ·) (hsums j)
  have hcoords := hproper hembed
  funext i
  exact Fin.ext (congrArg (fun c : (P.dilate b).Coord ↦ (c i : ℕ)) hcoords)

/-! ## Integral contraction in the ambient lattice -/

/-- Divide every ambient coordinate of a GAP's offset and steps by `k`.
The useful laws below assume the displayed data are actually divisible by
`k`; keeping the operation total makes it convenient to construct. -/
def ambientDiv (P : Erdos186.GAP ambient rank) (k : ℕ) :
    Erdos186.GAP ambient rank where
  offset := fun j ↦ P.offset j / (k : ℤ)
  steps := fun i j ↦ P.steps i j / (k : ℤ)
  widths := P.widths
  width_pos := P.width_pos

@[simp] theorem ambientDiv_widths (P : Erdos186.GAP ambient rank) (k : ℕ) :
    (P.ambientDiv k).widths = P.widths := rfl

@[simp] theorem ambientDiv_volume (P : Erdos186.GAP ambient rank) (k : ℕ) :
    (P.ambientDiv k).volume = P.volume := rfl

/-- Multiplying an integrally contracted point by the denominator recovers
the original displayed point with the same coefficient tuple. -/
theorem ambientDiv_coordPoint_mul (P : Erdos186.GAP ambient rank) (k : ℕ)
    (hoffset : ∀ j, (k : ℤ) ∣ P.offset j)
    (hsteps : ∀ i j, (k : ℤ) ∣ P.steps i j)
    (n : P.Coord) :
    (fun j ↦ (k : ℤ) * (P.ambientDiv k).coordPoint n j) =
      P.coordPoint n := by
  funext j
  simp only [ambientDiv, coordPoint]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · calc
      (k : ℤ) * (P.offset j / (k : ℤ)) =
          (P.offset j / (k : ℤ)) * (k : ℤ) := by ring
      _ = P.offset j := Int.ediv_mul_cancel (hoffset j)
  · apply Finset.sum_congr rfl
    intro i _hi
    calc
      (k : ℤ) * ((n i : ℤ) * (P.steps i j / (k : ℤ))) =
          (n i : ℤ) * ((P.steps i j / (k : ℤ)) * (k : ℤ)) := by ring
      _ = (n i : ℤ) * P.steps i j := by
        rw [Int.ediv_mul_cancel (hsteps i j)]

/-- Properness is preserved by an exact integral ambient contraction. -/
theorem ambientDiv_proper (P : Erdos186.GAP ambient rank) (k : ℕ)
    (hoffset : ∀ j, (k : ℤ) ∣ P.offset j)
    (hsteps : ∀ i j, (k : ℤ) ∣ P.steps i j)
    (hproper : P.Proper) :
    (P.ambientDiv k).Proper := by
  intro n m hnm
  apply hproper
  rw [← P.ambientDiv_coordPoint_mul k hoffset hsteps n,
    ← P.ambientDiv_coordPoint_mul k hoffset hsteps m, hnm]

/-- If `k*x` lies in the original GAP, then `x` lies in its exact ambient
contraction. -/
theorem mem_ambientDiv_of_mul_mem (P : Erdos186.GAP ambient rank) (k : ℕ)
    (hk : 0 < k) (hoffset : ∀ j, (k : ℤ) ∣ P.offset j)
    (hsteps : ∀ i j, (k : ℤ) ∣ P.steps i j)
    {x : LatticePoint ambient}
    (hx : (fun j ↦ (k : ℤ) * x j) ∈ P.carrier) :
    x ∈ (P.ambientDiv k).carrier := by
  obtain ⟨n, hn⟩ := mem_carrier_iff.mp hx
  apply mem_carrier_iff.mpr
  refine ⟨n, ?_⟩
  funext j
  have hrecover := congrFun
    (P.ambientDiv_coordPoint_mul k hoffset hsteps n) j
  have htarget := congrFun hn j
  apply mul_left_cancel₀ (show (k : ℤ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hk))
  exact hrecover.trans htarget

/-! ## Pulling a coordinate GAP through displayed steps -/

/-- Evaluate an integral coordinate vector against a fixed family of
ambient lattice vectors. -/
def evaluateSteps {source target : ℕ}
    (v : Fin source → LatticePoint target) (x : LatticePoint source) :
    LatticePoint target :=
  fun j ↦ ∑ i, x i * v i j

/-- Map a GAP in coefficient space through a fixed family of ambient
steps.  This is the additive extension of a proper GAP's identification
map used in CFP Lemmas 2.20 and 2.22. -/
def imageUnderSteps {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r) :
    Erdos186.GAP target r where
  offset := evaluateSteps v P.offset
  steps := fun q ↦ evaluateSteps v (P.steps q)
  widths := P.widths
  width_pos := P.width_pos

@[simp] theorem imageUnderSteps_widths {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r) :
    (P.imageUnderSteps v).widths = P.widths := rfl

@[simp] theorem imageUnderSteps_volume {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r) :
    (P.imageUnderSteps v).volume = P.volume := rfl

/-- Evaluation commutes with the GAP coordinate map. -/
theorem imageUnderSteps_coordPoint {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r)
    (n : P.Coord) :
    (P.imageUnderSteps v).coordPoint n =
      evaluateSteps v (P.coordPoint n) := by
  funext j
  simp only [imageUnderSteps, coordPoint, evaluateSteps]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- The carrier of the mapped GAP is the image of the original carrier. -/
theorem imageUnderSteps_carrier {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r) :
    (P.imageUnderSteps v).carrier = P.carrier.image (evaluateSteps v) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_carrier_iff.mp hx
    apply Finset.mem_image.mpr
    refine ⟨P.coordPoint n, P.coordPoint_mem_carrier n, ?_⟩
    rw [← hn, P.imageUnderSteps_coordPoint v n]
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨n, hn⟩ := mem_carrier_iff.mp hy
    apply mem_carrier_iff.mpr
    refine ⟨n, ?_⟩
    rw [P.imageUnderSteps_coordPoint v n, hn, hyx]

/-- Additive step evaluation commutes with integral GAP dilation. -/
theorem imageUnderSteps_dilate {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r)
    (k : ℕ) :
    (P.imageUnderSteps v).dilate k = (P.dilate k).imageUnderSteps v := by
  cases P
  rw [Erdos186.GAP.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  funext j
  simp only [dilate_offset, imageUnderSteps, evaluateSteps]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A coordinate-space proper GAP remains proper when the step-evaluation
map is injective on its carrier. -/
theorem imageUnderSteps_proper_of_injOn {source target r : ℕ}
    (v : Fin source → LatticePoint target) (P : Erdos186.GAP source r)
    (hP : P.Proper)
    (hinj : Set.InjOn (evaluateSteps v) P.carrier) :
    (P.imageUnderSteps v).Proper := by
  intro n m hnm
  apply hP
  apply hinj (P.coordPoint_mem_carrier n) (P.coordPoint_mem_carrier m)
  rw [P.imageUnderSteps_coordPoint v n,
    P.imageUnderSteps_coordPoint v m] at hnm
  exact hnm

/-- Divisibility of the evaluated generators extends to their entire
integral additive span.  This is the algebraic step which makes the
`2^(-y-1)` pullback in CFP Lemma 2.22 an honest integer GAP. -/
theorem dvd_evaluateSteps_of_mem_closure {source target : ℕ}
    (v : Fin source → LatticePoint target) (k : ℕ)
    (B : Finset (LatticePoint source))
    (hB : ∀ x ∈ B, ∀ j, (k : ℤ) ∣ evaluateSteps v x j)
    {x : LatticePoint source}
    (hx : x ∈ AddSubgroup.closure (B : Set (LatticePoint source))) :
    ∀ j, (k : ℤ) ∣ evaluateSteps v x j := by
  let H : AddSubgroup (LatticePoint source) :=
    { carrier := {x | ∀ j, (k : ℤ) ∣ evaluateSteps v x j}
      zero_mem' := by
        intro j
        simp [evaluateSteps]
      add_mem' := by
        intro a b ha hb j
        have hea : evaluateSteps v (a + b) j =
            evaluateSteps v a j + evaluateSteps v b j := by
          simp only [evaluateSteps, Pi.add_apply, add_mul,
            Finset.sum_add_distrib]
        rw [hea]
        exact dvd_add (ha j) (hb j)
      neg_mem' := by
        intro a ha j
        have heneg : evaluateSteps v (-a) j = -evaluateSteps v a j := by
          simp only [evaluateSteps, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
        rw [heneg]
        exact dvd_neg.mpr (ha j) }
  have hBH : (B : Set (LatticePoint source)) ⊆ H := by
    intro z hz
    exact hB z hz
  exact ((AddSubgroup.closure_le H).mpr hBH) hx

/-- A sequence in `ℤ` whose consecutive triples have zero second
difference is the arithmetic progression determined by its first two
values.  The bounded form is convenient for the coefficient recurrence in
the Bilu--Freiman prefix reduction. -/
theorem eq_mul_of_midpoint_recurrence (z : ℕ → ℤ) {M : ℕ}
    (hzero : z 0 = 0)
    (hrec : ∀ t, t + 2 ≤ M → 2 * z (t + 1) = z t + z (t + 2)) :
    ∀ t, t ≤ M → z t = (t : ℤ) * z 1 := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rcases t with _ | t
      · simpa using hzero
      · rcases t with _ | t
        · simp
        · have ht0 : t ≤ M := by omega
          have ht1 : t + 1 ≤ M := by omega
          have ht2 : t + 2 ≤ M := by omega
          have hzt := ih t (by omega) ht0
          have hzt1 := ih (t + 1) (by omega) ht1
          have hr := hrec t ht2
          rw [hzt, hzt1] at hr
          have hz2' : z (t + 2) =
              2 * ((t + 1 : ℕ) : ℤ) * z 1 - (t : ℤ) * z 1 := by
            linarith
          have hz2 : z (t + 2) = ((t + 2 : ℕ) : ℤ) * z 1 := by
            rw [hz2']
            push_cast
            ring
          simpa [Nat.add_assoc] using hz2

/-- In a `2`-proper GAP, coordinates displaying the consecutive multiples
`0,x,…,Mx` form an arithmetic progression after recentering at the
coordinate displaying zero.  This is the recurrence argument in CFP Lemma
2.22, stated independently of any tail/prefix choice. -/
theorem relativeCoeff_eq_mul_of_point_multiples {ambient rank M : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (h2proper : P.SProper 2) (hM : 1 ≤ M) (x : LatticePoint ambient)
    (c : Fin (M + 1) → P.Coord)
    (hc : ∀ t, P.coordPoint (c t) = fun j ↦ (t : ℤ) * x j) :
    ∀ t, hP.relativeCoeff (c t) =
      fun i ↦ (t : ℤ) *
        hP.relativeCoeff (c ⟨1, by omega⟩) i := by
  have hproper : P.Proper := h2proper.proper (by omega)
  have hc0 : c ⟨0, by omega⟩ = hP.center := by
    apply hproper
    rw [hc, hP.coordPoint_center]
    funext j
    simp
  intro u
  funext i
  let z : ℕ → ℤ := fun t ↦
    if ht : t ≤ M then
      (c ⟨t, by omega⟩ i : ℤ) - (hP.center i : ℤ)
    else 0
  have hz0 : z 0 = 0 := by
    simp only [z, dif_pos (by omega : 0 ≤ M)]
    have hc0i := congrArg (fun q : P.Coord ↦ (q i : ℤ)) hc0
    simpa using sub_eq_zero.mpr hc0i
  have hzrec : ∀ t, t + 2 ≤ M →
      2 * z (t + 1) = z t + z (t + 2) := by
    intro t ht
    have ht0 : t ≤ M := by omega
    have ht1 : t + 1 ≤ M := by omega
    let a : Fin 2 → P.Coord := fun _ ↦ c ⟨t + 1, by omega⟩
    let b : Fin 2 → P.Coord :=
      fun q ↦ if (q : ℕ) = 0 then c ⟨t, by omega⟩
        else c ⟨t + 2, by omega⟩
    have hab : P.tuplePointSum a = P.tuplePointSum b := by
      simp only [GAP.tuplePointSum, Fin.sum_univ_two, a, b]
      change P.coordPoint (c ⟨t + 1, by omega⟩) +
          P.coordPoint (c ⟨t + 1, by omega⟩) =
        P.coordPoint (c ⟨t, by omega⟩) +
          P.coordPoint (c ⟨t + 2, by omega⟩)
      funext j
      rw [hc, hc, hc]
      push_cast
      simp only [Pi.add_apply]
      ring
    have hcoeff := h2proper (by omega : 2 ≤ 2) a b hab
    have hi := congrFun hcoeff i
    simp only [GAP.totalCoeffs, Fin.sum_univ_two, a, b] at hi
    change (c ⟨t + 1, by omega⟩ i : ℕ) +
        (c ⟨t + 1, by omega⟩ i : ℕ) =
      (c ⟨t, by omega⟩ i : ℕ) +
        (c ⟨t + 2, by omega⟩ i : ℕ) at hi
    simp only [z, dif_pos ht0, dif_pos ht1, dif_pos ht]
    push_cast at hi
    linarith
  have huM : (u : ℕ) ≤ M := by omega
  have hzu := eq_mul_of_midpoint_recurrence z hz0 hzrec u huM
  have h1M : 1 ≤ M := hM
  simpa only [CFP.CenteredCertificate.relativeCoeff, z, dif_pos huM,
    dif_pos h1M] using hzu

/-- Restrict a coefficient vector to the displayed directions after the
first `d`. -/
def remainingCoord {ambient rank : ℕ} (P : Erdos186.GAP ambient rank)
    (d : ℕ) (n : P.Coord) : (P.remainingDimensions d).Coord :=
  fun i ↦ ⟨n (remainingIndex rank d i), (n _).isLt⟩

@[simp]
theorem remainingCoord_apply {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (d : ℕ) (n : P.Coord)
    (i : Fin (rank - min rank d)) :
    ((P.remainingCoord d n i :
      Fin ((P.remainingDimensions d).widths i)) : ℕ) =
        (n (remainingIndex rank d i) : ℕ) := rfl

/-- If more consecutive multiples of a point lie in a `2`-proper GAP than
there are coefficient vectors in its tail, then that point has zero in
every tail direction.  This is the finite pigeonhole step which deletes
the bounded Bilu--Freiman tail in CFP Lemma 2.22. -/
theorem remaining_relativeCoeff_eq_zero_of_point_multiples
    {ambient rank M : ℕ} (P : Erdos186.GAP ambient rank)
    (hP : CFP.CenteredCertificate P) (h2proper : P.SProper 2)
    (hM : 1 ≤ M) (d : ℕ)
    (htail : (P.remainingDimensions d).volume < M)
    (x : LatticePoint ambient) (c : Fin (M + 1) → P.Coord)
    (hc : ∀ t, P.coordPoint (c t) = fun j ↦ (t : ℤ) * x j) :
    ∀ i : Fin (rank - min rank d),
      hP.relativeCoeff (c ⟨1, by omega⟩)
        (remainingIndex rank d i) = 0 := by
  have hlinear := P.relativeCoeff_eq_mul_of_point_multiples
    hP h2proper hM x c hc
  intro i
  by_contra hnonzero
  let f : Fin (M + 1) → (P.remainingDimensions d).Coord :=
    fun t ↦ P.remainingCoord d (c t)
  have hfinj : Function.Injective f := by
    intro u v huv
    have huvi := congrArg
      (fun q : (P.remainingDimensions d).Coord ↦
        (q i : ℕ)) huv
    have hrel :
        hP.relativeCoeff (c u) (remainingIndex rank d i) =
          hP.relativeCoeff (c v) (remainingIndex rank d i) := by
      simp only [CFP.CenteredCertificate.relativeCoeff]
      rw [show (c u (remainingIndex rank d i) : ℕ) =
          (c v (remainingIndex rank d i) : ℕ) by
        simpa only [f, remainingCoord_apply] using huvi]
    have hu := congrFun (hlinear u) (remainingIndex rank d i)
    have hv := congrFun (hlinear v) (remainingIndex rank d i)
    rw [hu, hv] at hrel
    have huvZ : (u : ℤ) = (v : ℤ) :=
      mul_right_cancel₀ hnonzero hrel
    apply Fin.ext
    exact_mod_cast huvZ
  have hcard := Fintype.card_le_of_injective f hfinj
  have hle : M + 1 ≤ (P.remainingDimensions d).volume := by
    simpa only [Fintype.card_fin, Fintype.card_pi, GAP.volume] using hcard
  omega

/-- The prefix GAP centered at the coordinate displaying zero.  Unlike
`firstDimensions`, its offset uses only the prefix contribution, so its
carrier is the `Q` factor in the source decomposition `W ⊕ Q`. -/
def centeredFirstDimensions {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) : Erdos186.GAP ambient (min rank d) where
  offset := fun j ↦ -∑ i : Fin (min rank d),
    (hP.center ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ : ℤ) *
      P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ j
  steps := fun i ↦ P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩
  widths := fun i ↦ P.widths ⟨i, i.isLt.trans_le (min_le_left rank d)⟩
  width_pos := fun i ↦ P.width_pos ⟨i, i.isLt.trans_le (min_le_left rank d)⟩

/-- Restriction of a full coefficient vector to the centered prefix. -/
def centeredFirstCoord {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (n : P.Coord) : (P.centeredFirstDimensions hP d).Coord :=
  fun i ↦ ⟨n ⟨i, i.isLt.trans_le (min_le_left rank d)⟩, (n _).isLt⟩

@[simp]
theorem centeredFirstCoord_apply {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (n : P.Coord) (i : Fin (min rank d)) :
    ((P.centeredFirstCoord hP d n i :
      Fin ((P.centeredFirstDimensions hP d).widths i)) : ℕ) =
        (n ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ : ℕ) := rfl

/-- Evaluation in the centered prefix is evaluation of the prefix relative
coefficients against the original steps. -/
theorem centeredFirstDimensions_coordPoint {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (n : P.Coord) :
    (P.centeredFirstDimensions hP d).coordPoint
        (P.centeredFirstCoord hP d n) =
      fun j ↦ ∑ i : Fin (min rank d),
        hP.relativeCoeff n
            ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ *
          P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ j := by
  funext j
  simp only [centeredFirstDimensions, coordPoint, centeredFirstCoord,
    CFP.CenteredCertificate.relativeCoeff]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- Split a finite sum into the first `d` indices and the complementary
tail, using the exact indexing convention of `remainingDimensions`. -/
theorem sum_eq_first_add_remaining {rank d : ℕ} (f : Fin rank → ℤ) :
    (∑ i : Fin rank, f i) =
      (∑ i : Fin (min rank d),
        f ⟨i, i.isLt.trans_le (min_le_left rank d)⟩) +
      ∑ i : Fin (rank - min rank d), f (remainingIndex rank d i) := by
  have hkl : min rank d + (rank - min rank d) = rank :=
    Nat.add_sub_of_le (min_le_left rank d)
  have hsum := Fin.sum_univ_add
    (fun i : Fin (min rank d + (rank - min rank d)) ↦
      f (Fin.cast hkl i))
  calc
    (∑ i : Fin rank, f i) =
        ∑ i : Fin (min rank d + (rank - min rank d)),
          f (Fin.cast hkl i) := (Fin.sum_congr' f hkl).symm
    _ = (∑ i : Fin (min rank d),
          f (Fin.cast hkl (Fin.castAdd (rank - min rank d) i))) +
        ∑ i : Fin (rank - min rank d),
          f (Fin.cast hkl (Fin.natAdd (min rank d) i)) := hsum
    _ = (∑ i : Fin (min rank d),
          f ⟨i, i.isLt.trans_le (min_le_left rank d)⟩) +
        ∑ i : Fin (rank - min rank d),
          f (remainingIndex rank d i) := by rfl

/-- If all centered tail coordinates vanish, a point of the full GAP is
represented by the centered prefix GAP. -/
theorem coordPoint_eq_centeredFirstDimensions_of_remaining_zero
    {ambient rank : ℕ} (P : Erdos186.GAP ambient rank)
    (hP : CFP.CenteredCertificate P) (d : ℕ) (n : P.Coord)
    (htail : ∀ i : Fin (rank - min rank d),
      hP.relativeCoeff n (remainingIndex rank d i) = 0) :
    P.coordPoint n =
      (P.centeredFirstDimensions hP d).coordPoint
        (P.centeredFirstCoord hP d n) := by
  rw [hP.coordPoint_eq_relativePoint,
    P.centeredFirstDimensions_coordPoint hP d n]
  funext j
  simp only [CFP.CenteredCertificate.relativePoint]
  rw [sum_eq_first_add_remaining
    (fun i ↦ hP.relativeCoeff n i * P.steps i j)]
  have htailsum :
      (∑ i : Fin (rank - min rank d),
        hP.relativeCoeff n (remainingIndex rank d i) *
          P.steps (remainingIndex rank d i) j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    rw [htail i]
    simp
  rw [htailsum, add_zero]

/-- Embed a centered-prefix coordinate into the full centered integer box
by putting zero in every omitted direction. -/
def centeredFirstRelativeCoeff {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (n : (P.centeredFirstDimensions hP d).Coord) :
    Fin rank → ℤ := fun i ↦
  if hi : (i : ℕ) < min rank d then
    (n ⟨i, hi⟩ : ℤ) - (hP.center i : ℤ)
  else 0

theorem centeredFirstRelativeCoeff_inBox {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (n : (P.centeredFirstDimensions hP d).Coord) :
    hP.InBox (P.centeredFirstRelativeCoeff hP d n) := by
  intro i
  by_cases hi : (i : ℕ) < min rank d
  · have hn : (n ⟨i, hi⟩ : ℕ) < P.widths i := by
      simpa only [centeredFirstDimensions] using (n ⟨i, hi⟩).isLt
    simp only [centeredFirstRelativeCoeff, dif_pos hi,
      CFP.CenteredCertificate.lower, CFP.CenteredCertificate.upper]
    constructor <;> omega
  · simp only [centeredFirstRelativeCoeff, dif_neg hi]
    exact hP.lower_le_zero_le_upper i

/-- The centered prefix evaluates by first extending its coefficient vector
with zero tail coefficients and then using the full centered presentation. -/
theorem centeredFirstDimensions_coordPoint_eq_relativePoint
    {ambient rank : ℕ} (P : Erdos186.GAP ambient rank)
    (hP : CFP.CenteredCertificate P) (d : ℕ)
    (n : (P.centeredFirstDimensions hP d).Coord) :
    (P.centeredFirstDimensions hP d).coordPoint n =
      hP.relativePoint (P.centeredFirstRelativeCoeff hP d n) := by
  funext j
  simp only [coordPoint, centeredFirstDimensions,
    CFP.CenteredCertificate.relativePoint]
  rw [sum_eq_first_add_remaining
    (fun i ↦ P.centeredFirstRelativeCoeff hP d n i * P.steps i j)]
  have hprefix :
      (∑ i : Fin (min rank d),
        P.centeredFirstRelativeCoeff hP d n
            ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ *
          P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ j) =
        ∑ i : Fin (min rank d),
          ((n i : ℤ) -
              (hP.center
                ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ : ℤ)) *
            P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ j := by
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [centeredFirstRelativeCoeff,
      dif_pos i.isLt]
  have htail :
      (∑ i : Fin (rank - min rank d),
        P.centeredFirstRelativeCoeff hP d n (remainingIndex rank d i) *
          P.steps (remainingIndex rank d i) j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    have hnot : ¬ ((remainingIndex rank d i : Fin rank) : ℕ) <
        min rank d := by
      rw [remainingIndex_val]
      omega
    simp only [centeredFirstRelativeCoeff, dif_neg hnot, zero_mul]
  rw [hprefix, htail, add_zero]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- Every centered prefix of a proper GAP is proper. -/
theorem centeredFirstDimensions_proper {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (hproper : P.Proper) :
    (P.centeredFirstDimensions hP d).Proper := by
  intro n m hnm
  have hrel : P.centeredFirstRelativeCoeff hP d n =
      P.centeredFirstRelativeCoeff hP d m := by
    apply hP.relativePoint_injective_on hproper
    · exact P.centeredFirstRelativeCoeff_inBox hP d n
    · exact P.centeredFirstRelativeCoeff_inBox hP d m
    · rw [← P.centeredFirstDimensions_coordPoint_eq_relativePoint hP d n,
          ← P.centeredFirstDimensions_coordPoint_eq_relativePoint hP d m]
      exact hnm
  funext i
  apply Fin.ext
  have hi := congrFun hrel
    ⟨i, i.isLt.trans_le (min_le_left rank d)⟩
  simp only [centeredFirstRelativeCoeff, dif_pos i.isLt] at hi
  have hi' : (n i : ℤ) -
        (hP.center ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ : ℤ) =
      (m i : ℤ) -
        (hP.center ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ : ℤ) := by
    simpa only [Fin.eta] using hi
  have hz : (n i : ℤ) = (m i : ℤ) := by linarith
  exact_mod_cast hz

/-- The centered prefix contains zero. -/
theorem zero_mem_centeredFirstDimensions {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) : 0 ∈ (P.centeredFirstDimensions hP d).carrier := by
  apply mem_carrier_iff.mpr
  refine ⟨P.centeredFirstCoord hP d hP.center, ?_⟩
  rw [P.centeredFirstDimensions_coordPoint hP d hP.center]
  funext j
  simp [CFP.CenteredCertificate.relativeCoeff]

/-- The canonical centered certificate on the centered prefix. -/
def centeredFirstCertificate {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) : CFP.CenteredCertificate (P.centeredFirstDimensions hP d) where
  center := P.centeredFirstCoord hP d hP.center
  coordPoint_center := by
    rw [P.centeredFirstDimensions_coordPoint hP d hP.center]
    funext j
    simp [CFP.CenteredCertificate.relativeCoeff]

@[simp]
theorem centeredFirstCertificate_lower {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (i : Fin (min rank d)) :
    (P.centeredFirstCertificate hP d).lower i =
      hP.lower ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ := rfl

@[simp]
theorem centeredFirstCertificate_upper {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (d : ℕ) (i : Fin (min rank d)) :
    (P.centeredFirstCertificate hP d).upper i =
      hP.upper ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ := rfl

/-- The coefficient box attached to a centered GAP, in the axis-box format
used by CFP Corollary 2.17. -/
def centeredAxisBox {ambient rank : ℕ} (P : Erdos186.GAP ambient rank)
    (hP : CFP.CenteredCertificate P) : CFP.AxisBox rank where
  lower := hP.lower
  widths := P.widths
  width_pos := P.width_pos

@[simp]
theorem centeredAxisBox_volume {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P) :
    (P.centeredAxisBox hP).volume = P.volume := rfl

theorem mem_centeredAxisBox_iff {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (z : Fin rank → ℤ) :
    z ∈ (P.centeredAxisBox hP).carrier ↔ hP.InBox z := by
  rw [CFP.AxisBox.mem_carrier_iff]
  constructor
  · intro hz i
    have hi := hz i
    have hw := P.width_pos i
    simp only [centeredAxisBox, CFP.CenteredCertificate.upper,
      CFP.CenteredCertificate.lower] at hi ⊢
    constructor <;> omega
  · intro hz i
    have hi := hz i
    have hw := P.width_pos i
    simp only [centeredAxisBox, CFP.CenteredCertificate.upper,
      CFP.CenteredCertificate.lower] at hi ⊢
    constructor <;> omega

/-- Centered coefficient coordinates of a point in a proper GAP. -/
noncomputable def centeredCoordinateMap {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) : {x // x ∈ P.carrier} → LatticePoint rank :=
  fun x ↦ hP.relativeCoeff (P.coordinateMap hproper x)

theorem centeredCoordinateMap_mem {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) (x : {x // x ∈ P.carrier}) :
    P.centeredCoordinateMap hP hproper x ∈
      (P.centeredAxisBox hP).carrier := by
  rw [P.mem_centeredAxisBox_iff hP]
  exact hP.relativeCoeff_mem_box _

theorem centeredCoordinateMap_injective {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) :
    Function.Injective (P.centeredCoordinateMap hP hproper) := by
  intro x y hxy
  apply Subtype.ext
  rw [← P.coordPoint_coordinateMap hproper x,
    ← P.coordPoint_coordinateMap hproper y,
    hP.coordPoint_eq_relativePoint, hP.coordPoint_eq_relativePoint]
  exact congrArg hP.relativePoint hxy

/-- Coordinate image of a finite subset of a proper GAP carrier. -/
noncomputable def centeredCoordinateImage {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) (S : Finset {x // x ∈ P.carrier}) :
    Finset (LatticePoint rank) :=
  S.image (P.centeredCoordinateMap hP hproper)

@[simp]
theorem card_centeredCoordinateImage {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) (S : Finset {x // x ∈ P.carrier}) :
    (P.centeredCoordinateImage hP hproper S).card = S.card := by
  exact Finset.card_image_of_injective S
    (P.centeredCoordinateMap_injective hP hproper)

theorem centeredCoordinateImage_subset_axisBox {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) (S : Finset {x // x ∈ P.carrier}) :
    P.centeredCoordinateImage hP hproper S ⊆
      (P.centeredAxisBox hP).carrier := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
  exact P.centeredCoordinateMap_mem hP hproper x

/-! ## Deleting short centered directions -/

/-- Directions whose displayed width is at least the block scale. -/
abbrev WideDirection {ambient rank : ℕ} (P : Erdos186.GAP ambient rank)
    (M : ℕ) := {i : Fin rank // M ≤ P.widths i}

/-- Number of directions surviving deletion at scale `M`. -/
noncomputable def wideRank {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ) : ℕ :=
  Fintype.card (WideDirection P M)

/-- Canonical enumeration of the surviving directions. -/
noncomputable def wideIndex {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ) :
    Fin (P.wideRank M) ≃ WideDirection P M :=
  (Fintype.equivFin (WideDirection P M)).symm

/-- Projection to the directions whose width is at least `M`. -/
noncomputable def wideProjection {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ)
    (z : LatticePoint rank) : LatticePoint (P.wideRank M) :=
  fun j ↦ z (P.wideIndex M j)

/-- The original GAP steps restricted to directions surviving deletion. -/
noncomputable def wideSteps {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ) :
    Fin (P.wideRank M) → LatticePoint ambient :=
  fun j ↦ P.steps (P.wideIndex M j)

/-- Evaluation after projecting away short zero coordinates agrees with
evaluation against all original steps. -/
theorem evaluateSteps_wideProjection_of_support {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ) (z : LatticePoint rank)
    (hsupport : ∀ i, P.widths i < M → z i = 0) :
    evaluateSteps (P.wideSteps M) (P.wideProjection M z) =
      fun j ↦ ∑ i, z i * P.steps i j := by
  funext j
  classical
  change (∑ q : Fin (P.wideRank M),
      z (P.wideIndex M q) * P.steps (P.wideIndex M q) j) =
    ∑ i : Fin rank, z i * P.steps i j
  calc
    (∑ q : Fin (P.wideRank M),
        z (P.wideIndex M q) * P.steps (P.wideIndex M q) j) =
        ∑ i : WideDirection P M, z i * P.steps i j := by
      apply Fintype.sum_equiv (P.wideIndex M)
      intro q
      rfl
    _ = ∑ i : Fin rank, z i * P.steps i j := by
      let p : Fin rank → Prop := fun i ↦ M ≤ P.widths i
      have hcomplement :
          (∑ i : {i : Fin rank // ¬ p i}, z i * P.steps i j) = 0 := by
        apply Finset.sum_eq_zero
        intro i _hi
        have hi' : P.widths i < M := Nat.lt_of_not_ge i.property
        rw [hsupport i hi', zero_mul]
      have hsplit := Fintype.sum_subtype_add_sum_subtype p
        (fun i : Fin rank ↦ z i * P.steps i j)
      rw [hcomplement, add_zero] at hsplit
      simpa only [p, WideDirection] using hsplit

/-- Extend wide coordinates by zero on every deleted direction. -/
noncomputable def wideExtension {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ)
    (z : LatticePoint (P.wideRank M)) : LatticePoint rank :=
  fun i ↦ if hi : M ≤ P.widths i then
    z ((P.wideIndex M).symm ⟨i, hi⟩) else 0

@[simp]
theorem wideProjection_wideExtension {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ)
    (z : LatticePoint (P.wideRank M)) :
    P.wideProjection M (P.wideExtension M z) = z := by
  funext j
  simp only [wideProjection, wideExtension,
    (P.wideIndex M j).property, dite_true]
  have hsub :
      (⟨(P.wideIndex M j).val, (P.wideIndex M j).property⟩ :
        WideDirection P M) = P.wideIndex M j := Subtype.ext rfl
  rw [hsub, Equiv.symm_apply_apply]

theorem wideExtension_support {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ)
    (z : LatticePoint (P.wideRank M)) (i : Fin rank)
    (hi : P.widths i < M) : P.wideExtension M z i = 0 := by
  simp [wideExtension, Nat.not_le.mpr hi]

/-- The axis box left after deleting all directions shorter than `M`. -/
noncomputable def wideAxisBox {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (M : ℕ) (hM : 0 < M) : CFP.AxisBox (P.wideRank M) where
  lower := fun j ↦ hP.lower (P.wideIndex M j)
  widths := fun j ↦ P.widths (P.wideIndex M j)
  width_pos := fun j ↦ hM.trans_le (P.wideIndex M j).property

/-- Every surviving width is at least the deletion scale. -/
theorem wideAxisBox_minWidth {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (M : ℕ) (hM : 0 < M) (hrank : 0 < P.wideRank M) :
    M ≤ (P.wideAxisBox hP M hM).minWidth := by
  rw [CFP.AxisBox.minWidth, dif_pos hrank]
  apply Finset.le_inf'
  intro j _hj
  exact (P.wideIndex M j).property

/-- Deleting coordinates can only decrease the displayed box volume. -/
theorem wideAxisBox_volume_le_volume {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (M : ℕ) (hM : 0 < M) :
    (P.wideAxisBox hP M hM).volume ≤ P.volume := by
  classical
  let S := (Finset.univ : Finset (Fin rank)).filter
    (fun i ↦ M ≤ P.widths i)
  calc
    (P.wideAxisBox hP M hM).volume =
        ∏ j : Fin (P.wideRank M), P.widths (P.wideIndex M j) := rfl
    _ = ∏ i : WideDirection P M, P.widths i := by
      apply Fintype.prod_equiv (P.wideIndex M)
      intro j
      rfl
    _ = ∏ i ∈ S, P.widths i := by
      exact (Finset.prod_subtype
        (p := fun i : Fin rank ↦ M ≤ P.widths i) S
        (by intro i; simp [S]) P.widths).symm
    _ ≤ ∏ i : Fin rank, P.widths i := by
      apply Finset.prod_le_prod_of_subset_of_one_le'
        (show S ⊆ (Finset.univ : Finset (Fin rank)) by simp)
      intro i _hi _hiS
      exact P.width_pos i
    _ = P.volume := rfl

/-- Projecting a set supported on the surviving directions loses no
cardinality. -/
theorem card_image_wideProjection_of_support {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (M : ℕ)
    (S : Finset (LatticePoint rank))
    (hsupport : ∀ z ∈ S, ∀ i, P.widths i < M → z i = 0) :
    (S.image (P.wideProjection M)).card = S.card := by
  rw [Finset.card_image_iff]
  intro x hx y hy hxy
  funext i
  by_cases hi : M ≤ P.widths i
  · let j : Fin (P.wideRank M) :=
      (Fintype.equivFin (WideDirection P M)) ⟨i, hi⟩
    have hj := congrFun hxy j
    have hsub : P.wideIndex M j = (⟨i, hi⟩ : WideDirection P M) := by
      dsimp only [wideIndex, j]
      exact Equiv.symm_apply_apply _ _
    simpa only [wideProjection, hsub] using hj
  · have hi' : P.widths i < M := Nat.lt_of_not_ge hi
    rw [hsupport x hx i hi', hsupport y hy i hi']

/-- Projection of an actually centered coefficient set lies in the
wide-coordinate axis box. -/
theorem image_wideProjection_subset_wideAxisBox {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (M : ℕ) (hM : 0 < M) (S : Finset (LatticePoint rank))
    (hS : S ⊆ (P.centeredAxisBox hP).carrier) :
    S.image (P.wideProjection M) ⊆
      (P.wideAxisBox hP M hM).carrier := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  rw [CFP.AxisBox.mem_carrier_iff]
  intro j
  have hj := (P.mem_centeredAxisBox_iff hP x).mp (hS hx)
    (P.wideIndex M j)
  have hlen := hP.upper_sub_lower_add_one (P.wideIndex M j)
  simp only [wideAxisBox, wideProjection] at hj ⊢
  constructor
  · exact hj.1
  · omega

/-! ## Contracting centered lattice-basis progressions -/

/-- Contract the radii of a centered lattice-basis progression by an
integer denominator.  This is the literal finite GAP behind the paper's
notation `k⁻¹P`; it contracts coefficient radii, not ambient integer
coordinates. -/
noncomputable def basisContraction {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ) (k : ℕ) :
    Erdos186.GAP d d :=
  CFP.AdaptedHNF.centeredBasisGAP b (fun i ↦ radius i / k)

/-- The contracted basis progression is centered with the divided radii. -/
theorem basisContraction_centered {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ) (k : ℕ) :
    (basisContraction b radius k).Centered (fun i ↦ radius i / k) := by
  constructor
  · funext i
    rfl
  · rfl

/-- A contraction displayed in a genuine lattice basis is proper. -/
theorem basisContraction_proper {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ) (k : ℕ) :
    (basisContraction b radius k).Proper := by
  exact CFP.AdaptedHNF.centeredBasisGAP_proper b _

/-- Multiplying a point of the coefficient contraction by its denominator
returns to the original centered basis progression. -/
theorem smul_mem_centeredBasisGAP_of_mem_basisContraction
    {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ)
    {k : ℕ} (hk : 0 < k) {x : LatticePoint d}
    (hx : x ∈ (basisContraction b radius k).carrier) :
    (fun j ↦ (k : ℤ) * x j) ∈
      (CFP.AdaptedHNF.centeredBasisGAP b radius).carrier := by
  rw [basisContraction,
    CFP.centeredBasisGAP_carrier_eq_basisProgression] at hx
  rw [CFP.centeredBasisGAP_carrier_eq_basisProgression]
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨fun i ↦ (k : ℤ) * a i, ?_, ?_⟩
  · rw [CFP.mem_centeredCoefficientBox_iff]
    intro i
    have hai := (CFP.mem_centeredCoefficientBox_iff.mp ha) i
    calc
      |(k : ℤ) * a i| = (k : ℤ) * |a i| := by
        rw [abs_mul]
        norm_num
      _ ≤ (k : ℤ) * (radius i / k : ℕ) := by
        exact Int.mul_le_mul_of_nonneg_left hai (by positivity)
      _ ≤ (radius i : ℤ) := by
        exact_mod_cast (Nat.mul_div_le (radius i) k)
  · have hmodule :
        (∑ i, ((k : ℤ) * a i) • b i) =
          (k : ℤ) • ∑ i, a i • b i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [mul_smul]
    rw [hmodule]
    rfl

/-- The denominator-fold GAP dilation of a coefficient contraction is
contained in the original centered basis progression. -/
theorem dilate_basisContraction_carrier_subset_centeredBasisGAP
    {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ) (k : ℕ) :
    ((basisContraction b radius k).dilate k).carrier ⊆
      (CFP.AdaptedHNF.centeredBasisGAP b radius).carrier := by
  have heq : (basisContraction b radius k).dilate k =
      CFP.AdaptedHNF.centeredBasisGAP b
        (fun i ↦ k * (radius i / k)) := by
    apply Erdos186.GAP.ext
    · funext j
      simp only [basisContraction, Erdos186.GAP.dilate_offset,
        CFP.AdaptedHNF.centeredBasisGAP]
      rw [mul_neg, Finset.mul_sum]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      push_cast
      ring
    · rfl
    · funext i
      simp only [basisContraction, Erdos186.GAP.dilate_widths,
        CFP.AdaptedHNF.centeredBasisGAP_widths]
      rw [Nat.add_sub_cancel]
      ring
  rw [heq, CFP.centeredBasisGAP_carrier_eq_basisProgression,
    CFP.centeredBasisGAP_carrier_eq_basisProgression]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨a, ?_, rfl⟩
  rw [CFP.mem_centeredCoefficientBox_iff] at ha ⊢
  intro i
  exact (ha i).trans (by exact_mod_cast Nat.mul_div_le (radius i) k)

/-- A dilated contraction embeds in any coarser contraction once its
centered radii satisfy the evident coordinatewise inequality. -/
theorem dilate_basisContraction_carrier_subset_basisContraction_of_le
    {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ)
    (M C s : ℕ)
    (hscale : ∀ i, s * (radius i / M) ≤ radius i / C) :
    ((basisContraction b radius M).dilate s).carrier ⊆
      (basisContraction b radius C).carrier := by
  have heq : (basisContraction b radius M).dilate s =
      CFP.AdaptedHNF.centeredBasisGAP b
        (fun i ↦ s * (radius i / M)) := by
    apply Erdos186.GAP.ext
    · funext j
      simp only [basisContraction, Erdos186.GAP.dilate_offset,
        CFP.AdaptedHNF.centeredBasisGAP]
      rw [mul_neg, Finset.mul_sum]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      push_cast
      ring
    · rfl
    · funext i
      simp only [basisContraction, Erdos186.GAP.dilate_widths,
        CFP.AdaptedHNF.centeredBasisGAP_widths]
      rw [Nat.add_sub_cancel]
      ring
  rw [heq, basisContraction,
    CFP.centeredBasisGAP_carrier_eq_basisProgression,
    CFP.centeredBasisGAP_carrier_eq_basisProgression]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨a, ?_, rfl⟩
  rw [CFP.mem_centeredCoefficientBox_iff] at ha ⊢
  intro i
  exact (ha i).trans (by exact_mod_cast hscale i)

/-- Every dilation of a lattice-basis contraction remains proper in its
coordinate lattice. -/
theorem dilate_basisContraction_proper
    {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ) (M s : ℕ) :
    ((basisContraction b radius M).dilate s).Proper := by
  have heq : (basisContraction b radius M).dilate s =
      CFP.AdaptedHNF.centeredBasisGAP b
        (fun i ↦ s * (radius i / M)) := by
    apply Erdos186.GAP.ext
    · funext j
      simp only [basisContraction, Erdos186.GAP.dilate_offset,
        CFP.AdaptedHNF.centeredBasisGAP]
      rw [mul_neg, Finset.mul_sum]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      push_cast
      ring
    · rfl
    · funext i
      simp only [basisContraction, Erdos186.GAP.dilate_widths,
        CFP.AdaptedHNF.centeredBasisGAP_widths]
      rw [Nat.add_sub_cancel]
      ring
  rw [heq]
  exact CFP.AdaptedHNF.centeredBasisGAP_proper b _

/-- Properness of a pulled-back coarse contraction transfers to every
finer dilated contraction whose radii fit inside it. -/
theorem image_basisContraction_dilate_proper_of_le
    {d target : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ)
    (M C s : ℕ) (v : Fin d → LatticePoint target)
    (hcoarse : ((basisContraction b radius C).imageUnderSteps v).Proper)
    (hscale : ∀ i, s * (radius i / M) ≤ radius i / C) :
    (((basisContraction b radius M).imageUnderSteps v).dilate s).Proper := by
  rw [imageUnderSteps_dilate]
  apply imageUnderSteps_proper_of_injOn v
    ((basisContraction b radius M).dilate s)
    (dilate_basisContraction_proper b radius M s)
  intro x hx y hy hxy
  have hsubset :=
    dilate_basisContraction_carrier_subset_basisContraction_of_le
      b radius M C s hscale
  have hxC := hsubset hx
  have hyC := hsubset hy
  obtain ⟨nx, hnx⟩ := mem_carrier_iff.mp hxC
  obtain ⟨ny, hny⟩ := mem_carrier_iff.mp hyC
  have hcoord :
      ((basisContraction b radius C).imageUnderSteps v).coordPoint nx =
        ((basisContraction b radius C).imageUnderSteps v).coordPoint ny := by
    rw [imageUnderSteps_coordPoint, imageUnderSteps_coordPoint, hnx, hny]
    exact hxy
  have hnxy := hcoarse hcoord
  rw [← hnx, ← hny, hnxy]

/-- If a point lies in the generated lattice and its `k`-multiple lies in
the original centered basis progression, then the point lies in the
coefficient contraction.  Basis uniqueness is the divisibility mechanism
which is suppressed in the paper's `k⁻¹P` notation. -/
theorem mem_basisContraction_of_smul_mem_centeredBasisGAP
    {d : ℕ} {Γ : CFP.LatticeBasis.Sublattice d}
    (b : Basis (Fin d) ℤ Γ) (radius : Fin d → ℕ)
    {k : ℕ} (hk : 0 < k) {x : LatticePoint d} (hxΓ : x ∈ Γ)
    (hkx : (fun j ↦ (k : ℤ) * x j) ∈
      (CFP.AdaptedHNF.centeredBasisGAP b radius).carrier) :
    x ∈ (basisContraction b radius k).carrier := by
  let xΓ : Γ := ⟨x, hxΓ⟩
  let kxΓ : Γ := (k : ℤ) • xΓ
  have hkxval : ((kxΓ : Γ) : LatticePoint d) =
      fun j ↦ (k : ℤ) * x j := by
    rfl
  rw [← hkxval, CFP.centeredBasisGAP_carrier_eq_basisProgression] at hkx
  have hcoeff := (CFP.mem_basisProgression_iff b radius kxΓ).mp hkx
  rw [basisContraction,
    CFP.centeredBasisGAP_carrier_eq_basisProgression]
  apply (CFP.mem_basisProgression_iff b (fun i ↦ radius i / k) xΓ).mpr
  intro i
  have hi := hcoeff i
  have hrepr : CFP.LatticeBasis.basisCoeff b kxΓ i =
      (k : ℤ) * CFP.LatticeBasis.basisCoeff b xΓ i := by
    simp [kxΓ, CFP.LatticeBasis.basisCoeff]
  rw [hrepr, abs_mul] at hi
  norm_num at hi
  have hiNat : k * Int.natAbs (CFP.LatticeBasis.basisCoeff b xΓ i) ≤
      radius i := by
    rw [← Int.natCast_natAbs] at hi
    exact_mod_cast hi
  have hdiv : Int.natAbs (CFP.LatticeBasis.basisCoeff b xΓ i) ≤
      radius i / k := (Nat.le_div_iff_mul_le hk).2 (by
        simpa [Nat.mul_comm] using hiNat)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hdiv

/-- Properness of a centered GAP kills every sufficiently short relation
among its steps.  The coefficient interval need not be symmetric: any
vector in the difference box is realized as the difference of two points
of the original centered box. -/
theorem relativePoint_eq_zero_of_abs_le_width_sub_one
    {ambient rank : ℕ} (P : Erdos186.GAP ambient rank)
    (hP : CFP.CenteredCertificate P) (hproper : P.Proper)
    (z : Fin rank → ℤ)
    (hz : ∀ i, |z i| ≤ (P.widths i - 1 : ℕ))
    (hzero : hP.relativePoint z = 0) : z = 0 := by
  let a : Fin rank → ℤ := fun i ↦
    if 0 ≤ z i then hP.lower i + z i else hP.lower i
  let b : Fin rank → ℤ := fun i ↦
    if 0 ≤ z i then hP.lower i else hP.lower i - z i
  have ha : hP.InBox a := by
    intro i
    have hzi := hz i
    have hw := P.width_pos i
    have hlen := hP.upper_sub_lower_add_one i
    dsimp [a]
    split_ifs with hsign
    · rw [abs_of_nonneg hsign] at hzi
      constructor <;> omega
    · have hsign' : z i < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hsign'] at hzi
      constructor <;> omega
  have hb : hP.InBox b := by
    intro i
    have hzi := hz i
    have hw := P.width_pos i
    have hlen := hP.upper_sub_lower_add_one i
    dsimp [b]
    split_ifs with hsign
    · rw [abs_of_nonneg hsign] at hzi
      constructor <;> omega
    · have hsign' : z i < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hsign'] at hzi
      constructor <;> omega
  have hab : a - b = z := by
    funext i
    dsimp [a, b]
    split_ifs <;> ring
  have heval : hP.relativePoint a = hP.relativePoint b := by
    have hsub : hP.relativePoint (a - b) = 0 := by
      rw [hab]
      exact hzero
    funext j
    have hj := congrFun hsub j
    simp only [CFP.CenteredCertificate.relativePoint, Pi.sub_apply,
      sub_mul, Finset.sum_sub_distrib, Pi.zero_apply] at hj ⊢
    linarith
  have hab0 := hP.relativePoint_injective_on hproper ha hb heval
  rw [hab0, sub_self] at hab
  exact hab.symm

/-- The wide-step map has no short relation whenever the original GAP is
proper.  This is the kernel input consumed by the Corollary 2.17 pullback. -/
theorem wideSteps_kernel_of_proper {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hP : CFP.CenteredCertificate P)
    (hproper : P.Proper) (M : ℕ) (hM : 0 < M)
    (z : LatticePoint (P.wideRank M))
    (hz : ∀ j,
      |z j| ≤ ((P.wideAxisBox hP M hM).widths j - 1 : ℕ))
    (hzero : evaluateSteps (P.wideSteps M) z = 0) : z = 0 := by
  let zfull := P.wideExtension M z
  have hsupport : ∀ i, P.widths i < M → zfull i = 0 := by
    intro i hi
    exact P.wideExtension_support M z i hi
  have hbound : ∀ i, |zfull i| ≤ (P.widths i - 1 : ℕ) := by
    intro i
    by_cases hi : M ≤ P.widths i
    · let j := (P.wideIndex M).symm ⟨i, hi⟩
      have hzj := hz j
      simpa only [zfull, wideExtension, dif_pos hi, wideAxisBox,
        Equiv.apply_symm_apply, j] using hzj
    · have hi' : P.widths i < M := Nat.lt_of_not_ge hi
      rw [hsupport i hi', abs_zero]
      exact_mod_cast Nat.zero_le (P.widths i - 1)
  have heval : hP.relativePoint zfull = 0 := by
    change (fun j ↦ ∑ i, zfull i * P.steps i j) = 0
    rw [← P.evaluateSteps_wideProjection_of_support M zfull hsupport,
      P.wideProjection_wideExtension M z, hzero]
  have hzfull := P.relativePoint_eq_zero_of_abs_le_width_sub_one
    hP hproper zfull hbound heval
  have hzproj := congrArg (P.wideProjection M) hzfull
  dsimp only [zfull] at hzproj
  rw [P.wideProjection_wideExtension] at hzproj
  have hzeroProjection :
      P.wideProjection M (0 : LatticePoint rank) = 0 := by
    funext j
    rfl
  rwa [hzeroProjection] at hzproj

/-! ## Removing width-one directions -/

/-- Directions which contribute genuine freedom to a GAP presentation. -/
abbrev ActiveDirection {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) := {i : Fin rank // 2 ≤ P.widths i}

/-- Number of nontrivial displayed directions. -/
noncomputable def activeRank {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) : ℕ :=
  Fintype.card (ActiveDirection P)

/-- Canonical enumeration of nontrivial displayed directions. -/
noncomputable def activeIndex {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) :
    Fin P.activeRank ≃ ActiveDirection P :=
  (Fintype.equivFin (ActiveDirection P)).symm

/-- Delete all width-one directions, retaining the same offset. -/
noncomputable def activeDimensions {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) : Erdos186.GAP ambient P.activeRank where
  offset := P.offset
  steps := fun j ↦ P.steps (P.activeIndex j)
  widths := fun j ↦ P.widths (P.activeIndex j)
  width_pos := fun j ↦ (P.activeIndex j).property.trans' (by omega)

/-- Embed an active coefficient tuple into the original tuple by putting
zero in every width-one direction. -/
noncomputable def activeCoordToFull {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (n : P.activeDimensions.Coord) :
    P.Coord := fun i ↦
  if hi : 2 ≤ P.widths i then
    ⟨n ((P.activeIndex).symm ⟨i, hi⟩), by
      simpa only [activeDimensions, Equiv.apply_symm_apply] using
        (n ((P.activeIndex).symm ⟨i, hi⟩)).isLt⟩
  else ⟨0, P.width_pos i⟩

@[simp]
theorem activeCoordToFull_activeIndex {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (n : P.activeDimensions.Coord)
    (j : Fin P.activeRank) :
    P.activeCoordToFull n (P.activeIndex j) = n j := by
  apply Fin.ext
  simp only [activeCoordToFull, (P.activeIndex j).property, dite_true]
  have hsub :
      (⟨(P.activeIndex j).val, (P.activeIndex j).property⟩ :
        ActiveDirection P) = P.activeIndex j := Subtype.ext rfl
  rw [hsub, Equiv.symm_apply_apply]

@[simp]
theorem activeCoordToFull_activeDirection {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (n : P.activeDimensions.Coord)
    (i : ActiveDirection P) :
    (P.activeCoordToFull n i : ℕ) = n ((P.activeIndex).symm i) := by
  simp only [activeCoordToFull, i.property, dite_true]

/-- The active coefficient embedding is injective. -/
theorem activeCoordToFull_injective {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) :
    Function.Injective P.activeCoordToFull := by
  intro n m hnm
  funext j
  apply Fin.ext
  have hj := congrArg
    (fun c : P.Coord ↦ (c (P.activeIndex j) : ℕ)) hnm
  simpa only [P.activeCoordToFull_activeIndex] using hj

/-- Evaluation is unchanged by the active coefficient embedding. -/
theorem coordPoint_activeCoordToFull {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (n : P.activeDimensions.Coord) :
    P.coordPoint (P.activeCoordToFull n) =
      P.activeDimensions.coordPoint n := by
  funext j
  classical
  simp only [coordPoint, activeDimensions]
  apply congrArg (P.offset j + ·)
  let p : Fin rank → Prop := fun i ↦ 2 ≤ P.widths i
  have hcomplement :
      (∑ i : {i : Fin rank // ¬ p i},
        (P.activeCoordToFull n i : ℤ) * P.steps i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    simp [activeCoordToFull, p, i.property]
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun i : Fin rank ↦
      (P.activeCoordToFull n i : ℤ) * P.steps i j)
  rw [hcomplement, add_zero] at hsplit
  calc
    (∑ i : Fin rank, (P.activeCoordToFull n i : ℤ) * P.steps i j) =
        ∑ i : ActiveDirection P,
          (P.activeCoordToFull n i : ℤ) * P.steps i j := by
      simpa only [p, ActiveDirection] using hsplit.symm
    _ = ∑ i : ActiveDirection P,
        (n ((P.activeIndex).symm i) : ℤ) * P.steps i j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [P.activeCoordToFull_activeDirection]
    _ = ∑ q : Fin P.activeRank,
        (n q : ℤ) * P.steps (P.activeIndex q) j := by
      symm
      apply Fintype.sum_equiv (P.activeIndex)
      intro q
      rw [Equiv.symm_apply_apply]

/-- Active directions of a proper GAP remain proper. -/
theorem activeDimensions_proper {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (hproper : P.Proper) :
    P.activeDimensions.Proper := by
  intro n m hnm
  apply P.activeCoordToFull_injective
  apply hproper
  rw [P.coordPoint_activeCoordToFull, P.coordPoint_activeCoordToFull]
  exact hnm

/-- The active presentation is nondegenerate by construction. -/
theorem activeDimensions_nondegenerate {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) :
    P.activeDimensions.Nondegenerate := by
  intro j
  exact (P.activeIndex j).property

/-- The active rank never exceeds the original rank. -/
theorem activeRank_le {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) : P.activeRank ≤ rank := by
  simpa only [activeRank, Fintype.card_fin] using
    Fintype.card_subtype_le (fun i : Fin rank ↦ 2 ≤ P.widths i)

/-- Every active displayed point is also a displayed point of the original
GAP. -/
theorem activeDimensions_carrier_subset {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) :
    P.activeDimensions.carrier ⊆ P.carrier := by
  intro x hx
  obtain ⟨n, rfl⟩ := mem_carrier_iff.mp hx
  exact mem_carrier_iff.mpr
    ⟨P.activeCoordToFull n, P.coordPoint_activeCoordToFull n⟩

/-- Width-one coordinates are forced to be zero, so deleting them does not
change the carrier at scale one. -/
theorem carrier_activeDimensions {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) :
    P.activeDimensions.carrier = P.carrier := by
  apply Finset.Subset.antisymm P.activeDimensions_carrier_subset
  intro x hx
  obtain ⟨n, hn⟩ := mem_carrier_iff.mp hx
  let a : P.activeDimensions.Coord := fun j ↦
    ⟨n (P.activeIndex j), by
      simpa only [activeDimensions] using (n (P.activeIndex j)).isLt⟩
  have hembed : P.activeCoordToFull a = n := by
    funext i
    apply Fin.ext
    by_cases hi : 2 ≤ P.widths i
    · change (P.activeCoordToFull a i : ℕ) = n i
      rw [P.activeCoordToFull_activeDirection a ⟨i, hi⟩]
      dsimp only [a]
      have hidx := Equiv.apply_symm_apply P.activeIndex ⟨i, hi⟩
      exact congrArg (fun q : ActiveDirection P ↦ (n q : ℕ)) hidx
    · have hwidth : P.widths i = 1 := by
        have := P.width_pos i
        omega
      have hn0 : (n i : ℕ) = 0 := by
        have := (n i).isLt
        omega
      simp only [activeCoordToFull, hi, dite_false]
      exact hn0.symm
  apply mem_carrier_iff.mpr
  refine ⟨a, ?_⟩
  rw [← P.coordPoint_activeCoordToFull a, hembed, hn]

/-- The same carrier inclusion holds at every integral dilation scale. -/
theorem dilate_activeDimensions_carrier_subset_dilate
    {ambient rank : ℕ} (P : Erdos186.GAP ambient rank) (k : ℕ) :
    (P.activeDimensions.dilate k).carrier ⊆ (P.dilate k).carrier := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_carrier_iff.mp hx
  let m : (P.dilate k).Coord := fun i ↦
    if hi : 2 ≤ P.widths i then
      ⟨n ((P.activeIndex).symm ⟨i, hi⟩), by
        simpa only [activeDimensions, dilate_widths,
          Equiv.apply_symm_apply] using
          (n ((P.activeIndex).symm ⟨i, hi⟩)).isLt⟩
    else ⟨0, by simp⟩
  apply mem_carrier_iff.mpr
  refine ⟨m, ?_⟩
  rw [← hn]
  funext j
  classical
  simp only [coordPoint, dilate_offset, dilate_steps, activeDimensions]
  apply congrArg ((k : ℤ) * P.offset j + ·)
  let p : Fin rank → Prop := fun i ↦ 2 ≤ P.widths i
  have hcomplement :
      (∑ i : {i : Fin rank // ¬ p i},
        (m i : ℤ) * P.steps i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    simp [m, p, i.property]
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun i : Fin rank ↦ (m i : ℤ) * P.steps i j)
  rw [hcomplement, add_zero] at hsplit
  calc
    (∑ i : Fin rank, (m i : ℤ) * P.steps i j) =
        ∑ i : ActiveDirection P,
          (m i : ℤ) * P.steps i j := by
      simpa only [p, ActiveDirection] using hsplit.symm
    _ = ∑ i : ActiveDirection P,
        (n ((P.activeIndex).symm i) : ℤ) * P.steps i j := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hsub :
          (⟨i.val, i.property⟩ : ActiveDirection P) = i := Subtype.ext rfl
      simp only [m, i.property, dite_true, hsub]
    _ = ∑ q : Fin P.activeRank,
        (n q : ℤ) * P.steps (P.activeIndex q) j := by
      symm
      apply Fintype.sum_equiv (P.activeIndex)
      intro q
      rw [Equiv.symm_apply_apply]

/-- Embed a coefficient tuple of an active dilation into the corresponding
full dilation. -/
noncomputable def activeDilateCoordToFull {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (k : ℕ)
    (n : (P.activeDimensions.dilate k).Coord) : (P.dilate k).Coord :=
  fun i ↦ if hi : 2 ≤ P.widths i then
    ⟨n ((P.activeIndex).symm ⟨i, hi⟩), by
      simpa only [activeDimensions, dilate_widths,
        Equiv.apply_symm_apply] using
        (n ((P.activeIndex).symm ⟨i, hi⟩)).isLt⟩
  else ⟨0, by simp⟩

@[simp]
theorem activeDilateCoordToFull_activeIndex {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (k : ℕ)
    (n : (P.activeDimensions.dilate k).Coord)
    (j : Fin P.activeRank) :
    P.activeDilateCoordToFull k n (P.activeIndex j) = n j := by
  apply Fin.ext
  simp only [activeDilateCoordToFull, (P.activeIndex j).property, dite_true]
  have hsub :
      (⟨(P.activeIndex j).val, (P.activeIndex j).property⟩ :
        ActiveDirection P) = P.activeIndex j := Subtype.ext rfl
  rw [hsub, Equiv.symm_apply_apply]

@[simp]
theorem activeDilateCoordToFull_activeDirection {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (k : ℕ)
    (n : (P.activeDimensions.dilate k).Coord)
    (i : ActiveDirection P) :
    (P.activeDilateCoordToFull k n i : ℕ) =
      n ((P.activeIndex).symm i) := by
  simp only [activeDilateCoordToFull, i.property, dite_true]

theorem activeDilateCoordToFull_injective {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (k : ℕ) :
    Function.Injective (P.activeDilateCoordToFull k) := by
  intro n m hnm
  funext j
  apply Fin.ext
  have hj := congrArg
    (fun c : (P.dilate k).Coord ↦ (c (P.activeIndex j) : ℕ)) hnm
  simpa only [P.activeDilateCoordToFull_activeIndex] using hj

/-- The active-dilation coefficient embedding preserves evaluation. -/
theorem coordPoint_activeDilateCoordToFull {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (k : ℕ)
    (n : (P.activeDimensions.dilate k).Coord) :
    (P.dilate k).coordPoint (P.activeDilateCoordToFull k n) =
      (P.activeDimensions.dilate k).coordPoint n := by
  funext j
  classical
  simp only [coordPoint, dilate_offset, dilate_steps, activeDimensions]
  apply congrArg ((k : ℤ) * P.offset j + ·)
  let p : Fin rank → Prop := fun i ↦ 2 ≤ P.widths i
  have hcomplement :
      (∑ i : {i : Fin rank // ¬ p i},
        (P.activeDilateCoordToFull k n i : ℤ) * P.steps i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    simp [activeDilateCoordToFull, p, i.property]
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun i : Fin rank ↦
      (P.activeDilateCoordToFull k n i : ℤ) * P.steps i j)
  rw [hcomplement, add_zero] at hsplit
  calc
    (∑ i : Fin rank,
        (P.activeDilateCoordToFull k n i : ℤ) * P.steps i j) =
        ∑ i : ActiveDirection P,
          (P.activeDilateCoordToFull k n i : ℤ) * P.steps i j := by
      simpa only [p, ActiveDirection] using hsplit.symm
    _ = ∑ i : ActiveDirection P,
        (n ((P.activeIndex).symm i) : ℤ) * P.steps i j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [P.activeDilateCoordToFull_activeDirection]
    _ = ∑ q : Fin P.activeRank,
        (n q : ℤ) * P.steps (P.activeIndex q) j := by
      symm
      apply Fintype.sum_equiv (P.activeIndex)
      intro q
      rw [Equiv.symm_apply_apply]

/-- Properness of a full dilation descends to the active presentation. -/
theorem dilate_activeDimensions_proper {ambient rank : ℕ}
    (P : Erdos186.GAP ambient rank) (k : ℕ)
    (hproper : (P.dilate k).Proper) :
    (P.activeDimensions.dilate k).Proper := by
  intro n m hnm
  apply P.activeDilateCoordToFull_injective k
  apply hproper
  rw [P.coordPoint_activeDilateCoordToFull,
    P.coordPoint_activeDilateCoordToFull]
  exact hnm

end Erdos186.GAP

namespace Erdos186.CFP.HDimension

open GrowthLemmas
open scoped Pointwise

/-! ## Multifold sumsets and GAP envelopes -/

/-- Pulling the `C`‑contraction of the basis progression supplied by
Corollary 2.17 through an additive coordinate map is proper.  The geometric
containment in a translate of `C Q` is used only on differences, so no
divisibility of the translating vector is needed. -/
theorem image_basisContraction_proper_of_corollary217
    {d target : ℕ} {Q : AxisBox d} {B : Finset (BoxPoint d)}
    (cert : Corollary217Certificate Q B)
    (v : Fin d → LatticePoint target)
    (hkernel : ∀ z : LatticePoint d,
      (∀ i, |z i| ≤ (Q.widths i - 1 : ℕ)) →
      GAP.evaluateSteps v z = 0 → z = 0) :
    (GAP.imageUnderSteps v
      (GAP.basisContraction cert.basis cert.radius cert.constant)).Proper := by
  apply GAP.imageUnderSteps_proper_of_injOn
    v (GAP.basisContraction cert.basis cert.radius cert.constant)
    (GAP.basisContraction_proper cert.basis cert.radius cert.constant)
  intro x hx y hy hxy
  have hCx : (fun j ↦ (cert.constant : ℤ) * x j) ∈
      cert.progression.carrier := by
    rw [cert.progression_eq]
    exact GAP.smul_mem_centeredBasisGAP_of_mem_basisContraction
      cert.basis cert.radius cert.constant_pos hx
  have hCy : (fun j ↦ (cert.constant : ℤ) * y j) ∈
      cert.progression.carrier := by
    rw [cert.progression_eq]
    exact GAP.smul_mem_centeredBasisGAP_of_mem_basisContraction
      cert.basis cert.radius cert.constant_pos hy
  obtain ⟨qx, hqx, hqxeq⟩ :=
    Elementary.mem_translate_iff.mp (cert.geometric_bound hCx)
  obtain ⟨qy, hqy, hqyeq⟩ :=
    Elementary.mem_translate_iff.mp (cert.geometric_bound hCy)
  have hscale : ∀ i,
      (cert.constant : ℤ) * (x i - y i) = qx i - qy i := by
    intro i
    have hx' := congrFun hqxeq i
    have hy' := congrFun hqyeq i
    simp only [Pi.add_apply] at hx' hy'
    linarith
  have hbound : ∀ i, |x i - y i| ≤ (Q.widths i - 1 : ℕ) := by
    intro i
    have hqxi := ((AxisBox.mem_carrier_iff _).mp hqx) i
    have hqyi := ((AxisBox.mem_carrier_iff _).mp hqy) i
    simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
      add_zero] at hqxi hqyi
    have hqdiff : |qx i - qy i| ≤
        (cert.constant : ℤ) * (Q.widths i - 1 : ℕ) := by
      rw [abs_le]
      constructor <;> omega
    have hscaled : (cert.constant : ℤ) * |x i - y i| ≤
        (cert.constant : ℤ) * (Q.widths i - 1 : ℕ) := by
      calc
        (cert.constant : ℤ) * |x i - y i| =
            |(cert.constant : ℤ) * (x i - y i)| := by
          symm
          rw [abs_mul, abs_of_nonneg]
          exact_mod_cast Nat.zero_le cert.constant
        _ = |qx i - qy i| := congrArg abs (hscale i)
        _ ≤ (cert.constant : ℤ) * (Q.widths i - 1 : ℕ) := hqdiff
    exact (Int.mul_le_mul_left (show (0 : ℤ) < cert.constant by
      exact_mod_cast cert.constant_pos)).mp hscaled
  have hevalzero : GAP.evaluateSteps v (x - y) = 0 := by
    funext j
    have hj := congrFun hxy j
    simp only [GAP.evaluateSteps, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib, Pi.zero_apply] at hj ⊢
    linarith
  have hsubzero := hkernel (x - y) hbound hevalzero
  exact sub_eq_zero.mp hsubzero

/-- A coordinate whose displayed interval is shorter than the scaling
factor must vanish if its scaled value remains in the centered box. -/
theorem scaled_coordinate_eq_zero_of_width_lt
    {ambient rank M : ℕ} (Q : GAP ambient rank)
    (hQ : CenteredCertificate Q) (hM : 0 < M)
    (z : Fin rank → ℤ)
    (hzbox : hQ.InBox (fun i ↦ (M : ℤ) * z i))
    (i : Fin rank) (hwidth : Q.widths i < M) : z i = 0 := by
  have hb := hzbox i
  have hc := (hQ.center i).isLt
  simp only [CenteredCertificate.lower, CenteredCertificate.upper] at hb
  have hMZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hwZ : (Q.widths i : ℤ) < (M : ℤ) := by exact_mod_cast hwidth
  by_contra hz
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hza : z i ≤ -1 := by omega
    nlinarith
  · have hza : 1 ≤ z i := by omega
    nlinarith

/-- A centered GAP contains an `M`-fold sumset whenever every summand has
an integer coefficient vector whose `M`-multiple stays in the centered
coefficient box.  This is the convex-box implication hidden in the
notation `A ⊆ M⁻¹Q` in CFP Lemma 2.22. -/
theorem exists_relative_representative_multifold_of_scaled
    {A : Finset ℤ} {M rank : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hM : 0 < M)
    (hrep : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x) :
    ∀ x ∈ multifoldSumset M A, ∃ z : Fin rank → ℤ,
      hQ.InBox z ∧
      hQ.relativePoint z = BiluFreiman.integerPoint x ∧
      ∀ i, Q.widths i < M → z i = 0 := by
  intro x hx
  obtain ⟨f, hf, hsum⟩ := mem_multifoldSumset_iff.mp hx
  choose z hzbox hzpoint using fun q ↦ hrep (f q) (hf q)
  let total : Fin rank → ℤ := fun i ↦ ∑ q, z q i
  have htotal : hQ.InBox total := by
    intro i
    have hlo := Finset.sum_le_sum fun q (_hq : q ∈ Finset.univ) ↦
      (hzbox q i).1
    have hhi := Finset.sum_le_sum fun q (_hq : q ∈ Finset.univ) ↦
      (hzbox q i).2
    have hlo' : (M : ℤ) * hQ.lower i ≤ (M : ℤ) * total i := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, total, Finset.mul_sum] using hlo
    have hhi' : (M : ℤ) * total i ≤ (M : ℤ) * hQ.upper i := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, total, Finset.mul_sum] using hhi
    have hMZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
    exact ⟨(Int.mul_le_mul_left hMZ).mp hlo',
      (Int.mul_le_mul_left hMZ).mp hhi'⟩
  have hpoint : hQ.relativePoint total = BiluFreiman.integerPoint x := by
    rw [← hsum]
    funext j
    simp only [CenteredCertificate.relativePoint, total,
      BiluFreiman.integerPoint]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _hq
    simpa only [CenteredCertificate.relativePoint,
      BiluFreiman.integerPoint] using congrFun (hzpoint q) j
  refine ⟨total, htotal, hpoint, ?_⟩
  intro i hwidth
  apply Finset.sum_eq_zero
  intro q _hq
  have hscaled : (M : ℤ) * z q i = 0 := by
    have hb := hzbox q i
    have hc := (hQ.center i).isLt
    simp only [CenteredCertificate.lower, CenteredCertificate.upper] at hb
    have hMZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
    have hwZ : (Q.widths i : ℤ) < (M : ℤ) := by exact_mod_cast hwidth
    by_cases hz : z q i = 0
    · simp [hz]
    · rcases lt_or_gt_of_ne hz with hzneg | hzpos
      · have hza : z q i ≤ -1 := by omega
        nlinarith
      · have hza : 1 ≤ z q i := by omega
        nlinarith
  exact (mul_eq_zero.mp hscaled).resolve_left (by exact_mod_cast Nat.ne_of_gt hM)

theorem multifoldSumset_subset_of_scaled_relative_representatives
    {A : Finset ℤ} {M rank : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hM : 0 < M)
    (hrep : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x) :
    multifoldSumset M A ⊆ BiluFreiman.integerCarrier Q := by
  intro x hx
  obtain ⟨z, hzbox, hzpoint, _hzsupport⟩ :=
    exists_relative_representative_multifold_of_scaled Q hQ hM hrep x hx
  apply BiluFreiman.mem_integerCarrier_iff.mpr
  rw [← hzpoint]
  exact hQ.relativePoint_mem_carrier hzbox

/-- Choose the centered coefficient image of the block sumset.  The image
has exactly the same cardinality, contains zero, lies in the coefficient
box, and vanishes in every direction shorter than the block scale. -/
theorem exists_coordinateSet_multifold_of_scaled
    {A : Finset ℤ} {M rank : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hproper : Q.Proper)
    (hM : 0 < M) (hzero : 0 ∈ A)
    (hrep : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x) :
    ∃ B : Finset (LatticePoint rank),
      B.card = (multifoldSumset M A).card ∧
      (0 : LatticePoint rank) ∈ B ∧
      B ⊆ (Q.centeredAxisBox hQ).carrier ∧
      (∀ z ∈ B, ∀ i, Q.widths i < M → z i = 0) ∧
      (∀ z ∈ B, ∃ x ∈ multifoldSumset M A,
        hQ.relativePoint z = BiluFreiman.integerPoint x) ∧
      ∀ x ∈ multifoldSumset M A, ∃ z ∈ B,
        hQ.relativePoint z = BiluFreiman.integerPoint x := by
  let S := multifoldSumset M A
  have hchoice (x : {x // x ∈ S}) : ∃ z : Fin rank → ℤ,
      hQ.InBox z ∧ hQ.relativePoint z = BiluFreiman.integerPoint x ∧
        ∀ i, Q.widths i < M → z i = 0 :=
    exists_relative_representative_multifold_of_scaled
      Q hQ hM hrep x x.property
  let coord : {x // x ∈ S} → LatticePoint rank := fun x ↦
    Classical.choose (hchoice x)
  have hcoord_box (x : {x // x ∈ S}) : hQ.InBox (coord x) :=
    (Classical.choose_spec (hchoice x)).1
  have hcoord_point (x : {x // x ∈ S}) :
      hQ.relativePoint (coord x) = BiluFreiman.integerPoint x :=
    (Classical.choose_spec (hchoice x)).2.1
  have hcoord_support (x : {x // x ∈ S}) :
      ∀ i, Q.widths i < M → coord x i = 0 :=
    (Classical.choose_spec (hchoice x)).2.2
  have hcoord_inj : Function.Injective coord := by
    intro x y hxy
    apply Subtype.ext
    have hpoint := congrArg hQ.relativePoint hxy
    rw [hcoord_point x, hcoord_point y] at hpoint
    have hvalue := congrArg BiluFreiman.pointInteger hpoint
    simpa only [BiluFreiman.pointInteger_integerPoint] using hvalue
  let B : Finset (LatticePoint rank) := Finset.univ.image coord
  refine ⟨B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hcoord_inj,
      Finset.card_univ]
    simp [S]
  · have hzeroS : 0 ∈ S := zero_mem_multifoldSumset hzero M
    let x0 : {x // x ∈ S} := ⟨0, hzeroS⟩
    have hcoord0 : coord x0 = 0 := by
      apply hQ.relativePoint_injective_on hproper (hcoord_box x0)
      · intro i
        exact hQ.lower_le_zero_le_upper i
      · rw [hcoord_point]
        funext j
        simp [x0, BiluFreiman.integerPoint,
          CenteredCertificate.relativePoint]
    exact Finset.mem_image.mpr ⟨x0, Finset.mem_univ _, hcoord0⟩
  · intro z hz
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
    rw [Q.mem_centeredAxisBox_iff hQ]
    exact hcoord_box x
  · intro z hz i hi
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
    exact hcoord_support x i hi
  · intro z hz
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x, x.property, hcoord_point x⟩
  · intro x hx
    let xS : {x // x ∈ S} := ⟨x, hx⟩
    refine ⟨coord xS, Finset.mem_image.mpr
      ⟨xS, Finset.mem_univ _, rfl⟩, ?_⟩
    exact hcoord_point xS

/-- Delete every short zero coordinate from the coordinate image of the
block sumset.  The result has unchanged cardinality and its wide-step
evaluation is exactly the original integer block sum. -/
theorem exists_wideCoordinateSet_multifold_of_scaled
    {A : Finset ℤ} {M rank : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hproper : Q.Proper)
    (hM : 0 < M) (hzero : 0 ∈ A)
    (hrep : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x) :
    ∃ B : Finset (LatticePoint (Q.wideRank M)),
      B.card = (multifoldSumset M A).card ∧
      (0 : LatticePoint (Q.wideRank M)) ∈ B ∧
      B ⊆ (Q.wideAxisBox hQ M hM).carrier ∧
      (∀ z ∈ B, ∃ x ∈ multifoldSumset M A,
        GAP.evaluateSteps (Q.wideSteps M) z =
          BiluFreiman.integerPoint x) ∧
      ∀ x ∈ multifoldSumset M A, ∃ z ∈ B,
        GAP.evaluateSteps (Q.wideSteps M) z =
          BiluFreiman.integerPoint x := by
  obtain ⟨B₀, hcard, hzeroB₀, hbox, hsupport, hrepB₀, hsurjB₀⟩ :=
    exists_coordinateSet_multifold_of_scaled
      Q hQ hproper hM hzero hrep
  let B := B₀.image (Q.wideProjection M)
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Q.card_image_wideProjection_of_support M B₀ hsupport).trans hcard
  · apply Finset.mem_image.mpr
    refine ⟨0, hzeroB₀, ?_⟩
    funext j
    rfl
  · exact Q.image_wideProjection_subset_wideAxisBox hQ M hM B₀ hbox
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, hzx⟩ := hrepB₀ z₀ hz₀
    refine ⟨x, hx, ?_⟩
    calc
      GAP.evaluateSteps (Q.wideSteps M) (Q.wideProjection M z₀) =
          fun j ↦ ∑ i, z₀ i * Q.steps i j :=
        Q.evaluateSteps_wideProjection_of_support M z₀ (hsupport z₀ hz₀)
      _ = hQ.relativePoint z₀ := rfl
      _ = BiluFreiman.integerPoint x := hzx
  · intro x hx
    obtain ⟨z₀, hz₀, hzx⟩ := hsurjB₀ x hx
    refine ⟨Q.wideProjection M z₀,
      Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩, ?_⟩
    calc
      GAP.evaluateSteps (Q.wideSteps M) (Q.wideProjection M z₀) =
          fun j ↦ ∑ i, z₀ i * Q.steps i j :=
        Q.evaluateSteps_wideProjection_of_support M z₀ (hsupport z₀ hz₀)
      _ = hQ.relativePoint z₀ := rfl
      _ = BiluFreiman.integerPoint x := hzx

/-- An iterated coordinate sum evaluates to the corresponding multifold
integer sumset when every coordinate summand evaluates to a member of `S`. -/
theorem pointInteger_evaluateSteps_mem_multifoldSumset_of_mem_iterated
    {d C : ℕ} (v : Fin d → LatticePoint 1)
    (B : Finset (LatticePoint d)) (S : Finset ℤ)
    (hmap : ∀ z ∈ B, ∃ x ∈ S,
      GAP.evaluateSteps v z = BiluFreiman.integerPoint x)
    {z : LatticePoint d}
    (hz : z ∈ iteratedSumset (fun _ ↦ B) C) :
    BiluFreiman.pointInteger (GAP.evaluateSteps v z) ∈
      multifoldSumset C S := by
  induction C generalizing z with
  | zero =>
      rw [iteratedSumset_zero] at hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      simp only [GAP.evaluateSteps, BiluFreiman.pointInteger,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        multifoldSumset_zero, Finset.mem_singleton]
  | succ C ih =>
      rw [show C + 1 = Nat.succ C by omega, iteratedSumset_succ] at hz
      obtain ⟨u, hu, b, hb, hub⟩ := mem_pointwise_add_iff.mp hz
      have hu' := ih hu
      obtain ⟨x, hx, hbx⟩ := hmap b hb
      rw [mem_multifoldSumset_succ_iff]
      refine ⟨BiluFreiman.pointInteger (GAP.evaluateSteps v u), hu',
        x, hx, ?_⟩
      rw [← hub]
      calc
        BiluFreiman.pointInteger (GAP.evaluateSteps v u) + x =
            BiluFreiman.pointInteger (GAP.evaluateSteps v u) +
              BiluFreiman.pointInteger (GAP.evaluateSteps v b) := by
          rw [hbx, BiluFreiman.pointInteger_integerPoint]
        _ = BiluFreiman.pointInteger (GAP.evaluateSteps v (u + b)) := by
          simp only [GAP.evaluateSteps, BiluFreiman.pointInteger,
            Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The sum-covering half of Corollary 2.17 pulls back to the exact block
cover required in Lemma 2.22. -/
theorem basisContraction_blockCovered_of_corollary217
    {d M : ℕ} {Q : AxisBox d} {B : Finset (BoxPoint d)}
    (cert : Corollary217Certificate Q B)
    (v : Fin d → LatticePoint 1) (S : Finset ℤ)
    (hmap : ∀ z ∈ B, ∃ x ∈ S,
      GAP.evaluateSteps v z = BiluFreiman.integerPoint x) :
    translate
        (BiluFreiman.pointInteger
          (GAP.evaluateSteps v cert.sumTranslate))
        (BiluFreiman.integerCarrier
          (GAP.dilate M (GAP.imageUnderSteps v
            (GAP.basisContraction cert.basis cert.radius M)))) ⊆
      multifoldSumset cert.constant S := by
  intro x hx
  rw [mem_translate_iff] at hx
  obtain ⟨p, hp, hxp⟩ := hx
  have hpLattice : BiluFreiman.integerPoint p ∈
      (GAP.dilate M (GAP.imageUnderSteps v
        (GAP.basisContraction cert.basis cert.radius M))).carrier :=
    BiluFreiman.mem_integerCarrier_iff.mp hp
  rw [GAP.imageUnderSteps_dilate,
    GAP.imageUnderSteps_carrier] at hpLattice
  obtain ⟨q, hq, hqeval⟩ := Finset.mem_image.mp hpLattice
  have hqP : q ∈ cert.progression.carrier := by
    rw [cert.progression_eq]
    exact GAP.dilate_basisContraction_carrier_subset_centeredBasisGAP
      cert.basis cert.radius M hq
  have hsum : cert.sumTranslate + q ∈
      iteratedSumset (fun _ ↦ B) cert.constant := by
    apply cert.sum_covered
    exact Elementary.mem_translate_iff.mpr ⟨q, hqP, rfl⟩
  have hevalmem :=
    pointInteger_evaluateSteps_mem_multifoldSumset_of_mem_iterated
      v B S hmap hsum
  have heq :
      BiluFreiman.pointInteger
          (GAP.evaluateSteps v (cert.sumTranslate + q)) =
        BiluFreiman.pointInteger (GAP.evaluateSteps v cert.sumTranslate) + p := by
    calc
      BiluFreiman.pointInteger
          (GAP.evaluateSteps v (cert.sumTranslate + q)) =
          BiluFreiman.pointInteger (GAP.evaluateSteps v cert.sumTranslate) +
            BiluFreiman.pointInteger (GAP.evaluateSteps v q) := by
        simp only [GAP.evaluateSteps, Pi.add_apply, add_mul,
          Finset.sum_add_distrib, BiluFreiman.pointInteger]
      _ = BiluFreiman.pointInteger (GAP.evaluateSteps v cert.sumTranslate) + p := by
        rw [hqeval, BiluFreiman.pointInteger_integerPoint]
  rw [← hxp, ← heq]
  exact hevalmem

/-- With zero available for padding, every smaller multiple of one element
belongs to the indicated multifold sumset. -/
theorem mul_mem_multifoldSumset_of_le {A : Finset ℤ}
    (hzero : 0 ∈ A) {x : ℤ} (hx : x ∈ A) {t M : ℕ} (ht : t ≤ M) :
    (t : ℤ) * x ∈ multifoldSumset M A := by
  have htx : (t : ℤ) * x ∈ multifoldSumset t A := by
    apply mem_multifoldSumset_iff.mpr
    refine ⟨fun _ ↦ x, fun _ ↦ hx, ?_⟩
    simp
  exact multifoldSumset_mono_index hzero ht htx

/-- The active pullback of the Corollary 2.17 basis contraction contains
the original set.  The key point is that the coordinate of `x` occurring
in the block sumset is unique in the old proper GAP, while the lattice-basis
description turns membership of `M*x` into membership in the contraction. -/
theorem active_basisContraction_contains_of_corollary217
    {A : Finset ℤ} {M rank : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hproper : Q.Proper)
    (hM : 0 < M) (hzero : 0 ∈ A)
    (hrep : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x)
    (B : Finset (LatticePoint (Q.wideRank M)))
    (hBQ : B ⊆ (Q.wideAxisBox hQ M hM).carrier)
    (hsurj : ∀ x ∈ multifoldSumset M A, ∃ z ∈ B,
      GAP.evaluateSteps (Q.wideSteps M) z =
        BiluFreiman.integerPoint x)
    (cert : Corollary217Certificate (Q.wideAxisBox hQ M hM) B) :
    A ⊆ BiluFreiman.integerCarrier
      (GAP.activeDimensions (GAP.imageUnderSteps (Q.wideSteps M)
        (GAP.basisContraction cert.basis cert.radius M))) := by
  intro x hx
  obtain ⟨z, hzscaled, hzpoint⟩ := hrep x hx
  have hzsupport : ∀ i, Q.widths i < M → z i = 0 := by
    intro i hi
    exact scaled_coordinate_eq_zero_of_width_lt Q hQ hM z hzscaled i hi
  let w := Q.wideProjection M z
  have hwpoint : GAP.evaluateSteps (Q.wideSteps M) w =
      BiluFreiman.integerPoint x := by
    calc
      GAP.evaluateSteps (Q.wideSteps M) w =
          fun j ↦ ∑ i, z i * Q.steps i j :=
        Q.evaluateSteps_wideProjection_of_support M z hzsupport
      _ = hQ.relativePoint z := rfl
      _ = BiluFreiman.integerPoint x := hzpoint
  have hxS : x ∈ multifoldSumset M A := by
    have hxone := mul_mem_multifoldSumset_of_le hzero hx
      (show 1 ≤ M by omega)
    simpa using hxone
  obtain ⟨b, hbB, hbpoint⟩ := hsurj x hxS
  have hbbox := hBQ hbB
  have hzbox : hQ.InBox z := by
    intro i
    have hi := hzscaled i
    have hMZ : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have hlo := hQ.lower_nonpos i
    have hhi := hQ.upper_nonneg i
    constructor
    · by_cases hzsign : 0 ≤ z i
      · exact hlo.trans hzsign
      · have hzsign' : z i < 0 := lt_of_not_ge hzsign
        nlinarith [hi.1]
    · by_cases hzsign : 0 ≤ z i
      · nlinarith [hi.2]
      · exact (le_of_not_ge hzsign).trans hhi
  have hwbox : w ∈ (Q.wideAxisBox hQ M hM).carrier := by
    rw [AxisBox.mem_carrier_iff]
    intro j
    have hj := hzbox (Q.wideIndex M j)
    have hlen := hQ.upper_sub_lower_add_one (Q.wideIndex M j)
    simp only [GAP.wideAxisBox, GAP.wideProjection, w] at hj ⊢
    exact ⟨hj.1, by omega⟩
  have hbw : b = w := by
    apply sub_eq_zero.mp
    apply Q.wideSteps_kernel_of_proper hQ hproper M hM (b - w)
    · intro j
      have hbj := ((AxisBox.mem_carrier_iff _).mp hbbox) j
      have hwj := ((AxisBox.mem_carrier_iff _).mp hwbox) j
      have hwidth := (Q.wideAxisBox hQ M hM).width_pos j
      simp only [Pi.sub_apply]
      rw [abs_le]
      constructor <;> omega
    · funext j
      have hjb := congrFun hbpoint j
      have hjw := congrFun hwpoint j
      simp only [GAP.evaluateSteps, Pi.sub_apply, sub_mul,
        Finset.sum_sub_distrib, Pi.zero_apply] at hjb hjw ⊢
      linarith
  have hMwbox : (fun j ↦ (M : ℤ) * w j) ∈
      (Q.wideAxisBox hQ M hM).carrier := by
    rw [AxisBox.mem_carrier_iff]
    intro j
    have hj := hzscaled (Q.wideIndex M j)
    have hlen := hQ.upper_sub_lower_add_one (Q.wideIndex M j)
    simp only [GAP.wideAxisBox, GAP.wideProjection, w] at hj ⊢
    exact ⟨hj.1, by omega⟩
  have hwΓ : w ∈ generatedSublattice B := by
    rw [← hbw]
    exact subset_generatedSublattice B hbB
  have hMwΓ : (fun j ↦ (M : ℤ) * w j) ∈ generatedSublattice B := by
    change (M : ℤ) • w ∈ generatedSublattice B
    exact (generatedSublattice B).zsmul_mem hwΓ (M : ℤ)
  have hMwP := cert.box_lattice_subset _ hMwbox hMwΓ
  have hwcontract : w ∈
      (GAP.basisContraction cert.basis cert.radius M).carrier := by
    rw [cert.progression_eq] at hMwP
    exact GAP.mem_basisContraction_of_smul_mem_centeredBasisGAP
      cert.basis cert.radius hM hwΓ hMwP
  have hwimage : GAP.evaluateSteps (Q.wideSteps M) w ∈
      (GAP.imageUnderSteps (Q.wideSteps M)
        (GAP.basisContraction cert.basis cert.radius M)).carrier := by
    rw [GAP.imageUnderSteps_carrier]
    exact Finset.mem_image.mpr ⟨w, hwcontract, rfl⟩
  apply BiluFreiman.mem_integerCarrier_iff.mpr
  rw [GAP.carrier_activeDimensions]
  rwa [hwpoint] at hwimage

/-- The recursive finite sumset used in the CFP development agrees with
Mathlib's pointwise natural scalar action on finite sets. -/
theorem multifoldSumset_eq_nsmul (k : ℕ) (A : Finset ℤ) :
    multifoldSumset k A = k • A := by
  classical
  ext x
  rw [mem_multifoldSumset_iff, Finset.mem_nsmul]
  constructor
  · rintro ⟨f, hf, hsum⟩
    let points : Fin k → {a // a ∈ A} := fun i ↦ ⟨f i, hf i⟩
    refine ⟨points, ?_⟩
    rw [List.sum_ofFn]
    simpa [points] using hsum
  · rintro ⟨points, hsum⟩
    refine ⟨fun i ↦ points i, fun i ↦ (points i).property, ?_⟩
    rw [← List.sum_ofFn]
    exact hsum

/-- Multifold sumsets are monotone in their underlying finite set. -/
theorem multifoldSumset_mono_set (k : ℕ) {A B : Finset ℤ}
    (hAB : A ⊆ B) : multifoldSumset k A ⊆ multifoldSumset k B := by
  intro x hx
  obtain ⟨f, hf, hsum⟩ := mem_multifoldSumset_iff.mp hx
  exact mem_multifoldSumset_iff.mpr ⟨f, fun i ↦ hAB (hf i), hsum⟩

/-- The elementary interval bound used in CFP Lemmas 2.22 and 2.26:
an `h`-fold sumset of a subset of `[0,n-1]` has at most `h*n` elements. -/
theorem card_multifoldSumset_le_mul_of_subset_Icc {A : Finset ℤ}
    {h n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) :
    (multifoldSumset h A).card ≤ h * n := by
  have hsubset : multifoldSumset h A ⊆
      Finset.Icc (0 : ℤ) ((h * n : ℕ) - 1) := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := mem_multifoldSumset_iff.mp hx
    have hfIcc (i : Fin h) := Finset.mem_Icc.mp (hA (hf i))
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.sum_nonneg fun i _ ↦ (hfIcc i).1
    · have hsum : (∑ i, f i) ≤ ∑ _i : Fin h, ((n : ℤ) - 1) :=
        Finset.sum_le_sum fun i _ ↦ (hfIcc i).2
      calc
        (∑ i, f i) ≤ ∑ _i : Fin h, ((n : ℤ) - 1) := hsum
        _ = (h : ℤ) * ((n : ℤ) - 1) := by simp; ring
        _ ≤ ((h * n : ℕ) : ℤ) - 1 := by
          push_cast
          nlinarith
  calc
    (multifoldSumset h A).card ≤
        (Finset.Icc (0 : ℤ) ((h * n : ℕ) - 1)).card :=
      Finset.card_le_card hsubset
    _ = h * n := by
      rw [Int.card_Icc]
      simp only [sub_zero]
      have hhn : 0 < h * n := Nat.mul_pos hh hn
      omega

/-- Repeating one translate `k` times translates the `k`-fold sumset by
`k` times the translation vector. -/
theorem multifoldSumset_translate (k : ℕ) (t : ℤ) (A : Finset ℤ) :
    multifoldSumset k (translate t A) =
      translate ((k : ℤ) * t) (multifoldSumset k A) := by
  classical
  ext x
  simp only [mem_multifoldSumset_iff, mem_translate_iff]
  constructor
  · rintro ⟨f, hf, hsum⟩
    choose g hgA hfg using hf
    refine ⟨∑ i, g i, ⟨g, hgA, rfl⟩, ?_⟩
    rw [← hsum]
    simp_rw [← hfg]
    simp [Finset.sum_add_distrib]
  · rintro ⟨y, ⟨g, hgA, hgsum⟩, htx⟩
    refine ⟨fun i ↦ t + g i, ?_, ?_⟩
    · intro i
      exact ⟨g i, hgA i, rfl⟩
    · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hgsum]
      exact htx

/-- Iterating an `m`-fold sumset `k` times gives the `(k*m)`-fold sumset. -/
theorem multifoldSumset_multifold (k m : ℕ) (A : Finset ℤ) :
    multifoldSumset k (multifoldSumset m A) = multifoldSumset (k * m) A := by
  simp only [multifoldSumset_eq_nsmul, smul_smul]

/-- The doubling notation in the Bilu--Freiman interface agrees exactly
with doubling the number of summands. -/
theorem twoA_multifoldSumset (k : ℕ) (A : Finset ℤ) :
    BiluFreiman.twoA (multifoldSumset k A) =
      multifoldSumset (2 * k) A := by
  rw [show 2 * k = k + k by omega, multifoldSumset_add]
  ext x
  simp only [BiluFreiman.mem_twoA_iff, mem_sumset_iff]

/-- The fully constructed block-cover part of CFP Lemma 2.22, before the
slow-growth argument enlarges the proper scale from a fixed fraction of the
dyadic block scale to a fixed fraction of `h`. -/
structure Lemma222BlockApproximation
    (A : Finset ℤ) (rank rankBound : ℕ) where
  rank_le : rank ≤ rankBound
  progression : GAP 1 rank
  zero_mem : 0 ∈ A
  contains : A ⊆ BiluFreiman.integerCarrier progression
  nondegenerate : progression.Nondegenerate
  blockExponent : ℕ
  blockScale : ℕ
  blockScale_eq : blockScale = 2 ^ blockExponent
  blockScale_pos : 0 < blockScale
  coverExponent : ℕ
  coverMultiplier : ℕ
  coverMultiplier_eq : coverMultiplier = 2 ^ coverExponent
  coverMultiplier_pos : 0 < coverMultiplier
  blockTranslate : ℤ
  blockCovered :
    translate blockTranslate
      (BiluFreiman.integerCarrier (progression.dilate blockScale)) ⊆
      multifoldSumset (coverMultiplier * blockScale) A
  initialProperScale : ℕ
  initialProperScale_pos : 0 < initialProperScale
  initialProperScale_mul_cover :
    initialProperScale * coverMultiplier = blockScale
  initialProper : (progression.dilate initialProperScale).Proper

namespace Lemma222BlockApproximation

variable {A : Finset ℤ} {rank rankBound : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)

/-- The dyadic cover multiplier divides the dyadic block scale. -/
theorem coverExponent_le_blockExponent :
    W.coverExponent ≤ W.blockExponent := by
  apply (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ (2 : ℕ))).mp
  rw [← W.coverMultiplier_eq, ← W.blockScale_eq,
    ← W.initialProperScale_mul_cover]
  simpa using
    (Nat.mul_le_mul_right W.coverMultiplier W.initialProperScale_pos)

/-- Exact dyadic value of the initial proper scale.  This is the rounding
identity suppressed in the paper's notation `C⁻¹ 2^(y+1)`. -/
theorem initialProperScale_eq_pow_sub :
    W.initialProperScale =
      2 ^ (W.blockExponent - W.coverExponent) := by
  apply Nat.mul_right_cancel W.coverMultiplier_pos
  rw [W.initialProperScale_mul_cover, W.coverMultiplier_eq,
    W.blockScale_eq, ← pow_add,
    Nat.sub_add_cancel W.coverExponent_le_blockExponent]

end Lemma222BlockApproximation

/-- The actual Bilu--Freiman invocation in CFP Lemma 2.22, isolated from
the later dense-box upgrade.  A verified slow-growth scale produces the
source `Witness` without any additional assumption. -/
theorem exists_biluWitness_at_multifold_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement)
    (s d : ℕ) (hs : 0 < s) (hd : 0 < d)
    (delta : ℝ) (hdelta : 0 < delta) {A : Finset ℤ}
    (hzero : 0 ∈ A) (k : ℕ)
    (hgrowth :
      ((multifoldSumset (2 * k) A).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - delta) *
          (multifoldSumset k A).card) :
    ∃ C : ℕ, 0 < C ∧
      Nonempty (BiluFreiman.Witness s d C (multifoldSumset k A)) := by
  obtain ⟨C, hC, hCall⟩ := hBF s d hs hd delta hdelta
  refine ⟨C, hC, hCall (multifoldSumset k A) ?_ ?_⟩
  · exact ⟨0, zero_mem_multifoldSumset hzero k⟩
  · rw [twoA_multifoldSumset]
    exact hgrowth

/-- Dyadic specialization of the preceding Bilu invocation. -/
theorem exists_biluWitness_at_dyadic_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement)
    (s d : ℕ) (hs : 0 < s) (hd : 0 < d)
    (delta : ℝ) (hdelta : 0 < delta) {A : Finset ℤ}
    (hzero : 0 ∈ A) (y : ℕ)
    (hgrowth :
      ((multifoldSumset (2 ^ (y + 1)) A).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - delta) *
          (multifoldSumset (2 ^ y) A).card) :
    ∃ C : ℕ, 0 < C ∧
      Nonempty (BiluFreiman.Witness s d C (multifoldSumset (2 ^ y) A)) := by
  apply exists_biluWitness_at_multifold_of_biluFreiman
    hBF s d hs hd delta hdelta hzero (2 ^ y)
  simpa [pow_succ, mul_comm] using hgrowth

/-- Pointwise scaled-coordinate conclusion behind the Bilu prefix
reduction.  It is exposed separately so the short-coordinate deletion step
can reuse the same actual witness. -/
theorem exists_scaled_centeredPrefix_representative_of_witness
    {A : Finset ℤ} {y d C : ℕ}
    (W : BiluFreiman.Witness 2 d C
      (multifoldSumset (2 ^ y) A))
    (hP : CenteredCertificate W.progression)
    (hzero : 0 ∈ A) (hC : C < 2 ^ (y + 1))
    {x : ℤ} (hx : x ∈ A) :
    ∃ z : Fin (min W.rank d) → ℤ,
      (W.progression.centeredFirstCertificate hP d).InBox
        (fun i ↦ (2 ^ (y + 1) : ℕ) * z i) ∧
      (W.progression.centeredFirstCertificate hP d).relativePoint z =
        BiluFreiman.integerPoint x := by
  let M := 2 ^ (y + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMone : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hM)
  have hmem (t : Fin (M + 1)) :
      BiluFreiman.integerPoint ((t : ℤ) * x) ∈
        W.progression.carrier := by
    apply BiluFreiman.mem_integerCarrier_iff.mp
    apply W.twoA_subset
    rw [twoA_multifoldSumset]
    have htx := mul_mem_multifoldSumset_of_le hzero hx
      (show (t : ℕ) ≤ M by omega)
    simpa [M, pow_succ, mul_comm] using htx
  let c : Fin (M + 1) → W.progression.Coord := fun t ↦
    Classical.choose (GAP.mem_carrier_iff.mp (hmem t))
  have hc (t : Fin (M + 1)) :
      W.progression.coordPoint (c t) =
        BiluFreiman.integerPoint ((t : ℤ) * x) :=
    Classical.choose_spec (GAP.mem_carrier_iff.mp (hmem t))
  have hc' (t : Fin (M + 1)) :
      W.progression.coordPoint (c t) =
        fun j ↦ (t : ℤ) * BiluFreiman.integerPoint x j := by
    rw [hc]
    funext j
    rfl
  have htailVolume :
      (W.progression.remainingDimensions d).volume < M :=
    W.remainingDimensions_volume_le.trans_lt (by simpa [M] using hC)
  have htail :=
    W.progression.remaining_relativeCoeff_eq_zero_of_point_multiples
      hP W.sProper hMone d htailVolume
      (BiluFreiman.integerPoint x) c hc'
  let hQ := W.progression.centeredFirstCertificate hP d
  let n1 := W.progression.centeredFirstCoord hP d (c ⟨1, by omega⟩)
  let z : Fin (min W.rank d) → ℤ := hQ.relativeCoeff n1
  refine ⟨z, ?_, ?_⟩
  · intro i
    change hP.lower
          ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩ ≤
        (M : ℤ) * hP.relativeCoeff (c ⟨1, by omega⟩)
          ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩ ∧
      (M : ℤ) * hP.relativeCoeff (c ⟨1, by omega⟩)
          ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩ ≤
        hP.upper ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩
    have hlinear := W.progression.relativeCoeff_eq_mul_of_point_multiples
      hP W.sProper hMone (BiluFreiman.integerPoint x) c hc'
    have hi := congrFun (hlinear ⟨M, by omega⟩)
      ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩
    rw [← hi]
    exact hP.relativeCoeff_mem_box (c ⟨M, by omega⟩)
      ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩
  · calc
      hQ.relativePoint z =
          (W.progression.centeredFirstDimensions hP d).coordPoint n1 :=
        (hQ.coordPoint_eq_relativePoint n1).symm
      _ = W.progression.coordPoint (c ⟨1, by omega⟩) :=
        (W.progression.coordPoint_eq_centeredFirstDimensions_of_remaining_zero
          hP d (c ⟨1, by omega⟩) htail).symm
      _ = BiluFreiman.integerPoint x := by simpa using hc ⟨1, by omega⟩

/-- The complete Bilu-prefix reduction in the first half of CFP Lemma 2.22.
If the dyadic block scale is larger than the bounded Bilu tail, the centered
prefix is proper, contains zero, contains the entire block sumset, and has
volume at most `C` times that sumset's cardinality. -/
theorem exists_centered_biluPrefix_of_witness
    {A : Finset ℤ} {y d C : ℕ}
    (W : BiluFreiman.Witness 2 d C
      (multifoldSumset (2 ^ y) A))
    (hzero : 0 ∈ A) (hC : C < 2 ^ (y + 1)) :
    ∃ hP : CenteredCertificate W.progression,
      let Q := W.progression.centeredFirstDimensions hP d
      Q.Proper ∧
      0 ∈ Q.carrier ∧
      multifoldSumset (2 ^ (y + 1)) A ⊆
        BiluFreiman.integerCarrier Q ∧
      Q.volume ≤ C * (multifoldSumset (2 ^ (y + 1)) A).card := by
  let M := 2 ^ (y + 1)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hMone : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hM)
  have hzeroB : 0 ∈ multifoldSumset (2 ^ y) A :=
    zero_mem_multifoldSumset hzero _
  have hzeroTwo : 0 ∈
      BiluFreiman.twoA (multifoldSumset (2 ^ y) A) := by
    exact BiluFreiman.mem_twoA_iff.mpr
      ⟨0, hzeroB, 0, hzeroB, by simp⟩
  have hzeroP : (0 : LatticePoint 1) ∈ W.progression.carrier := by
    have := W.twoA_subset hzeroTwo
    rw [BiluFreiman.mem_integerCarrier_iff] at this
    convert this using 1
    funext j
    exact Subsingleton.elim j 0 ▸ rfl
  obtain ⟨hP⟩ := claim_2_6.mp hzeroP
  refine ⟨hP, W.progression.centeredFirstDimensions_proper hP d
      (W.proper (by omega)),
    W.progression.zero_mem_centeredFirstDimensions hP d, ?_, ?_⟩
  · apply multifoldSumset_subset_of_scaled_relative_representatives
      (W.progression.centeredFirstDimensions hP d)
      (W.progression.centeredFirstCertificate hP d) hM
    intro x hx
    have hmem (t : Fin (M + 1)) :
        BiluFreiman.integerPoint ((t : ℤ) * x) ∈
          W.progression.carrier := by
      apply BiluFreiman.mem_integerCarrier_iff.mp
      apply W.twoA_subset
      rw [twoA_multifoldSumset]
      have htx := mul_mem_multifoldSumset_of_le hzero hx
        (show (t : ℕ) ≤ M by omega)
      simpa [M, pow_succ, mul_comm] using htx
    let c : Fin (M + 1) → W.progression.Coord := fun t ↦
      Classical.choose (GAP.mem_carrier_iff.mp (hmem t))
    have hc (t : Fin (M + 1)) :
        W.progression.coordPoint (c t) =
          BiluFreiman.integerPoint ((t : ℤ) * x) :=
      Classical.choose_spec (GAP.mem_carrier_iff.mp (hmem t))
    have hc' (t : Fin (M + 1)) :
        W.progression.coordPoint (c t) =
          fun j ↦ (t : ℤ) * BiluFreiman.integerPoint x j := by
      rw [hc]
      funext j
      rfl
    have htailVolume :
        (W.progression.remainingDimensions d).volume < M :=
      W.remainingDimensions_volume_le.trans_lt (by simpa [M] using hC)
    have htail :=
      W.progression.remaining_relativeCoeff_eq_zero_of_point_multiples
        hP W.sProper hMone d htailVolume
        (BiluFreiman.integerPoint x) c hc'
    let Q := W.progression.centeredFirstDimensions hP d
    let hQ := W.progression.centeredFirstCertificate hP d
    let n1 := W.progression.centeredFirstCoord hP d (c ⟨1, by omega⟩)
    let z : Fin (min W.rank d) → ℤ := hQ.relativeCoeff n1
    refine ⟨z, ?_, ?_⟩
    · intro i
      change hP.lower
            ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩ ≤
          (M : ℤ) * hP.relativeCoeff (c ⟨1, by omega⟩)
            ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩ ∧
        (M : ℤ) * hP.relativeCoeff (c ⟨1, by omega⟩)
            ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩ ≤
          hP.upper ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩
      have hlinear := W.progression.relativeCoeff_eq_mul_of_point_multiples
        hP W.sProper hMone
        (BiluFreiman.integerPoint x) c hc'
      have hi := congrFun (hlinear ⟨M, by omega⟩)
        ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩
      rw [← hi]
      exact hP.relativeCoeff_mem_box (c ⟨M, by omega⟩)
        ⟨i, i.isLt.trans_le (min_le_left W.rank d)⟩
    · calc
        hQ.relativePoint z = hQ.relativePoint z := rfl
        _ = Q.coordPoint n1 := by
          exact (hQ.coordPoint_eq_relativePoint n1).symm
        _ = W.progression.coordPoint (c ⟨1, by omega⟩) :=
          (W.progression.coordPoint_eq_centeredFirstDimensions_of_remaining_zero
            hP d (c ⟨1, by omega⟩) htail).symm
        _ = BiluFreiman.integerPoint x := by simpa using hc ⟨1, by omega⟩
  · have hprefixVolume :
        (W.progression.centeredFirstDimensions hP d).volume ≤
          W.progression.volume := by
      have hpos := (W.progression.remainingDimensions d).volume_pos
      calc
        (W.progression.centeredFirstDimensions hP d).volume =
            (W.progression.firstDimensions d).volume := rfl
        _ ≤ (W.progression.firstDimensions d).volume *
            (W.progression.remainingDimensions d).volume :=
          Nat.le_mul_of_pos_right _ hpos
        _ = W.progression.volume :=
          (W.progression.volume_eq_firstDimensions_mul_remainingDimensions d).symm
    exact hprefixVolume.trans <| W.volume_le.trans_eq <| by
      rw [twoA_multifoldSumset]
      simp [pow_succ, mul_comm]

/-- A nonzero represented element forces at least one direction to survive
the block-scale width cutoff. -/
theorem wideRank_pos_of_scaled_of_exists_ne_zero
    {A : Finset ℤ} {M rank : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hM : 0 < M)
    (hscaled : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x)
    (hne : ∃ x ∈ A, x ≠ 0) :
    0 < Q.wideRank M := by
  by_contra hnot
  have hwide : Q.wideRank M = 0 := Nat.eq_zero_of_not_pos hnot
  obtain ⟨x, hx, hxne⟩ := hne
  obtain ⟨z, hzbox, hzpoint⟩ := hscaled x hx
  have hshort (i : Fin rank) : Q.widths i < M := by
    by_contra hi
    have hi' : M ≤ Q.widths i := Nat.le_of_not_gt hi
    have hpos : 0 < Fintype.card (GAP.WideDirection Q M) :=
      Fintype.card_pos_iff.mpr ⟨⟨i, hi'⟩⟩
    have : 0 < Q.wideRank M := by simpa only [GAP.wideRank] using hpos
    omega
  have hz : z = 0 := by
    funext i
    exact scaled_coordinate_eq_zero_of_width_lt
      Q hQ hM z hzbox i (hshort i)
  have hpoint : BiluFreiman.integerPoint x = 0 := by
    rw [← hzpoint, hz]
    funext j
    simp [CenteredCertificate.relativePoint]
  have hx0 := congrArg BiluFreiman.pointInteger hpoint
  apply hxne
  simpa only [BiluFreiman.pointInteger,
    BiluFreiman.integerPoint, Pi.zero_apply] using hx0

/-- If no direction of the centered Bilu prefix survives at the block
scale, the scaled-coordinate condition forces every element of `A` to be
zero.  The homogeneous rank-zero GAP then supplies the exact block cover
and properness certificate. -/
theorem exists_lemma222BlockApproximation_of_wideRank_eq_zero
    {A : Finset ℤ} {M rank rankBound : ℕ} (Q : GAP 1 rank)
    (hQ : CenteredCertificate Q) (hM : 0 < M) (hzero : 0 ∈ A)
    (hscaled : ∀ x ∈ A, ∃ z : Fin rank → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x)
    (hwide : Q.wideRank M = 0) :
    ∃ V : Lemma222BlockApproximation A 0 rankBound,
      V.coverExponent = 0 := by
  have hshort (i : Fin rank) : Q.widths i < M := by
    by_contra hi
    have hi' : M ≤ Q.widths i := Nat.le_of_not_gt hi
    have hpos : 0 < Fintype.card (GAP.WideDirection Q M) :=
      Fintype.card_pos_iff.mpr ⟨⟨i, hi'⟩⟩
    have : 0 < Q.wideRank M := by simpa only [GAP.wideRank] using hpos
    omega
  have hAzero : ∀ x ∈ A, x = 0 := by
    intro x hx
    obtain ⟨z, hzbox, hzpoint⟩ := hscaled x hx
    have hz : z = 0 := by
      funext i
      exact scaled_coordinate_eq_zero_of_width_lt
        Q hQ hM z hzbox i (hshort i)
    have hpoint : BiluFreiman.integerPoint x = 0 := by
      rw [← hzpoint, hz]
      funext j
      simp [CenteredCertificate.relativePoint]
    have hx0 := congrArg BiluFreiman.pointInteger hpoint
    simpa only [BiluFreiman.pointInteger,
      BiluFreiman.integerPoint, Pi.zero_apply] using hx0
  refine ⟨{
    rank_le := Nat.zero_le rankBound
    progression := GAPBuilders.zeroGAP 1
    zero_mem := hzero
    contains := ?_
    nondegenerate := ?_
    blockExponent := 0
    blockScale := 1
    blockScale_eq := by simp
    blockScale_pos := Nat.zero_lt_one
    coverExponent := 0
    coverMultiplier := 1
    coverMultiplier_eq := by simp
    coverMultiplier_pos := Nat.zero_lt_one
    blockTranslate := 0
    blockCovered := ?_
    initialProperScale := 1
    initialProperScale_pos := Nat.zero_lt_one
    initialProperScale_mul_cover := by simp
    initialProper := GAPBuilders.rankZero_proper _ }, rfl⟩
  · intro x hx
    have hx0 := hAzero x hx
    subst x
    rw [BiluFreiman.mem_integerCarrier_iff,
      GAPBuilders.zeroGAP_carrier]
    apply Finset.mem_singleton.mpr
    funext j
    rfl
  · intro i
    exact Fin.elim0 i
  · intro x hx
    rw [mem_translate_iff] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    have hpLattice := BiluFreiman.mem_integerCarrier_iff.mp hp
    rw [GAPBuilders.rankZero_dilate_carrier] at hpLattice
    have hpPoint := Finset.mem_singleton.mp hpLattice
    have hp0 := congrArg BiluFreiman.pointInteger hpPoint
    have hpzero : p = 0 := by
      simpa [GAPBuilders.zeroGAP, GAPBuilders.rankZero,
        BiluFreiman.pointInteger, BiluFreiman.integerPoint] using hp0
    subst p
    have hxzero : x = 0 := by simpa using hxp.symm
    subst x
    simpa using zero_mem_multifoldSumset hzero 1

/-- Corollary 2.17 constants can be chosen uniformly over every positive
rank at most a prescribed bound.  This finite induction is the exact
replacement for the paper's convention that constants depend only on the
ambient rank bound, and crucially chooses them before any Bilu witness. -/
theorem exists_uniform_corollary217Certificate
    (rankBound cNum cDen : ℕ) (hcNum : 0 < cNum)
    (hc : cNum ≤ cDen) :
    ∃ C widthThreshold : ℕ, 0 < C ∧ 0 < widthThreshold ∧
      ∀ r : ℕ, 0 < r → r ≤ rankBound →
        ∀ (Q : AxisBox r) (B : Finset (BoxPoint r)),
          widthThreshold ≤ Q.minWidth →
          (0 : BoxPoint r) ∈ B →
          B ⊆ Q.carrier →
          cNum * Q.volume ≤ cDen * B.card →
          ∃ cert : Corollary217Certificate Q B, cert.constant ≤ C := by
  induction rankBound with
  | zero =>
      refine ⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one, ?_⟩
      intro r hr hbound
      omega
  | succ rankBound ih =>
      obtain ⟨C₀, T₀, hC₀, hT₀, hcor₀⟩ := ih
      obtain ⟨C₁, T₁, hC₁, hcor₁⟩ :=
        exists_corollary217Certificate (rankBound + 1)
          (Nat.zero_lt_succ rankBound) cNum cDen hcNum hc
      refine ⟨max C₀ C₁, max T₀ T₁,
        hC₀.trans_le (Nat.le_max_left _ _),
        hT₀.trans_le (Nat.le_max_left _ _), ?_⟩
      intro r hr hbound Q B hwidth hzeroB hBQ hdensity
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · have hrank : r ≤ rankBound := Nat.lt_succ_iff.mp hlt
        obtain ⟨cert, hcert⟩ := hcor₀ r hr hrank Q B
          ((Nat.le_max_left T₀ T₁).trans hwidth)
          hzeroB hBQ hdensity
        exact ⟨cert, hcert.trans (Nat.le_max_left C₀ C₁)⟩
      · subst r
        obtain ⟨cert, hcert⟩ := hcor₁ Q B
          ((Nat.le_max_right T₀ T₁).trans hwidth)
          hzeroB hBQ hdensity
        exact ⟨cert, hcert.le.trans (Nat.le_max_right C₀ C₁)⟩

/-- Corollary 2.17 upgrades a positive-rank Bilu prefix to the complete
nondegenerate block-cover output of Lemma 2.22.  The returned threshold is
chosen after the two source constants but before the final size hypothesis;
it dominates both the dense-box width threshold and its cover multiplier. -/
theorem lemma222BlockApproximation_of_biluPrefix_of_uniformCorollary217
    {A : Finset ℤ} {y d C : ℕ}
    (W : BiluFreiman.Witness 2 d C
      (multifoldSumset (2 ^ y) A))
    (hP : CenteredCertificate W.progression)
    (hzero : 0 ∈ A) (hCpos : 0 < C) (hC : C < 2 ^ (y + 1))
    (hprefixProper :
      (W.progression.centeredFirstDimensions hP d).Proper)
    (hprefixVolume :
      (W.progression.centeredFirstDimensions hP d).volume ≤
        C * (multifoldSumset (2 ^ (y + 1)) A).card)
    (hwide : 0 < (W.progression.centeredFirstDimensions hP d).wideRank
      (2 ^ (y + 1)))
    (corollaryConstant widthThreshold : ℕ)
    (hcorollaryConstant : 0 < corollaryConstant)
    (hcor : ∀ r : ℕ, 0 < r → r ≤ d →
      ∀ (R : AxisBox r) (B : Finset (BoxPoint r)),
        widthThreshold ≤ R.minWidth →
        (0 : BoxPoint r) ∈ B → B ⊆ R.carrier →
        1 * R.volume ≤ C * B.card →
        ∃ cert : Corollary217Certificate R B,
          cert.constant ≤ corollaryConstant)
    (hlarge : max (2 ^ corollaryConstant) widthThreshold ≤
      2 ^ (y + 1)) :
    ∃ rank, ∃ V : Lemma222BlockApproximation A rank d,
      V.blockExponent = y + 1 ∧
        V.coverExponent ≤ corollaryConstant := by
  let Q := W.progression.centeredFirstDimensions hP d
  let hQ := W.progression.centeredFirstCertificate hP d
  let M := 2 ^ (y + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hscaled : ∀ x ∈ A, ∃ z : Fin (min W.rank d) → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x := by
    intro x hx
    simpa only [Q, hQ, M] using
      exists_scaled_centeredPrefix_representative_of_witness
        W hP hzero hC hx
  obtain ⟨B, hBcard, hzeroB, hBQ, hmap, hsurj⟩ :=
    exists_wideCoordinateSet_multifold_of_scaled
      Q hQ hprefixProper hM hzero hscaled
  have hdensity : (Q.wideAxisBox hQ M hM).volume ≤ C * B.card := by
    calc
      (Q.wideAxisBox hQ M hM).volume ≤ Q.volume :=
        Q.wideAxisBox_volume_le_volume hQ M hM
      _ ≤ C * (multifoldSumset M A).card := by
        simpa only [Q, M] using hprefixVolume
      _ = C * B.card := by rw [hBcard]
  have hwideLe : Q.wideRank M ≤ min W.rank d := by
    simpa only [GAP.wideRank, Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin (min W.rank d) ↦
        M ≤ Q.widths i)
  have hwideLeD : Q.wideRank M ≤ d :=
    hwideLe.trans (min_le_right W.rank d)
  have hC₁M : 2 ^ corollaryConstant ≤ M :=
    (Nat.le_max_left _ _).trans hlarge
  have hwidthM : widthThreshold ≤ M :=
    (Nat.le_max_right _ _).trans hlarge
  have hminWidth : widthThreshold ≤ (Q.wideAxisBox hQ M hM).minWidth :=
    hwidthM.trans (Q.wideAxisBox_minWidth hQ M hM hwide)
  obtain ⟨cert, hcertC⟩ := hcor (Q.wideRank M) hwide hwideLeD
    (Q.wideAxisBox hQ M hM) B hminWidth hzeroB hBQ
    (by simpa using hdensity)
  have hcertCpos : 0 < cert.constant := cert.constant_pos
  let D := 2 ^ cert.constant
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hcertDM : D ≤ M := by
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hcertC).trans hC₁M
  have hcertExp : cert.constant ≤ y + 1 := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ (2 : ℕ))).mp
    simpa only [D, M] using hcertDM
  have hDdvdM : D ∣ M := by
    refine ⟨2 ^ (y + 1 - cert.constant), ?_⟩
    dsimp [D, M]
    rw [← pow_add, Nat.add_comm cert.constant,
      Nat.sub_add_cancel hcertExp]
  have hcert_le_D : cert.constant ≤ D := by
    dsimp [D]
    induction cert.constant with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hp : 0 < 2 ^ n := by positivity
        omega
  let v := Q.wideSteps M
  let Pfull :=
    (GAP.basisContraction cert.basis cert.radius M).imageUnderSteps v
  let P := Pfull.activeDimensions
  let initialScale := M / D
  have hcoarse :
      (GAP.imageUnderSteps v
        (GAP.basisContraction cert.basis cert.radius cert.constant)).Proper := by
    apply image_basisContraction_proper_of_corollary217 cert v
    intro z hz hzeroEval
    exact Q.wideSteps_kernel_of_proper hQ hprefixProper M hM z hz hzeroEval
  have hscale : ∀ i,
      initialScale * (cert.radius i / M) ≤
        cert.radius i / cert.constant := by
    intro i
    apply (Nat.le_div_iff_mul_le hcertCpos).2
    calc
      initialScale * (cert.radius i / M) * cert.constant ≤
          initialScale * (cert.radius i / M) * D := by
        gcongr
      _ = (initialScale * D) * (cert.radius i / M) := by ring
      _ ≤ M * (cert.radius i / M) := by
        exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self M D)
      _ ≤ cert.radius i := Nat.mul_div_le _ _
  have hfullProper : (Pfull.dilate initialScale).Proper := by
    dsimp [Pfull, initialScale]
    exact GAP.image_basisContraction_dilate_proper_of_le
      cert.basis cert.radius M cert.constant (M / D) v
      hcoarse hscale
  have hproper : (P.dilate initialScale).Proper := by
    exact GAP.dilate_activeDimensions_proper Pfull initialScale hfullProper
  have hinitialPos : 0 < initialScale := by
    exact Nat.div_pos hcertDM hDpos
  have hinitialMul : initialScale * D = M := by
    dsimp [initialScale]
    exact Nat.div_mul_cancel hDdvdM
  have hcontains : A ⊆ BiluFreiman.integerCarrier P := by
    dsimp [P, Pfull, v]
    exact active_basisContraction_contains_of_corollary217
      Q hQ hprefixProper hM hzero hscaled B hBQ hsurj cert
  have hfullCover := basisContraction_blockCovered_of_corollary217 (M := M)
    cert v (multifoldSumset M A) hmap
  have hcover : translate
      (BiluFreiman.pointInteger (GAP.evaluateSteps v cert.sumTranslate))
      (BiluFreiman.integerCarrier (P.dilate M)) ⊆
      multifoldSumset (D * M) A := by
    rw [← multifoldSumset_multifold]
    intro x hx
    apply multifoldSumset_mono_index
      (zero_mem_multifoldSumset hzero M) hcert_le_D
    apply hfullCover
    rw [mem_translate_iff] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨a, ?_, rfl⟩
    apply BiluFreiman.mem_integerCarrier_iff.mpr
    apply GAP.dilate_activeDimensions_carrier_subset_dilate Pfull M
    exact BiluFreiman.mem_integerCarrier_iff.mp ha
  refine ⟨Pfull.activeRank, {
    rank_le := (Pfull.activeRank_le).trans
      (hwideLe.trans (min_le_right W.rank d))
    progression := P
    zero_mem := hzero
    contains := hcontains
    nondegenerate := Pfull.activeDimensions_nondegenerate
    blockExponent := y + 1
    blockScale := M
    blockScale_eq := by rfl
    blockScale_pos := hM
    coverExponent := cert.constant
    coverMultiplier := D
    coverMultiplier_eq := by rfl
    coverMultiplier_pos := hDpos
    blockTranslate :=
      BiluFreiman.pointInteger (GAP.evaluateSteps v cert.sumTranslate)
    blockCovered := hcover
    initialProperScale := initialScale
    initialProperScale_pos := hinitialPos
    initialProperScale_mul_cover := hinitialMul
    initialProper := hproper }, rfl, hcertC⟩

/-- Fixed-constant zero/positive-rank wrapper.  This is the form consumed by
the outer Bilu theorem, where every constant has already been chosen before
the set and its inverse-theorem witness. -/
theorem lemma222BlockApproximation_of_biluPrefix_allRanks_of_uniformCorollary217
    {A : Finset ℤ} {y d C : ℕ}
    (W : BiluFreiman.Witness 2 d C
      (multifoldSumset (2 ^ y) A))
    (hP : CenteredCertificate W.progression)
    (hzero : 0 ∈ A) (hCpos : 0 < C) (hC : C < 2 ^ (y + 1))
    (hprefixProper :
      (W.progression.centeredFirstDimensions hP d).Proper)
    (hprefixVolume :
      (W.progression.centeredFirstDimensions hP d).volume ≤
        C * (multifoldSumset (2 ^ (y + 1)) A).card)
    (corollaryConstant widthThreshold : ℕ)
    (hcorollaryConstant : 0 < corollaryConstant)
    (hcor : ∀ r : ℕ, 0 < r → r ≤ d →
      ∀ (R : AxisBox r) (B : Finset (BoxPoint r)),
        widthThreshold ≤ R.minWidth →
        (0 : BoxPoint r) ∈ B → B ⊆ R.carrier →
        1 * R.volume ≤ C * B.card →
        ∃ cert : Corollary217Certificate R B,
          cert.constant ≤ corollaryConstant)
    (hlarge : max (2 ^ corollaryConstant) widthThreshold ≤
      2 ^ (y + 1)) :
    ∃ rank, ∃ V : Lemma222BlockApproximation A rank d,
      V.coverExponent ≤ corollaryConstant := by
  let Q := W.progression.centeredFirstDimensions hP d
  let hQ := W.progression.centeredFirstCertificate hP d
  let M := 2 ^ (y + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  by_cases hwideZero : Q.wideRank M = 0
  · have hscaled : ∀ x ∈ A, ∃ z : Fin (min W.rank d) → ℤ,
        hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
          hQ.relativePoint z = BiluFreiman.integerPoint x := by
      intro x hx
      simpa only [Q, hQ, M] using
        exists_scaled_centeredPrefix_representative_of_witness
          W hP hzero hC hx
    obtain ⟨V, hVExponent⟩ :=
      exists_lemma222BlockApproximation_of_wideRank_eq_zero
        Q hQ hM hzero hscaled hwideZero
    exact ⟨0, V, hVExponent.le.trans (Nat.zero_le corollaryConstant)⟩
  · have hwide : 0 <
        (W.progression.centeredFirstDimensions hP d).wideRank
          (2 ^ (y + 1)) := by
      simpa only [Q, M] using Nat.pos_of_ne_zero hwideZero
    obtain ⟨rank, V, _hblockExponent, hcoverExponent⟩ :=
      lemma222BlockApproximation_of_biluPrefix_of_uniformCorollary217
        W hP hzero hCpos hC hprefixProper hprefixVolume hwide
        corollaryConstant widthThreshold hcorollaryConstant hcor hlarge
    exact ⟨rank, V, hcoverExponent⟩

/-- Existential-constant presentation of the positive-rank block
approximation.  The fixed-constant theorem above is the version used when
the constants must be chosen before the Bilu witness. -/
theorem exists_lemma222BlockApproximation_of_biluPrefix
    {A : Finset ℤ} {y d C : ℕ}
    (W : BiluFreiman.Witness 2 d C
      (multifoldSumset (2 ^ y) A))
    (hP : CenteredCertificate W.progression)
    (hzero : 0 ∈ A) (hCpos : 0 < C) (hC : C < 2 ^ (y + 1))
    (hprefixProper :
      (W.progression.centeredFirstDimensions hP d).Proper)
    (hprefixVolume :
      (W.progression.centeredFirstDimensions hP d).volume ≤
        C * (multifoldSumset (2 ^ (y + 1)) A).card)
    (hwide : 0 < (W.progression.centeredFirstDimensions hP d).wideRank
      (2 ^ (y + 1))) :
    ∃ threshold : ℕ, 0 < threshold ∧
      ∀ (_hlarge : threshold ≤ 2 ^ (y + 1)),
        ∃ rank, Nonempty (Lemma222BlockApproximation A rank d) := by
  obtain ⟨corollaryConstant, widthThreshold, hconstant,
      _hwidth, hcor⟩ :=
    exists_uniform_corollary217Certificate d 1 C
      (by simp) (by omega)
  let threshold := max (2 ^ corollaryConstant) widthThreshold
  have hthreshold : 0 < threshold :=
    (by positivity : 0 < 2 ^ corollaryConstant).trans_le
      (Nat.le_max_left _ _)
  refine ⟨threshold, hthreshold, ?_⟩
  intro hlarge
  obtain ⟨rank, V, _hblockExponent, _hbound⟩ :=
    lemma222BlockApproximation_of_biluPrefix_of_uniformCorollary217
    W hP hzero hCpos hC hprefixProper hprefixVolume hwide
    corollaryConstant widthThreshold hconstant hcor hlarge
  exact ⟨rank, ⟨V⟩⟩

/-- Complete finite-rank wrapper for the structural part of Lemma 2.22.
The positive-wide-rank branch is Corollary 2.17; the zero branch is the
rank-zero GAP constructed above, so no nonemptiness hypothesis on the
surviving set of directions is hidden in the conclusion. -/
theorem exists_lemma222BlockApproximation_of_biluPrefix_allRanks
    {A : Finset ℤ} {y d C : ℕ}
    (W : BiluFreiman.Witness 2 d C
      (multifoldSumset (2 ^ y) A))
    (hP : CenteredCertificate W.progression)
    (hzero : 0 ∈ A) (hCpos : 0 < C) (hC : C < 2 ^ (y + 1))
    (hprefixProper :
      (W.progression.centeredFirstDimensions hP d).Proper)
    (hprefixVolume :
      (W.progression.centeredFirstDimensions hP d).volume ≤
        C * (multifoldSumset (2 ^ (y + 1)) A).card) :
    ∃ threshold : ℕ, 0 < threshold ∧
      ∀ (_hlarge : threshold ≤ 2 ^ (y + 1)),
        ∃ rank, Nonempty (Lemma222BlockApproximation A rank d) := by
  let Q := W.progression.centeredFirstDimensions hP d
  let hQ := W.progression.centeredFirstCertificate hP d
  let M := 2 ^ (y + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  by_cases hwideZero : Q.wideRank M = 0
  · have hscaled : ∀ x ∈ A, ∃ z : Fin (min W.rank d) → ℤ,
        hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
          hQ.relativePoint z = BiluFreiman.integerPoint x := by
      intro x hx
      simpa only [Q, hQ, M] using
        exists_scaled_centeredPrefix_representative_of_witness
          W hP hzero hC hx
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    intro _hlarge
    refine ⟨0, ?_⟩
    obtain ⟨V, _hVExponent⟩ :=
      exists_lemma222BlockApproximation_of_wideRank_eq_zero
        Q hQ hM hzero hscaled hwideZero
    exact ⟨V⟩
  · have hwide : 0 <
        (W.progression.centeredFirstDimensions hP d).wideRank
          (2 ^ (y + 1)) := by
      simpa only [Q, M] using Nat.pos_of_ne_zero hwideZero
    exact exists_lemma222BlockApproximation_of_biluPrefix
      W hP hzero hCpos hC hprefixProper hprefixVolume hwide

/-- A dyadic slow-growth step gives the complete structural/block-cover
part of CFP Lemma 2.22.  The Bilu constant and the single block-size
threshold are chosen before `A`; the latter simultaneously dominates the
Bilu tail and every Corollary 2.17 constant for ranks at most `d`. -/
theorem exists_lemma222BlockApproximation_at_dyadic_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (d : ℕ) (hd : 0 < d) :
    ∃ biluConstant blockThreshold coverExponentBound : ℕ,
      0 < biluConstant ∧ 0 < blockThreshold ∧
      0 < coverExponentBound ∧
      ∀ {A : Finset ℤ}, 0 ∈ A → ∀ y : ℕ,
        blockThreshold ≤ 2 ^ (y + 1) →
        ((multifoldSumset (2 ^ (y + 1)) A).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - (1 : ℝ) / 2) *
            (multifoldSumset (2 ^ y) A).card →
        ∃ rank, ∃ V : Lemma222BlockApproximation A rank d,
          V.coverExponent ≤ coverExponentBound := by
  obtain ⟨biluConstant, hBiluConstant, hBilu⟩ :=
    hBF 2 d (by omega) hd ((1 : ℝ) / 2) (by norm_num)
  obtain ⟨corollaryConstant, widthThreshold, hcorollaryConstant,
      _hwidthThreshold, hcor⟩ :=
    exists_uniform_corollary217Certificate d 1 biluConstant
      (by simp) (by omega)
  let blockThreshold :=
    max (biluConstant + 1) (max (2 ^ corollaryConstant) widthThreshold)
  refine ⟨biluConstant, blockThreshold, corollaryConstant, hBiluConstant,
    (Nat.zero_lt_succ biluConstant).trans_le (Nat.le_max_left _ _),
    hcorollaryConstant, ?_⟩
  intro A hzero y hlarge hgrowth
  have hnonempty : (multifoldSumset (2 ^ y) A).Nonempty :=
    ⟨0, zero_mem_multifoldSumset hzero (2 ^ y)⟩
  have hdouble :
      ((BiluFreiman.twoA (multifoldSumset (2 ^ y) A)).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - (1 : ℝ) / 2) *
          (multifoldSumset (2 ^ y) A).card := by
    rw [twoA_multifoldSumset]
    simpa [pow_succ, mul_comm] using hgrowth
  obtain ⟨W⟩ := hBilu (multifoldSumset (2 ^ y) A)
    hnonempty hdouble
  have hBiluSmall : biluConstant < 2 ^ (y + 1) := by
    have hsucc : biluConstant + 1 ≤ 2 ^ (y + 1) :=
      (Nat.le_max_left _ _).trans hlarge
    omega
  obtain ⟨hP, hprefixProper, _hzeroPrefix, _hblockSubset,
      hprefixVolume⟩ :=
    exists_centered_biluPrefix_of_witness W hzero hBiluSmall
  have hcorLarge : max (2 ^ corollaryConstant) widthThreshold ≤
      2 ^ (y + 1) := (Nat.le_max_right _ _).trans hlarge
  exact
    lemma222BlockApproximation_of_biluPrefix_allRanks_of_uniformCorollary217
      W hP hzero hBiluConstant hBiluSmall hprefixProper hprefixVolume
      corollaryConstant widthThreshold hcorollaryConstant hcor hcorLarge

/-- Nontrivial-set refinement of the dyadic Bilu construction.  It records
that the returned block exponent is exactly the selected slow-growth scale,
which is needed by the source global-interval argument. -/
theorem exists_lemma222BlockApproximation_at_dyadic_of_biluFreiman_nontrivial
    (hBF : BiluFreiman.BiluFreimanStatement) (d : ℕ) (hd : 0 < d) :
    ∃ biluConstant blockThreshold coverExponentBound : ℕ,
      0 < biluConstant ∧ 0 < blockThreshold ∧
      0 < coverExponentBound ∧
      ∀ {A : Finset ℤ}, 0 ∈ A → (∃ x ∈ A, x ≠ 0) → ∀ y : ℕ,
        blockThreshold ≤ 2 ^ (y + 1) →
        ((multifoldSumset (2 ^ (y + 1)) A).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - (1 : ℝ) / 2) *
            (multifoldSumset (2 ^ y) A).card →
        ∃ rank, ∃ V : Lemma222BlockApproximation A rank d,
          V.blockExponent = y + 1 ∧
            V.coverExponent ≤ coverExponentBound := by
  obtain ⟨biluConstant, hBiluConstant, hBilu⟩ :=
    hBF 2 d (by omega) hd ((1 : ℝ) / 2) (by norm_num)
  obtain ⟨corollaryConstant, widthThreshold, hcorollaryConstant,
      _hwidthThreshold, hcor⟩ :=
    exists_uniform_corollary217Certificate d 1 biluConstant
      (by simp) (by omega)
  let blockThreshold :=
    max (biluConstant + 1) (max (2 ^ corollaryConstant) widthThreshold)
  refine ⟨biluConstant, blockThreshold, corollaryConstant, hBiluConstant,
    (Nat.zero_lt_succ biluConstant).trans_le (Nat.le_max_left _ _),
    hcorollaryConstant, ?_⟩
  intro A hzero hne y hlarge hgrowth
  have hnonempty : (multifoldSumset (2 ^ y) A).Nonempty :=
    ⟨0, zero_mem_multifoldSumset hzero (2 ^ y)⟩
  have hdouble :
      ((BiluFreiman.twoA (multifoldSumset (2 ^ y) A)).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - (1 : ℝ) / 2) *
          (multifoldSumset (2 ^ y) A).card := by
    rw [twoA_multifoldSumset]
    simpa [pow_succ, mul_comm] using hgrowth
  obtain ⟨W⟩ := hBilu (multifoldSumset (2 ^ y) A) hnonempty hdouble
  have hBiluSmall : biluConstant < 2 ^ (y + 1) := by
    have hsucc : biluConstant + 1 ≤ 2 ^ (y + 1) :=
      (Nat.le_max_left _ _).trans hlarge
    omega
  obtain ⟨hP, hprefixProper, _hzeroPrefix, _hblockSubset,
      hprefixVolume⟩ :=
    exists_centered_biluPrefix_of_witness W hzero hBiluSmall
  let Q := W.progression.centeredFirstDimensions hP d
  let hQ := W.progression.centeredFirstCertificate hP d
  let M := 2 ^ (y + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hscaled : ∀ x ∈ A, ∃ z : Fin (min W.rank d) → ℤ,
      hQ.InBox (fun i ↦ (M : ℤ) * z i) ∧
        hQ.relativePoint z = BiluFreiman.integerPoint x := by
    intro x hx
    simpa only [Q, hQ, M] using
      exists_scaled_centeredPrefix_representative_of_witness
        W hP hzero hBiluSmall hx
  have hwide : 0 <
      (W.progression.centeredFirstDimensions hP d).wideRank
        (2 ^ (y + 1)) := by
    simpa only [Q, M] using
      wideRank_pos_of_scaled_of_exists_ne_zero Q hQ hM hscaled hne
  have hcorLarge : max (2 ^ corollaryConstant) widthThreshold ≤
      2 ^ (y + 1) := (Nat.le_max_right _ _).trans hlarge
  exact lemma222BlockApproximation_of_biluPrefix_of_uniformCorollary217
    W hP hzero hBiluConstant hBiluSmall hprefixProper hprefixVolume hwide
    corollaryConstant widthThreshold hcorollaryConstant hcor hcorLarge

/-- The block threshold and dyadic cover-exponent bound can be chosen
uniformly for every positive slow-growth dimension up to a fixed bound. -/
theorem exists_uniform_lemma222BlockApproximation_at_dyadic_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (dimensionBound : ℕ) :
    ∃ blockThreshold coverExponentBound : ℕ,
      0 < blockThreshold ∧ 0 < coverExponentBound ∧
      ∀ d : ℕ, 0 < d → d ≤ dimensionBound →
        ∀ {A : Finset ℤ}, 0 ∈ A → ∀ y : ℕ,
          blockThreshold ≤ 2 ^ (y + 1) →
          ((multifoldSumset (2 ^ (y + 1)) A).card : ℝ) ≤
            Real.rpow 2 ((d : ℝ) + 1 - (1 : ℝ) / 2) *
              (multifoldSumset (2 ^ y) A).card →
          ∃ rank, ∃ V : Lemma222BlockApproximation A rank d,
            V.coverExponent ≤ coverExponentBound := by
  induction dimensionBound with
  | zero =>
      refine ⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one, ?_⟩
      intro d hd hbound
      omega
  | succ D ih =>
      obtain ⟨T₀, E₀, hT₀, hE₀, h₀⟩ := ih
      obtain ⟨_C, T₁, E₁, _hC, hT₁, hE₁, h₁⟩ :=
        exists_lemma222BlockApproximation_at_dyadic_of_biluFreiman
          hBF (D + 1) (Nat.zero_lt_succ D)
      refine ⟨max T₀ T₁, max E₀ E₁,
        hT₀.trans_le (Nat.le_max_left _ _),
        hE₀.trans_le (Nat.le_max_left _ _), ?_⟩
      intro d hd hbound A hzero y hlarge hgrowth
      rcases Nat.lt_or_eq_of_le hbound with hdlt | rfl
      · obtain ⟨rank, V, hV⟩ := h₀ d hd (Nat.lt_succ_iff.mp hdlt)
          hzero y ((Nat.le_max_left T₀ T₁).trans hlarge) hgrowth
        exact ⟨rank, V, hV.trans (Nat.le_max_left E₀ E₁)⟩
      · obtain ⟨rank, V, hV⟩ := h₁ hzero y
          ((Nat.le_max_right T₀ T₁).trans hlarge) hgrowth
        exact ⟨rank, V, hV.trans (Nat.le_max_right E₀ E₁)⟩

/-- Uniform nontrivial-set refinement, retaining the selected block
exponent through the finite maximum over all possible slow-growth
dimensions. -/
theorem exists_uniform_lemma222BlockApproximation_at_dyadic_of_biluFreiman_nontrivial
    (hBF : BiluFreiman.BiluFreimanStatement) (dimensionBound : ℕ) :
    ∃ blockThreshold coverExponentBound : ℕ,
      0 < blockThreshold ∧ 0 < coverExponentBound ∧
      ∀ d : ℕ, 0 < d → d ≤ dimensionBound →
        ∀ {A : Finset ℤ}, 0 ∈ A → (∃ x ∈ A, x ≠ 0) → ∀ y : ℕ,
          blockThreshold ≤ 2 ^ (y + 1) →
          ((multifoldSumset (2 ^ (y + 1)) A).card : ℝ) ≤
            Real.rpow 2 ((d : ℝ) + 1 - (1 : ℝ) / 2) *
              (multifoldSumset (2 ^ y) A).card →
          ∃ rank, ∃ V : Lemma222BlockApproximation A rank d,
            V.blockExponent = y + 1 ∧
              V.coverExponent ≤ coverExponentBound := by
  induction dimensionBound with
  | zero =>
      refine ⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one, ?_⟩
      intro d hd hbound
      omega
  | succ D ih =>
      obtain ⟨T₀, E₀, hT₀, hE₀, h₀⟩ := ih
      obtain ⟨_C, T₁, E₁, _hC, hT₁, hE₁, h₁⟩ :=
        exists_lemma222BlockApproximation_at_dyadic_of_biluFreiman_nontrivial
          hBF (D + 1) (Nat.zero_lt_succ D)
      refine ⟨max T₀ T₁, max E₀ E₁,
        hT₀.trans_le (Nat.le_max_left _ _),
        hE₀.trans_le (Nat.le_max_left _ _), ?_⟩
      intro d hd hbound A hzero hne y hlarge hgrowth
      rcases Nat.lt_or_eq_of_le hbound with hdlt | rfl
      · obtain ⟨rank, V, hblock, hcover⟩ :=
          h₀ d hd (Nat.lt_succ_iff.mp hdlt) hzero hne y
            ((Nat.le_max_left T₀ T₁).trans hlarge) hgrowth
        exact ⟨rank, V, hblock,
          hcover.trans (Nat.le_max_left E₀ E₁)⟩
      · obtain ⟨rank, V, hblock, hcover⟩ := h₁ hzero hne y
          ((Nat.le_max_right T₀ T₁).trans hlarge) hgrowth
        exact ⟨rank, V, hblock,
          hcover.trans (Nat.le_max_right E₀ E₁)⟩

/-- A dyadic slow-growth witness at dimension `d`, with the half exponent
removed by squaring:
`|2^(e+1)A| ≤ 2^(d+1/2)|2^eA|` is recorded as the displayed natural
number inequality. -/
def HasDyadicSquaredSlowGrowth
    (A : Finset ℤ) (dimension first last : ℕ) : Prop :=
  ∃ e, first ≤ e ∧ e < last ∧
    (multifoldSumset (2 ^ (e + 1)) A).card ^ 2 ≤
      2 ^ (2 * dimension + 1) *
        (multifoldSumset (2 ^ e) A).card ^ 2

/-- The squared natural-number slow-growth inequality implies exactly the
real `2^(d+1/2)` inequality required by the Bilu--Freiman interface. -/
theorem real_dyadicSlowGrowth_of_squared {A : Finset ℤ} {dimension e : ℕ}
    (hslow :
      (multifoldSumset (2 ^ (e + 1)) A).card ^ 2 ≤
        2 ^ (2 * dimension + 1) *
          (multifoldSumset (2 ^ e) A).card ^ 2) :
    ((multifoldSumset (2 ^ (e + 1)) A).card : ℝ) ≤
      Real.rpow 2 ((dimension : ℝ) + 1 - (1 : ℝ) / 2) *
        (multifoldSumset (2 ^ e) A).card := by
  let R : ℝ := Real.rpow 2 ((dimension : ℝ) + 1 - (1 : ℝ) / 2)
  have hRsq : R ^ 2 = ((2 ^ (2 * dimension + 1) : ℕ) : ℝ) := by
    calc
      R ^ 2 = R ^ (2 : ℝ) :=
        (Real.rpow_natCast R 2).symm
      _ = Real.rpow 2
          (((dimension : ℝ) + 1 - (1 : ℝ) / 2) * 2) := by
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = Real.rpow 2 ((2 * dimension + 1 : ℕ) : ℝ) := by
        congr 1
        push_cast
        ring
      _ = (2 : ℝ) ^ (2 * dimension + 1) :=
        Real.rpow_natCast 2 (2 * dimension + 1)
      _ = ((2 ^ (2 * dimension + 1) : ℕ) : ℝ) := by norm_num
  have hreal :
      ((multifoldSumset (2 ^ (e + 1)) A).card : ℝ) ^ 2 ≤
        ((2 ^ (2 * dimension + 1) : ℕ) : ℝ) *
          ((multifoldSumset (2 ^ e) A).card : ℝ) ^ 2 := by
    exact_mod_cast hslow
  rw [← hRsq, ← mul_pow] at hreal
  exact (sq_le_sq₀ (by positivity)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by positivity))).mp hreal

/-- Exact finite meaning of "`d₀` is the least dimension with a slow
dyadic step" in CFP Lemma 2.22. -/
def IsMinimalDyadicGrowthDimension
    (A : Finset ℤ) (dimension first last : ℕ) : Prop :=
  HasDyadicSquaredSlowGrowth A dimension first last ∧
    ∀ d, d < dimension →
      ¬ HasDyadicSquaredSlowGrowth A d first last

/-- On every nonempty dyadic interval, a set containing zero has a least
slow-growth dimension.  This discharges the existence implicit in the
source phrase "let `d₀` be the smallest integer". -/
theorem exists_minimalDyadicGrowthDimension
    {A : Finset ℤ} {first last : ℕ}
    (hzero : 0 ∈ A) (hinterval : first < last) :
    ∃ dimension,
      IsMinimalDyadicGrowthDimension A dimension first last := by
  classical
  let X := (multifoldSumset (2 ^ (first + 1)) A).card
  let Y := (multifoldSumset (2 ^ first) A).card
  have hY : 0 < Y := by
    apply Finset.card_pos.mpr
    exact ⟨0, zero_mem_multifoldSumset hzero (2 ^ first)⟩
  have hXpow : X ^ 2 ≤ 2 ^ (2 * X) := by
    calc
      X ^ 2 ≤ 2 * X ^ 2 + 1 := by omega
      _ ≤ 2 ^ (2 * X) := Nat.two_mul_sq_add_one_le_two_pow_two_mul X
  have hslowAtX : HasDyadicSquaredSlowGrowth A X first last := by
    refine ⟨first, Nat.le_refl first, hinterval, ?_⟩
    calc
      X ^ 2 ≤ 2 ^ (2 * X) := hXpow
      _ ≤ 2 ^ (2 * X + 1) :=
        Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      _ ≤ 2 ^ (2 * X + 1) * Y ^ 2 :=
        Nat.le_mul_of_pos_right _ (pow_pos hY 2)
  let hex : ∃ d, HasDyadicSquaredSlowGrowth A d first last := ⟨X, hslowAtX⟩
  let dimension := Nat.find hex
  refine ⟨dimension, Nat.find_spec hex, ?_⟩
  intro d hd
  apply Nat.find_min hex
  simpa only [dimension] using hd

/-- A nontrivial set cannot have slow-growth dimension zero.  This removes
the positivity side condition from the public source-facing theorem: it is
forced by leastness unless the input set is the singleton `{0}`. -/
theorem minimalDyadicGrowthDimension_pos_of_exists_ne_zero
    {A : Finset ℤ} {dimension first last : ℕ}
    (hzero : 0 ∈ A) (hne : ∃ x ∈ A, x ≠ 0)
    (hminimal : IsMinimalDyadicGrowthDimension A dimension first last) :
    0 < dimension := by
  by_contra hdimension
  have hdimensionZero : dimension = 0 := Nat.eq_zero_of_not_pos hdimension
  subst dimension
  obtain ⟨e, _hfirst, _hlast, hslow⟩ := hminimal.1
  let S := multifoldSumset (2 ^ e) A
  let T := multifoldSumset (2 ^ (e + 1)) A
  have hzeroS : 0 ∈ S := by
    exact zero_mem_multifoldSumset hzero (2 ^ e)
  obtain ⟨x, hx, hxne⟩ := hne
  have hxOne : x ∈ multifoldSumset 1 A := by
    simpa [multifoldSumset] using hx
  have hxS : x ∈ S := by
    exact multifoldSumset_mono_index hzero
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))) hxOne
  have hScard : 2 ≤ S.card := by
    have : 1 < S.card := Finset.one_lt_card.mpr
      ⟨0, hzeroS, x, hxS, Ne.symm hxne⟩
    omega
  have hSnonempty : S.Nonempty := ⟨0, hzeroS⟩
  have hdouble : 2 * S.card - 1 ≤ T.card := by
    have hcd := cauchy_davenport_of_isAddTorsionFree
      hSnonempty hSnonempty
    have hadd : S + S = sumset S S := by
      ext z
      simp only [Finset.mem_add, mem_sumset_iff]
    have hsumset : sumset S S = T := by
      calc
        sumset S S = multifoldSumset (2 ^ e + 2 ^ e) A := by
          simpa only [S] using (multifoldSumset_add (2 ^ e) (2 ^ e) A).symm
        _ = T := by
          dsimp only [T]
          apply congrArg (fun n ↦ multifoldSumset n A)
          rw [pow_succ]
          omega
    rw [hadd, hsumset] at hcd
    simpa only [two_mul] using hcd
  have hslow' : T.card ^ 2 ≤ 2 * S.card ^ 2 := by
    norm_num at hslow
    simpa only [T, S] using hslow
  have hdoubleSq := Nat.pow_le_pow_left hdouble 2
  have hsub : 2 * S.card - 1 + 1 = 2 * S.card :=
    Nat.sub_add_cancel (by omega)
  nlinarith

/-- Squared-cardinality form of the `d₀ - 1/2` lower growth forced by
minimality of `d₀`.  Squaring removes square roots and makes the finite
iteration entirely natural-number valued. -/
def DyadicLowerGrowth (A : Finset ℤ) (dimension first last : ℕ) : Prop :=
  ∀ e, first ≤ e → e < last →
    2 ^ (2 * dimension - 1) *
        (multifoldSumset (2 ^ e) A).card ^ 2 <
      (multifoldSumset (2 ^ (e + 1)) A).card ^ 2

/-- Minimality at dimension `d₀` gives the strict lower-growth inequality
at every scale by ruling out a slow step at `d₀ - 1`. -/
theorem dyadicLowerGrowth_of_minimalDimension
    {A : Finset ℤ} {dimension first last : ℕ}
    (hdimension : 0 < dimension)
    (hminimal : IsMinimalDyadicGrowthDimension
      A dimension first last) :
    DyadicLowerGrowth A dimension first last := by
  intro e hfirst hlast
  have hnot := hminimal.2 (dimension - 1) (by omega)
  by_contra hgrowth
  apply hnot
  refine ⟨e, hfirst, hlast, ?_⟩
  have hexponent : 2 * (dimension - 1) + 1 = 2 * dimension - 1 := by
    omega
  rw [hexponent]
  exact Nat.le_of_not_gt hgrowth

/-- Iteration of the exact squared lower-growth inequality. -/
theorem dyadicLowerGrowth_iterate {A : Finset ℤ} {dimension start steps : ℕ}
    (hsteps : 0 < steps)
    (hgrowth : DyadicLowerGrowth A dimension start (start + steps)) :
    (2 ^ (2 * dimension - 1)) ^ steps *
        (multifoldSumset (2 ^ start) A).card ^ 2 <
      (multifoldSumset (2 ^ (start + steps)) A).card ^ 2 := by
  induction steps with
  | zero => omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [DyadicLowerGrowth] using
          hgrowth start (Nat.le_refl start) (by omega)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hgrowth' : DyadicLowerGrowth A dimension start (start + n) := by
          intro e hstart he
          exact hgrowth e hstart (by omega)
        have hih := ih hnpos hgrowth'
        have hlast := hgrowth (start + n) (by omega) (by omega)
        have hfactor : 0 < 2 ^ (2 * dimension - 1) := by positivity
        calc
          (2 ^ (2 * dimension - 1)) ^ (n + 1) *
                (multifoldSumset (2 ^ start) A).card ^ 2 =
              2 ^ (2 * dimension - 1) *
                ((2 ^ (2 * dimension - 1)) ^ n *
                  (multifoldSumset (2 ^ start) A).card ^ 2) := by
            rw [pow_succ]
            ring
          _ < 2 ^ (2 * dimension - 1) *
                (multifoldSumset (2 ^ (start + n)) A).card ^ 2 :=
            Nat.mul_lt_mul_of_pos_left hih hfactor
          _ < (multifoldSumset (2 ^ (start + (n + 1))) A).card ^ 2 := by
            simpa [add_assoc] using hlast

/-- A dimension- and cover-exponent-only terminal interval length for the
maximal-proper-scale contradiction. -/
def terminalGrowthSteps (rankBound coverExponentBound : ℕ) : ℕ :=
  4 * rankBound + 4 * coverExponentBound * rankBound + 1

theorem terminalGrowthSteps_pos (rankBound coverExponentBound : ℕ) :
    0 < terminalGrowthSteps rankBound coverExponentBound := by
  simp only [terminalGrowthSteps]
  omega

/-- The explicit terminal length uniformly discharges the numerical
inequality in the maximal-proper-scale argument for every output rank and
cover exponent below their fixed bounds. -/
theorem terminalGrowthSteps_numeric
    {rank rankBound coverExponent coverExponentBound : ℕ}
    (hrank : rank ≤ rankBound)
    (hcover : coverExponent ≤ coverExponentBound) :
    ((rank * 2 ^ rank) *
        (2 ^ (2 * coverExponent +
          terminalGrowthSteps rankBound coverExponentBound)) ^
            (rank - 1)) ^ 2 ≤
      (2 ^ (2 * rankBound - 1)) ^
        terminalGrowthSteps rankBound coverExponentBound := by
  let steps := terminalGrowthSteps rankBound coverExponentBound
  by_cases hrankZero : rank = 0
  · subst rank
    simp
  have hrankPos : 0 < rank := Nat.pos_of_ne_zero hrankZero
  have hrankPower : rank * 2 ^ rank ≤ 2 ^ (2 * rank) := by
    calc
      rank * 2 ^ rank ≤ 2 ^ rank * 2 ^ rank := by
        gcongr
        exact (Nat.lt_two_pow_self).le
      _ = 2 ^ (2 * rank) := by
        rw [← pow_add]
        congr 1
        omega
  have hfactor :
      (2 ^ (2 * coverExponent + steps)) ^ (rank - 1) =
        2 ^ ((2 * coverExponent + steps) * (rank - 1)) := by
    exact (Nat.pow_mul 2 (2 * coverExponent + steps) (rank - 1)).symm
  have hinside :
      (rank * 2 ^ rank) *
          (2 ^ (2 * coverExponent + steps)) ^ (rank - 1) ≤
        2 ^ (2 * rank +
          (2 * coverExponent + steps) * (rank - 1)) := by
    rw [hfactor, pow_add]
    exact Nat.mul_le_mul_right _ hrankPower
  have hexponent :
      2 * (2 * rank + (2 * coverExponent + steps) * (rank - 1)) ≤
        (2 * rankBound - 1) * steps := by
    dsimp [steps, terminalGrowthSteps]
    cases rank with
    | zero => contradiction
    | succ r =>
        cases rankBound with
        | zero => omega
        | succ d =>
            have hrd : r ≤ d := by omega
            let s := 4 * (d + 1) +
              4 * coverExponentBound * (d + 1) + 1
            have hsum : 2 * coverExponent + s ≤
                2 * coverExponentBound + s := by
              dsimp [s]
              omega
            have hprod : (2 * coverExponent + s) * r ≤
                (2 * coverExponentBound + s) * d :=
              Nat.mul_le_mul hsum hrd
            have hfirst :
                2 * (2 * (r + 1) + (2 * coverExponent + s) * r) ≤
                  2 * (2 * (d + 1) +
                    (2 * coverExponentBound + s) * d) := by
              omega
            have hfinal :
                2 * (2 * (d + 1) +
                    (2 * coverExponentBound + s) * d) ≤
                  (2 * (d + 1) - 1) * s := by
              rw [show 2 * (d + 1) - 1 = 2 * d + 1 by omega]
              dsimp [s]
              nlinarith
            exact hfirst.trans hfinal
  change
    ((rank * 2 ^ rank) *
        (2 ^ (2 * coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
      (2 ^ (2 * rankBound - 1)) ^ steps
  calc
    ((rank * 2 ^ rank) *
        (2 ^ (2 * coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rank +
          (2 * coverExponent + steps) * (rank - 1))) ^ 2 :=
      Nat.pow_le_pow_left hinside 2
    _ = 2 ^ (2 * (2 * rank +
          (2 * coverExponent + steps) * (rank - 1))) := by
      rw [show 2 * (2 * rank +
          (2 * coverExponent + steps) * (rank - 1)) =
        (2 * rank + (2 * coverExponent + steps) * (rank - 1)) * 2 by ring,
        Nat.pow_mul]
    _ ≤ 2 ^ ((2 * rankBound - 1) * steps) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hexponent
    _ = (2 ^ (2 * rankBound - 1)) ^ steps := Nat.pow_mul _ _ _

/-- A covered translate can be repeated any number of times. -/
theorem iterate_translate_subset {A S : Finset ℤ} {m : ℕ} {t : ℤ}
    (hcover : translate t S ⊆ multifoldSumset m A) (k : ℕ) :
    translate ((k : ℤ) * t) (multifoldSumset k S) ⊆
      multifoldSumset (k * m) A := by
  have hmono := multifoldSumset_mono_set k hcover
  rwa [multifoldSumset_translate, multifoldSumset_multifold] at hmono

/-- Integer carriers commute exactly with integral GAP dilation. -/
theorem integerCarrier_dilate_eq_multifoldSumset {r : ℕ}
    (P : GAP 1 r) (k : ℕ) :
    BiluFreiman.integerCarrier (P.dilate k) =
      multifoldSumset k (BiluFreiman.integerCarrier P) := by
  classical
  rw [multifoldSumset_eq_nsmul, BiluFreiman.integerCarrier]
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [dilate_carrier_eq_nsmul_carrier, Finset.mem_nsmul] at hx
    obtain ⟨points, hpoints⟩ := hx
    let values : Fin k → {a // a ∈ P.carrier.image BiluFreiman.pointInteger} :=
      fun i ↦ ⟨BiluFreiman.pointInteger (points i),
        Finset.mem_image.mpr ⟨points i, (points i).property, rfl⟩⟩
    apply Finset.mem_nsmul.mpr
    refine ⟨values, ?_⟩
    rw [List.sum_ofFn, ← BiluFreiman.pointInteger_integerPoint
      (∑ i, (values i : ℤ))]
    apply congrArg BiluFreiman.pointInteger
    have hpoints' : (∑ i, (points i : LatticePoint 1)) = x := by
      simpa only [List.sum_ofFn] using hpoints
    rw [← hpoints']
    funext j
    simp only [Finset.sum_apply, values, BiluFreiman.integerPoint]
    apply Finset.sum_congr rfl
    intro i _hi
    exact congrArg (points i : LatticePoint 1) (Subsingleton.elim 0 j)
  · intro hz
    rw [Finset.mem_nsmul] at hz
    obtain ⟨values, hvalues⟩ := hz
    let points : Fin k → {x // x ∈ P.carrier} := fun i ↦
      ⟨BiluFreiman.integerPoint (values i),
        BiluFreiman.mem_integerCarrier_iff.mp (values i).property⟩
    have hpoints :
        (List.ofFn (fun i ↦ (points i : LatticePoint 1))).sum =
          BiluFreiman.integerPoint z := by
      funext j
      rw [List.sum_ofFn]
      simp only [Finset.sum_apply, points, BiluFreiman.integerPoint]
      rw [← List.sum_ofFn]
      exact congrArg (fun w : ℤ ↦ w) hvalues
    refine ⟨BiluFreiman.integerPoint z, ?_, BiluFreiman.pointInteger_integerPoint z⟩
    rw [dilate_carrier_eq_nsmul_carrier, Finset.mem_nsmul]
    exact ⟨points, hpoints⟩

/-- Evaluating the sum-coordinate in the exact dilation gives the sum of
the represented points. -/
theorem coordPoint_totalCoordInDilate_self {r k : ℕ} (P : GAP 1 r)
    (a : Fin k → P.Coord) :
    (P.dilate k).coordPoint (P.totalCoordInDilate (Nat.le_refl k) a) =
      P.tuplePointSum a := by
  rw [P.tuplePointSum_eq]
  funext j
  simp only [GAP.coordPoint, GAP.dilate_offset,
    GAP.dilate_steps, GAP.totalCoordInDilate_apply]

/-- If `A` is contained in a GAP, its `h`-fold sumset is contained in the
integer carrier of the displayed `h`-dilation.  This is the easy inclusion
`hA ⊆ hP` in Corollary 2.24. -/
theorem multifoldSumset_subset_integerCarrier_dilate {r h : ℕ}
    {A : Finset ℤ} (P : GAP 1 r)
    (hA : A ⊆ BiluFreiman.integerCarrier P) :
    multifoldSumset h A ⊆ BiluFreiman.integerCarrier (P.dilate h) := by
  intro x hx
  obtain ⟨f, hfA, hsum⟩ := mem_multifoldSumset_iff.mp hx
  have hfcarrier (i : Fin h) : BiluFreiman.integerPoint (f i) ∈ P.carrier :=
    BiluFreiman.mem_integerCarrier_iff.mp (hA (hfA i))
  let a : Fin h → P.Coord := fun i ↦
    Classical.choose (GAP.mem_carrier_iff.mp (hfcarrier i))
  have ha (i : Fin h) : P.coordPoint (a i) = BiluFreiman.integerPoint (f i) :=
    Classical.choose_spec (GAP.mem_carrier_iff.mp (hfcarrier i))
  apply BiluFreiman.mem_integerCarrier_iff.mpr
  rw [← hsum]
  refine GAP.mem_carrier_iff.mpr
    ⟨P.totalCoordInDilate (Nat.le_refl h) a, ?_⟩
  rw [coordPoint_totalCoordInDilate_self P a]
  funext j
  simp only [GAP.tuplePointSum, Finset.sum_apply, ha,
    BiluFreiman.integerPoint]

namespace Lemma222BlockApproximation

variable {A : Finset ℤ} {rank rankBound : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)

/-- Repeating the covered block and using downward monotonicity bounds the
cardinality at every dyadic proper scale by a later dyadic sumset. -/
theorem card_initial_dyadic_dilate_le (u : ℕ) :
    (W.progression.dilate
        (W.initialProperScale * 2 ^ u)).carrier.card ≤
      (multifoldSumset
        (2 ^ (W.blockExponent + W.coverExponent + u)) A).card := by
  let q := 2 ^ u
  have hzeroP : 0 ∈ BiluFreiman.integerCarrier W.progression :=
    W.contains W.zero_mem
  have hinitialLe : W.initialProperScale ≤ W.blockScale := by
    rw [← W.initialProperScale_mul_cover]
    exact Nat.le_mul_of_pos_right _ W.coverMultiplier_pos
  have hscale : W.initialProperScale * q ≤ q * W.blockScale := by
    calc
      W.initialProperScale * q ≤ W.blockScale * q := by gcongr
      _ = q * W.blockScale := by ring
  have hsmall :
      BiluFreiman.integerCarrier
          (W.progression.dilate (W.initialProperScale * q)) ⊆
        BiluFreiman.integerCarrier
          (W.progression.dilate (q * W.blockScale)) := by
    rw [integerCarrier_dilate_eq_multifoldSumset,
      integerCarrier_dilate_eq_multifoldSumset]
    exact multifoldSumset_mono_index hzeroP hscale
  have hiter := iterate_translate_subset W.blockCovered q
  have hiter' :
      translate ((q : ℤ) * W.blockTranslate)
          (BiluFreiman.integerCarrier
            (W.progression.dilate (q * W.blockScale))) ⊆
        multifoldSumset (q * (W.coverMultiplier * W.blockScale)) A := by
    simpa only [← integerCarrier_dilate_eq_multifoldSumset,
      GAP.dilate_dilate] using hiter
  have hindex : q * (W.coverMultiplier * W.blockScale) =
      2 ^ (W.blockExponent + W.coverExponent + u) := by
    dsimp [q]
    rw [W.coverMultiplier_eq, W.blockScale_eq,
      ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    (W.progression.dilate
        (W.initialProperScale * 2 ^ u)).carrier.card =
        (BiluFreiman.integerCarrier
          (W.progression.dilate (W.initialProperScale * q))).card := by
      rw [BiluFreiman.card_integerCarrier]
    _ ≤ (BiluFreiman.integerCarrier
          (W.progression.dilate (q * W.blockScale))).card :=
      Finset.card_le_card hsmall
    _ = (translate ((q : ℤ) * W.blockTranslate)
          (BiluFreiman.integerCarrier
            (W.progression.dilate (q * W.blockScale)))).card := by
      rw [card_translate]
    _ ≤ (multifoldSumset
          (q * (W.coverMultiplier * W.blockScale)) A).card :=
      Finset.card_le_card hiter'
    _ = (multifoldSumset
          (2 ^ (W.blockExponent + W.coverExponent + u)) A).card := by
      rw [hindex]

/-- The sumset at the far end of the growth interval lies in the large
dilation to which Corollary 2.21 is applied. -/
theorem card_dyadic_sumset_le_large_dilate (u steps : ℕ) :
    (multifoldSumset
        (2 ^ (W.blockExponent + W.coverExponent + u + steps)) A).card ≤
      ((W.progression.dilate
          (W.initialProperScale * 2 ^ u)).dilate
            (2 ^ (2 * W.coverExponent + steps))).carrier.card := by
  have hscale :
      2 ^ (W.blockExponent + W.coverExponent + u + steps) =
        2 ^ (2 * W.coverExponent + steps) *
          (W.initialProperScale * 2 ^ u) := by
    have hcoverLe := W.coverExponent_le_blockExponent
    rw [W.initialProperScale_eq_pow_sub,
      ← pow_add, ← pow_add]
    congr 1
    omega
  have hsubset := multifoldSumset_subset_integerCarrier_dilate
    (h := 2 ^ (W.blockExponent + W.coverExponent + u + steps))
    W.progression W.contains
  calc
    (multifoldSumset
        (2 ^ (W.blockExponent + W.coverExponent + u + steps)) A).card ≤
        (BiluFreiman.integerCarrier
          (W.progression.dilate
            (2 ^ (W.blockExponent + W.coverExponent + u + steps)))).card :=
      Finset.card_le_card hsubset
    _ = (BiluFreiman.integerCarrier
          ((W.progression.dilate
            (W.initialProperScale * 2 ^ u)).dilate
              (2 ^ (2 * W.coverExponent + steps)))).card := by
      rw [GAP.dilate_dilate, hscale]
    _ = ((W.progression.dilate
          (W.initialProperScale * 2 ^ u)).dilate
            (2 ^ (2 * W.coverExponent + steps))).carrier.card :=
      BiluFreiman.card_integerCarrier _

end Lemma222BlockApproximation

/-! ## The exact finite approximation certificate -/

/-- An exact natural-number version of the structural conclusion extracted
from CFP Lemma 2.22 and stated in Corollary 2.24.

`translatePoint + (k P)` is contained in the `h`-fold sumset, `k P` is
proper, and `k` is at least the fixed rational proportion
`scaleNum / scaleDen` of `h`.
-/
structure HApproximation (A : Finset ℤ) (h rank scaleNum scaleDen : ℕ) where
  progression : GAP 1 rank
  zero_mem : 0 ∈ A
  contains : A ⊆ BiluFreiman.integerCarrier progression
  nondegenerate : progression.Nondegenerate
  scale : ℕ
  scale_pos : 0 < scale
  scale_le : scale ≤ h
  scaleNum_pos : 0 < scaleNum
  scaleDen_pos : 0 < scaleDen
  scale_lower : scaleNum * h ≤ scaleDen * scale
  dilate_proper : (progression.dilate scale).Proper
  translatePoint : ℤ
  covered :
    translate translatePoint
      (BiluFreiman.integerCarrier (progression.dilate scale)) ⊆
      multifoldSumset h A

/-- The exceptional set `{0}` has the required approximation in rank zero
at every admissible source scale.  Keeping this case separate lets the
Bilu--Freiman consumer be stated for all sets containing zero. -/
theorem hApproximation_of_eq_singleton_zero
    {A : Finset ℤ} {h propernessDenominator : ℕ}
    (hA : A = {0}) (hdenominator : 0 < propernessDenominator)
    (hdenominatorLarge : propernessDenominator ≤ h) :
    Nonempty (HApproximation A h 0 1 (2 * propernessDenominator)) := by
  let target := h / propernessDenominator
  have htargetPos : 0 < target :=
    Nat.div_pos hdenominatorLarge hdenominator
  have hzero : 0 ∈ A := by rw [hA]; simp
  have hscaleLower : h ≤ (2 * propernessDenominator) * target := by
    have hmod : h % propernessDenominator < propernessDenominator :=
      Nat.mod_lt h hdenominator
    have hdecomp : h % propernessDenominator +
        propernessDenominator * target = h := by
      simpa only [target] using Nat.mod_add_div h propernessDenominator
    have hdenominator_le : propernessDenominator ≤
        propernessDenominator * target := by
      calc
        propernessDenominator = propernessDenominator * 1 := by simp
        _ ≤ propernessDenominator * target :=
          Nat.mul_le_mul_left propernessDenominator htargetPos
    calc
      h = h % propernessDenominator +
          propernessDenominator * target := hdecomp.symm
      _ ≤ propernessDenominator * target +
          propernessDenominator * target :=
        Nat.add_le_add_right (hmod.le.trans hdenominator_le) _
      _ = (2 * propernessDenominator) * target := by ring
  refine ⟨{
    progression := GAPBuilders.zeroGAP 1
    zero_mem := hzero
    contains := ?_
    nondegenerate := fun i ↦ Fin.elim0 i
    scale := target
    scale_pos := htargetPos
    scale_le := Nat.div_le_self h propernessDenominator
    scaleNum_pos := Nat.zero_lt_one
    scaleDen_pos := Nat.mul_pos (by omega) hdenominator
    scale_lower := by simpa using hscaleLower
    dilate_proper := GAPBuilders.rankZero_proper _
    translatePoint := 0
    covered := ?_ }⟩
  · intro x hx
    have hxzero : x = 0 := Finset.mem_singleton.mp (hA ▸ hx)
    subst x
    rw [BiluFreiman.mem_integerCarrier_iff,
      GAPBuilders.zeroGAP_carrier]
    exact Finset.mem_singleton.mpr rfl
  · intro x hx
    rw [mem_translate_iff] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    have hpLattice := BiluFreiman.mem_integerCarrier_iff.mp hp
    rw [GAPBuilders.rankZero_dilate_carrier] at hpLattice
    have hpPoint := Finset.mem_singleton.mp hpLattice
    have hpzero : p = 0 := by
      have := congrArg BiluFreiman.pointInteger hpPoint
      simpa [GAPBuilders.zeroGAP, GAPBuilders.rankZero,
        BiluFreiman.pointInteger, BiluFreiman.integerPoint] using this
    subst p
    have hxzero : x = 0 := by simpa using hpx.symm
    subst x
    exact zero_mem_multifoldSumset hzero h

namespace HApproximation

variable {A : Finset ℤ} {h rank scaleNum scaleDen : ℕ}
    (W : HApproximation A h rank scaleNum scaleDen)

/-- The upper half of the GAP approximation, `hA ⊆ hP`. -/
theorem multifoldSumset_subset_dilate :
    multifoldSumset h A ⊆
      BiluFreiman.integerCarrier (W.progression.dilate h) :=
  multifoldSumset_subset_integerCarrier_dilate W.progression W.contains

/-- The covered translate has exactly the displayed dilated volume. -/
theorem card_translated_dilate :
    (translate W.translatePoint
      (BiluFreiman.integerCarrier
        (W.progression.dilate W.scale))).card =
        (W.progression.dilate W.scale).volume := by
  rw [card_translate, BiluFreiman.card_integerCarrier,
    W.progression.dilate W.scale |>.card_carrier_eq_volume W.dilate_proper]

/-- Coverage gives the first exact cardinal comparison. -/
theorem dilated_volume_le_card_multifoldSumset :
    (W.progression.dilate W.scale).volume ≤
      (multifoldSumset h A).card := by
  rw [← W.card_translated_dilate]
  exact Finset.card_le_card W.covered

/-- Exact integral form of
`|hA| >= (scale / 2)^rank * Vol(P)`.
-/
theorem scale_pow_mul_volume_le :
    W.scale ^ rank * W.progression.volume ≤
      2 ^ rank * (multifoldSumset h A).card := by
  exact (W.progression.pow_mul_volume_le_pow_two_mul_volume_dilate
      W.nondegenerate W.scale).trans
    (Nat.mul_le_mul_left (2 ^ rank) W.dilated_volume_le_card_multifoldSumset)

/-- Division-free uniform version of the preceding estimate.  This is the
precise finite meaning of
`|hA| ≫ h^rank Vol(P)`, with constant depending only on the two scale
parameters.
-/
theorem h_pow_mul_volume_le :
    (scaleNum * h) ^ rank * W.progression.volume ≤
      (2 * scaleDen) ^ rank * (multifoldSumset h A).card := by
  calc
    (scaleNum * h) ^ rank * W.progression.volume ≤
        (scaleDen * W.scale) ^ rank * W.progression.volume :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left W.scale_lower rank)
    _ = scaleDen ^ rank *
        (W.scale ^ rank * W.progression.volume) := by ring
    _ ≤ scaleDen ^ rank *
        (2 ^ rank * (multifoldSumset h A).card) :=
      Nat.mul_le_mul_left _ W.scale_pow_mul_volume_le
    _ = (2 * scaleDen) ^ rank * (multifoldSumset h A).card := by ring

include W

/-- Consecutive doubling of the number of summands costs only a constant
depending on the approximation rank and its fixed scale denominator.  This
is the upper comparison used for consecutive source thresholds in the
proof of CFP Theorem 1.5. -/
theorem card_two_mul_multifoldSumset_le :
    (multifoldSumset (2 * h) A).card ≤
      (6 * scaleDen) ^ rank * (multifoldSumset h A).card := by
  have hh : 0 < h := W.scale_pos.trans_le W.scale_le
  have hcontains : multifoldSumset (2 * h) A ⊆
      BiluFreiman.integerCarrier (W.progression.dilate (2 * h)) :=
    multifoldSumset_subset_integerCarrier_dilate W.progression W.contains
  have hupper : (multifoldSumset (2 * h) A).card ≤
      (2 * h + 1) ^ rank * W.progression.volume := by
    calc
      (multifoldSumset (2 * h) A).card ≤
          (BiluFreiman.integerCarrier
            (W.progression.dilate (2 * h))).card :=
        Finset.card_le_card hcontains
      _ = (W.progression.dilate (2 * h)).carrier.card :=
        BiluFreiman.card_integerCarrier _
      _ ≤ (W.progression.dilate (2 * h)).volume :=
        (W.progression.dilate (2 * h)).card_carrier_le_volume
      _ ≤ (2 * h + 1) ^ rank * W.progression.volume :=
        W.progression.volume_dilate_le (2 * h)
  have hbase : 2 * h + 1 ≤ 3 * h := by omega
  have hscale : h ^ rank ≤ (scaleNum * h) ^ rank := by
    apply Nat.pow_le_pow_left
    calc
      h = 1 * h := by simp
      _ ≤ scaleNum * h := Nat.mul_le_mul_right h W.scaleNum_pos
  calc
    (multifoldSumset (2 * h) A).card ≤
        (2 * h + 1) ^ rank * W.progression.volume := hupper
    _ ≤ (3 * h) ^ rank * W.progression.volume := by gcongr
    _ = 3 ^ rank * (h ^ rank * W.progression.volume) := by
      rw [mul_pow]
      ring
    _ ≤ 3 ^ rank *
        ((2 * scaleDen) ^ rank * (multifoldSumset h A).card) := by
      exact Nat.mul_le_mul_left (3 ^ rank)
        ((Nat.mul_le_mul_right W.progression.volume hscale).trans
          W.h_pow_mul_volume_le)
    _ = (6 * scaleDen) ^ rank * (multifoldSumset h A).card := by
      have hsix : 3 ^ rank * (2 * scaleDen) ^ rank =
          (6 * scaleDen) ^ rank := by
        rw [← mul_pow]
        congr 1
        ring
      rw [← hsix]
      ring

/-- Exact finite version of the dimension bound in CFP Lemma 2.26.  The
last hypothesis is the explicit replacement for "`h` sufficiently large":
whenever `rank > beta + 1`, the fixed constant is dominated by the surplus
power of `h`. -/
theorem rank_le_beta_add_one_of_card_le_pow (beta : ℕ)
    (hcard : (multifoldSumset h A).card ≤ h ^ (beta + 1))
    (hlarge : beta + 1 < rank →
      (2 * scaleDen) ^ rank * h ^ (beta + 1) <
        (scaleNum * h) ^ rank) :
    rank ≤ beta + 1 := by
  by_contra hnot
  have hrank : beta + 1 < rank := Nat.lt_of_not_ge hnot
  have hbound : (scaleNum * h) ^ rank ≤
      (2 * scaleDen) ^ rank * h ^ (beta + 1) := by
    calc
      (scaleNum * h) ^ rank ≤
          (scaleNum * h) ^ rank * W.progression.volume :=
        Nat.le_mul_of_pos_right _ W.progression.volume_pos
      _ ≤ (2 * scaleDen) ^ rank * (multifoldSumset h A).card :=
        W.h_pow_mul_volume_le
      _ ≤ (2 * scaleDen) ^ rank * h ^ (beta + 1) := by gcongr
  exact (not_lt_of_ge hbound) (hlarge hrank)

/-- Interval-input form of the preceding dimension bound.  The hypotheses
`A ⊆ [0,n-1]` and `n ≤ h^beta` give the source estimate
`|hA| ≤ h*n ≤ h^(beta+1)` exactly. -/
theorem rank_le_beta_add_one_of_interval (beta n : ℕ)
    (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hnpower : n ≤ h ^ beta)
    (hlarge : beta + 1 < rank →
      (2 * scaleDen) ^ rank * h ^ (beta + 1) <
        (scaleNum * h) ^ rank) :
    rank ≤ beta + 1 := by
  apply W.rank_le_beta_add_one_of_card_le_pow beta
  · calc
      (multifoldSumset h A).card ≤ h * n :=
        card_multifoldSumset_le_mul_of_subset_Icc hh hn hA
      _ ≤ h * h ^ beta := Nat.mul_le_mul_left h hnpower
      _ = h ^ (beta + 1) := by rw [pow_succ]; ring
  · exact hlarge

/-- Forgetting the quantitative part gives a bounding GAP for `A`. -/
def toBoundingGAP : BoundingBox.BoundingGAP A rank where
  progression := W.progression
  bounds := by
    rintro ⟨z, hz⟩
    have hz' := BiluFreiman.mem_integerCarrier_iff.mp (W.contains hz)
    change BiluFreiman.integerPoint z ∈ W.progression.carrier
    exact hz'

@[simp]
theorem toBoundingGAP_progression :
    W.toBoundingGAP.progression = W.progression := rfl

/-- Minimality of the `rank`-bounding box. -/
theorem boundingBox_volume_le (hrank : 0 < rank) :
    (BoundingBox.dBoundingBox A rank hrank).progression.volume ≤
      W.progression.volume :=
  BoundingBox.dBoundingBox_minimal' A rank hrank W.toBoundingGAP

include W

/-- CFP Lemma 2.26, cardinality part, with every implicit constant exposed.
The selected minimal bounding GAP can replace the progression in the lower
bound because its volume is no larger.
-/
theorem h_pow_mul_boundingBox_volume_le (hrank : 0 < rank) :
    (scaleNum * h) ^ rank *
        (BoundingBox.dBoundingBox A rank hrank).progression.volume ≤
      (2 * scaleDen) ^ rank * (multifoldSumset h A).card := by
  exact (Nat.mul_le_mul_left _
      (HApproximation.boundingBox_volume_le W hrank)).trans
    (HApproximation.h_pow_mul_volume_le W)

/-- Properness part of CFP Lemma 2.26 in exact finite form.  The displayed
strict inequality is precisely the numerical condition obtained by choosing
the paper's constant `c_beta` sufficiently small.  No asymptotic notation or
hidden threshold is used. -/
theorem boundingBox_dilate_proper_of_numeric (hrank : 0 < rank)
    {q : ℕ} (hqh : q ≤ h)
    (hnumeric :
      (2 * scaleDen) ^ rank *
          (rank * q * (h + 1) ^ (rank - 1)) <
        (scaleNum * h) ^ rank) :
    ((BoundingBox.dBoundingBox A rank hrank).progression.dilate q).Proper := by
  let B : GAP 1 rank :=
    (BoundingBox.dBoundingBox A rank hrank).progression
  have hcontains : A ⊆ BiluFreiman.integerCarrier B := by
    intro z hz
    apply BiluFreiman.mem_integerCarrier_iff.mpr
    change BoundingBox.intPoint z ∈ B.carrier
    exact BoundingBox.dBoundingBox_mem_carrier A rank hrank hz
  have hsumset : multifoldSumset h A ⊆
      BiluFreiman.integerCarrier (B.dilate h) :=
    multifoldSumset_subset_integerCarrier_dilate B hcontains
  have hcard : (multifoldSumset h A).card ≤ (B.dilate h).carrier.card := by
    calc
      (multifoldSumset h A).card ≤
          (BiluFreiman.integerCarrier (B.dilate h)).card :=
        Finset.card_le_card hsumset
      _ = (B.dilate h).carrier.card := BiluFreiman.card_integerCarrier _
  by_contra hnot
  have hboundary : (B.dilate h).carrier.card ≤
      rank * q * (h + 1) ^ (rank - 1) * B.volume :=
    GAP.card_dilate_le_rank_mul_scale_mul_pow_of_not_proper B hqh hnot
  have hlower := HApproximation.h_pow_mul_boundingBox_volume_le W hrank
  change (scaleNum * h) ^ rank * B.volume ≤
      (2 * scaleDen) ^ rank * (multifoldSumset h A).card at hlower
  have hupper :
      (2 * scaleDen) ^ rank * (multifoldSumset h A).card ≤
        (2 * scaleDen) ^ rank *
          (rank * q * (h + 1) ^ (rank - 1) * B.volume) := by
    gcongr
    exact hcard.trans hboundary
  have hstrict :
      (2 * scaleDen) ^ rank *
          (rank * q * (h + 1) ^ (rank - 1) * B.volume) <
        (scaleNum * h) ^ rank * B.volume := by
    have hvol : 0 < B.volume := B.volume_pos
    calc
      (2 * scaleDen) ^ rank *
          (rank * q * (h + 1) ^ (rank - 1) * B.volume) =
          ((2 * scaleDen) ^ rank *
            (rank * q * (h + 1) ^ (rank - 1))) * B.volume := by ring
      _ < (scaleNum * h) ^ rank * B.volume :=
        Nat.mul_lt_mul_of_pos_right hnumeric hvol
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- Fixed-rational-scale form of the properness conclusion in CFP Lemma
2.26.  The denominator condition is dimension-only once the scale parameters
are fixed.  The resulting dilation is exactly `floor (h / K)`. -/
theorem boundingBox_dilate_div_proper (hrank : 0 < rank) (K : ℕ)
    (hK :
      (2 * scaleDen) ^ rank * rank * 2 ^ (rank - 1) <
        K * scaleNum ^ rank) :
    ((BoundingBox.dBoundingBox A rank hrank).progression.dilate (h / K)).Proper := by
  have hh : 0 < h := W.scale_pos.trans_le W.scale_le
  have hqh : h / K ≤ h := Nat.div_le_self h K
  apply HApproximation.boundingBox_dilate_proper_of_numeric W hrank hqh
  by_cases hq : h / K = 0
  · simpa [hq] using
      (pow_pos (Nat.mul_pos W.scaleNum_pos hh) rank)
  · have hqpos : 0 < h / K := Nat.pos_of_ne_zero hq
    have hbase : h + 1 ≤ 2 * h := by omega
    have hpow : (h + 1) ^ (rank - 1) ≤
        (2 * h) ^ (rank - 1) := Nat.pow_le_pow_left hbase _
    have hquot : K * (h / K) ≤ h := Nat.mul_div_le h K
    calc
      (2 * scaleDen) ^ rank *
          (rank * (h / K) * (h + 1) ^ (rank - 1)) ≤
          ((2 * scaleDen) ^ rank * rank * 2 ^ (rank - 1)) *
            ((h / K) * h ^ (rank - 1)) := by
        calc
          (2 * scaleDen) ^ rank *
              (rank * (h / K) * (h + 1) ^ (rank - 1)) ≤
              (2 * scaleDen) ^ rank *
                (rank * (h / K) * (2 * h) ^ (rank - 1)) := by gcongr
          _ = ((2 * scaleDen) ^ rank * rank * 2 ^ (rank - 1)) *
              ((h / K) * h ^ (rank - 1)) := by
            rw [mul_pow]
            ring
      _ < (K * scaleNum ^ rank) * ((h / K) * h ^ (rank - 1)) :=
        Nat.mul_lt_mul_of_pos_right hK (Nat.mul_pos hqpos (by positivity))
      _ ≤ scaleNum ^ rank * h * h ^ (rank - 1) := by
        calc
          (K * scaleNum ^ rank) * ((h / K) * h ^ (rank - 1)) =
              scaleNum ^ rank * (K * (h / K)) * h ^ (rank - 1) := by ring
          _ ≤ scaleNum ^ rank * h * h ^ (rank - 1) := by gcongr
      _ = (scaleNum * h) ^ rank := by
        cases rank with
        | zero => omega
        | succ r =>
            simp only [Nat.succ_sub_one, pow_succ, mul_pow]
            ring

end HApproximation

/-! ## Lemma 2.22 to Corollary 2.24 -/

/-- Exact integral output of CFP Lemma 2.22 needed for Corollary 2.24.

The paper's `P = 2^(-y-1) Q` is represented directly as `progression`;
`blockScale` is `2^(y+1)` and `coverMultiplier` is the constant `C`.
Thus one block of `coverMultiplier * blockScale` summands covers a translate
of `blockScale P`.  `properScale` records the larger proper dilation supplied
by Lemma 2.22.  The last two fields are the exact finite inequalities used
when the covered block is repeated and padded with zeroes.
-/
structure Lemma222Approximation (A : Finset ℤ) (h rank : ℕ) where
  rankBound : ℕ
  rank_le : rank ≤ rankBound
  progression : GAP 1 rank
  zero_mem : 0 ∈ A
  contains : A ⊆ BiluFreiman.integerCarrier progression
  nondegenerate : progression.Nondegenerate
  blockScale : ℕ
  blockScale_pos : 0 < blockScale
  coverMultiplier : ℕ
  coverMultiplier_pos : 0 < coverMultiplier
  blockTranslate : ℤ
  blockCovered :
    translate blockTranslate
      (BiluFreiman.integerCarrier (progression.dilate blockScale)) ⊆
      multifoldSumset (coverMultiplier * blockScale) A
  properScale : ℕ
  proper : (progression.dilate properScale).Proper
  repeatedScale_le_proper :
    (h / (coverMultiplier * blockScale)) * blockScale ≤ properScale
  large : 2 * (coverMultiplier * blockScale) ≤ h

/-- The maximal-proper-scale argument in CFP Lemma 2.22, separated from the
final choice of the covered scale.  This formulation is important for the
source constant hierarchy: the Corollary 2.17 cover multiplier belongs to
`W`, while `target` may be chosen using a different, larger final
denominator. -/
theorem dilate_proper_of_block_of_dyadicLowerGrowth
    {A : Finset ℤ} {rank rankBound target maxExponent steps : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (htarget : target ≤ W.initialProperScale * 2 ^ maxExponent)
    (hsteps : 0 < steps)
    (hgrowth : DyadicLowerGrowth A rankBound
      (W.blockExponent + W.coverExponent)
      (W.blockExponent + W.coverExponent + maxExponent + steps))
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    (W.progression.dilate target).Proper := by
  classical
  by_contra htargetNot
  let ProperAt : ℕ → Prop := fun u ↦
    (W.progression.dilate
      (W.initialProperScale * 2 ^ u)).Proper
  let u := Nat.findGreatest ProperAt maxExponent
  have hProperAtZero : ProperAt 0 := by
    simpa only [ProperAt, pow_zero, mul_one] using W.initialProper
  have hu : ProperAt u := by
    exact Nat.findGreatest_spec (P := ProperAt)
      (Nat.zero_le maxExponent) hProperAtZero
  have hule : u ≤ maxExponent := Nat.findGreatest_le _
  have hult : u < maxExponent := by
    by_contra hnot
    have hueq : u = maxExponent := Nat.le_antisymm hule (Nat.le_of_not_gt hnot)
    have hmaxProper : (W.progression.dilate
        (W.initialProperScale * 2 ^ maxExponent)).Proper := by
      simpa only [ProperAt, hueq] using hu
    have : (W.progression.dilate target).Proper :=
      GAP.dilate_proper_mono W.progression htarget hmaxProper
    exact htargetNot this
  have hnextNot : ¬ ProperAt (u + 1) :=
    Nat.findGreatest_is_greatest (P := ProperAt)
      (Nat.lt_succ_self u) (Nat.succ_le_of_lt hult)
  let R := W.progression.dilate
    (W.initialProperScale * 2 ^ u)
  have hRproper : R.Proper := by simpa only [R, ProperAt] using hu
  have hRdouble : ¬ (R.dilate 2).Proper := by
    intro hproper
    apply hnextNot
    have hscale :
        2 * (W.initialProperScale * 2 ^ u) =
          W.initialProperScale * 2 ^ (u + 1) := by
      rw [pow_succ]
      ring
    simpa only [ProperAt, R, GAP.dilate_dilate, hscale] using hproper
  let k := 2 ^ (2 * W.coverExponent + steps)
  have hkpos : 0 < k := by dsimp [k]; positivity
  have hk : 1 ≤ k := hkpos
  have hcor :=
    GAP.card_dilate_le_pow_sub_one_mul_card_of_proper_of_two_not_proper
      R hk hRproper hRdouble
  let start := W.blockExponent + W.coverExponent + u
  have hbase := W.card_initial_dyadic_dilate_le u
  have hfar := W.card_dyadic_sumset_le_large_dilate u steps
  have hupper :
      (multifoldSumset (2 ^ (start + steps)) A).card ≤
        ((rank * 2 ^ rank) * k ^ (rank - 1)) *
          (multifoldSumset (2 ^ start) A).card := by
    calc
      (multifoldSumset (2 ^ (start + steps)) A).card ≤
          (R.dilate k).carrier.card := by
        simpa only [start, R, k, add_assoc] using hfar
      _ ≤ ((rank * 2 ^ rank) * k ^ (rank - 1)) *
            R.carrier.card := hcor
      _ ≤ ((rank * 2 ^ rank) * k ^ (rank - 1)) *
            (multifoldSumset (2 ^ start) A).card := by
        gcongr
  have hlocal : DyadicLowerGrowth A rankBound start (start + steps) := by
    intro e hse hes
    apply hgrowth e
    · dsimp [start] at hse ⊢
      omega
    · dsimp [start] at hes ⊢
      omega
  have hlower := dyadicLowerGrowth_iterate hsteps hlocal
  have hupperSq :
      (multifoldSumset (2 ^ (start + steps)) A).card ^ 2 ≤
        (((rank * 2 ^ rank) * k ^ (rank - 1)) *
          (multifoldSumset (2 ^ start) A).card) ^ 2 :=
    Nat.pow_le_pow_left hupper 2
  have hnumeric' :
      (((rank * 2 ^ rank) * k ^ (rank - 1)) ^ 2) ≤
        (2 ^ (2 * rankBound - 1)) ^ steps := by
    simpa only [k] using hnumeric
  have hfinal :
      (((rank * 2 ^ rank) * k ^ (rank - 1)) *
          (multifoldSumset (2 ^ start) A).card) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps *
          (multifoldSumset (2 ^ start) A).card ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ hnumeric'
  exact (not_lt_of_ge (hupperSq.trans hfinal)) hlower

/-- Source-horizon form of the maximal-proper-scale argument.  Here `last`
is the integral upper endpoint corresponding to `log₂(h / T)`.  Choosing
`propernessDenominator` at least
`T * 2^(2 * coverExponent + steps + 1)` guarantees that any last proper
dyadic scale below `floor (h / propernessDenominator)` leaves `steps` full
lower-growth doublings before `last`. -/
theorem dilate_div_proper_of_block_of_globalMinimalGrowthDimension
    {A : Finset ℤ}
    {h rank rankBound propernessDenominator horizonFactor steps first last : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (hrankBound : 0 < rankBound)
    (hdenominator : 0 < propernessDenominator)
    (hdenominatorHierarchy :
      horizonFactor * 2 ^ (2 * W.coverExponent + steps + 1) ≤
        propernessDenominator)
    (hhorizon : h < horizonFactor * 2 ^ (last + 1))
    (hsteps : 0 < steps)
    (hminimal : IsMinimalDyadicGrowthDimension A rankBound first last)
    (hstart : first ≤ W.blockExponent + W.coverExponent)
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    (W.progression.dilate (h / propernessDenominator)).Proper := by
  classical
  let target := h / propernessDenominator
  have htwoFactor : 2 * horizonFactor ≤ propernessDenominator := by
    calc
      2 * horizonFactor = horizonFactor * 2 ^ 1 := by simp; ring
      _ ≤ horizonFactor *
          2 ^ (2 * W.coverExponent + steps + 1) := by
        exact Nat.mul_le_mul_left horizonFactor <|
          Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      _ ≤ propernessDenominator := hdenominatorHierarchy
  have htargetTop : target ≤ W.initialProperScale * 2 ^ last := by
    have hstrict : h < propernessDenominator * 2 ^ last := by
      calc
        h < horizonFactor * 2 ^ (last + 1) := hhorizon
        _ = (2 * horizonFactor) * 2 ^ last := by
          rw [pow_succ]
          ring
        _ ≤ propernessDenominator * 2 ^ last := by gcongr
    have htargetLt : target < 2 ^ last := by
      apply (Nat.div_lt_iff_lt_mul hdenominator).2
      simpa [mul_comm] using hstrict
    calc
      target ≤ 2 ^ last := htargetLt.le
      _ = 1 * 2 ^ last := by simp
      _ ≤ W.initialProperScale * 2 ^ last := by
        gcongr
        exact W.initialProperScale_pos
  by_contra htargetNot
  let ProperAt : ℕ → Prop := fun u ↦
    (W.progression.dilate
      (W.initialProperScale * 2 ^ u)).Proper
  let u := Nat.findGreatest ProperAt last
  have hProperAtZero : ProperAt 0 := by
    simpa only [ProperAt, pow_zero, mul_one] using W.initialProper
  have hu : ProperAt u := by
    exact Nat.findGreatest_spec (P := ProperAt)
      (Nat.zero_le last) hProperAtZero
  have hule : u ≤ last := Nat.findGreatest_le _
  have hult : u < last := by
    by_contra hnot
    have hueq : u = last := Nat.le_antisymm hule (Nat.le_of_not_gt hnot)
    have hlastProper : (W.progression.dilate
        (W.initialProperScale * 2 ^ last)).Proper := by
      simpa only [ProperAt, hueq] using hu
    have : (W.progression.dilate target).Proper :=
      GAP.dilate_proper_mono W.progression htargetTop hlastProper
    exact htargetNot this
  have hnextNot : ¬ ProperAt (u + 1) :=
    Nat.findGreatest_is_greatest (P := ProperAt)
      (Nat.lt_succ_self u) (Nat.succ_le_of_lt hult)
  let R := W.progression.dilate
    (W.initialProperScale * 2 ^ u)
  have hRproper : R.Proper := by simpa only [R, ProperAt] using hu
  have hRdouble : ¬ (R.dilate 2).Proper := by
    intro hproper
    apply hnextNot
    have hscale :
        2 * (W.initialProperScale * 2 ^ u) =
          W.initialProperScale * 2 ^ (u + 1) := by
      rw [pow_succ]
      ring
    simpa only [ProperAt, R, GAP.dilate_dilate, hscale] using hproper
  have hRscaleLt : W.initialProperScale * 2 ^ u < target := by
    by_contra hnot
    have htargetLe : target ≤ W.initialProperScale * 2 ^ u :=
      Nat.le_of_not_gt hnot
    have : (W.progression.dilate target).Proper :=
      GAP.dilate_proper_mono W.progression htargetLe hRproper
    exact htargetNot this
  have hRscaleMul :
      (W.initialProperScale * 2 ^ u) * propernessDenominator < h := by
    have hdiv := (Nat.lt_div_iff_mul_lt hdenominator).1 hRscaleLt
    exact hdiv.trans_le (Nat.sub_le h (propernessDenominator - 1))
  have hend :
      W.blockExponent + W.coverExponent + u + steps ≤ last := by
    have hscaleIdentity :
        horizonFactor * 2 ^ (2 * W.coverExponent + steps + 1) *
            (W.initialProperScale * 2 ^ u) =
          horizonFactor *
            2 ^ (W.blockExponent + W.coverExponent + u + steps + 1) := by
      rw [W.initialProperScale_eq_pow_sub]
      calc
        horizonFactor * 2 ^ (2 * W.coverExponent + steps + 1) *
              (2 ^ (W.blockExponent - W.coverExponent) * 2 ^ u) =
            horizonFactor *
              (2 ^ (2 * W.coverExponent + steps + 1) *
                2 ^ (W.blockExponent - W.coverExponent) * 2 ^ u) := by ring
        _ = horizonFactor *
              2 ^ ((2 * W.coverExponent + steps + 1) +
                (W.blockExponent - W.coverExponent) + u) := by
          rw [← pow_add, ← pow_add]
        _ = horizonFactor *
              2 ^ (W.blockExponent + W.coverExponent + u + steps + 1) := by
          congr 2
          have hcoverLe := W.coverExponent_le_blockExponent
          omega
    have hbelow :
        horizonFactor *
            2 ^ (W.blockExponent + W.coverExponent + u + steps + 1) < h := by
      rw [← hscaleIdentity]
      calc
        horizonFactor * 2 ^ (2 * W.coverExponent + steps + 1) *
              (W.initialProperScale * 2 ^ u) ≤
            propernessDenominator *
              (W.initialProperScale * 2 ^ u) := by gcongr
        _ = (W.initialProperScale * 2 ^ u) *
              propernessDenominator := by ring
        _ < h := hRscaleMul
    have hpowers :
        2 ^ (W.blockExponent + W.coverExponent + u + steps + 1) <
          2 ^ (last + 1) := by
      apply Nat.lt_of_mul_lt_mul_left
      exact hbelow.trans hhorizon
    have hexponents :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpowers
    omega
  let k := 2 ^ (2 * W.coverExponent + steps)
  have hkpos : 0 < k := by dsimp [k]; positivity
  have hk : 1 ≤ k := hkpos
  have hcor :=
    GAP.card_dilate_le_pow_sub_one_mul_card_of_proper_of_two_not_proper
      R hk hRproper hRdouble
  let start := W.blockExponent + W.coverExponent + u
  have hbase := W.card_initial_dyadic_dilate_le u
  have hfar := W.card_dyadic_sumset_le_large_dilate u steps
  have hupper :
      (multifoldSumset (2 ^ (start + steps)) A).card ≤
        ((rank * 2 ^ rank) * k ^ (rank - 1)) *
          (multifoldSumset (2 ^ start) A).card := by
    calc
      (multifoldSumset (2 ^ (start + steps)) A).card ≤
          (R.dilate k).carrier.card := by
        simpa only [start, R, k, add_assoc] using hfar
      _ ≤ ((rank * 2 ^ rank) * k ^ (rank - 1)) * R.carrier.card := hcor
      _ ≤ ((rank * 2 ^ rank) * k ^ (rank - 1)) *
            (multifoldSumset (2 ^ start) A).card := by
        gcongr
  have hglobal := dyadicLowerGrowth_of_minimalDimension hrankBound hminimal
  have hlocal : DyadicLowerGrowth A rankBound start (start + steps) := by
    intro e hse hes
    apply hglobal e
    · exact hstart.trans (by dsimp [start] at hse ⊢; omega)
    · exact hes.trans_le (by dsimp [start] at hend ⊢; omega)
  have hlower := dyadicLowerGrowth_iterate hsteps hlocal
  have hupperSq :
      (multifoldSumset (2 ^ (start + steps)) A).card ^ 2 ≤
        (((rank * 2 ^ rank) * k ^ (rank - 1)) *
          (multifoldSumset (2 ^ start) A).card) ^ 2 :=
    Nat.pow_le_pow_left hupper 2
  have hnumeric' :
      (((rank * 2 ^ rank) * k ^ (rank - 1)) ^ 2) ≤
        (2 ^ (2 * rankBound - 1)) ^ steps := by
    simpa only [k] using hnumeric
  have hfinal :
      (((rank * 2 ^ rank) * k ^ (rank - 1)) *
          (multifoldSumset (2 ^ start) A).card) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps *
          (multifoldSumset (2 ^ start) A).card ^ 2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ hnumeric'
  exact (not_lt_of_ge (hupperSq.trans hfinal)) hlower

/-- Once the final `floor (h / C₀)` dilate is known proper, repetition of
the original `C * blockScale` cover and the inequality `2C ≤ C₀` give
the exact constant-scale `HApproximation`. -/
theorem hApproximation_of_block_of_properTarget_separated
    {A : Finset ℤ} {h rank rankBound propernessDenominator : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (hdenominator : 0 < propernessDenominator)
    (hseparated : 2 * W.coverMultiplier ≤ propernessDenominator)
    (hblockLarge : 2 * (W.coverMultiplier * W.blockScale) ≤ h)
    (hdenominatorLarge : propernessDenominator ≤ h)
    (hproper :
      (W.progression.dilate (h / propernessDenominator)).Proper) :
    Nonempty
      (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  classical
  let blockSize := W.coverMultiplier * W.blockScale
  let blockCount := h / blockSize
  let target := h / propernessDenominator
  have hblockSizePos : 0 < blockSize := by
    dsimp [blockSize]
    exact Nat.mul_pos W.coverMultiplier_pos W.blockScale_pos
  have hblockSizeLe : blockSize ≤ h :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < 2)).trans hblockLarge
  have hblockCountPos : 0 < blockCount :=
    Nat.div_pos hblockSizeLe hblockSizePos
  have htargetPos : 0 < target := by
    dsimp [target]
    exact Nat.div_pos hdenominatorLarge hdenominator
  have htarget_le_repeated : target ≤ blockCount * W.blockScale := by
    have hdivision : h < blockSize * (blockCount + 1) := by
      simpa only [blockCount] using Nat.lt_mul_div_succ h hblockSizePos
    have hcount : blockCount + 1 ≤ 2 * blockCount := by omega
    have hupper : h <
        (2 * W.coverMultiplier) * (blockCount * W.blockScale) := by
      calc
        h < blockSize * (blockCount + 1) := hdivision
        _ ≤ blockSize * (2 * blockCount) := by gcongr
        _ = (2 * W.coverMultiplier) *
            (blockCount * W.blockScale) := by
          dsimp [blockSize]
          ring
    have htargetMul : target * propernessDenominator ≤ h := by
      simpa only [target] using Nat.div_mul_le_self h propernessDenominator
    have hmul : (2 * W.coverMultiplier) * target <
        (2 * W.coverMultiplier) * (blockCount * W.blockScale) := by
      calc
        (2 * W.coverMultiplier) * target ≤
            propernessDenominator * target := by gcongr
        _ = target * propernessDenominator := by ring
        _ ≤ h := htargetMul
        _ < (2 * W.coverMultiplier) *
            (blockCount * W.blockScale) := hupper
    exact (Nat.lt_of_mul_lt_mul_left hmul).le
  have hscaleLower : h ≤ (2 * propernessDenominator) * target := by
    have hmod : h % propernessDenominator < propernessDenominator :=
      Nat.mod_lt h hdenominator
    have hdecomp : h % propernessDenominator +
        propernessDenominator * target = h := by
      simpa only [target] using Nat.mod_add_div h propernessDenominator
    have hdenominator_le : propernessDenominator ≤
        propernessDenominator * target := by
      calc
        propernessDenominator = propernessDenominator * 1 := by simp
        _ ≤ propernessDenominator * target :=
          Nat.mul_le_mul_left propernessDenominator htargetPos
    calc
      h = h % propernessDenominator +
          propernessDenominator * target := hdecomp.symm
      _ ≤ propernessDenominator * target +
          propernessDenominator * target :=
        Nat.add_le_add_right (hmod.le.trans hdenominator_le) _
      _ = (2 * propernessDenominator) * target := by ring
  refine ⟨{
    progression := W.progression
    zero_mem := W.zero_mem
    contains := W.contains
    nondegenerate := W.nondegenerate
    scale := target
    scale_pos := htargetPos
    scale_le := by
      dsimp [target]
      exact Nat.div_le_self h propernessDenominator
    scaleNum_pos := Nat.zero_lt_one
    scaleDen_pos := Nat.mul_pos (by omega) hdenominator
    scale_lower := by simpa using hscaleLower
    dilate_proper := by simpa only [target] using hproper
    translatePoint := (blockCount : ℤ) * W.blockTranslate
    covered := ?_ }⟩
  have hiter := iterate_translate_subset W.blockCovered blockCount
  have hcarrier :
      multifoldSumset blockCount
          (BiluFreiman.integerCarrier
            (W.progression.dilate W.blockScale)) =
        BiluFreiman.integerCarrier
          (W.progression.dilate (blockCount * W.blockScale)) := by
    rw [← integerCarrier_dilate_eq_multifoldSumset, GAP.dilate_dilate]
  rw [hcarrier] at hiter
  have hzeroP : 0 ∈ BiluFreiman.integerCarrier W.progression :=
    W.contains W.zero_mem
  have hsmall :
      BiluFreiman.integerCarrier (W.progression.dilate target) ⊆
        BiluFreiman.integerCarrier
          (W.progression.dilate (blockCount * W.blockScale)) := by
    rw [integerCarrier_dilate_eq_multifoldSumset,
      integerCarrier_dilate_eq_multifoldSumset]
    exact multifoldSumset_mono_index hzeroP htarget_le_repeated
  have htranslated :
      translate ((blockCount : ℤ) * W.blockTranslate)
          (BiluFreiman.integerCarrier (W.progression.dilate target)) ⊆
        multifoldSumset (blockCount * blockSize) A := by
    intro x hx
    apply hiter
    rw [mem_translate_iff] at hx ⊢
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hsmall hp, hpx⟩
  apply htranslated.trans
  apply multifoldSumset_mono_index W.zero_mem
  dsimp [blockCount, blockSize]
  exact Nat.div_mul_le_self h (W.coverMultiplier * W.blockScale)

/-- Complete source-horizon form of CFP Lemma 2.22/Corollary 2.24 for a
constructed block approximation. -/
theorem hApproximation_of_block_of_sourceMinimalGrowth
    {A : Finset ℤ}
    {h rank rankBound propernessDenominator horizonFactor steps first last : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (hrankBound : 0 < rankBound)
    (hdenominator : 0 < propernessDenominator)
    (hseparated : 2 * W.coverMultiplier ≤ propernessDenominator)
    (hblockLarge : 2 * (W.coverMultiplier * W.blockScale) ≤ h)
    (hdenominatorLarge : propernessDenominator ≤ h)
    (hdenominatorHierarchy :
      horizonFactor * 2 ^ (2 * W.coverExponent + steps + 1) ≤
        propernessDenominator)
    (hhorizon : h < horizonFactor * 2 ^ (last + 1))
    (hsteps : 0 < steps)
    (hminimal : IsMinimalDyadicGrowthDimension A rankBound first last)
    (hstart : first ≤ W.blockExponent + W.coverExponent)
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    Nonempty
      (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  apply hApproximation_of_block_of_properTarget_separated W
    hdenominator hseparated hblockLarge hdenominatorLarge
  exact dilate_div_proper_of_block_of_globalMinimalGrowthDimension W
    hrankBound hdenominator hdenominatorHierarchy hhorizon
    hsteps hminimal hstart hnumeric

/-- Uniform nontrivial-set consumer for the complete CFP Lemma 2.22 and
Corollary 2.24 construction.  All numerical constants are chosen before
`A`, `h`, the least slow-growth dimension, and its selected scale. -/
theorem exists_uniform_sourceHApproximation_of_biluFreiman_nontrivial
    (hBF : BiluFreiman.BiluFreimanStatement) (dimensionBound : ℕ) :
    ∃ blockThreshold coverExponentBound steps horizonFactor
        propernessDenominator : ℕ,
      0 < blockThreshold ∧ 0 < coverExponentBound ∧ 0 < steps ∧
      0 < horizonFactor ∧ 0 < propernessDenominator ∧
      ∀ {A : Finset ℤ} {h dimension first last : ℕ},
        0 ∈ A → (∃ x ∈ A, x ≠ 0) →
        dimension ≤ dimensionBound →
        IsMinimalDyadicGrowthDimension A dimension first last →
        blockThreshold ≤ 2 ^ (first + 1) →
        horizonFactor * 2 ^ last ≤ h →
        h < horizonFactor * 2 ^ (last + 1) →
        propernessDenominator ≤ h →
        ∃ rank, rank ≤ dimension ∧ Nonempty
          (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  obtain ⟨blockThreshold, coverExponentBound, hblockThreshold,
      hcoverExponentBound, hblocks⟩ :=
    exists_uniform_lemma222BlockApproximation_at_dyadic_of_biluFreiman_nontrivial
      hBF dimensionBound
  let steps := terminalGrowthSteps dimensionBound coverExponentBound
  let horizonFactor := max blockThreshold (2 * 2 ^ coverExponentBound)
  let propernessDenominator :=
    max (2 * 2 ^ coverExponentBound)
      (horizonFactor * 2 ^ (2 * coverExponentBound + steps + 1))
  have hsteps : 0 < steps := by
    simpa only [steps] using
      terminalGrowthSteps_pos dimensionBound coverExponentBound
  have hhorizonFactor : 0 < horizonFactor :=
    hblockThreshold.trans_le (Nat.le_max_left _ _)
  have hpropernessDenominator : 0 < propernessDenominator := by
    exact (Nat.mul_pos (by omega) (pow_pos (by omega) _)).trans_le
      (Nat.le_max_left _ _)
  refine ⟨blockThreshold, coverExponentBound, steps, horizonFactor,
    propernessDenominator, hblockThreshold, hcoverExponentBound, hsteps,
    hhorizonFactor, hpropernessDenominator, ?_⟩
  intro A h dimension first last hzero hne hdimensionBound hminimal
    hthreshold hhorizonLower hhorizonUpper hdenominatorLarge
  have hdimension : 0 < dimension :=
    minimalDyadicGrowthDimension_pos_of_exists_ne_zero hzero hne hminimal
  let actualSteps := terminalGrowthSteps dimension coverExponentBound
  have hactualSteps : 0 < actualSteps := by
    simpa only [actualSteps] using
      terminalGrowthSteps_pos dimension coverExponentBound
  have hactualStepsBound : actualSteps ≤ steps := by
    dsimp only [actualSteps, steps, terminalGrowthSteps]
    exact Nat.add_le_add_right
      (Nat.add_le_add
        (Nat.mul_le_mul_left 4 hdimensionBound)
        (Nat.mul_le_mul_left (4 * coverExponentBound) hdimensionBound)) 1
  obtain ⟨y, hyfirst, hylast, hslow⟩ := hminimal.1
  have hthresholdY : blockThreshold ≤ 2 ^ (y + 1) := by
    exact hthreshold.trans
      (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
  obtain ⟨rank, V, hblockExponent, hcoverExponent⟩ :=
    hblocks dimension hdimension hdimensionBound hzero hne y hthresholdY
      (real_dyadicSlowGrowth_of_squared hslow)
  have hblockScale : V.blockScale = 2 ^ (y + 1) := by
    rw [V.blockScale_eq, hblockExponent]
  have hblockScaleUpper : V.blockScale ≤ 2 ^ last := by
    rw [hblockScale]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  have hcoverMultiplier : V.coverMultiplier ≤ 2 ^ coverExponentBound := by
    rw [V.coverMultiplier_eq]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hcoverExponent
  have hblockLarge : 2 * (V.coverMultiplier * V.blockScale) ≤ h := by
    calc
      2 * (V.coverMultiplier * V.blockScale) ≤
          2 * (2 ^ coverExponentBound * 2 ^ last) := by gcongr
      _ = (2 * 2 ^ coverExponentBound) * 2 ^ last := by ring
      _ ≤ horizonFactor * 2 ^ last := by
        gcongr
        exact Nat.le_max_right _ _
      _ ≤ h := hhorizonLower
  have hseparated :
      2 * V.coverMultiplier ≤ propernessDenominator := by
    calc
      2 * V.coverMultiplier ≤ 2 * 2 ^ coverExponentBound := by gcongr
      _ ≤ propernessDenominator := Nat.le_max_left _ _
  have hdenominatorHierarchy :
      horizonFactor * 2 ^ (2 * V.coverExponent + actualSteps + 1) ≤
        propernessDenominator := by
    calc
      horizonFactor * 2 ^ (2 * V.coverExponent + actualSteps + 1) ≤
          horizonFactor * 2 ^
            (2 * coverExponentBound + steps + 1) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      _ ≤ propernessDenominator := Nat.le_max_right _ _
  have hstart : first ≤ V.blockExponent + V.coverExponent := by
    rw [hblockExponent]
    omega
  have hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * V.coverExponent + actualSteps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * dimension - 1)) ^ actualSteps := by
    simpa only [actualSteps] using
      terminalGrowthSteps_numeric V.rank_le hcoverExponent
  refine ⟨rank, V.rank_le, ?_⟩
  exact hApproximation_of_block_of_sourceMinimalGrowth V hdimension
    hpropernessDenominator hseparated hblockLarge hdenominatorLarge
    hdenominatorHierarchy hhorizonUpper hactualSteps hminimal hstart hnumeric

/-- Source-facing all-set form of CFP Lemma 2.22/Corollary 2.24.  The
singleton `{0}` is handled by a rank-zero GAP; every other set containing
zero automatically has positive least slow-growth dimension and therefore
uses the genuine Bilu--Freiman block construction above. -/
theorem exists_uniform_sourceHApproximation_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (dimensionBound : ℕ) :
    ∃ blockThreshold coverExponentBound steps horizonFactor
        propernessDenominator : ℕ,
      0 < blockThreshold ∧ 0 < coverExponentBound ∧ 0 < steps ∧
      0 < horizonFactor ∧ 0 < propernessDenominator ∧
      ∀ {A : Finset ℤ} {h dimension first last : ℕ},
        0 ∈ A → dimension ≤ dimensionBound →
        IsMinimalDyadicGrowthDimension A dimension first last →
        blockThreshold ≤ 2 ^ (first + 1) →
        horizonFactor * 2 ^ last ≤ h →
        h < horizonFactor * 2 ^ (last + 1) →
        propernessDenominator ≤ h →
        ∃ rank, rank ≤ dimension ∧ Nonempty
          (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  obtain ⟨blockThreshold, coverExponentBound, steps, horizonFactor,
      propernessDenominator, hblockThreshold, hcoverExponentBound, hsteps,
      hhorizonFactor, hpropernessDenominator, hconsumer⟩ :=
    exists_uniform_sourceHApproximation_of_biluFreiman_nontrivial
      hBF dimensionBound
  refine ⟨blockThreshold, coverExponentBound, steps, horizonFactor,
    propernessDenominator, hblockThreshold, hcoverExponentBound, hsteps,
    hhorizonFactor, hpropernessDenominator, ?_⟩
  intro A h dimension first last hzero hdimensionBound hminimal
    hthreshold hhorizonLower hhorizonUpper hdenominatorLarge
  by_cases hsingleton : A = {0}
  · exact ⟨0, Nat.zero_le dimension,
      hApproximation_of_eq_singleton_zero hsingleton
      hpropernessDenominator hdenominatorLarge⟩
  · have hne : ∃ x ∈ A, x ≠ 0 := by
      by_contra hnot
      apply hsingleton
      ext x
      constructor
      · intro hx
        have hxzero : x = 0 := by
          by_contra hxzero
          exact hnot ⟨x, hx, hxzero⟩
        simpa only [Finset.mem_singleton] using hxzero
      · intro hx
        have hxzero : x = 0 := Finset.mem_singleton.mp hx
        simpa only [hxzero] using hzero
    exact hconsumer hzero hne hdimensionBound hminimal hthreshold
      hhorizonLower hhorizonUpper hdenominatorLarge

/-- Correct separated-constant form of CFP Lemma 2.22 and Corollary 2.24.

`W.coverMultiplier` is the Corollary 2.17 block multiplier `C`.  The
independent `propernessDenominator` is the later constant `C₀` used to
choose the final proper scale `floor (h / C₀)`.  Repeating the original
blocks produces the larger scale
`floor (h / (C * blockScale)) * blockScale`; the hypothesis
`2 * C ≤ C₀` makes it legitimate to shrink that covered dilate to the
proper `floor (h / C₀)` dilate.  In particular, no padding of a block from
`C` summands to `C₀` summands is used in the maximal-scale argument. -/
theorem hApproximation_of_block_of_dyadicLowerGrowth_separated
    {A : Finset ℤ} {h rank rankBound propernessDenominator
      maxExponent steps : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (hdenominator : 0 < propernessDenominator)
    (hseparated : 2 * W.coverMultiplier ≤ propernessDenominator)
    (hblockLarge : 2 * (W.coverMultiplier * W.blockScale) ≤ h)
    (hdenominatorLarge : propernessDenominator ≤ h)
    (htarget : h / propernessDenominator ≤
      W.initialProperScale * 2 ^ maxExponent)
    (hsteps : 0 < steps)
    (hgrowth : DyadicLowerGrowth A rankBound
      (W.blockExponent + W.coverExponent)
      (W.blockExponent + W.coverExponent + maxExponent + steps))
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    Nonempty
      (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  classical
  let blockSize := W.coverMultiplier * W.blockScale
  let blockCount := h / blockSize
  let target := h / propernessDenominator
  have hblockSizePos : 0 < blockSize := by
    dsimp [blockSize]
    exact Nat.mul_pos W.coverMultiplier_pos W.blockScale_pos
  have hblockSizeLe : blockSize ≤ h := by
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < 2)).trans hblockLarge
  have hblockCountPos : 0 < blockCount :=
    Nat.div_pos hblockSizeLe hblockSizePos
  have htargetPos : 0 < target := by
    dsimp [target]
    exact Nat.div_pos hdenominatorLarge hdenominator
  have htargetProper : (W.progression.dilate target).Proper := by
    apply dilate_proper_of_block_of_dyadicLowerGrowth W
    · simpa only [target] using htarget
    · exact hsteps
    · exact hgrowth
    · exact hnumeric
  have htarget_le_repeated : target ≤ blockCount * W.blockScale := by
    have hdivision : h < blockSize * (blockCount + 1) := by
      simpa only [blockCount] using Nat.lt_mul_div_succ h hblockSizePos
    have hcount : blockCount + 1 ≤ 2 * blockCount := by omega
    have hupper : h <
        (2 * W.coverMultiplier) * (blockCount * W.blockScale) := by
      calc
        h < blockSize * (blockCount + 1) := hdivision
        _ ≤ blockSize * (2 * blockCount) := by gcongr
        _ = (2 * W.coverMultiplier) *
            (blockCount * W.blockScale) := by
          dsimp [blockSize]
          ring
    have htargetMul : target * propernessDenominator ≤ h := by
      simpa only [target] using
        Nat.div_mul_le_self h propernessDenominator
    have hmul : (2 * W.coverMultiplier) * target <
        (2 * W.coverMultiplier) * (blockCount * W.blockScale) := by
      calc
        (2 * W.coverMultiplier) * target ≤
            propernessDenominator * target := by gcongr
        _ = target * propernessDenominator := by ring
        _ ≤ h := htargetMul
        _ < (2 * W.coverMultiplier) *
            (blockCount * W.blockScale) := hupper
    exact (Nat.lt_of_mul_lt_mul_left hmul).le
  have hscaleLower : h ≤
      (2 * propernessDenominator) * target := by
    have hmod : h % propernessDenominator < propernessDenominator :=
      Nat.mod_lt h hdenominator
    have hdecomp : h % propernessDenominator +
        propernessDenominator * target = h := by
      simpa only [target] using Nat.mod_add_div h propernessDenominator
    have hdenominator_le : propernessDenominator ≤
        propernessDenominator * target := by
      calc
        propernessDenominator = propernessDenominator * 1 := by simp
        _ ≤ propernessDenominator * target :=
          Nat.mul_le_mul_left propernessDenominator htargetPos
    calc
      h = h % propernessDenominator +
          propernessDenominator * target := hdecomp.symm
      _ ≤ propernessDenominator * target +
          propernessDenominator * target :=
        Nat.add_le_add_right (hmod.le.trans hdenominator_le) _
      _ = (2 * propernessDenominator) * target := by ring
  refine ⟨{
    progression := W.progression
    zero_mem := W.zero_mem
    contains := W.contains
    nondegenerate := W.nondegenerate
    scale := target
    scale_pos := htargetPos
    scale_le := by
      dsimp [target]
      exact Nat.div_le_self h propernessDenominator
    scaleNum_pos := Nat.zero_lt_one
    scaleDen_pos := Nat.mul_pos (by omega) hdenominator
    scale_lower := by simpa using hscaleLower
    dilate_proper := htargetProper
    translatePoint := (blockCount : ℤ) * W.blockTranslate
    covered := ?_ }⟩
  have hiter := iterate_translate_subset W.blockCovered blockCount
  have hcarrier :
      multifoldSumset blockCount
          (BiluFreiman.integerCarrier
            (W.progression.dilate W.blockScale)) =
        BiluFreiman.integerCarrier
          (W.progression.dilate (blockCount * W.blockScale)) := by
    rw [← integerCarrier_dilate_eq_multifoldSumset,
      GAP.dilate_dilate]
  rw [hcarrier] at hiter
  have hzeroP : 0 ∈ BiluFreiman.integerCarrier W.progression :=
    W.contains W.zero_mem
  have hsmall :
      BiluFreiman.integerCarrier (W.progression.dilate target) ⊆
        BiluFreiman.integerCarrier
          (W.progression.dilate (blockCount * W.blockScale)) := by
    rw [integerCarrier_dilate_eq_multifoldSumset,
      integerCarrier_dilate_eq_multifoldSumset]
    exact multifoldSumset_mono_index hzeroP htarget_le_repeated
  have htranslated :
      translate ((blockCount : ℤ) * W.blockTranslate)
          (BiluFreiman.integerCarrier (W.progression.dilate target)) ⊆
        multifoldSumset (blockCount * blockSize) A := by
    intro x hx
    apply hiter
    rw [mem_translate_iff] at hx ⊢
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hsmall hp, hpx⟩
  apply htranslated.trans
  apply multifoldSumset_mono_index W.zero_mem
  dsimp [blockCount, blockSize]
  exact Nat.div_mul_le_self h (W.coverMultiplier * W.blockScale)

/-- Minimal-growth source form of the preceding separated-constant theorem. -/
theorem hApproximation_of_block_of_minimalGrowthDimension_separated
    {A : Finset ℤ} {h rank rankBound propernessDenominator
      maxExponent steps : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (hrankBound : 0 < rankBound)
    (hdenominator : 0 < propernessDenominator)
    (hseparated : 2 * W.coverMultiplier ≤ propernessDenominator)
    (hblockLarge : 2 * (W.coverMultiplier * W.blockScale) ≤ h)
    (hdenominatorLarge : propernessDenominator ≤ h)
    (htarget : h / propernessDenominator ≤
      W.initialProperScale * 2 ^ maxExponent)
    (hsteps : 0 < steps)
    (hminimal : IsMinimalDyadicGrowthDimension A rankBound
      (W.blockExponent + W.coverExponent)
      (W.blockExponent + W.coverExponent + maxExponent + steps))
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    Nonempty
      (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  apply hApproximation_of_block_of_dyadicLowerGrowth_separated W
    hdenominator hseparated hblockLarge hdenominatorLarge htarget hsteps
  · exact dyadicLowerGrowth_of_minimalDimension hrankBound hminimal
  · exact hnumeric

/-- Source-interval form of the separated-constant construction.  The
minimality defining `d₀` is stated once on the paper's global dyadic
interval.  The two endpoint inequalities then restrict its forced lower
growth to the post-selected block interval used by the maximal-proper-scale
argument. -/
theorem hApproximation_of_block_of_globalMinimalGrowthDimension_separated
    {A : Finset ℤ}
    {h rank rankBound propernessDenominator maxExponent steps first last : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (hrankBound : 0 < rankBound)
    (hdenominator : 0 < propernessDenominator)
    (hseparated : 2 * W.coverMultiplier ≤ propernessDenominator)
    (hblockLarge : 2 * (W.coverMultiplier * W.blockScale) ≤ h)
    (hdenominatorLarge : propernessDenominator ≤ h)
    (htarget : h / propernessDenominator ≤
      W.initialProperScale * 2 ^ maxExponent)
    (hsteps : 0 < steps)
    (hminimal : IsMinimalDyadicGrowthDimension A rankBound first last)
    (hstart : first ≤ W.blockExponent + W.coverExponent)
    (hend : W.blockExponent + W.coverExponent + maxExponent + steps ≤ last)
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    Nonempty
      (HApproximation A h rank 1 (2 * propernessDenominator)) := by
  apply hApproximation_of_block_of_dyadicLowerGrowth_separated W
    hdenominator hseparated hblockLarge hdenominatorLarge htarget hsteps
  · have hglobal := dyadicLowerGrowth_of_minimalDimension hrankBound hminimal
    intro e heStart heEnd
    exact hglobal e (hstart.trans heStart) (heEnd.trans_le hend)
  · exact hnumeric

/-- Exact finite substitute for CFP Lemma 2.22, lines 1358--1408.

The exponent `maxExponent` is the finite replacement for the upper
logarithmic endpoint, while `steps` is the terminal slow-growth interval.
Minimality of the chosen dimension supplies `DyadicLowerGrowth`; the last
displayed inequality is precisely the point at which the fixed constant is
chosen large enough.  The proof selects the greatest proper dyadic scale and
uses Corollary 2.21 at its first nonproper double. -/
theorem lemma222Approximation_of_block_of_dyadicLowerGrowth
    {A : Finset ℤ} {h rank rankBound : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (safety maxExponent steps : ℕ)
    (hlarge :
      2 * ((W.coverMultiplier * 2 ^ safety) * W.blockScale) ≤ h)
    (htarget :
      (h / ((W.coverMultiplier * 2 ^ safety) * W.blockScale)) *
          W.blockScale ≤
        W.initialProperScale * 2 ^ maxExponent)
    (hsteps : 0 < steps)
    (hgrowth : DyadicLowerGrowth A rankBound
      (W.blockExponent + W.coverExponent)
      (W.blockExponent + W.coverExponent + maxExponent + steps))
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    Nonempty (Lemma222Approximation A h rank) := by
  classical
  refine ⟨?_⟩
  let finalCover := W.coverMultiplier * 2 ^ safety
  let target :=
    (h / (finalCover * W.blockScale)) * W.blockScale
  have htargetProper : (W.progression.dilate target).Proper :=
    dilate_proper_of_block_of_dyadicLowerGrowth W htarget hsteps hgrowth hnumeric
  exact {
    rankBound := rankBound
    rank_le := W.rank_le
    progression := W.progression
    zero_mem := W.zero_mem
    contains := W.contains
    nondegenerate := W.nondegenerate
    blockScale := W.blockScale
    blockScale_pos := W.blockScale_pos
    coverMultiplier := finalCover
    coverMultiplier_pos := Nat.mul_pos W.coverMultiplier_pos (by positivity)
    blockTranslate := W.blockTranslate
    blockCovered := by
      apply W.blockCovered.trans
      apply multifoldSumset_mono_index W.zero_mem
      dsimp [finalCover]
      have hspos : 0 < 2 ^ safety := by positivity
      have hs : 1 ≤ 2 ^ safety := hspos
      calc
        W.coverMultiplier * W.blockScale =
            (W.coverMultiplier * 1) * W.blockScale := by ring
        _ ≤ (W.coverMultiplier * 2 ^ safety) * W.blockScale := by gcongr
    properScale := target
    proper := htargetProper
    repeatedScale_le_proper := Nat.le_refl target
    large := hlarge }

/-- Source-facing maximal-scale theorem: the lower-growth hypothesis is
derived, rather than assumed, from leastness of the slow-growth dimension. -/
theorem lemma222Approximation_of_block_of_minimalGrowthDimension
    {A : Finset ℤ} {h rank rankBound : ℕ}
    (W : Lemma222BlockApproximation A rank rankBound)
    (safety maxExponent steps : ℕ)
    (hrankBound : 0 < rankBound)
    (hlarge :
      2 * ((W.coverMultiplier * 2 ^ safety) * W.blockScale) ≤ h)
    (htarget :
      (h / ((W.coverMultiplier * 2 ^ safety) * W.blockScale)) *
          W.blockScale ≤
        W.initialProperScale * 2 ^ maxExponent)
    (hsteps : 0 < steps)
    (hminimal : IsMinimalDyadicGrowthDimension A rankBound
      (W.blockExponent + W.coverExponent)
      (W.blockExponent + W.coverExponent + maxExponent + steps))
    (hnumeric :
      ((rank * 2 ^ rank) *
          (2 ^ (2 * W.coverExponent + steps)) ^ (rank - 1)) ^ 2 ≤
        (2 ^ (2 * rankBound - 1)) ^ steps) :
    Nonempty (Lemma222Approximation A h rank) := by
  apply lemma222Approximation_of_block_of_dyadicLowerGrowth W
    safety maxExponent steps hlarge htarget hsteps
  · exact dyadicLowerGrowth_of_minimalDimension hrankBound hminimal
  · exact hnumeric

namespace Lemma222Approximation

variable {A : Finset ℤ} {h rank : ℕ} (W : Lemma222Approximation A h rank)

/-- The repeated block count does not exceed the available number of
summands. -/
theorem repeatedBlockCount_le :
    (h / (W.coverMultiplier * W.blockScale)) *
        (W.coverMultiplier * W.blockScale) ≤ h := by
  simpa [mul_comm] using
    Nat.mul_div_le h (W.coverMultiplier * W.blockScale)

/-- The final progression scale is positive. -/
theorem repeatedScale_pos :
    0 < (h / (W.coverMultiplier * W.blockScale)) * W.blockScale := by
  have hmpos : 0 < W.coverMultiplier * W.blockScale :=
    Nat.mul_pos W.coverMultiplier_pos W.blockScale_pos
  have hmle : W.coverMultiplier * W.blockScale ≤ h :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < 2)).trans W.large
  exact Nat.mul_pos (Nat.div_pos hmle hmpos) W.blockScale_pos

/-- The final progression scale is at most `h`. -/
theorem repeatedScale_le :
    (h / (W.coverMultiplier * W.blockScale)) * W.blockScale ≤ h := by
  calc
    (h / (W.coverMultiplier * W.blockScale)) * W.blockScale ≤
        (h / (W.coverMultiplier * W.blockScale)) *
          (W.coverMultiplier * W.blockScale) := by
      gcongr
      calc
        W.blockScale = 1 * W.blockScale := by simp
        _ ≤ W.coverMultiplier * W.blockScale :=
          Nat.mul_le_mul_right W.blockScale W.coverMultiplier_pos
    _ ≤ h := W.repeatedBlockCount_le

/-- Rounding down the number of covered blocks loses at most the explicit
factor `2 * coverMultiplier`. -/
theorem scale_lower :
    h ≤ (2 * W.coverMultiplier) *
      ((h / (W.coverMultiplier * W.blockScale)) * W.blockScale) := by
  let m := W.coverMultiplier * W.blockScale
  let q := h / m
  have hmpos : 0 < m := Nat.mul_pos W.coverMultiplier_pos W.blockScale_pos
  have hmle : m ≤ h := (Nat.le_mul_of_pos_left _ (by omega : 0 < 2)).trans W.large
  have hqpos : 0 < q := Nat.div_pos hmle hmpos
  have hmod : h % m < m := Nat.mod_lt h hmpos
  have hdecomp : h % m + m * q = h := Nat.mod_add_div h m
  have hm_le_mq : m ≤ m * q := by
    calc m = m * 1 := by simp
         _ ≤ m * q := Nat.mul_le_mul_left m hqpos
  have hh : h ≤ 2 * (m * q) := by omega
  dsimp [m, q] at hh ⊢
  calc
    h ≤ 2 * ((W.coverMultiplier * W.blockScale) *
        (h / (W.coverMultiplier * W.blockScale))) := hh
    _ = (2 * W.coverMultiplier) *
        ((h / (W.coverMultiplier * W.blockScale)) * W.blockScale) := by ring

/-- CFP Corollary 2.24: repeat the translated block from Lemma 2.22 and pad
the unused summands by zero.  All floor losses and constants are explicit. -/
noncomputable def toHApproximation :
    HApproximation A h rank 1 (2 * W.coverMultiplier) where
  progression := W.progression
  zero_mem := W.zero_mem
  contains := W.contains
  nondegenerate := W.nondegenerate
  scale := (h / (W.coverMultiplier * W.blockScale)) * W.blockScale
  scale_pos := W.repeatedScale_pos
  scale_le := W.repeatedScale_le
  scaleNum_pos := by simp
  scaleDen_pos := Nat.mul_pos (by omega) W.coverMultiplier_pos
  scale_lower := by simpa using W.scale_lower
  dilate_proper :=
    GAP.dilate_proper_mono W.progression W.repeatedScale_le_proper W.proper
  translatePoint :=
    (h / (W.coverMultiplier * W.blockScale) : ℤ) * W.blockTranslate
  covered := by
    let q := h / (W.coverMultiplier * W.blockScale)
    let m := W.coverMultiplier * W.blockScale
    have hiter := iterate_translate_subset W.blockCovered q
    have hcarrier :
        multifoldSumset q
            (BiluFreiman.integerCarrier
              (W.progression.dilate W.blockScale)) =
          BiluFreiman.integerCarrier
            (W.progression.dilate (q * W.blockScale)) := by
      rw [← integerCarrier_dilate_eq_multifoldSumset,
        GAP.dilate_dilate]
    rw [hcarrier] at hiter
    have hpad : multifoldSumset (q * m) A ⊆ multifoldSumset h A :=
      multifoldSumset_mono_index W.zero_mem W.repeatedBlockCount_le
    exact hiter.trans hpad

/-- CFP Lemma 2.26, specialized to the progression produced by Lemma 2.22.
The only loss between the paper's informal `\gg` and this exact statement is
the displayed constant `(4 * coverMultiplier)^rank`. -/
theorem h_pow_mul_boundingBox_volume_le (hrank : 0 < rank) :
    h ^ rank *
        (BoundingBox.dBoundingBox A rank hrank).progression.volume ≤
      (4 * W.coverMultiplier) ^ rank *
        (multifoldSumset h A).card := by
  have hbound := HApproximation.h_pow_mul_boundingBox_volume_le
    W.toHApproximation hrank
  rw [show 2 * (2 * W.coverMultiplier) = 4 * W.coverMultiplier by omega]
    at hbound
  simpa using hbound

/-- The properness clause of CFP Lemma 2.26, again specialized to a Lemma
2.22 certificate.  The hypothesis is an exact finite choice of the paper's
small constant: any `K` satisfying it makes the `floor (h / K)` dilation of
the minimal rank-`rank` bounding box proper. -/
theorem boundingBox_dilate_div_proper (hrank : 0 < rank) (K : ℕ)
    (hK :
      (4 * W.coverMultiplier) ^ rank * rank * 2 ^ (rank - 1) < K) :
    ((BoundingBox.dBoundingBox A rank hrank).progression.dilate
      (h / K)).Proper := by
  apply HApproximation.boundingBox_dilate_div_proper
    W.toHApproximation hrank K
  rw [show 2 * (2 * W.coverMultiplier) = 4 * W.coverMultiplier by omega]
  simpa using hK

/-- The `d ≤ beta + 1` part of CFP Lemma 2.26 for the output of Lemma
2.22.  The final implication is the exact finite large-`h` threshold. -/
theorem rank_le_beta_add_one_of_interval (beta n : ℕ)
    (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hnpower : n ≤ h ^ beta)
    (hlarge : beta + 1 < rank →
      (4 * W.coverMultiplier) ^ rank * h ^ (beta + 1) < h ^ rank) :
    rank ≤ beta + 1 := by
  apply HApproximation.rank_le_beta_add_one_of_interval
    W.toHApproximation beta n hh hn hA hnpower
  intro hrank
  have h := hlarge hrank
  rw [show 2 * (2 * W.coverMultiplier) = 4 * W.coverMultiplier by omega]
  simpa using h

/-- A simpler sufficient threshold for the preceding theorem: it is enough
that `h` exceed the fixed constant `(4*C)^rank`. -/
theorem rank_le_beta_add_one_of_interval_of_h_large (beta n : ℕ)
    (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hnpower : n ≤ h ^ beta)
    (hhlarge : (4 * W.coverMultiplier) ^ rank < h) :
    rank ≤ beta + 1 := by
  apply W.rank_le_beta_add_one_of_interval beta n hh hn hA hnpower
  intro hrank
  have hexponent : 1 ≤ rank - (beta + 1) := by omega
  have hpow : h ≤ h ^ (rank - (beta + 1)) := by
    simpa using pow_le_pow_right' (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh))
      hexponent
  have hconstant :
      (4 * W.coverMultiplier) ^ rank < h ^ (rank - (beta + 1)) :=
    hhlarge.trans_le hpow
  calc
    (4 * W.coverMultiplier) ^ rank * h ^ (beta + 1) <
        h ^ (rank - (beta + 1)) * h ^ (beta + 1) :=
      Nat.mul_lt_mul_of_pos_right hconstant (pow_pos hh _)
    _ = h ^ rank := by
      rw [← pow_add]
      congr 1
      omega

end Lemma222Approximation

/-! ## The least certified dimension -/

/-- Rank `d` supports the fixed-scale `h`-approximation. -/
def HasHApproximation (A : Finset ℤ) (h scaleNum scaleDen d : ℕ) : Prop :=
  Nonempty (HApproximation A h d scaleNum scaleDen)

/-- The exact Lemma 2.22 certificate gives the approximation asserted by
CFP Corollary 2.24. -/
theorem Lemma222Approximation.hasHApproximation {A : Finset ℤ}
    {h rank : ℕ} (W : Lemma222Approximation A h rank) :
    HasHApproximation A h 1 (2 * W.coverMultiplier) rank :=
  ⟨W.toHApproximation⟩

/-- The least rank supporting an approximation at the fixed rational scale.
It is zero when no such rank exists; all specification lemmas below state
the mathematically relevant nonemptiness hypothesis explicitly. -/
noncomputable def hDimension (A : Finset ℤ) (h scaleNum scaleDen : ℕ) : ℕ :=
  sInf {d : ℕ | HasHApproximation A h scaleNum scaleDen d}

theorem hDimension_hasHApproximation {A : Finset ℤ}
    {h scaleNum scaleDen : ℕ}
    (hex : ∃ d, HasHApproximation A h scaleNum scaleDen d) :
    HasHApproximation A h scaleNum scaleDen
      (hDimension A h scaleNum scaleDen) := by
  change sInf {d : ℕ | HasHApproximation A h scaleNum scaleDen d} ∈
    {d : ℕ | HasHApproximation A h scaleNum scaleDen d}
  apply Nat.sInf_mem
  obtain ⟨d, hd⟩ := hex
  exact ⟨d, hd⟩

theorem hDimension_le_of_hasHApproximation {A : Finset ℤ}
    {h scaleNum scaleDen d : ℕ}
    (hd : HasHApproximation A h scaleNum scaleDen d) :
    hDimension A h scaleNum scaleDen ≤ d := by
  exact Nat.sInf_le hd

/-- The rank bound in Lemma 2.22 transfers to the least certified
`h`-dimension. -/
theorem hDimension_le_of_lemma222 {A : Finset ℤ} {h rank : ℕ}
    (W : Lemma222Approximation A h rank) :
    hDimension A h 1 (2 * W.coverMultiplier) ≤ rank :=
  hDimension_le_of_hasHApproximation W.hasHApproximation

/-- The explicit rank bound carried by Lemma 2.22 bounds `hDimension`. -/
theorem hDimension_le_lemma222_rankBound {A : Finset ℤ} {h rank : ℕ}
    (W : Lemma222Approximation A h rank) :
    hDimension A h 1 (2 * W.coverMultiplier) ≤ W.rankBound :=
  (hDimension_le_of_lemma222 W).trans W.rank_le

/-- Lemma 2.22's certificate, the interval bound, and the large-`h`
inequality together give the source bound on `h`-dimension. -/
theorem hDimension_le_beta_add_one_of_lemma222 {A : Finset ℤ}
    {h rank n : ℕ} (W : Lemma222Approximation A h rank) (beta : ℕ)
    (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hnpower : n ≤ h ^ beta)
    (hlarge : beta + 1 < rank →
      (4 * W.coverMultiplier) ^ rank * h ^ (beta + 1) < h ^ rank) :
    hDimension A h 1 (2 * W.coverMultiplier) ≤ beta + 1 :=
  (hDimension_le_of_lemma222 W).trans
    (W.rank_le_beta_add_one_of_interval beta n hh hn hA hnpower hlarge)

/-- Convenient threshold form of the preceding `h`-dimension bound. -/
theorem hDimension_le_beta_add_one_of_lemma222_of_h_large
    {A : Finset ℤ} {h rank n : ℕ}
    (W : Lemma222Approximation A h rank) (beta : ℕ)
    (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hnpower : n ≤ h ^ beta)
    (hhlarge : (4 * W.coverMultiplier) ^ rank < h) :
    hDimension A h 1 (2 * W.coverMultiplier) ≤ beta + 1 :=
  (hDimension_le_of_lemma222 W).trans
    (W.rank_le_beta_add_one_of_interval_of_h_large
      beta n hh hn hA hnpower hhlarge)

/-- Any uniform rank bound furnished by Lemma 2.22 bounds the resulting
`h`-dimension.  In the paper the proof supplies `rankBound = floor β + 1`
after the explicit sufficiently-large threshold is met. -/
theorem hDimension_le_rankBound {A : Finset ℤ}
    {h scaleNum scaleDen rankBound : ℕ}
    (hex : ∃ d ≤ rankBound,
      HasHApproximation A h scaleNum scaleDen d) :
    hDimension A h scaleNum scaleDen ≤ rankBound := by
  obtain ⟨d, hdD, hd⟩ := hex
  exact (hDimension_le_of_hasHApproximation hd).trans hdD

/-- A canonical actual approximation at the least certified dimension. -/
noncomputable def hDimensionApproximation (A : Finset ℤ)
    (h scaleNum scaleDen : ℕ)
    (hex : ∃ d, HasHApproximation A h scaleNum scaleDen d) :
    HApproximation A h (hDimension A h scaleNum scaleDen)
      scaleNum scaleDen :=
  Classical.choice (hDimension_hasHApproximation hex)

/-- The canonical least-rank approximation gives the upper GAP envelope
`hA ⊆ hP` from Corollary 2.24. -/
theorem hDimension_multifoldSumset_subset_dilate {A : Finset ℤ}
    {h scaleNum scaleDen : ℕ}
    (hex : ∃ d, HasHApproximation A h scaleNum scaleDen d) :
    multifoldSumset h A ⊆
      BiluFreiman.integerCarrier
        ((hDimensionApproximation A h scaleNum scaleDen hex).progression.dilate h) :=
  (hDimensionApproximation A h scaleNum scaleDen hex).multifoldSumset_subset_dilate

/-- The cardinality estimate of Lemma 2.26 at the least certified rank.
It is stated without division, so the dependence on the fixed rational
scale is exact over natural numbers. -/
theorem hDimension_h_pow_mul_boundingBox_volume_le {A : Finset ℤ}
    {h scaleNum scaleDen : ℕ}
    (hex : ∃ d, HasHApproximation A h scaleNum scaleDen d)
    (hdim : 0 < hDimension A h scaleNum scaleDen) :
    (scaleNum * h) ^ hDimension A h scaleNum scaleDen *
        (BoundingBox.dBoundingBox A (hDimension A h scaleNum scaleDen)
          hdim).progression.volume ≤
      (2 * scaleDen) ^ hDimension A h scaleNum scaleDen *
        (multifoldSumset h A).card :=
  HApproximation.h_pow_mul_boundingBox_volume_le
    (hDimensionApproximation A h scaleNum scaleDen hex) hdim

/-- The boundedness part of CFP Lemma 2.26 for the least certified
`h`-dimension, with the interval, power, and finite threshold hypotheses
all exposed. -/
theorem hDimension_le_beta_add_one_of_interval {A : Finset ℤ}
    {h scaleNum scaleDen n : ℕ} (beta : ℕ)
    (hex : ∃ d, HasHApproximation A h scaleNum scaleDen d)
    (hh : 0 < h) (hn : 0 < n)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hnpower : n ≤ h ^ beta)
    (hlarge : beta + 1 < hDimension A h scaleNum scaleDen →
      (2 * scaleDen) ^ hDimension A h scaleNum scaleDen *
          h ^ (beta + 1) <
        (scaleNum * h) ^ hDimension A h scaleNum scaleDen) :
    hDimension A h scaleNum scaleDen ≤ beta + 1 :=
  HApproximation.rank_le_beta_add_one_of_interval
    (hDimensionApproximation A h scaleNum scaleDen hex)
    beta n hh hn hA hnpower hlarge

/-- The properness estimate of Lemma 2.26 at the least certified rank.  As
above, `K` is an exact natural denominator for the small dimension-dependent
constant in the paper. -/
theorem hDimension_boundingBox_dilate_div_proper {A : Finset ℤ}
    {h scaleNum scaleDen : ℕ}
    (hex : ∃ d, HasHApproximation A h scaleNum scaleDen d)
    (hdim : 0 < hDimension A h scaleNum scaleDen) (K : ℕ)
    (hK :
      (2 * scaleDen) ^ hDimension A h scaleNum scaleDen *
          hDimension A h scaleNum scaleDen *
          2 ^ (hDimension A h scaleNum scaleDen - 1) <
        K * scaleNum ^ hDimension A h scaleNum scaleDen) :
    ((BoundingBox.dBoundingBox A (hDimension A h scaleNum scaleDen)
        hdim).progression.dilate (h / K)).Proper :=
  HApproximation.boundingBox_dilate_div_proper
    (hDimensionApproximation A h scaleNum scaleDen hex) hdim K hK

end Erdos186.CFP.HDimension
