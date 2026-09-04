/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.CyclicCompositions

/-!
# Erdős Problem 446: capped compositions

This file formalizes the deletion-and-rotation estimate in Ford's proof.
After one overlarge coordinate is deleted, the remaining tail has total at
most its length.  Averaging over its cyclic rotations gains the factor which
makes the union bound over all coordinates uniform in the dimension.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Weak compositions of `n` into `d` labelled parts. -/
def compositionsOf (d n : ℕ) : Finset (Fin d → ℕ) :=
  Finset.finAntidiagonal d n

theorem mem_compositionsOf {d n : ℕ} {b : Fin d → ℕ} :
    b ∈ compositionsOf d n ↔ ∑ i : Fin d, b i = n := by
  simp [compositionsOf]

theorem inv_compositionFactorial_eq_multinomial_div_of_mem
    {d n : ℕ} {b : Fin d → ℕ} (hb : b ∈ compositionsOf d n) :
    1 / compositionFactorial b =
      (Nat.multinomial Finset.univ b : ℝ) / (n.factorial : ℝ) := by
  have hsum : ∑ i : Fin d, b i = n := mem_compositionsOf.mp hb
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin d)) b
  rw [hsum] at hspec
  have hspecR :
      compositionFactorial b * (Nat.multinomial Finset.univ b : ℝ) =
        (n.factorial : ℝ) := by
    dsimp [compositionFactorial]
    exact_mod_cast hspec
  have hfacPos : (0 : ℝ) < n.factorial := by positivity
  have hweightPos : 0 < compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  field_simp [hfacPos.ne', hweightPos.ne']
  nlinarith

theorem sum_multinomial_compositionsOf (d n : ℕ) :
    (∑ b ∈ compositionsOf d n,
      Nat.multinomial Finset.univ b) = d ^ n := by
  have h := Finset.sum_pow_eq_sum_piAntidiag
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun _i : Fin d ↦ (1 : ℕ)) n
  have hfin :
      Finset.piAntidiag (Finset.univ : Finset (Fin d)) n =
        compositionsOf d n := by
    ext b
    simp [compositionsOf]
  rw [← hfin]
  simpa using h.symm

/-- Exponential multinomial identity in reciprocal-factorial form. -/
theorem sum_inv_compositionFactorial_compositionsOf (d n : ℕ) :
    (∑ b ∈ compositionsOf d n, 1 / compositionFactorial b) =
      (d : ℝ) ^ n / (n.factorial : ℝ) := by
  calc
    (∑ b ∈ compositionsOf d n, 1 / compositionFactorial b) =
        ∑ b ∈ compositionsOf d n,
          (Nat.multinomial Finset.univ b : ℝ) /
            (n.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact inv_compositionFactorial_eq_multinomial_div_of_mem hb
    _ = (((∑ b ∈ compositionsOf d n,
          Nat.multinomial Finset.univ b) : ℕ) : ℝ) /
          (n.factorial : ℝ) := by
      rw [← Finset.sum_div]
      congr 1
      norm_cast
    _ = (d : ℝ) ^ n / (n.factorial : ℝ) := by
      rw [sum_multinomial_compositionsOf]
      norm_cast

theorem prod_compositionFactor_eq_pow_div {d n : ℕ}
    {b : Fin d → ℕ} (hb : b ∈ compositionsOf d n) :
    (List.ofFn (compositionFactor b)).prod =
      (2 : ℝ) ^ n / (2 : ℝ) ^ d := by
  have hsum : ∑ i : Fin d, b i = n := mem_compositionsOf.mp hb
  rw [Fin.prod_ofFn]
  simp only [compositionFactor]
  calc
    (∏ i : Fin d, (2 : ℝ) ^ b i / 2) =
        (∏ i : Fin d, (2 : ℝ) ^ b i) /
          ∏ _i : Fin d, (2 : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = (2 : ℝ) ^ (∑ i : Fin d, b i) / (2 : ℝ) ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    _ = (2 : ℝ) ^ n / (2 : ℝ) ^ d := by rw [hsum]

theorem inv_prod_compositionFactor_eq_pow_sub {d n : ℕ}
    (hnd : n ≤ d) {b : Fin d → ℕ} (hb : b ∈ compositionsOf d n) :
    1 / (List.ofFn (compositionFactor b)).prod = (2 : ℝ) ^ (d - n) := by
  rw [prod_compositionFactor_eq_pow_div hb]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [one_div, inv_div]
  have hpow : (2 : ℝ) ^ d =
      (2 : ℝ) ^ (d - n) * (2 : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  apply (div_eq_iff (pow_ne_zero _ htwo)).2
  simpa [mul_comm] using hpow

theorem prod_compositionFactor_le_one {d n : ℕ}
    (hnd : n ≤ d) {b : Fin d → ℕ} (hb : b ∈ compositionsOf d n) :
    (List.ofFn (compositionFactor b)).prod ≤ 1 := by
  rw [prod_compositionFactor_eq_pow_div hb]
  exact (div_le_one (by positivity)).2 (by gcongr <;> norm_num)

theorem compositionPenalty_pos_of_pos_length {d : ℕ} (hd : 0 < d)
    (b : Fin d → ℕ) : 0 < compositionPenalty b := by
  apply prefixProductMass_pos
  · intro hnil
    have := congrArg List.length hnil
    simp [hd.ne'] at this
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact compositionFactor_pos b i

/-- The cyclic estimate for the tail left after deleting a large
coordinate.  The extra `1` in the denominator is the prefix ending at the
deleted coordinate itself. -/
theorem sum_inv_one_add_compositionPenalty_rotate_le {d n : ℕ}
    (hd : 0 < d) (hnd : n ≤ d) {b : Fin d → ℕ}
    (hb : b ∈ compositionsOf d n) :
    (∑ r : Fin d,
      1 / (1 + compositionPenalty (rotateComposition r b))) ≤
        (2 : ℝ) ^ (d - n) := by
  let l := List.ofFn (compositionFactor b)
  have hl : l ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [l, hd.ne'] at this
  have hpos : ∀ x ∈ l, 0 < x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact compositionFactor_pos b i
  have hprodLe : l.prod ≤ 1 := prod_compositionFactor_le_one hnd hb
  have hcycle := sum_inv_prefixProductMass_rotate_le_inv_prod hl hpos hprodLe
  calc
    (∑ r : Fin d,
        1 / (1 + compositionPenalty (rotateComposition r b))) ≤
        ∑ r : Fin d, 1 / compositionPenalty (rotateComposition r b) := by
      apply Finset.sum_le_sum
      intro r _hr
      have hpenPos := compositionPenalty_pos_of_pos_length hd
        (rotateComposition r b)
      exact (one_div_le_one_div_of_le hpenPos (le_add_of_nonneg_left zero_le_one))
    _ = ∑ r : Fin d,
          1 / prefixProductMass (l.rotate r.val) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [compositionPenalty]
      have hfactor :
          compositionFactor (rotateComposition r b) =
            rotateComposition r (compositionFactor b) := by
        funext i
        rfl
      rw [hfactor, ofFn_rotateComposition]
    _ = ∑ r ∈ Finset.range d,
          1 / prefixProductMass (l.rotate r) := by
      exact (Finset.sum_range
        (fun r : ℕ ↦ 1 / prefixProductMass (l.rotate r))).symm
    _ ≤ 1 / l.prod := by simpa [l] using hcycle
    _ = (2 : ℝ) ^ (d - n) := by
      exact inv_prod_compositionFactor_eq_pow_sub hnd hb

noncomputable def deletedTailWeight {d : ℕ} (b : Fin d → ℕ) : ℝ :=
  1 / (compositionFactorial b * (1 + compositionPenalty b))

theorem deletedTailWeight_nonneg {d : ℕ} (b : Fin d → ℕ) :
    0 ≤ deletedTailWeight b := by
  exact div_nonneg zero_le_one (mul_nonneg (by
    dsimp [compositionFactorial]
    positivity) (by
      have : 0 ≤ compositionPenalty b := prefixProductMass_nonneg fun x hx ↦ by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact (compositionFactor_pos b i).le
      positivity))

theorem deletedTailWeight_rotate {d : ℕ} (r : Fin d)
    (b : Fin d → ℕ) :
    deletedTailWeight (rotateComposition r b) =
      (1 / compositionFactorial b) *
        (1 / (1 + compositionPenalty (rotateComposition r b))) := by
  rw [deletedTailWeight, compositionFactorial_rotate]
  have hfac : compositionFactorial b ≠ 0 := by
    dsimp [compositionFactorial]
    positivity
  field_simp [hfac]

/-- Averaging all cyclic tail rotations gives the factorial sum with a
factor equal to the tail length. -/
theorem card_mul_sum_deletedTailWeight_le (d n : ℕ)
    (hd : 0 < d) (hnd : n ≤ d) :
    (d : ℝ) * (∑ b ∈ compositionsOf d n, deletedTailWeight b) ≤
      (2 : ℝ) ^ (d - n) *
        ((d : ℝ) ^ n / (n.factorial : ℝ)) := by
  calc
    (d : ℝ) * (∑ b ∈ compositionsOf d n, deletedTailWeight b) =
        ∑ r : Fin d, ∑ b ∈ compositionsOf d n, deletedTailWeight b := by
      simp
    _ = ∑ r : Fin d, ∑ b ∈ compositionsOf d n,
          deletedTailWeight (rotateComposition r b) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact Finset.sum_equiv (rotateComposition r)
        (fun b ↦ by simp only [mem_compositionsOf, sum_rotateComposition])
        (fun _b _hb ↦ rfl) |>.symm
    _ = ∑ b ∈ compositionsOf d n, ∑ r : Fin d,
          deletedTailWeight (rotateComposition r b) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b ∈ compositionsOf d n,
          (1 / compositionFactorial b) * (2 : ℝ) ^ (d - n) := by
      apply Finset.sum_le_sum
      intro b hb
      simp_rw [deletedTailWeight_rotate]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left
      · exact sum_inv_one_add_compositionPenalty_rotate_le hd hnd hb
      · exact div_nonneg zero_le_one (by
          dsimp [compositionFactorial]
          positivity)
    _ = (2 : ℝ) ^ (d - n) *
          ((d : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [← Finset.sum_mul, sum_inv_compositionFactorial_compositionsOf]
      ring

/-! ## Splitting a composition at the deleted coordinate -/

/-- Split a tuple into the coordinates before a distinguished coordinate,
that coordinate, and the coordinates after it. -/
def splitCompositionEquiv (j d : ℕ) :
    ((Fin j → ℕ) × (ℕ × (Fin d → ℕ))) ≃
      (Fin (j + (d + 1)) → ℕ) :=
  (Equiv.prodCongr (Equiv.refl (Fin j → ℕ))
      (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ℕ))).trans
    (Fin.appendEquiv j (d + 1))

/-- Reassemble a tuple from the prefix, distinguished coordinate, and tail. -/
def joinComposition {j d : ℕ} (a : Fin j → ℕ) (l : ℕ)
    (c : Fin d → ℕ) : Fin (j + (d + 1)) → ℕ :=
  splitCompositionEquiv j d (a, l, c)

@[simp] theorem joinComposition_eq_append {j d : ℕ}
    (a : Fin j → ℕ) (l : ℕ) (c : Fin d → ℕ) :
    joinComposition a l c = Fin.append a (Fin.cons l c) := rfl

theorem sum_joinComposition {j d : ℕ} (a : Fin j → ℕ)
    (l : ℕ) (c : Fin d → ℕ) :
    (∑ i, joinComposition a l c i) =
      (∑ i, a i) + l + ∑ i, c i := by
  rw [joinComposition_eq_append, Fin.sum_univ_add, Fin.sum_univ_succ]
  simp [add_assoc]

theorem compositionFactorial_joinComposition {j d : ℕ}
    (a : Fin j → ℕ) (l : ℕ) (c : Fin d → ℕ) :
    compositionFactorial (joinComposition a l c) =
      compositionFactorial a * (l.factorial : ℝ) * compositionFactorial c := by
  simp only [compositionFactorial, joinComposition_eq_append,
    Fin.prod_univ_add, Fin.prod_univ_succ, Fin.append_left,
    Fin.append_right, Fin.cons_zero, Fin.cons_succ]
  ring

theorem compositionFactor_joinComposition {j d : ℕ}
    (a : Fin j → ℕ) (l : ℕ) (c : Fin d → ℕ) :
    compositionFactor (joinComposition a l c) =
      Fin.append (compositionFactor a)
        (Fin.cons ((2 : ℝ) ^ l / 2) (compositionFactor c)) := by
  funext i
  refine Fin.addCases (fun q ↦ ?_) (fun q ↦ ?_) i
  · simp [compositionFactor]
  · refine Fin.cases ?_ (fun t ↦ ?_) q
    · simp [compositionFactor]
    · simp [compositionFactor]

theorem compositionPenalty_joinComposition {j d : ℕ}
    (a : Fin j → ℕ) (l : ℕ) (c : Fin d → ℕ) :
    compositionPenalty (joinComposition a l c) =
      prefixProductMass (List.ofFn (compositionFactor a)) +
        (List.ofFn (compositionFactor a)).prod *
          (((2 : ℝ) ^ l / 2) * (1 + compositionPenalty c)) := by
  rw [compositionPenalty, compositionFactor_joinComposition,
    List.ofFn_fin_append, prefixProductMass_append]
  simp only [List.ofFn_cons, List.prod_cons, List.prod_nil,
    prefixProductMass_cons, compositionPenalty]

theorem prod_compositionFactor_eq_pow_sum_div {j : ℕ}
    (a : Fin j → ℕ) :
    (List.ofFn (compositionFactor a)).prod =
      (2 : ℝ) ^ (∑ i, a i) / (2 : ℝ) ^ j := by
  rw [Fin.prod_ofFn]
  simp only [compositionFactor]
  calc
    (∏ i : Fin j, (2 : ℝ) ^ a i / 2) =
        (∏ i : Fin j, (2 : ℝ) ^ a i) /
          ∏ _i : Fin j, (2 : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = (2 : ℝ) ^ (∑ i : Fin j, a i) / (2 : ℝ) ^ j := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

theorem compositionCycleWeight_join_le {j d s l : ℕ}
    {a : Fin j → ℕ} (ha : a ∈ compositionsOf j s)
    (c : Fin d → ℕ) :
    compositionCycleWeight (joinComposition a l c) ≤
      ((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
        (1 / compositionFactorial a) *
        (1 / (l.factorial : ℝ)) * deletedTailWeight c := by
  have hsum : ∑ i, a i = s := mem_compositionsOf.mp ha
  have hprefixNonneg :
      0 ≤ prefixProductMass (List.ofFn (compositionFactor a)) :=
    prefixProductMass_nonneg fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact (compositionFactor_pos a i).le
  have hprodPos : 0 < (List.ofFn (compositionFactor a)).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact compositionFactor_pos a i
  have hfactorPos : 0 < (2 : ℝ) ^ l / 2 := by positivity
  have htailNonneg : 0 ≤ compositionPenalty c :=
    prefixProductMass_nonneg fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact (compositionFactor_pos c i).le
  have hfacAPos : 0 < compositionFactorial a := by
    dsimp [compositionFactorial]
    positivity
  have hfacCPos : 0 < compositionFactorial c := by
    dsimp [compositionFactorial]
    positivity
  have hlFacPos : (0 : ℝ) < l.factorial := by positivity
  have hdenomPos : 0 < compositionFactorial (joinComposition a l c) *
      compositionPenalty (joinComposition a l c) := by
    apply mul_pos
    · dsimp [compositionFactorial]
      positivity
    · rw [compositionPenalty_joinComposition]
      positivity
  have hsmallDenomPos : 0 <
      (compositionFactorial a * (l.factorial : ℝ) * compositionFactorial c) *
        ((List.ofFn (compositionFactor a)).prod *
          (((2 : ℝ) ^ l / 2) * (1 + compositionPenalty c))) := by
    exact mul_pos (mul_pos (mul_pos hfacAPos hlFacPos) hfacCPos)
      (mul_pos hprodPos (mul_pos hfactorPos (by linarith)))
  have hdenomLe :
      (compositionFactorial a * (l.factorial : ℝ) * compositionFactorial c) *
          ((List.ofFn (compositionFactor a)).prod *
            (((2 : ℝ) ^ l / 2) * (1 + compositionPenalty c))) ≤
        compositionFactorial (joinComposition a l c) *
          compositionPenalty (joinComposition a l c) := by
    rw [compositionFactorial_joinComposition,
      compositionPenalty_joinComposition]
    apply mul_le_mul_of_nonneg_left
    · exact le_add_of_nonneg_left hprefixNonneg
    · exact mul_nonneg (mul_nonneg hfacAPos.le hlFacPos.le) hfacCPos.le
  rw [compositionCycleWeight]
  calc
    1 / (compositionFactorial (joinComposition a l c) *
          compositionPenalty (joinComposition a l c)) ≤
        1 / ((compositionFactorial a * (l.factorial : ℝ) *
          compositionFactorial c) *
          ((List.ofFn (compositionFactor a)).prod *
            (((2 : ℝ) ^ l / 2) * (1 + compositionPenalty c)))) :=
      one_div_le_one_div_of_le hsmallDenomPos hdenomLe
    _ = ((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
        (1 / compositionFactorial a) *
        (1 / (l.factorial : ℝ)) * deletedTailWeight c := by
      rw [prod_compositionFactor_eq_pow_sum_div, hsum, deletedTailWeight]
      rw [pow_add (2 : ℝ) s l, pow_succ]
      field_simp

/-! ## Fiber decomposition of the bad-coordinate sum -/

abbrev SplitComposition (j d : ℕ) :=
  (Fin j → ℕ) × (ℕ × (Fin d → ℕ))

def splitPrefix {j d : ℕ} (x : SplitComposition j d) : Fin j → ℕ := x.1

def splitValue {j d : ℕ} (x : SplitComposition j d) : ℕ := x.2.1

def splitTail {j d : ℕ} (x : SplitComposition j d) : Fin d → ℕ := x.2.2

def splitBadCompositions (j d k L : ℕ) :
    Finset (SplitComposition j d) :=
  ((compositionsOf (j + (d + 1)) k).filter fun b ↦
      L < b (Fin.natAdd j (0 : Fin (d + 1)))).map
    (splitCompositionEquiv j d).symm.toEmbedding

@[simp] theorem splitCompositionEquiv_apply (j d : ℕ)
    (x : SplitComposition j d) :
    splitCompositionEquiv j d x =
      joinComposition x.1 x.2.1 x.2.2 := rfl

theorem mem_splitBadCompositions {j d k L : ℕ}
    {x : SplitComposition j d} :
    x ∈ splitBadCompositions j d k L ↔
      (∑ i, splitPrefix x i) + splitValue x +
          ∑ i, splitTail x i = k ∧
        L < splitValue x := by
  rw [splitBadCompositions, Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hxeq : splitCompositionEquiv j d x = b := by
      calc
        splitCompositionEquiv j d x =
            splitCompositionEquiv j d ((splitCompositionEquiv j d).symm b) :=
          congrArg (splitCompositionEquiv j d) hbx.symm
        _ = b := (splitCompositionEquiv j d).apply_symm_apply b
    have hbmem := Finset.mem_filter.mp hb
    constructor
    · have hsum := mem_compositionsOf.mp hbmem.1
      rw [← hxeq, splitCompositionEquiv_apply,
        sum_joinComposition] at hsum
      exact hsum
    · have hl := hbmem.2
      rw [← hxeq, splitCompositionEquiv_apply,
        joinComposition_eq_append] at hl
      simpa [splitValue] using hl
  · rintro ⟨hsum, hl⟩
    refine ⟨splitCompositionEquiv j d x, ?_, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · rw [mem_compositionsOf, splitCompositionEquiv_apply,
        sum_joinComposition]
      exact hsum
    · rw [splitCompositionEquiv_apply, joinComposition_eq_append]
      simpa [splitValue] using hl
    · exact (splitCompositionEquiv j d).symm_apply_apply x

theorem sum_bad_compositionCycleWeight_eq_split (j d k L : ℕ) :
    (∑ b ∈ (compositionsOf (j + (d + 1)) k).filter (fun b ↦
        L < b (Fin.natAdd j (0 : Fin (d + 1)))),
      compositionCycleWeight b) =
    ∑ x ∈ splitBadCompositions j d k L,
      compositionCycleWeight (splitCompositionEquiv j d x) := by
  rw [splitBadCompositions, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro b hb
  change compositionCycleWeight b = compositionCycleWeight
    (splitCompositionEquiv j d ((splitCompositionEquiv j d).symm b))
  rw [(splitCompositionEquiv j d).apply_symm_apply]

def pairToSplitEmbedding {j d : ℕ} (l : ℕ) :
    ((Fin j → ℕ) × (Fin d → ℕ)) ↪ SplitComposition j d where
  toFun ac := (ac.1, l, ac.2)
  inj' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    exact Prod.ext (congrArg (fun x ↦ x.1) h)
      (congrArg (fun x ↦ x.2.2) h)

theorem splitBad_fiber_eq_map_product {j d k L l s : ℕ}
    (hlL : L < l) (hlk : l ≤ k) (hsk : s ≤ k - l) :
    ((splitBadCompositions j d k L).filter (fun x ↦ splitValue x = l)).filter
        (fun x ↦ ∑ i, splitPrefix x i = s) =
      ((compositionsOf j s) ×ˢ (compositionsOf d (k - l - s))).map
        (pairToSplitEmbedding l) := by
  ext x
  simp only [Finset.mem_filter, mem_splitBadCompositions, Finset.mem_map,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨htotal, hbad⟩, hvalue⟩, hprefix⟩
    let a : Fin j → ℕ := splitPrefix x
    let c : Fin d → ℕ := splitTail x
    have hprefixA : ∑ i, a i = s := by simpa [a] using hprefix
    have htotal' : s + l + ∑ i, c i = k := by
      calc
        s + l + ∑ i, c i =
            (∑ i, splitPrefix x i) + splitValue x +
              ∑ i, splitTail x i := by
          rw [hprefix, hvalue]
        _ = k := htotal
    have htail : ∑ i, c i = k - l - s := by
      change ∑ i, c i = _
      omega
    refine ⟨(a, c), ⟨mem_compositionsOf.mpr ?_,
      mem_compositionsOf.mpr htail⟩, ?_⟩
    · exact hprefixA
    · rcases x with ⟨xPrefix, xValue, xTail⟩
      simp only [a, c, splitPrefix, splitTail, splitValue] at hvalue ⊢
      subst xValue
      rfl
  · rintro ⟨ac, hac, rfl⟩
    rcases hac with ⟨ha, hc⟩
    have hsumA := mem_compositionsOf.mp ha
    have hsumC := mem_compositionsOf.mp hc
    change (((∑ i, ac.1 i) + l + ∑ i, ac.2 i = k ∧ L < l) ∧
      l = l) ∧ ∑ i, ac.1 i = s
    constructor
    · constructor
      · exact ⟨by omega, hlL⟩
      · rfl
    · exact hsumA

theorem sum_splitBad_fiber_eq_product {j d k L l s : ℕ}
    (hlL : L < l) (hlk : l ≤ k) (hsk : s ≤ k - l) :
    (∑ x ∈ ((splitBadCompositions j d k L).filter
        (fun x ↦ splitValue x = l)).filter
          (fun x ↦ ∑ i, splitPrefix x i = s),
      compositionCycleWeight (splitCompositionEquiv j d x)) =
      ∑ ac ∈ (compositionsOf j s) ×ˢ
          (compositionsOf d (k - l - s)),
        compositionCycleWeight (joinComposition ac.1 l ac.2) := by
  rw [splitBad_fiber_eq_map_product hlL hlk hsk, Finset.sum_map]
  rfl

theorem sum_splitBad_eq_nested (j d k L : ℕ) :
    (∑ x ∈ splitBadCompositions j d k L,
      compositionCycleWeight (splitCompositionEquiv j d x)) =
      ∑ l ∈ Finset.Icc (L + 1) k,
        ∑ s ∈ Finset.range (k - l + 1),
          ∑ ac ∈ (compositionsOf j s) ×ˢ
              (compositionsOf d (k - l - s)),
            compositionCycleWeight (joinComposition ac.1 l ac.2) := by
  have hlmaps : ∀ x ∈ splitBadCompositions j d k L,
      splitValue x ∈ Finset.Icc (L + 1) k := by
    intro x hx
    have hx' := mem_splitBadCompositions.mp hx
    rw [Finset.mem_Icc]
    constructor
    · omega
    · have hprefix : 0 ≤ ∑ i, splitPrefix x i := Nat.zero_le _
      have htail : 0 ≤ ∑ i, splitTail x i := Nat.zero_le _
      omega
  rw [← Finset.sum_fiberwise_of_maps_to hlmaps]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_Icc.mp hl
  let S := (splitBadCompositions j d k L).filter
    (fun x ↦ splitValue x = l)
  have hsmaps : ∀ x ∈ S,
      (∑ i, splitPrefix x i) ∈ Finset.range (k - l + 1) := by
    intro x hx
    have hxFilter := Finset.mem_filter.mp hx
    have hxSplit := mem_splitBadCompositions.mp hxFilter.1
    rw [Finset.mem_range]
    have htail : 0 ≤ ∑ i, splitTail x i := Nat.zero_le _
    omega
  change (∑ x ∈ S,
      compositionCycleWeight (splitCompositionEquiv j d x)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hsmaps]
  apply Finset.sum_congr rfl
  intro s hs
  have hsk : s ≤ k - l := by
    have := Finset.mem_range.mp hs
    omega
  exact sum_splitBad_fiber_eq_product (by omega) hl'.2 hsk

theorem card_mul_sum_joinComposition_le
    {j d k l s : ℕ} (hd : 0 < d) (hdim : k = j + (d + 1))
    (hlk : l ≤ k) (hsk : s ≤ k - l) (hj : j + 1 ≤ s + l) :
    (d : ℝ) *
        (∑ ac ∈ (compositionsOf j s) ×ˢ
            (compositionsOf d (k - l - s)),
          compositionCycleWeight (joinComposition ac.1 l ac.2)) ≤
      ((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
        ((j : ℝ) ^ s / (s.factorial : ℝ)) *
        (1 / (l.factorial : ℝ)) *
        ((2 : ℝ) ^ (d - (k - l - s)) *
          ((d : ℝ) ^ (k - l - s) /
            ((k - l - s).factorial : ℝ))) := by
  let A := compositionsOf j s
  let C := compositionsOf d (k - l - s)
  let Q : ℝ := (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)
  let R : ℝ := 1 / (l.factorial : ℝ)
  have hnle : k - l - s ≤ d := by omega
  have hsum :
      (∑ ac ∈ A ×ˢ C,
          compositionCycleWeight (joinComposition ac.1 l ac.2)) ≤
        Q * (∑ a ∈ A, 1 / compositionFactorial a) * R *
          (∑ c ∈ C, deletedTailWeight c) := by
    calc
      (∑ ac ∈ A ×ˢ C,
          compositionCycleWeight (joinComposition ac.1 l ac.2)) ≤
          ∑ ac ∈ A ×ˢ C,
            Q * (1 / compositionFactorial ac.1) * R *
              deletedTailWeight ac.2 := by
        apply Finset.sum_le_sum
        intro ac hac
        have ha : ac.1 ∈ compositionsOf j s := by
          exact (Finset.mem_product.mp hac).1
        simpa [Q, R] using compositionCycleWeight_join_le ha ac.2
      _ = ∑ a ∈ A, ∑ c ∈ C,
            Q * (1 / compositionFactorial a) * R *
              deletedTailWeight c := by
        rw [Finset.sum_product]
      _ = Q * (∑ a ∈ A, 1 / compositionFactorial a) * R *
          (∑ c ∈ C, deletedTailWeight c) := by
        calc
          (∑ a ∈ A, ∑ c ∈ C,
              Q * (1 / compositionFactorial a) * R *
                deletedTailWeight c) =
              ∑ a ∈ A,
                (Q * (1 / compositionFactorial a) * R) *
                  (∑ c ∈ C, deletedTailWeight c) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
          _ = (∑ a ∈ A, Q * (1 / compositionFactorial a) * R) *
                (∑ c ∈ C, deletedTailWeight c) := by
            rw [Finset.sum_mul]
          _ = Q * (∑ a ∈ A, 1 / compositionFactorial a) * R *
                (∑ c ∈ C, deletedTailWeight c) := by
            congr 1
            rw [Finset.mul_sum, Finset.sum_mul]
  have htail := card_mul_sum_deletedTailWeight_le d (k - l - s) hd hnle
  have hnonneg : 0 ≤ Q * (∑ a ∈ A, 1 / compositionFactorial a) * R := by
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hA : 0 ≤ ∑ a ∈ A, 1 / compositionFactorial a := by
      apply Finset.sum_nonneg
      intro a ha
      exact div_nonneg zero_le_one (by
        dsimp [compositionFactorial]
        positivity)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    exact mul_nonneg (mul_nonneg hQ hA) hR
  calc
    (d : ℝ) *
        (∑ ac ∈ (compositionsOf j s) ×ˢ
            (compositionsOf d (k - l - s)),
          compositionCycleWeight (joinComposition ac.1 l ac.2)) =
        (d : ℝ) *
          (∑ ac ∈ A ×ˢ C,
            compositionCycleWeight (joinComposition ac.1 l ac.2)) := rfl
    _ ≤ (d : ℝ) *
        (Q * (∑ a ∈ A, 1 / compositionFactorial a) * R *
          (∑ c ∈ C, deletedTailWeight c)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Q * (∑ a ∈ A, 1 / compositionFactorial a) * R) *
        ((d : ℝ) * (∑ c ∈ C, deletedTailWeight c)) := by ring
    _ ≤ (Q * (∑ a ∈ A, 1 / compositionFactorial a) * R) *
        ((2 : ℝ) ^ (d - (k - l - s)) *
          ((d : ℝ) ^ (k - l - s) /
            ((k - l - s).factorial : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (by simpa [C] using htail) hnonneg
    _ = _ := by
      rw [show (∑ a ∈ A, 1 / compositionFactorial a) =
          (j : ℝ) ^ s / (s.factorial : ℝ) by
        simpa [A] using sum_inv_compositionFactorial_compositionsOf j s]

theorem ford_power_ratio_cancel {j d k l s : ℕ}
    (hdim : k = j + (d + 1)) (hlk : l ≤ k)
    (hsk : s ≤ k - l) (hj : j + 1 ≤ s + l) :
    ((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
        (2 : ℝ) ^ (d - (k - l - s)) = 1 := by
  have hexp : j + 1 + (d - (k - l - s)) = s + l := by omega
  have hpow : (2 : ℝ) ^ (s + l) =
      (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (d - (k - l - s)) := by
    rw [← pow_add, hexp]
  rw [div_mul_eq_mul_div, ← hpow]
  field_simp

/-- The exponential generating functions for reciprocal factorials multiply
according to the ordinary binomial theorem. -/
theorem sum_pow_div_factorial_convolution (a b m : ℕ) :
    (∑ s ∈ Finset.range (m + 1),
      (a : ℝ) ^ s / (s.factorial : ℝ) *
        ((b : ℝ) ^ (m - s) / ((m - s).factorial : ℝ))) =
      ((a + b : ℕ) : ℝ) ^ m / (m.factorial : ℝ) := by
  have hterm : ∀ s ∈ Finset.range (m + 1),
      (a : ℝ) ^ s / (s.factorial : ℝ) *
          ((b : ℝ) ^ (m - s) / ((m - s).factorial : ℝ)) =
        ((m.choose s : ℕ) : ℝ) *
          ((a : ℝ) ^ s * (b : ℝ) ^ (m - s)) /
            (m.factorial : ℝ) := by
    intro s hs
    have hsm : s ≤ m := by
      have := Finset.mem_range.mp hs
      omega
    have hfac := Nat.choose_mul_factorial_mul_factorial hsm
    have hfacR :
        ((m.choose s : ℕ) : ℝ) * (s.factorial : ℝ) *
            ((m - s).factorial : ℝ) = (m.factorial : ℝ) := by
      exact_mod_cast hfac
    have hsfac : (s.factorial : ℝ) ≠ 0 := by positivity
    have hmsfac : ((m - s).factorial : ℝ) ≠ 0 := by positivity
    have hmfac : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hsfac, hmsfac, hmfac]
    rw [← hfacR]
    ring
  calc
    (∑ s ∈ Finset.range (m + 1),
        (a : ℝ) ^ s / (s.factorial : ℝ) *
          ((b : ℝ) ^ (m - s) / ((m - s).factorial : ℝ))) =
        ∑ s ∈ Finset.range (m + 1),
          ((m.choose s : ℕ) : ℝ) *
            ((a : ℝ) ^ s * (b : ℝ) ^ (m - s)) /
              (m.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (∑ s ∈ Finset.range (m + 1),
          (a : ℝ) ^ s * (b : ℝ) ^ (m - s) *
            ((m.choose s : ℕ) : ℝ)) /
          (m.factorial : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ((a + b : ℕ) : ℝ) ^ m / (m.factorial : ℝ) := by
      rw [show (((a + b : ℕ) : ℝ)) = (a : ℝ) + (b : ℝ) by norm_num,
        add_pow]

/-- Ford's deleted-coordinate estimate before the final factorial-tail
comparison. -/
theorem card_mul_badCoordinateWeight_le (j d L : ℕ)
    (hd : 0 < d) (hjL : j ≤ L) :
    (d : ℝ) *
        (∑ b ∈ (compositionsOf (j + (d + 1)) (j + (d + 1))).filter
            (fun b ↦ L < b (Fin.natAdd j (0 : Fin (d + 1)))),
          compositionCycleWeight b) ≤
      ∑ l ∈ Finset.Icc (L + 1) (j + (d + 1)),
        (1 / (l.factorial : ℝ)) *
          (((j + d : ℕ) : ℝ) ^ (j + (d + 1) - l) /
            ((j + (d + 1) - l).factorial : ℝ)) := by
  let k := j + (d + 1)
  rw [sum_bad_compositionCycleWeight_eq_split,
    sum_splitBad_eq_nested]
  change (d : ℝ) *
      (∑ l ∈ Finset.Icc (L + 1) k,
        ∑ s ∈ Finset.range (k - l + 1),
          ∑ ac ∈ (compositionsOf j s) ×ˢ
              (compositionsOf d (k - l - s)),
            compositionCycleWeight (joinComposition ac.1 l ac.2)) ≤ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.mul_sum]
  have hlIcc := Finset.mem_Icc.mp hl
  calc
    (∑ s ∈ Finset.range (k - l + 1),
        (d : ℝ) *
          (∑ ac ∈ (compositionsOf j s) ×ˢ
              (compositionsOf d (k - l - s)),
            compositionCycleWeight (joinComposition ac.1 l ac.2))) ≤
        ∑ s ∈ Finset.range (k - l + 1),
          ((j : ℝ) ^ s / (s.factorial : ℝ)) *
            (1 / (l.factorial : ℝ)) *
            ((d : ℝ) ^ (k - l - s) /
              ((k - l - s).factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsk : s ≤ k - l := by
        have := Finset.mem_range.mp hs
        omega
      have hj : j + 1 ≤ s + l := by omega
      calc
        (d : ℝ) *
            (∑ ac ∈ (compositionsOf j s) ×ˢ
                (compositionsOf d (k - l - s)),
              compositionCycleWeight (joinComposition ac.1 l ac.2)) ≤
            ((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
              ((j : ℝ) ^ s / (s.factorial : ℝ)) *
              (1 / (l.factorial : ℝ)) *
              ((2 : ℝ) ^ (d - (k - l - s)) *
                ((d : ℝ) ^ (k - l - s) /
                  ((k - l - s).factorial : ℝ))) :=
          card_mul_sum_joinComposition_le hd rfl hlIcc.2 hsk hj
        _ = ((j : ℝ) ^ s / (s.factorial : ℝ)) *
              (1 / (l.factorial : ℝ)) *
              ((d : ℝ) ^ (k - l - s) /
                ((k - l - s).factorial : ℝ)) := by
          have hcancel := ford_power_ratio_cancel
            (j := j) (d := d) (k := k) (l := l) (s := s)
            rfl hlIcc.2 hsk hj
          calc
            ((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
                ((j : ℝ) ^ s / (s.factorial : ℝ)) *
                (1 / (l.factorial : ℝ)) *
                ((2 : ℝ) ^ (d - (k - l - s)) *
                  ((d : ℝ) ^ (k - l - s) /
                    ((k - l - s).factorial : ℝ))) =
                (((2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (s + l)) *
                  (2 : ℝ) ^ (d - (k - l - s))) *
                  (((j : ℝ) ^ s / (s.factorial : ℝ)) *
                    (1 / (l.factorial : ℝ)) *
                    ((d : ℝ) ^ (k - l - s) /
                      ((k - l - s).factorial : ℝ))) := by ring
            _ = _ := by rw [hcancel]; ring
    _ = (1 / (l.factorial : ℝ)) *
          (((j + d : ℕ) : ℝ) ^ (k - l) /
            ((k - l).factorial : ℝ)) := by
      calc
        (∑ s ∈ Finset.range (k - l + 1),
            ((j : ℝ) ^ s / (s.factorial : ℝ)) *
              (1 / (l.factorial : ℝ)) *
              ((d : ℝ) ^ (k - l - s) /
                ((k - l - s).factorial : ℝ))) =
            (1 / (l.factorial : ℝ)) *
              ∑ s ∈ Finset.range (k - l + 1),
                ((j : ℝ) ^ s / (s.factorial : ℝ)) *
                  ((d : ℝ) ^ (k - l - s) /
                    ((k - l - s).factorial : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = (1 / (l.factorial : ℝ)) *
            (((j + d : ℕ) : ℝ) ^ (k - l) /
              ((k - l).factorial : ℝ)) := by
          rw [sum_pow_div_factorial_convolution]

theorem factorial_le_factorial_mul_pow {K l : ℕ} (hlK : l ≤ K) :
    K.factorial ≤ (K - l).factorial * K ^ l := by
  calc
    K.factorial = (K - l).factorial * K.descFactorial l := by
      rw [Nat.factorial_mul_descFactorial hlK]
    _ ≤ (K - l).factorial * K ^ l := by
      exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow K l)

theorem badCoordinateSummand_le_cycleMass {K l : ℕ}
    (hK : 0 < K) (hlK : l ≤ K) :
    (1 / (l.factorial : ℝ)) *
        (((K - 1 : ℕ) : ℝ) ^ (K - l) /
          ((K - l).factorial : ℝ)) ≤
      (K : ℝ) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
          (1 / (l.factorial : ℝ)) := by
  have hbase : (((K - 1 : ℕ) : ℝ)) ^ (K - l) ≤
      (K : ℝ) ^ (K - l) := by
    gcongr
    exact_mod_cast (Nat.pred_le K)
  have hfacNat := factorial_le_factorial_mul_pow hlK
  have hfac : (K.factorial : ℝ) ≤
      ((K - l).factorial : ℝ) * (K : ℝ) ^ l := by
    exact_mod_cast hfacNat
  have hpow : (K : ℝ) ^ (K - l) * (K : ℝ) ^ l =
      (K : ℝ) * (K : ℝ) ^ (K - 1) := by
    rw [← pow_add]
    have hexp : K - l + l = K := by omega
    rw [hexp]
    conv_lhs => rw [show K = (K - 1) + 1 by omega]
    rw [pow_succ]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ K)]
    ring
  have hcross :
      (((K - 1 : ℕ) : ℝ)) ^ (K - l) * (K.factorial : ℝ) ≤
        ((K : ℝ) * (K : ℝ) ^ (K - 1)) *
          ((K - l).factorial : ℝ) := by
    calc
      (((K - 1 : ℕ) : ℝ)) ^ (K - l) * (K.factorial : ℝ) ≤
          (K : ℝ) ^ (K - l) * (K.factorial : ℝ) := by
        exact mul_le_mul_of_nonneg_right hbase (by positivity)
      _ ≤ (K : ℝ) ^ (K - l) *
          (((K - l).factorial : ℝ) * (K : ℝ) ^ l) := by
        exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = ((K : ℝ) * (K : ℝ) ^ (K - 1)) *
          ((K - l).factorial : ℝ) := by rw [← hpow]; ring
  have hdiv :
      (((K - 1 : ℕ) : ℝ)) ^ (K - l) /
          ((K - l).factorial : ℝ) ≤
        (K : ℝ) * (K : ℝ) ^ (K - 1) /
          (K.factorial : ℝ) := by
    exact (div_le_div_iff₀ (by positivity : (0 : ℝ) < (K - l).factorial)
      (by positivity : (0 : ℝ) < K.factorial)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)
  have hlFac : 0 ≤ 1 / (l.factorial : ℝ) := by positivity
  calc
    (1 / (l.factorial : ℝ)) *
        (((K - 1 : ℕ) : ℝ) ^ (K - l) /
          ((K - l).factorial : ℝ)) ≤
        (1 / (l.factorial : ℝ)) *
          ((K : ℝ) * (K : ℝ) ^ (K - 1) /
            (K.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv hlFac
    _ = (K : ℝ) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
          (1 / (l.factorial : ℝ)) := by ring

theorem two_pow_pred_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ n.factorial := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hprev := ih hn1
        rw [Nat.factorial_succ]
        calc
          2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
            rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
            omega
          _ ≤ (n + 1) * n.factorial :=
            Nat.mul_le_mul (by omega) hprev

theorem inv_factorial_le_two_div_pow {n : ℕ} (hn : 1 ≤ n) :
    1 / (n.factorial : ℝ) ≤ 2 / (2 : ℝ) ^ n := by
  have hfacNat := two_pow_pred_le_factorial hn
  have hfac : (2 : ℝ) ^ (n - 1) ≤ (n.factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    ring
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < n.factorial)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).2
  rw [hpow]
  nlinarith

theorem sum_Icc_two_div_pow (L n : ℕ) :
    (∑ l ∈ Finset.Icc (L + 1) (L + n), 2 / (2 : ℝ) ^ l) =
      2 / (2 : ℝ) ^ L - 2 / (2 : ℝ) ^ (L + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      change (∑ l ∈ Finset.Icc (L + 1) (L + n + 1),
          2 / (2 : ℝ) ^ l) =
        2 / (2 : ℝ) ^ L - 2 / (2 : ℝ) ^ (L + n + 1)
      rw [Finset.sum_Icc_succ_top (by omega : L + 1 ≤ L + n + 1), ih,
        pow_succ]
      have hpow : (2 : ℝ) ^ (L + n) ≠ 0 := by positivity
      field_simp [hpow]
      ring

theorem sum_inv_factorial_Icc_le (L K : ℕ) :
    (∑ l ∈ Finset.Icc (L + 1) K, 1 / (l.factorial : ℝ)) ≤
      2 / (2 : ℝ) ^ L := by
  by_cases hLK : L ≤ K
  · calc
      (∑ l ∈ Finset.Icc (L + 1) K,
          1 / (l.factorial : ℝ)) ≤
          ∑ l ∈ Finset.Icc (L + 1) K, 2 / (2 : ℝ) ^ l := by
        apply Finset.sum_le_sum
        intro l hl
        exact inv_factorial_le_two_div_pow
          (by have := (Finset.mem_Icc.mp hl).1; omega)
      _ = 2 / (2 : ℝ) ^ L - 2 / (2 : ℝ) ^ K := by
        simpa [Nat.add_sub_of_le hLK] using sum_Icc_two_div_pow L (K - L)
      _ ≤ 2 / (2 : ℝ) ^ L := sub_le_self _ (by positivity)
  · have hK : K < L + 1 := by omega
    rw [Finset.Icc_eq_empty (by omega : ¬ L + 1 ≤ K)]
    simp only [one_div, sum_empty, ge_iff_le]
    positivity

theorem badCoordinateWeight_le (j d L : ℕ) (hd : 0 < d)
    (hjL : j ≤ L) (hK : j + (d + 1) ≤ 2 * d) :
    (∑ b ∈ (compositionsOf (j + (d + 1)) (j + (d + 1))).filter
        (fun b ↦ L < b (Fin.natAdd j (0 : Fin (d + 1)))),
      compositionCycleWeight b) ≤
      (4 / (2 : ℝ) ^ L) *
        (((j + (d + 1) : ℕ) : ℝ) ^ (j + (d + 1) - 1) /
          ((j + (d + 1)).factorial : ℝ)) := by
  let K := j + (d + 1)
  have hbad := card_mul_badCoordinateWeight_le j d L hd hjL
  have hterm : ∀ l ∈ Finset.Icc (L + 1) K,
      (1 / (l.factorial : ℝ)) *
          (((j + d : ℕ) : ℝ) ^ (K - l) /
            ((K - l).factorial : ℝ)) ≤
        (K : ℝ) * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
          (1 / (l.factorial : ℝ)) := by
    intro l hl
    have hlK := (Finset.mem_Icc.mp hl).2
    have hpred : K - 1 = j + d := by omega
    simpa [hpred] using badCoordinateSummand_le_cycleMass
      (K := K) (l := l) (by omega) hlK
  have htail := sum_inv_factorial_Icc_le L K
  have hcycleNonneg : 0 ≤ (K : ℝ) ^ (K - 1) / (K.factorial : ℝ) := by
    positivity
  have hsum :
      (∑ l ∈ Finset.Icc (L + 1) K,
        (1 / (l.factorial : ℝ)) *
          (((j + d : ℕ) : ℝ) ^ (K - l) /
            ((K - l).factorial : ℝ))) ≤
        (K : ℝ) * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
          (2 / (2 : ℝ) ^ L) := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (L + 1) K,
          (K : ℝ) * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
            (1 / (l.factorial : ℝ)) := Finset.sum_le_sum hterm
      _ = (K : ℝ) * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
          (∑ l ∈ Finset.Icc (L + 1) K,
            1 / (l.factorial : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left htail
        (mul_nonneg (by positivity) hcycleNonneg)
  apply le_of_mul_le_mul_left
  · calc
    (d : ℝ) *
        (∑ b ∈ (compositionsOf (j + (d + 1)) (j + (d + 1))).filter
            (fun b ↦ L < b (Fin.natAdd j (0 : Fin (d + 1)))),
          compositionCycleWeight b) ≤
        ∑ l ∈ Finset.Icc (L + 1) K,
          (1 / (l.factorial : ℝ)) *
            (((j + d : ℕ) : ℝ) ^ (K - l) /
              ((K - l).factorial : ℝ)) := by simpa [K] using hbad
    _ ≤ (K : ℝ) * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
          (2 / (2 : ℝ) ^ L) := hsum
    _ ≤ (d : ℝ) *
        ((4 / (2 : ℝ) ^ L) *
          ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))) := by
      have hKR : (K : ℝ) ≤ 2 * d := by exact_mod_cast hK
      have hpowPos : 0 < (2 : ℝ) ^ L := by positivity
      have hfactor : 0 ≤
          ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
            (2 / (2 : ℝ) ^ L) := by positivity
      calc
        (K : ℝ) * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
            (2 / (2 : ℝ) ^ L) = (K : ℝ) *
              (((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
                (2 / (2 : ℝ) ^ L)) := by ring
        _ ≤ (2 * (d : ℝ)) *
              (((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) *
                (2 / (2 : ℝ) ^ L)) :=
          mul_le_mul_of_nonneg_right hKR hfactor
        _ = (d : ℝ) *
            ((4 / (2 : ℝ) ^ L) *
              ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))) := by ring
  · positivity

theorem compositionCycleWeight_nonneg {K : ℕ} (b : Fin K → ℕ) :
    0 ≤ compositionCycleWeight b := by
  rw [compositionCycleWeight]
  exact div_nonneg zero_le_one (mul_nonneg (by
    dsimp [compositionFactorial]
    positivity) (prefixProductMass_nonneg fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact (compositionFactor_pos b i).le))

theorem badCoordinateWeight_le_reindexed {K : ℕ} (j d L : ℕ)
    (hdim : K = j + (d + 1)) (i : Fin K) (hi : i.val = j)
    (hd : 0 < d) (hjL : j ≤ L) (hK : K ≤ 2 * d) :
    (∑ b ∈ (compositionsOf K K).filter (fun b ↦ L < b i),
      compositionCycleWeight b) ≤
      (4 / (2 : ℝ) ^ L) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  subst K
  have hi' : i = Fin.natAdd j (0 : Fin (d + 1)) := by
    apply Fin.ext
    exact hi
  subst i
  apply badCoordinateWeight_le j d L hd hjL
  exact hK

/-- Coordinate-indexed form of `badCoordinateWeight_le`. -/
theorem badCoordinateWeight_le_fin {K : ℕ} (i : Fin K) (L : ℕ)
    (hL : L < K) (hiL : i.val ≤ L) (hdouble : 2 * (i.val + 1) ≤ K) :
    (∑ b ∈ (compositionsOf K K).filter (fun b ↦ L < b i),
      compositionCycleWeight b) ≤
      (4 / (2 : ℝ) ^ L) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  let j := i.val
  let d := K - (i.val + 1)
  have hd : 0 < d := by dsimp [d]; omega
  have hdim : K = j + (d + 1) := by dsimp [j, d]; omega
  apply badCoordinateWeight_le_reindexed j d L hdim i rfl hd hiL
  omega

/-- Ford's one-sided cap on the composition attached to blocks starting at
absolute block index `M`. -/
def IsFordCapped {K : ℕ} (M : ℕ) (b : Fin K → ℕ) : Prop :=
  ∀ i : Fin K, b i ≤ M * (M + i.val)

noncomputable def cappedCompositions (M K : ℕ) : Finset (Fin K → ℕ) := by
  classical
  exact (compositions K).filter (IsFordCapped M)

theorem mem_cappedCompositions {M K : ℕ} {b : Fin K → ℕ} :
    b ∈ cappedCompositions M K ↔
      b ∈ compositions K ∧ IsFordCapped M b := by
  classical
  simp [cappedCompositions]

theorem sum_cycleWeight_le_capped_add_bad (M K : ℕ) :
    (∑ b ∈ compositions K, compositionCycleWeight b) ≤
      (∑ b ∈ cappedCompositions M K, compositionCycleWeight b) +
        ∑ i : Fin K,
          ∑ b ∈ (compositions K).filter
              (fun b ↦ M * (M + i.val) < b i),
            compositionCycleWeight b := by
  classical
  calc
    (∑ b ∈ compositions K, compositionCycleWeight b) ≤
        ∑ b ∈ compositions K,
          ((if IsFordCapped M b then compositionCycleWeight b else 0) +
            ∑ i : Fin K,
              if M * (M + i.val) < b i then compositionCycleWeight b else 0) := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hcap : IsFordCapped M b
      · simp only [hcap, if_true]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi ↦ by
          split_ifs
          · exact compositionCycleWeight_nonneg b
          · exact le_rfl)
      · have hbad : ∃ i : Fin K, M * (M + i.val) < b i := by
          simpa [IsFordCapped, not_forall, not_le] using hcap
        obtain ⟨i, hi⟩ := hbad
        simp only [hcap, if_false, zero_add]
        have hnonneg : ∀ q ∈ (Finset.univ : Finset (Fin K)),
            0 ≤ if M * (M + q.val) < b q then compositionCycleWeight b else 0 := by
          intro q hq
          split_ifs
          · exact compositionCycleWeight_nonneg b
          · exact le_rfl
        have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ i)
        simpa [hi] using hsingle
    _ = (∑ b ∈ cappedCompositions M K, compositionCycleWeight b) +
        ∑ i : Fin K,
          ∑ b ∈ (compositions K).filter
              (fun b ↦ M * (M + i.val) < b i),
            compositionCycleWeight b := by
      rw [Finset.sum_add_distrib]
      congr 1
      · simp [cappedCompositions, Finset.sum_filter]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.sum_filter]

theorem badFordCoordinateWeight_le {M K : ℕ} (hM : 2 ≤ M)
    (i : Fin K) :
    (∑ b ∈ (compositions K).filter
        (fun b ↦ M * (M + i.val) < b i),
      compositionCycleWeight b) ≤
      (4 / (2 : ℝ) ^ (M * (M + i.val))) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  let L := M * (M + i.val)
  by_cases hLK : L < K
  · have hiL : i.val ≤ L := by
      dsimp [L]
      have hMi : i.val ≤ M + i.val := Nat.le_add_left _ _
      have hmul : M + i.val ≤ M * (M + i.val) := by
        have hpos : 0 < M + i.val := by omega
        nlinarith [Nat.le_mul_of_pos_left (M + i.val) (by omega : 0 < M)]
      exact hMi.trans hmul
    have htwo : 2 * (i.val + 1) ≤ K := by
      have hLi : 2 * (i.val + 1) ≤ L := by
        dsimp [L]
        nlinarith [Nat.mul_le_mul hM
          (show i.val + 1 ≤ M + i.val by omega)]
      omega
    simpa [L, compositions, compositionsOf] using
      badCoordinateWeight_le_fin i L hLK hiL htwo
  · have hKL : K ≤ L := by omega
    have hempty : (compositions K).filter
        (fun b ↦ L < b i) = ∅ := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hb, hbad⟩
        have hsum := mem_compositions.mp hb
        have hbi : b i ≤ ∑ q : Fin K, b q := by
          exact Finset.single_le_sum (fun q hq ↦ Nat.zero_le _) (Finset.mem_univ i)
        omega
      · simp
    rw [show M * (M + i.val) = L by rfl, hempty]
    simp only [sum_empty, Nat.ofNat_pos, div_pos_iff_of_pos_left, pow_pos, mul_nonneg_iff_of_pos_left, ge_iff_le]
    positivity

theorem fordCapExponent_lower {M i : ℕ} (hM : 1 ≤ M) :
    M * M + i ≤ M * (M + i) := by
  rw [Nat.mul_add]
  exact Nat.add_le_add_left (by
    simpa using Nat.mul_le_mul_right i hM) (M * M)

theorem sum_ford_bad_coeff_le (M K : ℕ) (hM : 1 ≤ M) :
    (∑ i : Fin K, 4 / (2 : ℝ) ^ (M * (M + i.val))) ≤
      16 / (2 : ℝ) ^ (M * M) := by
  have hpoint : ∀ i : Fin K,
      4 / (2 : ℝ) ^ (M * (M + i.val)) ≤
        (4 / (2 : ℝ) ^ (M * M)) *
          (((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i.val) := by
    intro i
    have hexp := fordCapExponent_lower (i := i.val) hM
    have hpow : (2 : ℝ) ^ (M * M + i.val) ≤
        (2 : ℝ) ^ (M * (M + i.val)) := by gcongr <;> norm_num
    calc
      4 / (2 : ℝ) ^ (M * (M + i.val)) ≤
          4 / (2 : ℝ) ^ (M * M + i.val) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
      _ = (4 / (2 : ℝ) ^ (M * M)) *
          (1 / (2 : ℝ) ^ i.val) := by
        rw [pow_add]
        field_simp
      _ ≤ (4 / (2 : ℝ) ^ (M * M)) *
          (((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i.val) := by
        apply mul_le_mul_of_nonneg_left
        · apply div_le_div_of_nonneg_right
          · norm_num
          · positivity
        · positivity
  calc
    (∑ i : Fin K, 4 / (2 : ℝ) ^ (M * (M + i.val))) ≤
        ∑ i : Fin K, (4 / (2 : ℝ) ^ (M * M)) *
          (((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i.val) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (4 / (2 : ℝ) ^ (M * M)) *
        ∑ i ∈ Finset.range K,
          (((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i) := by
      rw [← Finset.mul_sum, Finset.sum_range]
    _ ≤ (4 / (2 : ℝ) ^ (M * M)) * 4 := by
      exact mul_le_mul_of_nonneg_left (weighted_geometric_one_le K) (by positivity)
    _ = 16 / (2 : ℝ) ^ (M * M) := by ring

theorem sum_badFordCoordinateWeight_le {M K : ℕ} (hM : 2 ≤ M) :
    (∑ i : Fin K,
        ∑ b ∈ (compositions K).filter
            (fun b ↦ M * (M + i.val) < b i),
          compositionCycleWeight b) ≤
      (16 / (2 : ℝ) ^ (M * M)) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  have hcycle : 0 ≤ (K : ℝ) ^ (K - 1) / (K.factorial : ℝ) := by
    positivity
  calc
    (∑ i : Fin K,
        ∑ b ∈ (compositions K).filter
            (fun b ↦ M * (M + i.val) < b i),
          compositionCycleWeight b) ≤
        ∑ i : Fin K,
          (4 / (2 : ℝ) ^ (M * (M + i.val))) *
            ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
      exact Finset.sum_le_sum fun i hi ↦ badFordCoordinateWeight_le hM i
    _ = (∑ i : Fin K, 4 / (2 : ℝ) ^ (M * (M + i.val))) *
          ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ (16 / (2 : ℝ) ^ (M * M)) *
          ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (sum_ford_bad_coeff_le M K (by omega)) hcycle

theorem sixteen_div_two_pow_sq_le_half {M : ℕ} (hM : 3 ≤ M) :
    16 / (2 : ℝ) ^ (M * M) ≤ 1 / 2 := by
  have hsq : 9 ≤ M * M := by nlinarith
  have hpow : (512 : ℝ) ≤ (2 : ℝ) ^ (M * M) := by
    calc
      (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ (2 : ℝ) ^ (M * M) := by gcongr <;> norm_num
  have hpowPos : 0 < (2 : ℝ) ^ (M * M) := by positivity
  apply (div_le_iff₀ hpowPos).2
  nlinarith

/-- The one-sided Ford caps retain at least half of the exact unrestricted
cycle weight. -/
theorem cappedComposition_cycleWeight_lower {M K : ℕ}
    (hM : 3 ≤ M) (hK : 0 < K) :
    (1 / 2 : ℝ) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) ≤
      ∑ b ∈ cappedCompositions M K, compositionCycleWeight b := by
  let S : ℝ := (K : ℝ) ^ (K - 1) / (K.factorial : ℝ)
  let G : ℝ := ∑ b ∈ cappedCompositions M K, compositionCycleWeight b
  let B : ℝ := ∑ i : Fin K,
    ∑ b ∈ (compositions K).filter
        (fun b ↦ M * (M + i.val) < b i), compositionCycleWeight b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hunrestricted :
      (∑ b ∈ compositions K, compositionCycleWeight b) = S := by
    simpa [S] using sum_compositionCycleWeight K hK
  have hcover : S ≤ G + B := by
    rw [← hunrestricted]
    exact sum_cycleWeight_le_capped_add_bad M K
  have hbad : B ≤ (16 / (2 : ℝ) ^ (M * M)) * S := by
    simpa [B, S] using sum_badFordCoordinateWeight_le (K := K) (by omega : 2 ≤ M)
  have hcoeff := sixteen_div_two_pow_sq_le_half hM
  have hbadHalf : B ≤ (1 / 2 : ℝ) * S :=
    hbad.trans (mul_le_mul_of_nonneg_right hcoeff hS)
  have hretained : (1 / 2 : ℝ) * S ≤ G := by linarith
  simpa [G, S] using hretained

end Erdos446
