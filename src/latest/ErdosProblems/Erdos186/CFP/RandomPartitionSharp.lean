/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomPartition

/-!
# Source-scale finite coloring for the CFP random partition

This file proves the additive-capacity form of the finite random-coloring
step.  For a fixed obstacle `T` and color `i`, a coloring is assigned weight

`prod x in T, if c x = i then 1 else 2`.

The sum of these weights over all colorings is exactly

`(2*q+1)^|T| * (q+1)^(N-|T|)`.

Consequently colorings using color `i` at most `t` times on `T` are
exponentially sparse once `|T|` is at least `(2*q+1)*(t+k)`.  A finite union
bound over all obstacle/color pairs gives the source-scale additive loss
`O(q*(t+log events))`, rather than the multiplicative
`O(q*t*log events)` furnished by the chunk argument.
-/

namespace Erdos186.CFP.RandomPartition

open scoped BigOperators
open Stability

noncomputable section

variable {X I : Type*} [Fintype X] [DecidableEq X]
  [Fintype I] [DecidableEq I]

/-- Exponential weight detecting colorings with few occurrences of `i` on
`T`. -/
def coloringWeight {q : ℕ} (T : Finset X) (i : Fin (q + 1))
    (c : X → Fin (q + 1)) : ℕ :=
  ∏ x, if x ∈ T then (if c x = i then 1 else 2) else 1

theorem sum_colorWeight_at {q : ℕ} (i : Fin (q + 1)) :
    (∑ a : Fin (q + 1), if a = i then 1 else 2) = 2 * q + 1 := by
  classical
  have herase :
      (∑ a ∈ (Finset.univ.erase i : Finset (Fin (q + 1))),
        if a = i then 1 else 2) = 2 * q := by
    calc
      (∑ a ∈ (Finset.univ.erase i : Finset (Fin (q + 1))),
          if a = i then 1 else 2) =
          ∑ _a ∈ (Finset.univ.erase i : Finset (Fin (q + 1))), 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [(Finset.mem_erase.mp ha).1]
      _ = 2 * q := by simp; omega
  calc
    (∑ a : Fin (q + 1), if a = i then 1 else 2) =
        (∑ a ∈ (Finset.univ.erase i : Finset (Fin (q + 1))),
          if a = i then 1 else 2) + 1 := by
      symm
      simpa using Finset.sum_erase_add (Finset.univ : Finset (Fin (q + 1)))
        (fun a ↦ if a = i then (1 : ℕ) else 2) (Finset.mem_univ i)
    _ = 2 * q + 1 := by rw [herase]

/-- Exact total exponential weight over all `(q+1)`-colorings. -/
theorem sum_coloringWeight {q : ℕ} (T : Finset X) (i : Fin (q + 1)) :
    (∑ c : X → Fin (q + 1), coloringWeight T i c) =
      (2 * q + 1) ^ T.card *
        (q + 1) ^ (Fintype.card X - T.card) := by
  change (∑ c : X → Fin (q + 1),
      ∏ x, if x ∈ T then (if c x = i then 1 else 2) else 1) = _
  rw [← (Fintype.prod_sum (fun x (_a : Fin (q + 1)) ↦
    if x ∈ T then (if _a = i then 1 else 2) else 1))]
  simp only [Finset.sum_ite_irrel, sum_colorWeight_at, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Finset.prod_ite (s := Finset.univ)]
  simp only [Finset.prod_const]
  have hfilter : (Finset.univ : Finset X).filter (· ∈ T) = T := by
    ext
    simp
  have hcompl : (Finset.univ : Finset X).filter (· ∉ T) =
      Finset.univ \ T := by
    ext
    simp
  rw [hfilter, hcompl, Finset.card_sdiff_of_subset (Finset.subset_univ T)]
  simp

/-- Number of elements of `T` receiving color `i`. -/
def colorHits {q : ℕ} (T : Finset X) (i : Fin (q + 1))
    (c : X → Fin (q + 1)) : ℕ :=
  (T.filter fun x ↦ c x = i).card

/-- Colorings which use color `i` at most `t` times on `T`. -/
def fewColorColorings {q : ℕ} (T : Finset X) (i : Fin (q + 1))
    (t : ℕ) : Finset (X → Fin (q + 1)) :=
  Finset.univ.filter fun c ↦ colorHits T i c ≤ t

theorem coloringWeight_eq {q : ℕ} (T : Finset X) (i : Fin (q + 1))
    (c : X → Fin (q + 1)) :
    coloringWeight T i c = 2 ^ (T.card - colorHits T i c) := by
  classical
  simp only [coloringWeight]
  rw [Finset.prod_ite (s := Finset.univ)]
  simp only [Finset.prod_const, one_pow]
  have hfilter : (Finset.univ : Finset X).filter (· ∈ T) = T := by
    ext
    simp
  rw [hfilter]
  rw [Finset.prod_ite (s := T)]
  simp only [Finset.prod_const, one_pow, one_mul]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := T) (fun x ↦ c x = i)
  have hexp : (T.filter fun x ↦ ¬c x = i).card =
      T.card - colorHits T i c := by
    rw [colorHits]
    omega
  simpa only [Finset.sum_boole, mul_one, hexp]

theorem pow_card_sub_le_coloringWeight_of_few {q t : ℕ}
    (T : Finset X) (i : Fin (q + 1))
    {c : X → Fin (q + 1)} (hc : c ∈ fewColorColorings T i t) :
    2 ^ (T.card - t) ≤ coloringWeight T i c := by
  rw [coloringWeight_eq]
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  have hhits : colorHits T i c ≤ t := (Finset.mem_filter.mp hc).2
  omega

theorem card_few_mul_pow_le {q t : ℕ}
    (T : Finset X) (i : Fin (q + 1)) :
    (fewColorColorings T i t).card * 2 ^ (T.card - t) ≤
      (2 * q + 1) ^ T.card *
        (q + 1) ^ (Fintype.card X - T.card) := by
  rw [← sum_coloringWeight T i]
  calc
    (fewColorColorings T i t).card * 2 ^ (T.card - t) =
        ∑ _c ∈ fewColorColorings T i t, 2 ^ (T.card - t) := by simp
    _ ≤ ∑ c ∈ fewColorColorings T i t, coloringWeight T i c := by
      exact Finset.sum_le_sum fun c hc ↦
        pow_card_sub_le_coloringWeight_of_few T i hc
    _ ≤ ∑ c : X → Fin (q + 1), coloringWeight T i c := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)

/-- One block of `2*q+1` obstacle elements gains one binary factor after
paying for one required hit. -/
theorem block_suppression {q t k : ℕ} :
    2 ^ k * (2 * q + 1) ^ ((2 * q + 1) * (t + k)) ≤
      2 ^ ((2 * q + 1) * (t + k) - t) *
        (q + 1) ^ ((2 * q + 1) * (t + k)) := by
  let b := 2 * q + 1
  let M := b * (t + k)
  have hb : 0 < b := by simp [b]
  have htM : t ≤ M := by
    calc
      t ≤ t + k := Nat.le_add_right _ _
      _ ≤ b * (t + k) := Nat.le_mul_of_pos_left _ hb
  have hblock := two_pow_mul_pow_le_succ_pow b (t + k) hb
  have hfactor : b + 1 = 2 * (q + 1) := by simp [b]; omega
  have hrewritten :
      2 ^ t * (2 ^ k * b ^ M) ≤
        2 ^ t * (2 ^ (M - t) * (q + 1) ^ M) := by
    calc
      2 ^ t * (2 ^ k * b ^ M) = 2 ^ (t + k) * b ^ M := by
        rw [pow_add]
        ring
      _ ≤ (b + 1) ^ M := by simpa [M] using hblock
      _ = (2 * (q + 1)) ^ M := by rw [hfactor]
      _ = 2 ^ M * (q + 1) ^ M := by rw [mul_pow]
      _ = 2 ^ t * (2 ^ (M - t) * (q + 1) ^ M) := by
        rw [← pow_mul_pow_sub 2 htM]
        ring
  exact Nat.le_of_mul_le_mul_left hrewritten (by positivity)

/-- The block estimate remains valid after adding arbitrary further
obstacle elements. -/
theorem additive_suppression {q t k m : ℕ}
    (hm : (2 * q + 1) * (t + k) ≤ m) :
    2 ^ k * (2 * q + 1) ^ m ≤
      2 ^ (m - t) * (q + 1) ^ m := by
  let b := 2 * q + 1
  let M := b * (t + k)
  let u := m - M
  have hMm : M ≤ m := by simpa [M, b] using hm
  have hmEq : M + u = m := by omega
  have htM : t ≤ M := by
    calc
      t ≤ t + k := Nat.le_add_right _ _
      _ ≤ b * (t + k) := Nat.le_mul_of_pos_left _ (by simp [b])
  have hbase : b ≤ 2 * (q + 1) := by dsimp [b]; omega
  have htail : b ^ u ≤ (2 * (q + 1)) ^ u :=
    Nat.pow_le_pow_left hbase u
  have hblock := block_suppression (q := q) (t := t) (k := k)
  change 2 ^ k * b ^ m ≤ 2 ^ (m - t) * (q + 1) ^ m
  calc
    2 ^ k * b ^ m =
        (2 ^ k * b ^ M) * b ^ u := by rw [← hmEq, pow_add]; ring
    _ ≤ (2 ^ (M - t) * (q + 1) ^ M) *
        (2 * (q + 1)) ^ u := Nat.mul_le_mul hblock htail
    _ = 2 ^ (m - t) * (q + 1) ^ m := by
      rw [mul_pow]
      have hsub : M - t + u = m - t := by omega
      calc
        2 ^ (M - t) * (q + 1) ^ M *
              (2 ^ u * (q + 1) ^ u) =
            (2 ^ (M - t) * 2 ^ u) *
              ((q + 1) ^ M * (q + 1) ^ u) := by ring
        _ = 2 ^ (m - t) * (q + 1) ^ m := by
          rw [← pow_add, hsub, ← pow_add, hmEq]

theorem card_few_mul_pow_le_total {q t k : ℕ}
    (T : Finset X) (i : Fin (q + 1))
    (hsize : (2 * q + 1) * (t + k) ≤ T.card) :
    (fewColorColorings T i t).card * 2 ^ k ≤
      (q + 1) ^ Fintype.card X := by
  have hTN : T.card ≤ Fintype.card X := by
    simpa using Finset.card_le_card (Finset.subset_univ T)
  have hweight := card_few_mul_pow_le (X := X) (t := t) T i
  have hsuppress := additive_suppression
    (q := q) (t := t) (k := k) (m := T.card) hsize
  have hmultiplied :
      2 ^ k * ((fewColorColorings T i t).card * 2 ^ (T.card - t)) ≤
        2 ^ k * ((2 * q + 1) ^ T.card *
          (q + 1) ^ (Fintype.card X - T.card)) :=
    Nat.mul_le_mul_left _ hweight
  have hchain :
      2 ^ (T.card - t) * ((fewColorColorings T i t).card * 2 ^ k) ≤
        2 ^ (T.card - t) * (q + 1) ^ Fintype.card X := by
    calc
      2 ^ (T.card - t) * ((fewColorColorings T i t).card * 2 ^ k) =
          2 ^ k * ((fewColorColorings T i t).card *
            2 ^ (T.card - t)) := by ring
      _ ≤ 2 ^ k * ((2 * q + 1) ^ T.card *
          (q + 1) ^ (Fintype.card X - T.card)) := hmultiplied
      _ = (2 ^ k * (2 * q + 1) ^ T.card) *
          (q + 1) ^ (Fintype.card X - T.card) := by ring
      _ ≤ (2 ^ (T.card - t) * (q + 1) ^ T.card) *
          (q + 1) ^ (Fintype.card X - T.card) :=
        Nat.mul_le_mul_right _ hsuppress
      _ = 2 ^ (T.card - t) * (q + 1) ^ Fintype.card X := by
        calc
          (2 ^ (T.card - t) * (q + 1) ^ T.card) *
                (q + 1) ^ (Fintype.card X - T.card) =
              2 ^ (T.card - t) *
                ((q + 1) ^ T.card *
                  (q + 1) ^ (Fintype.card X - T.card)) := by ring
          _ = _ := by rw [pow_mul_pow_sub _ hTN]
  exact Nat.le_of_mul_le_mul_left hchain (by positivity)

private noncomputable def badFewColorings {q t : ℕ}
    (obstacle : I → Finset X) : Finset (X → Fin (q + 1)) := by
  classical
  exact (Finset.univ : Finset I).biUnion fun o ↦
    (Finset.univ : Finset (Fin (q + 1))).biUnion fun i ↦
      fewColorColorings (obstacle o) i t

private theorem card_badFewColorings_mul_pow_le {q t k : ℕ}
    (obstacle : I → Finset X)
    (hsize : ∀ o, (2 * q + 1) * (t + k) ≤ (obstacle o).card) :
    (badFewColorings (q := q) (t := t) obstacle).card * 2 ^ k ≤
      Fintype.card I * (q + 1) *
        (q + 1) ^ Fintype.card X := by
  classical
  have hcard : (badFewColorings (q := q) (t := t) obstacle).card ≤
      ∑ o : I, ∑ i : Fin (q + 1),
        (fewColorColorings (obstacle o) i t).card := by
    unfold badFewColorings
    calc
      ((Finset.univ : Finset I).biUnion fun o ↦
          (Finset.univ : Finset (Fin (q + 1))).biUnion fun i ↦
            fewColorColorings (obstacle o) i t).card ≤
          ∑ o : I,
            ((Finset.univ : Finset (Fin (q + 1))).biUnion fun i ↦
              fewColorColorings (obstacle o) i t).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ o : I, ∑ i : Fin (q + 1),
          (fewColorColorings (obstacle o) i t).card := by
        apply Finset.sum_le_sum
        intro o ho
        exact Finset.card_biUnion_le
  calc
    (badFewColorings (q := q) (t := t) obstacle).card * 2 ^ k ≤
        (∑ o : I, ∑ i : Fin (q + 1),
          (fewColorColorings (obstacle o) i t).card) * 2 ^ k :=
      Nat.mul_le_mul_right _ hcard
    _ = ∑ o : I, ∑ i : Fin (q + 1),
          (fewColorColorings (obstacle o) i t).card * 2 ^ k := by
      simp only [Finset.sum_mul]
    _ ≤ ∑ _o : I, ∑ _i : Fin (q + 1),
          (q + 1) ^ Fintype.card X := by
      apply Finset.sum_le_sum
      intro o ho
      apply Finset.sum_le_sum
      intro i hi
      exact card_few_mul_pow_le_total (obstacle o) i (hsize o)
    _ = Fintype.card I * (q + 1) *
          (q + 1) ^ Fintype.card X := by simp [mul_assoc]

/-- Additive-capacity finite coloring lemma.  The logarithmic cost `k` is
added to, rather than multiplied by, the required survivor count `t`. -/
theorem exists_coloring_robust_on_obstacles_additive {q t k : ℕ}
    {obstacle : I → Finset X}
    (hevents : Fintype.card I * (q + 1) < 2 ^ k)
    (hsize : ∀ o, (2 * q + 1) * (t + k) ≤ (obstacle o).card) :
    ∃ c : X → Fin (q + 1),
      ∀ o i, t < (colorClass c i ∩ obstacle o).card := by
  classical
  have hbadPow := card_badFewColorings_mul_pow_le
    (q := q) (t := t) (k := k) obstacle hsize
  have htotalPos : 0 < (q + 1) ^ Fintype.card X := by positivity
  have hstrict :
      (badFewColorings (q := q) (t := t) obstacle).card * 2 ^ k <
        (q + 1) ^ Fintype.card X * 2 ^ k := by
    apply hbadPow.trans_lt
    calc
      Fintype.card I * (q + 1) *
          (q + 1) ^ Fintype.card X <
          2 ^ k * (q + 1) ^ Fintype.card X :=
        (Nat.mul_lt_mul_right htotalPos).mpr hevents
      _ = (q + 1) ^ Fintype.card X * 2 ^ k := by ring
  have hbad : (badFewColorings (q := q) (t := t) obstacle).card <
      (Finset.univ : Finset (X → Fin (q + 1))).card := by
    have hcancel := Nat.lt_of_mul_lt_mul_right hstrict
    simpa [Fintype.card_fun] using hcancel
  have hex : ∃ c : X → Fin (q + 1),
      c ∉ badFewColorings (q := q) (t := t) obstacle := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (X → Fin (q + 1))) ⊆
        badFewColorings (q := q) (t := t) obstacle := by
      intro c hc
      exact h c
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hbad
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  intro o i
  have hnot : c ∉ fewColorColorings (obstacle o) i t := by
    intro hmem
    apply hc
    apply Finset.mem_biUnion.mpr
    refine ⟨o, Finset.mem_univ _, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩
  have hhits : t < colorHits (obstacle o) i c := by
    simp only [fewColorColorings, Finset.mem_filter, Finset.mem_univ,
      true_and] at hnot
    omega
  have heq : (colorClass c i ∩ obstacle o).card =
      colorHits (obstacle o) i c := by
    congr 1
    ext x
    simp only [colorClass, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact and_comm
  rw [heq]
  exact hhits

section StrongInheritance

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Deterministic part of full strong-stability inheritance, separated from
the coloring estimate. -/
theorem stronglyStableFor_anchoredColorClass_of_robust_obstacles
    {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor A box x maxRank differenceBound relevant φ C0)
    (family : WeakBoxFamily W A box maxRank differenceBound)
    (c : {a // a ∈ A} → Fin (q + 1))
    (hc : ∀ o : StrongObstacleIndex (W := W) A relevant φ, ∀ i,
      t < (colorClass c i ∩ strongObstacle family o).card) :
    ∀ i, StronglyStableFor (anchoredColorClass A c i) box t maxRank
      differenceBound relevant φ C0 := by
  classical
  let G : {d // d ∈ relevant} → Type := fun d ↦ LatticePoint d.1
  let ψ : ∀ d, {a // a ∈ A} → G d := fun d a ↦ φ d.1 a.1
  intro i
  let e : {a // a ∈ A} ↪ ℤ := ⟨Subtype.val, Subtype.val_injective⟩
  let part := anchoredColorClass A c i
  have hpartA : part ⊆ A := by
    intro a ha
    simp only [part, anchoredColorClass, Finset.mem_insert,
      Finset.mem_map] at ha
    rcases ha with rfl | ⟨b, hb, rfl⟩
    · exact hstable.weaklyStable.zero_mem
    · exact b.2
  have hweakPart : WeaklyStableFor part box t maxRank differenceBound := by
    refine ⟨by simp [part, anchoredColorClass], ?_⟩
    intro B hBpart hlarge hzeroB d hd hdRank P hsteps hvolume
    intro hcontained
    have hzeroP : integerPoint 0 ∈ P.carrier :=
      hcontained (integerPoint_mem_integerPoints_iff.mpr hzeroB)
    obtain ⟨w, hw⟩ := family.covers hd hdRank P hsteps hvolume hzeroP
    let T := colorClass c i ∩ weakBoxObstacle family w
    have hTlarge : t < T.card := hc (Sum.inl w) i
    have hTsub : T.map e ⊆ part \ B := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      have hbcolor := (Finset.mem_inter.mp hb).1
      have hboutside := (Finset.mem_inter.mp hb).2
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨b, hbcolor, rfl⟩)
      · intro hbB
        have hbP : integerPoint b.1 ∈ P.carrier :=
          hcontained (integerPoint_mem_integerPoints_iff.mpr hbB)
        have hbGap : b.1 ∈ outsideGAP A (family.gap w) := by
          simpa [weakBoxObstacle, outsideGAP] using hboutside
        have hbOutP : b.1 ∈ outsideGAP A P := by
          rw [hw]
          exact hbGap
        exact (Finset.mem_filter.mp hbOutP).2 hbP
    have hTcard : T.card ≤ (part \ B).card := by
      rw [← Finset.card_map e]
      exact Finset.card_le_card hTsub
    have hdiff : (part \ B).card = part.card - B.card :=
      Finset.card_sdiff_of_subset hBpart
    have hdiffle : (part \ B).card ≤ t := by
      rw [hdiff]
      omega
    omega
  refine ⟨hweakPart, hstable.C0_pos, ?_⟩
  intro d hd B hBpart hlarge hzeroB
  let S := (colorClass c i).filter fun a ↦ a.1 ∈ B
  have hScolor : S ⊆ colorClass c i := Finset.filter_subset _ _
  have hmapSB : S.map e ⊆ B := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact (Finset.mem_filter.mp hb).2
  have hmissing : (colorClass c i \ S).map e ⊆ part \ B := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    have hbc := (Finset.mem_sdiff.mp hb).1
    have hbnot := (Finset.mem_sdiff.mp hb).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨b, hbc, rfl⟩), ?_⟩
    intro hbB
    exact hbnot (Finset.mem_filter.mpr ⟨hbc, hbB⟩)
  have hmissCard : (colorClass c i \ S).card ≤ (part \ B).card := by
    rw [← Finset.card_map e]
    exact Finset.card_le_card hmissing
  have hpartDiff : (part \ B).card = part.card - B.card :=
    Finset.card_sdiff_of_subset hBpart
  have hSloss : (colorClass c i).card ≤ S.card + t := by
    have hsmall : (part \ B).card ≤ t / C0 := by
      rw [hpartDiff]
      apply Nat.sub_le_iff_le_add.mpr
      simpa [add_comm] using hlarge
    have hquot : t / C0 ≤ t := Nat.div_le_self _ _
    have hsdiff : (colorClass c i \ S).card =
        (colorClass c i).card - S.card :=
      Finset.card_sdiff_of_subset hScolor
    have htotal : (colorClass c i \ S).card + S.card =
        (colorClass c i).card :=
      Finset.card_sdiff_add_card_eq_card hScolor
    rw [hsdiff] at hmissCard
    omega
  have hprofile := generatedProfile_eq_of_distinct_robust_obstacles G ψ c
    (fun w j ↦ hc (Sum.inr w) j) i hScolor hSloss ⟨d, hd⟩
  have hSA : generatedSubgroup (φ d) (S.map e) =
      generatedSubgroup (φ d) A := by
    change generatedSubgroup (fun a : {a // a ∈ A} ↦ φ d a.1) S =
      generatedSubgroup (fun a : {a // a ∈ A} ↦ φ d a.1)
        Finset.univ at hprofile
    rw [generatedSubgroup_subtype_map (φ d) A S,
      generatedSubgroup_subtype_univ (φ d) A] at hprofile
    simpa [e] using hprofile
  have hBA : B ⊆ A := hBpart.trans hpartA
  have hpartSpan : generatedSubgroup (φ d) part =
      generatedSubgroup (φ d) A := by
    apply le_antisymm
    · exact generatedSubgroup_mono hpartA
    · rw [← hSA]
      exact generatedSubgroup_mono (hmapSB.trans hBpart)
  apply Eq.trans ?_ hpartSpan.symm
  apply le_antisymm
  · exact generatedSubgroup_mono hBA
  · rw [← hSA]
    exact generatedSubgroup_mono hmapSB

/-- The distinct-span obstacles also retain the original generated subgroup
in every relevant coordinate system.  This is recorded separately because
`StronglyStableFor` only remembers robustness inside the color class, not
the equality of that class's ambient span with the source span. -/
theorem anchoredColorClass_generatedSubgroup_eq_of_robust_obstacles
    {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor A box x maxRank differenceBound relevant φ C0)
    (family : WeakBoxFamily W A box maxRank differenceBound)
    (c : {a // a ∈ A} → Fin (q + 1))
    (hc : ∀ o : StrongObstacleIndex (W := W) A relevant φ, ∀ i,
      t < (colorClass c i ∩ strongObstacle family o).card) :
    ∀ i d, d ∈ relevant →
      generatedSubgroup (φ d) (anchoredColorClass A c i) =
        generatedSubgroup (φ d) A := by
  classical
  let G : {d // d ∈ relevant} → Type := fun d ↦ LatticePoint d.1
  let ψ : ∀ d, {a // a ∈ A} → G d := fun d a ↦ φ d.1 a.1
  intro i d hd
  let e : {a // a ∈ A} ↪ ℤ := ⟨Subtype.val, Subtype.val_injective⟩
  let S := colorClass c i
  have hprofile := generatedProfile_eq_of_distinct_robust_obstacles G ψ c
    (fun w j ↦ hc (Sum.inr w) j) i (Finset.Subset.rfl) (by omega)
      ⟨d, hd⟩
  have hcolorSpan : generatedSubgroup (φ d) (S.map e) =
      generatedSubgroup (φ d) A := by
    change generatedSubgroup (fun a : {a // a ∈ A} ↦ φ d a.1) S =
      generatedSubgroup (fun a : {a // a ∈ A} ↦ φ d a.1)
        Finset.univ at hprofile
    rw [generatedSubgroup_subtype_map (φ d) A S,
      generatedSubgroup_subtype_univ (φ d) A] at hprofile
    simpa only [e] using hprofile
  apply le_antisymm
  · apply generatedSubgroup_mono
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hstable.weaklyStable.zero_mem
    · obtain ⟨z, _hz, rfl⟩ := Finset.mem_map.mp ha
      exact z.2
  · rw [← hcolorSpan]
    apply generatedSubgroup_mono
    intro a ha
    exact Finset.mem_insert_of_mem ha

/-- Adjoining an anchor that maps to zero does not change the generated
coordinate subgroup.  This converts the common-span conclusion for
`anchoredColorClass` to the unanchored integer color class used by greedy
selection. -/
theorem generatedSubgroup_insert_zero_eq {d : ℕ} (φ : ℤ → LatticePoint d)
    (S : Finset ℤ) (hφzero : φ 0 = 0) :
    generatedSubgroup φ (insert 0 S) = generatedSubgroup φ S := by
  apply le_antisymm
  · rw [generatedSubgroup, AddSubgroup.closure_le]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [hφzero]
      exact AddSubgroup.zero_mem _
    · exact AddSubgroup.subset_closure ⟨z, hz, rfl⟩
  · exact generatedSubgroup_mono (Finset.subset_insert 0 S)

/-- Source-facing full inheritance theorem with additive coloring capacity.
The number of canonical obstacles is bounded polynomially, and the logarithm
is paid once, additively to the survivor count `t`. -/
theorem exists_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
    {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t n exponent : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor A box x maxRank differenceBound relevant φ C0)
    (hφzero : ∀ d ∈ relevant, φ d 0 = 0)
    (hfamily : CanonicalObstaclePolynomialBound A box maxRank differenceBound
      relevant φ n exponent)
    (_hq : 0 < q)
    (hcapacity :
      (2 * q + 1) *
          (t + (Nat.log 2 (n ^ exponent * (q + 1)) + 1)) ≤
        x / C0 + 1) :
    ∃ c : {a // a ∈ A} → Fin (q + 1),
      (∀ i, StronglyStableFor (anchoredColorClass A c i) box t maxRank
        differenceBound relevant φ C0) ∧
      (∀ i d, d ∈ relevant →
        generatedSubgroup (φ d) (anchoredColorClass A c i) =
          generatedSubgroup (φ d) A) := by
  classical
  let W := WeakTraceIndex A box maxRank differenceBound
  let family : WeakBoxFamily W A box maxRank differenceBound :=
    canonicalWeakBoxFamily A box maxRank differenceBound
  let I := StrongObstacleIndex (W := W) A relevant φ
  let k := Nat.log 2 (n ^ exponent * (q + 1)) + 1
  let G : {d // d ∈ relevant} → Type := fun d ↦ LatticePoint d.1
  let ψ : ∀ d, {a // a ∈ A} → G d := fun d a ↦ φ d.1 a.1
  have hspanSubtype :
      SpanRobust (⟨0, hstable.weaklyStable.zero_mem⟩ : {a // a ∈ A})
        Finset.univ (x / C0) relevant (fun d a ↦ φ d a.1) :=
    spanRobust_subtype hstable.spanRobust hstable.weaklyStable.zero_mem
  have hobstacle : ∀ o : I,
      (2 * q + 1) * (t + k) ≤ (strongObstacle family o).card := by
    intro o
    cases o with
    | inl w =>
        have hw := card_weakBoxObstacle_gt hstable.weaklyStable family w
        have hdiv : x / C0 ≤ x := Nat.div_le_self _ _
        exact hcapacity.trans ((Nat.succ_le_succ hdiv).trans
          (Nat.succ_le_iff.mpr hw))
    | inr w =>
        obtain ⟨S, hgen⟩ :=
          exists_closure_eq_of_mem_generatedSubgroupValues G ψ w.1 w.2.2.1
        have hgen' : generatedSubgroup (ψ w.1) S = w.2.1 := by
          simpa [generatedSubgroup] using hgen
        have hproperFull : w.2.1 < generatedSubgroup (ψ w.1) Finset.univ := by
          simpa [generatedSubgroup] using
            distinctSpanIndex_lt_closure_univ G ψ w
        have hw := card_outside_generatedSubgroup_gt hspanSubtype
          (Finset.mem_univ _) (hφzero w.1.1 w.1.2) w.1.2
          (B := S)
          (by
            rw [hgen']
            exact hproperFull)
        have hobs : distinctSpanObstacle G ψ w =
            outsideGeneratedSubgroup (ψ w.1) Finset.univ S := by
          ext a
          simp [distinctSpanObstacle, outsideGeneratedSubgroup, hgen']
        change _ ≤ (distinctSpanObstacle G ψ w).card
        rw [hobs]
        exact hcapacity.trans (Nat.succ_le_iff.mpr hw)
  have heventsLe : Fintype.card I * (q + 1) ≤
      n ^ exponent * (q + 1) := Nat.mul_le_mul_right _ hfamily
  have hevents : Fintype.card I * (q + 1) < 2 ^ k :=
    heventsLe.trans_lt (by
      dsimp [k]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two _)
  obtain ⟨c, hc⟩ := exists_coloring_robust_on_obstacles_additive
    (obstacle := strongObstacle family) hevents hobstacle
  exact ⟨c,
    stronglyStableFor_anchoredColorClass_of_robust_obstacles
      hstable family c hc,
    anchoredColorClass_generatedSubgroup_eq_of_robust_obstacles
      hstable family c hc⟩

/-- Compatibility form of the additive inheritance theorem when only the
per-color stability certificate is needed. -/
theorem exists_coloring_stronglyStableFor_of_polynomial_bound_additive
    {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t n exponent : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor A box x maxRank differenceBound relevant φ C0)
    (hφzero : ∀ d ∈ relevant, φ d 0 = 0)
    (hfamily : CanonicalObstaclePolynomialBound A box maxRank differenceBound
      relevant φ n exponent)
    (hq : 0 < q)
    (hcapacity :
      (2 * q + 1) *
          (t + (Nat.log 2 (n ^ exponent * (q + 1)) + 1)) ≤
        x / C0 + 1) :
    ∃ c : {a // a ∈ A} → Fin (q + 1),
      ∀ i, StronglyStableFor (anchoredColorClass A c i) box t maxRank
        differenceBound relevant φ C0 := by
  obtain ⟨c, hcolor, _hspan⟩ :=
    exists_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
      hstable hφzero hfamily hq hcapacity
  exact ⟨c, hcolor⟩

end StrongInheritance

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.exists_coloring_robust_on_obstacles_additive
#print axioms
  Erdos186.CFP.RandomPartition.exists_coloring_stronglyStableFor_of_polynomial_bound_additive
#print axioms
  Erdos186.CFP.RandomPartition.exists_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
