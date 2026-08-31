/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import ErdosProblems.Erdos13.Erdos13Kneser

/-!
# The additive-combinatorial lemma used for Erdős Problem 13

This file contains a finitary proof of the strict form of the
Bardaji--Grynkiewicz alternative needed in Bedert's argument.  The proof is
split into two parts.  First, the stable-hole argument proves that two
normalized subsets of integer intervals have a long interval in their
sumset once the larger diameter is at most the sum of their cardinalities
minus three.  Second, Kneser's theorem applied modulo the larger diameter
supplies this diameter estimate when the cardinality-growth alternative
fails.
-/

open Finset Nat
open scoped Pointwise

namespace Erdos13Additive

/-! ## Elementary hole counts -/

/-- Holes of `S` in the natural interval `[0,M]`. -/
def holes (S : Finset ℕ) (M : ℕ) : Finset ℕ := Icc 0 M \ S

@[simp] lemma mem_holes {S : Finset ℕ} {M x : ℕ} :
    x ∈ holes S M ↔ x ≤ M ∧ x ∉ S := by
  simp [holes]

lemma card_holes {S : Finset ℕ} {M : ℕ} (hS : S ⊆ Icc 0 M) :
    (holes S M).card = M + 1 - S.card := by
  rw [holes, card_sdiff_of_subset hS]
  simp

/-- Holes restricted to a closed subinterval. -/
def holesIcc (S : Finset ℕ) (a b : ℕ) : Finset ℕ := Icc a b \ S

@[simp] lemma mem_holesIcc {S : Finset ℕ} {a b x : ℕ} :
    x ∈ holesIcc S a b ↔ a ≤ x ∧ x ≤ b ∧ x ∉ S := by
  simp only [holesIcc, mem_sdiff, mem_Icc]
  aesop

lemma holesIcc_subset_holes {S : Finset ℕ} {M a b : ℕ}
    (_ha : a ≤ b) (hb : b ≤ M) : holesIcc S a b ⊆ holes S M := by
  intro x hx
  have hx' := mem_holesIcc.mp hx
  exact mem_holes.mpr ⟨hx'.2.1.trans hb, hx'.2.2⟩

lemma card_holesIcc_le_card_holes {S : Finset ℕ} {M a b : ℕ}
    (ha : a ≤ b) (hb : b ≤ M) :
    (holesIcc S a b).card ≤ (holes S M).card :=
  card_le_card (holesIcc_subset_holes ha hb)

lemma card_holesIcc_le_length {S : Finset ℕ} {a b : ℕ} :
    (holesIcc S a b).card ≤ b + 1 - a := by
  exact (card_le_card sdiff_subset).trans_eq (by simp)

/-- Two interval hole counts are bounded by the total hole count plus the
hole count in the overlap.  This is the inclusion--exclusion estimate used
in the stable-hole argument. -/
lemma card_holesIcc_add_le_total_add_overlap {S : Finset ℕ} {M a b c d : ℕ}
    (hab : a ≤ b) (hcd : c ≤ d) (hbM : b ≤ M) (hdM : d ≤ M) :
    (holesIcc S a b).card + (holesIcc S c d).card ≤
      (holes S M).card + (holesIcc S (max a c) (min b d)).card := by
  let X := holesIcc S a b
  let Y := holesIcc S c d
  have hXY : X ∪ Y ⊆ holes S M := by
    exact union_subset (holesIcc_subset_holes hab hbM)
      (holesIcc_subset_holes hcd hdM)
  have hinter : X ∩ Y ⊆ holesIcc S (max a c) (min b d) := by
    intro x hx
    have hxX := mem_holesIcc.mp (mem_of_mem_inter_left hx)
    have hxY := mem_holesIcc.mp (mem_of_mem_inter_right hx)
    exact mem_holesIcc.mpr ⟨by omega, by omega, hxX.2.2⟩
  have hcardUnion := card_le_card hXY
  have hcardInter := card_le_card hinter
  have hident : (X ∪ Y).card + (X ∩ Y).card =
      (holesIcc S a b).card + (holesIcc S c d).card := by
    simpa [X, Y] using card_union_add_card_inter X Y
  omega

/-! ## The normalized long-interval theorem -/

/-- The holes of a normalized sumset in its full ambient interval. -/
def sumHoles (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  Icc 0 (M + N) \ (A + B)

/-- Left-stable holes of `B`. -/
def leftStable (A B : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (holes B N).filter fun x ↦ x ∉ A + B

/-- Right-stable holes of `B`, where `M` is the maximum of `A`. -/
def rightStable (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  (holes B N).filter fun x ↦ x + M ∉ A + B

def stableHoles (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  leftStable A B N ∪ rightStable A B M N

def unstableHoles (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  holes B N \ stableHoles A B M N

@[simp] lemma mem_leftStable {A B : Finset ℕ} {N x : ℕ} :
    x ∈ leftStable A B N ↔ x ≤ N ∧ x ∉ B ∧ x ∉ A + B := by
  simp only [leftStable, mem_filter, mem_holes]
  aesop

@[simp] lemma mem_rightStable {A B : Finset ℕ} {M N x : ℕ} :
    x ∈ rightStable A B M N ↔
      x ≤ N ∧ x ∉ B ∧ x + M ∉ A + B := by
  simp only [rightStable, mem_filter, mem_holes]
  aesop

@[simp] lemma mem_stableHoles {A B : Finset ℕ} {M N x : ℕ} :
    x ∈ stableHoles A B M N ↔
      x ∈ leftStable A B N ∨ x ∈ rightStable A B M N := by
  simp [stableHoles]

@[simp] lemma mem_unstableHoles {A B : Finset ℕ} {M N x : ℕ} :
    x ∈ unstableHoles A B M N ↔
      x ≤ N ∧ x ∉ B ∧ x ∉ stableHoles A B M N := by
  simp only [unstableHoles, mem_sdiff, mem_holes]
  aesop

/-- If a sum below the smaller diameter is absent, the two prefixes contain
at least as many holes as there are candidate representations. -/
lemma prefix_hole_count {A B : Finset ℕ} {M N x : ℕ}
    (_hA : A ⊆ Icc 0 M) (_hB : B ⊆ Icc 0 N) (_hxN : x ≤ N)
    (hx : x ∉ A + B) :
    x + 1 ≤ (holesIcc A 0 x).card + (holesIcc B 0 x).card := by
  let U := Icc 0 x
  let X := U.filter fun b ↦ x - b ∉ A
  let Y := holesIcc B 0 x
  have hcover : U ⊆ X ∪ Y := by
    intro b hb
    have hb' := mem_Icc.mp hb
    by_cases ha : x - b ∈ A
    · have hbB : b ∉ B := by
        intro hbmem
        apply hx
        have heq : x - b + b = x := Nat.sub_add_cancel hb'.2
        rw [← heq]
        exact Finset.add_mem_add ha hbmem
      exact mem_union_right _ (mem_holesIcc.mpr ⟨by omega, hb'.2, hbB⟩)
    · exact mem_union_left _ (by simp [X, U, hb, ha])
  have hX : X.image (fun b ↦ x - b) ⊆ holesIcc A 0 x := by
    intro a ha
    simp only [mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' := mem_filter.mp hb
    exact mem_holesIcc.mpr ⟨by omega, Nat.sub_le _ _, hb'.2⟩
  have hinj : Set.InjOn (fun b : ℕ ↦ x - b) X := by
    intro b hb c hc hbc
    have hbU := mem_Icc.mp (mem_filter.mp hb).1
    have hcU := mem_Icc.mp (mem_filter.mp hc).1
    change x - b = x - c at hbc
    omega
  have hXcard : X.card ≤ (holesIcc A 0 x).card := by
    rw [← card_image_iff.mpr hinj]
    exact card_le_card hX
  have hcoverCard := card_le_card hcover
  have hunionCard := card_union_le X Y
  change x + 1 ≤ _
  have hUcard : U.card = x + 1 := by simp [U]
  rw [hUcard] at hcoverCard
  change (X ∪ Y).card ≤ X.card + (holesIcc B 0 x).card at hunionCard
  omega

/-- The reflected version of `prefix_hole_count` for a missing sum at the
right end of the ambient sum interval. -/
lemma suffix_hole_count {A B : Finset ℕ} {M N z : ℕ}
    (hMN : N ≤ M) (hzM : M ≤ z) (hzMN : z ≤ M + N)
    (hz : z ∉ A + B) :
    M + N - z + 1 ≤
      (holesIcc A (z - N) M).card + (holesIcc B (z - M) N).card := by
  let U := Icc (z - M) N
  let X := U.filter fun b ↦ z - b ∉ A
  let Y := holesIcc B (z - M) N
  have hcover : U ⊆ X ∪ Y := by
    intro b hb
    have hb' := mem_Icc.mp hb
    by_cases ha : z - b ∈ A
    · have hbB : b ∉ B := by
        intro hbmem
        apply hz
        have hbz : b ≤ z := by omega
        have heq : z - b + b = z := Nat.sub_add_cancel hbz
        rw [← heq]
        exact Finset.add_mem_add ha hbmem
      exact mem_union_right _ (mem_holesIcc.mpr ⟨hb'.1, hb'.2, hbB⟩)
    · exact mem_union_left _ (by simp [X, U, hb, ha])
  have hX : X.image (fun b ↦ z - b) ⊆ holesIcc A (z - N) M := by
    intro a ha
    simp only [mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' := mem_filter.mp hb
    have hbU := mem_Icc.mp hb'.1
    exact mem_holesIcc.mpr ⟨by omega, by omega, hb'.2⟩
  have hinj : Set.InjOn (fun b : ℕ ↦ z - b) X := by
    intro b hb c hc hbc
    have hbU := mem_Icc.mp (mem_filter.mp hb).1
    have hcU := mem_Icc.mp (mem_filter.mp hc).1
    change z - b = z - c at hbc
    have hbz : b ≤ z := by omega
    have hcz : c ≤ z := by omega
    omega
  have hXcard : X.card ≤ (holesIcc A (z - N) M).card := by
    rw [← card_image_iff.mpr hinj]
    exact card_le_card hX
  have hcoverCard := card_le_card hcover
  have hunionCard := card_union_le X Y
  have hUcard : U.card = M + N - z + 1 := by
    simp only [U, card_Icc]
    omega
  rw [hUcard] at hcoverCard
  change (X ∪ Y).card ≤ X.card + (holesIcc B (z - M) N).card at hunionCard
  omega

/-- Proposition 4.1 of Bardaji--Grynkiewicz: if the larger-diameter set
has at most `|B|-1` holes, the whole middle interval is in the sumset. -/
lemma middle_interval_subset_sum {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (_hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hhole : (holes A M).card + 1 ≤ B.card) :
    Icc N M ⊆ A + B := by
  intro x hx
  have hxI := mem_Icc.mp hx
  by_contra hxsum
  let U := Icc 0 N
  let X := U.filter fun b ↦ x - b ∉ A
  let Y := holes B N
  have hcover : U ⊆ X ∪ Y := by
    intro b hb
    have hb' := mem_Icc.mp hb
    by_cases ha : x - b ∈ A
    · have hbB : b ∉ B := by
        intro hbmem
        apply hxsum
        have hbx : b ≤ x := hb'.2.trans hxI.1
        have heq : x - b + b = x := Nat.sub_add_cancel hbx
        rw [← heq]
        exact Finset.add_mem_add ha hbmem
      exact mem_union_right _ (mem_holes.mpr ⟨hb'.2, hbB⟩)
    · exact mem_union_left _ (by simp [X, U, hb, ha])
  have hX : X.image (fun b ↦ x - b) ⊆ holes A M := by
    intro a ha
    simp only [mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' := mem_filter.mp hb
    exact mem_holes.mpr ⟨by omega, hb'.2⟩
  have hinj : Set.InjOn (fun b : ℕ ↦ x - b) X := by
    intro b hb c hc hbc
    have hbU := mem_Icc.mp (mem_filter.mp hb).1
    have hcU := mem_Icc.mp (mem_filter.mp hc).1
    change x - b = x - c at hbc
    have hbx : b ≤ x := hbU.2.trans hxI.1
    have hcx : c ≤ x := hcU.2.trans hxI.1
    omega
  have hXcard : X.card ≤ (holes A M).card := by
    rw [← card_image_iff.mpr hinj]
    exact card_le_card hX
  have hcoverCard := card_le_card hcover
  have hunionCard := card_union_le X Y
  have hUcard : U.card = N + 1 := by simp [U]
  have hNcover : N + 1 ≤ X.card + (holes B N).card := by
    calc
      N + 1 = U.card := hUcard.symm
      _ ≤ (X ∪ Y).card := hcoverCard
      _ ≤ X.card + Y.card := hunionCard
      _ = X.card + (holes B N).card := by rfl
  have hBh := card_holes hB
  have hBcard : B.card ≤ N + 1 := by
    simpa using card_le_card hB
  have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
  omega

/-- A hole of `B` cannot be both left- and right-stable under the strict
hole hypothesis. -/
lemma disjoint_left_right {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    Disjoint (leftStable A B N) (rightStable A B M N) := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  have hxL' := mem_leftStable.mp hxL
  have hxR' := mem_rightStable.mp hxR
  have hp := prefix_hole_count hA hB hxL'.1 hxL'.2.2
  have hs := suffix_hole_count hMN (by omega) (by omega) hxR'.2.2
  have hs' : N - x + 1 ≤
      (holesIcc A (x + M - N) M).card + (holesIcc B x N).card := by
    have heq : M + N - (x + M) = N - x := by omega
    rw [heq] at hs
    have heq' : x + M - M = x := by omega
    rw [heq'] at hs
    exact hs
  have hAparts := card_holesIcc_add_le_total_add_overlap
    (S := A) (M := M) (a := 0) (b := x) (c := x + M - N) (d := M)
    (by omega) (by omega) (by omega) (by omega)
  have hBparts := card_holesIcc_add_le_total_add_overlap
    (S := B) (M := N) (a := 0) (b := x) (c := x) (d := N)
    (by omega) (by omega) (by omega) (by omega)
  have hAover : (holesIcc A (max 0 (x + M - N)) (min x M)).card ≤ 1 := by
    have hsub : holesIcc A (max 0 (x + M - N)) (min x M) ⊆ {x} := by
      intro y hy
      have hy' := mem_holesIcc.mp hy
      simp only [mem_singleton]
      omega
    exact (card_le_card hsub).trans_eq (by simp)
  have hBover : (holesIcc B (max 0 x) (min x N)).card ≤ 1 := by
    have hsub : holesIcc B (max 0 x) (min x N) ⊆ {x} := by
      intro y hy
      have hy' := mem_holesIcc.mp hy
      simp only [max_eq_right (Nat.zero_le x), min_eq_left hxL'.1] at hy'
      simp only [mem_singleton]
      omega
    exact (card_le_card hsub).trans_eq (by simp)
  have hAh := card_holes hA
  have hBh := card_holes hB
  have hAcard : A.card ≤ M + 1 := by simpa using card_le_card hA
  have hBcard : B.card ≤ N + 1 := by simpa using card_le_card hB
  have hAhAdd : (holes A M).card + A.card = M + 1 := by omega
  have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
  have hsplit : (x + 1) + (N - x + 1) = N + 2 := by omega
  omega

@[simp] lemma mem_sumHoles {A B : Finset ℕ} {M N z : ℕ} :
    z ∈ sumHoles A B M N ↔ z ≤ M + N ∧ z ∉ A + B := by
  simp [sumHoles]

def stableProjection (M N z : ℕ) : ℕ :=
  if z < N then z else z - M

lemma add_subset_ambient {A B : Finset ℕ} {M N : ℕ}
    (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N) :
    A + B ⊆ Icc 0 (M + N) := by
  intro z hz
  simp only [Finset.mem_add] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  have ha' := mem_Icc.mp (hA ha)
  have hb' := mem_Icc.mp (hB hb)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma card_sumHoles {A B : Finset ℕ} {M N : ℕ}
    (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N) :
    (sumHoles A B M N).card = M + N + 1 - (A + B).card := by
  rw [sumHoles, card_sdiff_of_subset (add_subset_ambient hA hB)]
  simp

/-- The missing sums project bijectively to the stable holes of `B`. -/
lemma image_stableProjection_sumHoles {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    (sumHoles A B M N).image (stableProjection M N) =
      stableHoles A B M N := by
  have hmid := middle_interval_subset_sum hMN hA hB (by omega)
  ext x
  constructor
  · intro hx
    simp only [mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' := mem_sumHoles.mp hz
    by_cases hzN : z < N
    · have hzB : z ∉ B := by
        intro hzB
        apply hz'.2
        simpa using Finset.add_mem_add hA0 hzB
      apply mem_stableHoles.mpr
      left
      simpa only [stableProjection, if_pos hzN] using
        (mem_leftStable.mpr ⟨by omega, hzB, hz'.2⟩)
    · have hMz : M < z := by
        by_contra hnot
        have : z ∈ Icc N M := mem_Icc.mpr ⟨by omega, by omega⟩
        exact hz'.2 (hmid this)
      have hzsub : z - M ≤ N := by omega
      have hzB : z - M ∉ B := by
        intro hzB
        apply hz'.2
        have heq : M + (z - M) = z := by omega
        rw [← heq]
        exact Finset.add_mem_add hAM hzB
      apply mem_stableHoles.mpr
      right
      simp only [stableProjection, if_neg hzN]
      have he : z - M + M = z := Nat.sub_add_cancel (by omega)
      exact mem_rightStable.mpr ⟨hzsub, hzB, by simpa [he] using hz'.2⟩
  · intro hx
    rcases mem_stableHoles.mp hx with hxL | hxR
    · have hxL' := mem_leftStable.mp hxL
      have hxN : x < N := by
        by_contra hnot
        have hxEq : x = N := by omega
        subst x
        exact hxL'.2.2 (hmid (mem_Icc.mpr ⟨le_rfl, hMN⟩))
      apply mem_image.mpr
      refine ⟨x, mem_sumHoles.mpr ⟨by omega, hxL'.2.2⟩, ?_⟩
      simp [stableProjection, hxN]
    · have hxR' := mem_rightStable.mp hxR
      let z := x + M
      have hzN : ¬ z < N := by dsimp [z]; omega
      apply mem_image.mpr
      refine ⟨z, mem_sumHoles.mpr ⟨by dsimp [z]; omega, hxR'.2.2⟩, ?_⟩
      simp [stableProjection, z, hzN]

lemma stableProjection_injOn_sumHoles {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    Set.InjOn (stableProjection M N) (sumHoles A B M N) := by
  have hmid := middle_interval_subset_sum hMN hA hB (by omega)
  have hdisj := disjoint_left_right hMN hA hB hhole
  intro z hz w hw heq
  have hz' := mem_sumHoles.mp hz
  have hw' := mem_sumHoles.mp hw
  by_cases hzN : z < N
  · have hzB : z ∉ B := by
      intro hzB
      exact hz'.2 (by simpa using Finset.add_mem_add hA0 hzB)
    have hzL : z ∈ leftStable A B N :=
      mem_leftStable.mpr ⟨by omega, hzB, hz'.2⟩
    by_cases hwN : w < N
    · simpa [stableProjection, hzN, hwN] using heq
    · have hMw : M < w := by
        by_contra hnot
        exact hw'.2 (hmid (mem_Icc.mpr ⟨by omega, by omega⟩))
      have hwB : w - M ∉ B := by
        intro hb
        apply hw'.2
        have he : M + (w - M) = w := by omega
        rw [← he]
        exact Finset.add_mem_add hAM hb
      have hwR : w - M ∈ rightStable A B M N :=
        mem_rightStable.mpr ⟨by omega, hwB, by
          have he : w - M + M = w := Nat.sub_add_cancel (by omega)
          simpa [he] using hw'.2⟩
      have hproj : z = w - M := by simpa [stableProjection, hzN, hwN] using heq
      rw [← hproj] at hwR
      exact (Finset.disjoint_left.mp hdisj hzL hwR).elim
  · have hMz : M < z := by
      by_contra hnot
      exact hz'.2 (hmid (mem_Icc.mpr ⟨by omega, by omega⟩))
    by_cases hwN : w < N
    · have hwB : w ∉ B := by
        intro hb
        exact hw'.2 (by simpa using Finset.add_mem_add hA0 hb)
      have hwL : w ∈ leftStable A B N :=
        mem_leftStable.mpr ⟨by omega, hwB, hw'.2⟩
      have hzB : z - M ∉ B := by
        intro hb
        apply hz'.2
        have he : M + (z - M) = z := by omega
        rw [← he]
        exact Finset.add_mem_add hAM hb
      have hzR : z - M ∈ rightStable A B M N :=
        mem_rightStable.mpr ⟨by omega, hzB, by
          have he : z - M + M = z := Nat.sub_add_cancel (by omega)
          simpa [he] using hz'.2⟩
      have hproj : z - M = w := by simpa [stableProjection, hzN, hwN] using heq
      rw [hproj] at hzR
      exact (Finset.disjoint_left.mp hdisj hwL hzR).elim
    · have heq' : z - M = w - M := by simpa [stableProjection, hzN, hwN] using heq
      omega

lemma card_stableHoles {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    (stableHoles A B M N).card = (sumHoles A B M N).card := by
  rw [← image_stableProjection_sumHoles hMN hA hB hA0 hAM hhole,
    card_image_iff.mpr (stableProjection_injOn_sumHoles hMN hA hB hA0 hAM hhole)]

lemma stableHoles_subset_holes (A B : Finset ℕ) (M N : ℕ) :
    stableHoles A B M N ⊆ holes B N := by
  intro x hx
  rcases mem_stableHoles.mp hx with hx | hx
  · have hx' := mem_leftStable.mp hx
    exact mem_holes.mpr ⟨hx'.1, hx'.2.1⟩
  · have hx' := mem_rightStable.mp hx
    exact mem_holes.mpr ⟨hx'.1, hx'.2.1⟩

lemma card_stable_add_unstable (A B : Finset ℕ) (M N : ℕ) :
    (stableHoles A B M N).card + (unstableHoles A B M N).card =
      (holes B N).card := by
  have hsub := stableHoles_subset_holes A B M N
  rw [add_comm]
  simpa [unstableHoles] using card_sdiff_add_card_eq_card hsub

/-- In an inverted pair of disjoint finite ordered sets one can choose a
pair with no member of either set strictly between the two endpoints. -/
lemma exists_adjacent_inversion {L R : Finset ℕ}
    (hinv : ∃ x ∈ L, ∃ y ∈ R, y < x) :
    ∃ x ∈ L, ∃ y ∈ R, y < x ∧
      ∀ z, y < z → z < x → z ∉ L ∪ R := by
  let P : ℕ → Prop := fun d ↦ ∃ x ∈ L, ∃ y ∈ R, y < x ∧ x - y = d
  have hP : ∃ d, P d := by
    obtain ⟨x, hx, y, hy, hyx⟩ := hinv
    exact ⟨x - y, x, hx, y, hy, hyx, rfl⟩
  let d := Nat.find hP
  obtain ⟨x, hx, y, hy, hyx, hxy⟩ := Nat.find_spec hP
  refine ⟨x, hx, y, hy, hyx, ?_⟩
  intro z hyz hzx hz
  rcases mem_union.mp hz with hzL | hzR
  · have hmin : d ≤ z - y := Nat.find_min' hP ⟨z, hzL, y, hy, hyz, rfl⟩
    dsimp [d] at hxy hmin
    omega
  · have hmin : d ≤ x - z := Nat.find_min' hP ⟨x, hx, z, hzR, hzx, rfl⟩
    dsimp [d] at hxy hmin
    omega

/-- Under the strict small-sumset slack, every left-stable hole precedes
every right-stable hole.  This is Proposition 4.5 of the cited paper; the
strict slack used by Bedert avoids its boundary equality case. -/
lemma leftStable_lt_rightStable {A B : Finset ℕ} {M N r : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card)
    (hsumcard : (A + B).card + 1 = A.card + B.card + r)
    (hr : r + 3 ≤ B.card) :
    ∀ x ∈ leftStable A B N, ∀ y ∈ rightStable A B M N, x < y := by
  have hdisj := disjoint_left_right hMN hA hB hhole
  have hsumAmbient := add_subset_ambient hA hB
  have hsumCardLe : (A + B).card ≤ M + N + 1 := by
    simpa using card_le_card hsumAmbient
  have hAcard : A.card ≤ M + 1 := by simpa using card_le_card hA
  have hBcard : B.card ≤ N + 1 := by simpa using card_le_card hB
  have hAh := card_holes hA
  have hBh := card_holes hB
  have hSh := card_sumHoles hA hB
  have hstable := card_stableHoles hMN hA hB hA0 hAM hhole
  have hpartition := card_stable_add_unstable A B M N
  have hAhAdd : (holes A M).card + A.card = M + 1 := by omega
  have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
  have hShAdd : (sumHoles A B M N).card + (A + B).card = M + N + 1 := by omega
  have hunstable : (unstableHoles A B M N).card + (holes A M).card = r := by omega
  intro x hxL y hyR
  by_contra hxy
  have hyx : y < x := by
    have hne : x ≠ y := by
      intro he
      subst y
      exact Finset.disjoint_left.mp hdisj hxL hyR
    omega
  have hinv : ∃ x ∈ leftStable A B N, ∃ y ∈ rightStable A B M N, y < x :=
    ⟨x, hxL, y, hyR, hyx⟩
  obtain ⟨x, hxL, y, hyR, hyx, hadj⟩ := exists_adjacent_inversion hinv
  have hxL' := mem_leftStable.mp hxL
  have hyR' := mem_rightStable.mp hyR
  have hp := prefix_hole_count hA hB hxL'.1 hxL'.2.2
  have hs0 := suffix_hole_count hMN (by omega) (by omega) hyR'.2.2
  have hs : N - y + 1 ≤
      (holesIcc A (y + M - N) M).card + (holesIcc B y N).card := by
    have heq : M + N - (y + M) = N - y := by omega
    rw [heq] at hs0
    have heq' : y + M - M = y := by omega
    rw [heq'] at hs0
    exact hs0
  have hAparts := card_holesIcc_add_le_total_add_overlap
    (S := A) (M := M) (a := 0) (b := x) (c := y + M - N) (d := M)
    (by omega) (by omega) (by omega) (by omega)
  have hBparts := card_holesIcc_add_le_total_add_overlap
    (S := B) (M := N) (a := 0) (b := x) (c := y) (d := N)
    (by omega) (by omega) (by omega) (by omega)
  have hBover :
      (holesIcc B (max 0 y) (min x N)).card ≤
        (unstableHoles A B M N).card + 2 := by
    have hsub : holesIcc B (max 0 y) (min x N) ⊆
        unstableHoles A B M N ∪ {y, x} := by
      intro z hz
      have hz' := mem_holesIcc.mp hz
      by_cases hzy : z = y
      · subst z
        exact mem_union_right _ (by simp)
      by_cases hzx : z = x
      · subst z
        exact mem_union_right _ (by simp)
      have hyz : y < z := by omega
      have hzxlt : z < x := by omega
      have hnotstable : z ∉ stableHoles A B M N := by
        intro hzstable
        exact hadj z hyz hzxlt (by simpa [stableHoles] using hzstable)
      exact mem_union_left _ (mem_unstableHoles.mpr ⟨by omega, hz'.2.2, hnotstable⟩)
    have hc := card_le_card hsub
    have hu := card_union_le (unstableHoles A B M N) {y, x}
    have hpair : ({y, x} : Finset ℕ).card ≤ 2 := by
      rw [Finset.card_pair (by omega)]
    omega
  by_cases hsep : x < y + M - N
  · have hAover :
        (holesIcc A (max 0 (y + M - N)) (min x M)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' := mem_holesIcc.mp hz
      omega
    have hBlen : (holesIcc B (max 0 y) (min x N)).card ≤ x - y + 1 := by
      have hc := card_holesIcc_le_length (S := B) (a := max 0 y) (b := min x N)
      omega
    omega
  · have hAover :
        (holesIcc A (max 0 (y + M - N)) (min x M)).card ≤
          x - y + N - M + 1 := by
      have hc := card_holesIcc_le_length (S := A)
        (a := max 0 (y + M - N)) (b := min x M)
      omega
    omega

/-- Once cuts have been chosen after all left-stable holes and before all
right-stable holes, the interval between them contains no sumset holes. -/
lemma interval_between_stable_cuts {A B : Finset ℕ} {M N lo c : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 1 ≤ B.card)
    (hcN : c ≤ N + 1)
    (hleft : ∀ x ∈ leftStable A B N, x < lo)
    (hright : ∀ x ∈ rightStable A B M N, c ≤ x) :
    Icc lo (M + c - 1) ⊆ A + B := by
  have hmid := middle_interval_subset_sum hMN hA hB hhole
  intro z hz
  have hzI := mem_Icc.mp hz
  by_contra hzsum
  by_cases hzN : z < N
  · have hzB : z ∉ B := by
      intro hb
      exact hzsum (by simpa using Finset.add_mem_add hA0 hb)
    have hzL : z ∈ leftStable A B N :=
      mem_leftStable.mpr ⟨by omega, hzB, hzsum⟩
    exact (not_lt_of_ge hzI.1) (hleft z hzL)
  · have hMz : M < z := by
      by_contra hnot
      exact hzsum (hmid (mem_Icc.mpr ⟨by omega, by omega⟩))
    let x := z - M
    have hxN : x ≤ N := by dsimp [x]; omega
    have hxB : x ∉ B := by
      intro hb
      apply hzsum
      have heq : M + x = z := by dsimp [x]; omega
      rw [← heq]
      exact Finset.add_mem_add hAM hb
    have hxR : x ∈ rightStable A B M N := by
      apply mem_rightStable.mpr
      refine ⟨hxN, hxB, ?_⟩
      have heq : x + M = z := by dsimp [x]; omega
      simpa [heq] using hzsum
    have hcx := hright x hxR
    dsimp [x] at hcx
    have heq : M + (z - M) = z := by omega
    omega

/-- The strict form of Theorem 1.1 of Bardaji--Grynkiewicz used below.
The sets are normalized to have minima zero and maxima `M,N`. -/
theorem normalized_long_interval {A B : Finset ℕ} {M N r : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A) (_hB0 : 0 ∈ B) (_hBN : N ∈ B)
    (hdiam : M + 3 ≤ A.card + B.card)
    (hsumcard : (A + B).card + 1 = A.card + B.card + r)
    (hr : r + 3 ≤ B.card) :
    ∃ lo, Icc lo (lo + (A.card + B.card - 2)) ⊆ A + B := by
  have hAcard : A.card ≤ M + 1 := by simpa using card_le_card hA
  have hBcard : B.card ≤ N + 1 := by simpa using card_le_card hB
  have hAh := card_holes hA
  have hhole : (holes A M).card + 2 ≤ B.card := by omega
  have horder := leftStable_lt_rightStable hMN hA hB hA0 hAM hhole hsumcard hr
  let L := leftStable A B N
  let R := rightStable A B M N
  by_cases hL : L.Nonempty
  · let e := L.max' hL
    have heL : e ∈ L := L.max'_mem hL
    have heN : e ≤ N := (mem_leftStable.mp heL).1
    have hleft : ∀ x ∈ L, x < e + 1 := by
      intro x hx
      exact Nat.lt_succ_of_le (L.le_max' x hx)
    by_cases hR : R.Nonempty
    · let c := R.min' hR
      have hcR : c ∈ R := R.min'_mem hR
      have hcN : c ≤ N := (mem_rightStable.mp hcR).1
      have hright : ∀ x ∈ R, c ≤ x := by
        intro x hx
        exact R.min'_le x hx
      have hec : e < c := horder e heL c hcR
      have hp0 := prefix_hole_count hA hB heN (mem_leftStable.mp heL).2.2
      have hs0 := suffix_hole_count hMN (by omega) (by omega)
        (mem_rightStable.mp hcR).2.2
      have hs : N - c + 1 ≤
          (holesIcc A (c + M - N) M).card + (holesIcc B c N).card := by
        have heq : M + N - (c + M) = N - c := by omega
        rw [heq] at hs0
        have heq' : c + M - M = c := by omega
        rw [heq'] at hs0
        exact hs0
      have hAparts := card_holesIcc_add_le_total_add_overlap
        (S := A) (M := M) (a := 0) (b := e) (c := c + M - N) (d := M)
        (by omega) (by omega) (by omega) (by omega)
      have hBparts := card_holesIcc_add_le_total_add_overlap
        (S := B) (M := N) (a := 0) (b := e) (c := c) (d := N)
        (by omega) (by omega) (by omega) (by omega)
      have hAover :
          (holesIcc A (max 0 (c + M - N)) (min e M)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hz' := mem_holesIcc.mp hz
        omega
      have hBover : (holesIcc B (max 0 c) (min e N)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hz' := mem_holesIcc.mp hz
        omega
      have hBh := card_holes hB
      have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
      have hgap : A.card + B.card - 1 ≤ M + c - (e + 1) := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := e + 1) (c := c) (by simpa [L] using hleft) (by simpa [R] using hright)
      refine ⟨e + 1, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨hz'.1, by omega⟩
    · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      have hp := prefix_hole_count hA hB heN (mem_leftStable.mp heL).2.2
      have hApart := card_holesIcc_le_card_holes (S := A) (M := M)
        (a := 0) (b := e) (by omega) (by omega)
      have hBpart := card_holesIcc_le_card_holes (S := B) (M := N)
        (a := 0) (b := e) (by omega) (by omega)
      have hBh := card_holes hB
      have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
      have hgap : A.card + B.card - 1 ≤ M + (N + 1) - (e + 1) := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := e + 1) (c := N + 1) (by simpa [L] using hleft)
        (by intro x hx; simp [R, hRempty] at hx)
      refine ⟨e + 1, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨hz'.1, by omega⟩
  · have hLempty : L = ∅ := not_nonempty_iff_eq_empty.mp hL
    by_cases hR : R.Nonempty
    · let c := R.min' hR
      have hcR : c ∈ R := R.min'_mem hR
      have hcN : c ≤ N := (mem_rightStable.mp hcR).1
      have hright : ∀ x ∈ R, c ≤ x := by
        intro x hx
        exact R.min'_le x hx
      have hs0 := suffix_hole_count hMN (by omega) (by omega)
        (mem_rightStable.mp hcR).2.2
      have hs : N - c + 1 ≤
          (holesIcc A (c + M - N) M).card + (holesIcc B c N).card := by
        have heq : M + N - (c + M) = N - c := by omega
        rw [heq] at hs0
        have heq' : c + M - M = c := by omega
        rw [heq'] at hs0
        exact hs0
      have hApart := card_holesIcc_le_card_holes (S := A) (M := M)
        (a := c + M - N) (b := M) (by omega) (by omega)
      have hBpart := card_holesIcc_le_card_holes (S := B) (M := N)
        (a := c) (b := N) (by omega) (by omega)
      have hBh := card_holes hB
      have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
      have hgap : A.card + B.card - 1 ≤ M + c := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := 0) (c := c) (by intro x hx; simp [L, hLempty] at hx)
        (by simpa [R] using hright)
      refine ⟨0, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      have hgap : A.card + B.card - 1 ≤ M + (N + 1) := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := 0) (c := N + 1) (by intro x hx; simp [L, hLempty] at hx)
        (by intro x hx; simp [R, hRempty] at hx)
      refine ⟨0, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨by omega, by omega⟩

/-! ## Residue representatives for Ruzsa's diameter estimate -/

def modImage (S : Finset ℕ) (v : ℕ) : Finset (ZMod v) :=
  S.image fun x : ℕ ↦ (x : ZMod v)

def modFiber (S : Finset ℕ) (v : ℕ) (c : ZMod v) : Finset ℕ :=
  S.filter fun x ↦ (x : ZMod v) = c

@[simp] lemma mem_modImage {S : Finset ℕ} {v : ℕ} {c : ZMod v} :
    c ∈ modImage S v ↔ ∃ x ∈ S, (x : ZMod v) = c := by
  simp [modImage]

@[simp] lemma mem_modFiber {S : Finset ℕ} {v x : ℕ} {c : ZMod v} :
    x ∈ modFiber S v c ↔ x ∈ S ∧ (x : ZMod v) = c := by
  simp [modFiber]

lemma modFiber_nonempty {S : Finset ℕ} {v : ℕ} {c : ZMod v}
    (hc : c ∈ modImage S v) : (modFiber S v c).Nonempty := by
  obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
  exact ⟨x, mem_modFiber.mpr ⟨hx, hxc⟩⟩

/-- The least integer of `S` in a residue represented by `S`. -/
noncomputable def residueRep (S : Finset ℕ) (v : ℕ)
    (c : ↑(modImage S v)) : ℕ :=
  (modFiber S v c.1).min' (modFiber_nonempty c.2)

lemma residueRep_mem (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    residueRep S v c ∈ S := by
  exact (mem_modFiber.mp ((modFiber S v c.1).min'_mem (modFiber_nonempty c.2))).1

lemma residueRep_cast (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    ((residueRep S v c : ℕ) : ZMod v) = c.1 := by
  exact (mem_modFiber.mp ((modFiber S v c.1).min'_mem (modFiber_nonempty c.2))).2

lemma residueRep_le {S : Finset ℕ} {v z : ℕ} (c : ↑(modImage S v))
    (hz : z ∈ S) (hzc : (z : ZMod v) = c.1) : residueRep S v c ≤ z := by
  apply (modFiber S v c.1).min'_le z
  exact mem_modFiber.mpr ⟨hz, hzc⟩

lemma residueRep_injective (S : Finset ℕ) (v : ℕ) :
    Function.Injective (residueRep S v) := by
  intro c d hcd
  apply Subtype.ext
  rw [← residueRep_cast S v c, ← residueRep_cast S v d, hcd]

noncomputable def residueReps (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (modImage S v).attach.image (residueRep S v)

lemma card_residueReps (S : Finset ℕ) (v : ℕ) :
    (residueReps S v).card = (modImage S v).card := by
  rw [residueReps, card_image_of_injective _ (residueRep_injective S v)]
  simp

lemma residueReps_subset (S : Finset ℕ) (v : ℕ) : residueReps S v ⊆ S := by
  intro z hz
  simp only [residueReps, mem_image] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  exact residueRep_mem S v c

lemma cast_mem_modImage_of_mem_residueReps {S : Finset ℕ} {v z : ℕ}
    (hz : z ∈ residueReps S v) : (z : ZMod v) ∈ modImage S v := by
  simp only [residueReps, mem_image] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  rw [residueRep_cast]
  exact c.2

lemma residueRep_of_cast {S : Finset ℕ} {v z : ℕ} (hz : z ∈ S) :
    residueRep S v ⟨(z : ZMod v), mem_modImage.mpr ⟨z, hz, rfl⟩⟩ ≤ z := by
  exact residueRep_le _ hz rfl

/-- Reduction modulo `v` commutes with a natural-number sumset. -/
lemma modImage_add (A B : Finset ℕ) (v : ℕ) :
    modImage (A + B) v = modImage A v + modImage B v := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc
    simp only [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    apply Finset.mem_add.mpr
    refine ⟨(a : ZMod v), mem_modImage.mpr ⟨a, ha, rfl⟩,
      (b : ZMod v), mem_modImage.mpr ⟨b, hb, rfl⟩, ?_⟩
    simpa using hzc
  · intro hc
    simp only [Finset.mem_add] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    obtain ⟨x, hx, hxa⟩ := mem_modImage.mp ha
    obtain ⟨y, hy, hyb⟩ := mem_modImage.mp hb
    apply mem_modImage.mpr
    refine ⟨x + y, Finset.add_mem_add hx hy, ?_⟩
    push_cast
    rw [hxa, hyb]

/-- The `v`-shifted copy of `A` used for the extra lift in every residue
represented by `A`. -/
def shiftedBy (A : Finset ℕ) (v : ℕ) : Finset ℕ := A.image fun a ↦ a + v

lemma card_shiftedBy (A : Finset ℕ) (v : ℕ) : (shiftedBy A v).card = A.card := by
  rw [shiftedBy, Finset.card_image_of_injective]
  intro x y h
  change x + v = y + v at h
  omega

lemma shiftedBy_subset_add {A B : Finset ℕ} {v : ℕ} (hvB : v ∈ B) :
    shiftedBy A v ⊆ A + B := by
  intro z hz
  simp only [shiftedBy, mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  exact Finset.add_mem_add ha hvB

lemma residueReps_disjoint_shiftedBy {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (_huv : u ≤ v) (hv : 0 < v)
    (_hA0 : 0 ∈ A) (hB0 : 0 ∈ B) :
    Disjoint (residueReps (A + B) v) (shiftedBy A v) := by
  rw [Finset.disjoint_left]
  intro z hzR hzE
  simp only [shiftedBy, mem_image] at hzE
  obtain ⟨a, ha, rfl⟩ := hzE
  simp only [residueReps, mem_image] at hzR
  obtain ⟨c, hc, hrep⟩ := hzR
  have hcast : c.1 = (a : ZMod v) := by
    rw [← residueRep_cast (A + B) v c, hrep]
    simp
  let ca : ↑(modImage (A + B) v) :=
    ⟨(a : ZMod v), mem_modImage.mpr ⟨a, Finset.add_mem_add ha hB0, rfl⟩⟩
  have hca : c = ca := by
    apply Subtype.ext
    exact hcast
  subst c
  have hle : residueRep (A + B) v ca ≤ a :=
    residueRep_le ca (Finset.add_mem_add ha hB0) rfl
  have haU := mem_Icc.mp (hA ha)
  dsimp [ca] at hrep hle
  omega

/-- Ruzsa's basic lift count, equation (4.3): there is one sum for each
sum residue and one further sum for each member of the smaller-diameter
summand. -/
lemma card_modImage_add_add_card_le {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v) (hA0 : 0 ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B) :
    (modImage (A + B) v).card + A.card ≤ (A + B).card := by
  have hR := residueReps_subset (A + B) v
  have hE := shiftedBy_subset_add (A := A) hvB
  have hdisj := residueReps_disjoint_shiftedBy hA huv hv hA0 hB0
  rw [← card_residueReps (A + B) v, ← card_shiftedBy A v,
    ← card_union_of_disjoint hdisj]
  exact card_le_card (union_subset hR hE)

lemma natCast_injOn_Ico {v : ℕ} :
    Set.InjOn (fun x : ℕ ↦ (x : ZMod v)) (Ico 0 v) := by
  intro x hx y hy hxy
  have hx' := mem_Ico.mp hx
  have hy' := mem_Ico.mp hy
  have hv : 0 < v := by omega
  have hvx := congrArg ZMod.val hxy
  rw [ZMod.val_natCast_of_lt hx'.2, ZMod.val_natCast_of_lt hy'.2] at hvx
  exact hvx

lemma card_modImage_eq_card_of_lt {S : Finset ℕ} {u v : ℕ}
    (hS : S ⊆ Icc 0 u) (huv : u < v) : (modImage S v).card = S.card := by
  apply card_image_iff.mpr
  apply (natCast_injOn_Ico (v := v)).mono
  intro x hx
  have hx' := mem_Icc.mp (hS hx)
  exact mem_Ico.mpr ⟨hx'.1, hx'.2.trans_lt huv⟩

lemma erase_top_subset_Ico {S : Finset ℕ} {v : ℕ} (hS : S ⊆ Icc 0 v) :
    S.erase v ⊆ Ico 0 v := by
  intro x hx
  have hxS := mem_of_mem_erase hx
  have hxI := mem_Icc.mp (hS hxS)
  have hxne := ne_of_mem_erase hx
  exact mem_Ico.mpr ⟨hxI.1, lt_of_le_of_ne hxI.2 hxne⟩

lemma modImage_erase_top {S : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (h0 : 0 ∈ S) (_hvS : v ∈ S) : modImage (S.erase v) v = modImage S v := by
  ext c
  constructor
  · intro hc
    obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
    exact mem_modImage.mpr ⟨x, mem_of_mem_erase hx, hxc⟩
  · intro hc
    obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
    by_cases hxv : x = v
    · subst x
      apply mem_modImage.mpr
      refine ⟨0, mem_erase.mpr ⟨by omega, h0⟩, ?_⟩
      simpa using hxc
    · exact mem_modImage.mpr ⟨x, mem_erase.mpr ⟨hxv, hx⟩, hxc⟩

lemma card_modImage_add_one_eq {S : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (hS : S ⊆ Icc 0 v) (h0 : 0 ∈ S) (hvS : v ∈ S) :
    (modImage S v).card + 1 = S.card := by
  have hinj : Set.InjOn (fun x : ℕ ↦ (x : ZMod v)) (S.erase v) :=
    (natCast_injOn_Ico (v := v)).mono (erase_top_subset_Ico hS)
  rw [← modImage_erase_top hv h0 hvS, modImage, card_image_iff.mpr hinj,
    card_erase_of_mem hvS]
  have : 0 < S.card := card_pos.mpr ⟨v, hvS⟩
  omega

lemma zero_mem_modImage {S : Finset ℕ} {v : ℕ} (h0 : 0 ∈ S) :
    (0 : ZMod v) ∈ modImage S v := mem_modImage.mpr ⟨0, h0, by simp⟩

lemma modImage_nonempty {S : Finset ℕ} {v : ℕ} (hS : S.Nonempty) :
    (modImage S v).Nonempty := hS.image _

lemma zero_mem_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) : 0 ∈ C.addStab := by
  exact hC.zero_mem_addStab

lemma addStab_add_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x y : G}
    (hx : x ∈ C.addStab) (hy : y ∈ C.addStab) : x + y ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx hy ⊢
  exact (AddAction.stabilizer G (C : Set G)).add_mem hx hy

lemma addStab_neg_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x : G}
    (hx : x ∈ C.addStab) : -x ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx ⊢
  exact (AddAction.stabilizer G (C : Set G)).neg_mem hx

lemma addStab_sub_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x y : G}
    (hx : x ∈ C.addStab) (hy : y ∈ C.addStab) : x - y ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx hy ⊢
  exact (AddAction.stabilizer G (C : Set G)).sub_mem hx hy

/-- If all residues of a set of integers lie in a subgroup and their
integer gcd is one, that subgroup is all of `ZMod v`. -/
lemma stabilizer_eq_top_of_gcd_one {S : Finset ℕ} {v : ℕ}
    (hgcd : S.gcd (fun n ↦ (n : ℤ)) = 1)
    (K : AddSubgroup (ZMod v)) (hS : ∀ n ∈ S, (n : ZMod v) ∈ K) : K = ⊤ := by
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul S (fun n ↦ (n : ℤ))
  have hterms : ∀ n ∈ S, (n : ZMod v) * (g n : ZMod v) ∈ K := by
    intro n hn
    have hnK := hS n hn
    have hz := K.zsmul_mem hnK (g n)
    simpa [smul_eq_mul, mul_comm] using hz
  have hsum : ((∑ n ∈ S, (n : ℤ) * g n : ℤ) : ZMod v) ∈ K := by
    push_cast
    exact K.sum_mem fun n hn ↦ hterms n hn
  have hone : (1 : ZMod v) ∈ K := by
    rw [hgcd] at hg
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod v)) hg
    norm_num at hcast
    rw [hcast]
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using hsum
  apply (AddSubgroup.eq_top_iff' K).mpr
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
  rw [← hz]
  simpa [smul_eq_mul] using K.zsmul_mem hone z

/-! ## The refined lift across a missing stabilizer coset -/

/-- The least integer representative of a residue of `S` which is outside
the prescribed residue set `D`. -/
noncomputable def residueRepOutside (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) (c : ↑(modImage S v \ D)) : ℕ :=
  residueRep S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

/-- One least representative for every residue of `S` outside `D`. -/
noncomputable def residueRepsOutside (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  (modImage S v \ D).attach.image (residueRepOutside S v D)

lemma residueRepOutside_mem (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v))
    (c : ↑(modImage S v \ D)) : residueRepOutside S v D c ∈ S := by
  exact residueRep_mem S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

lemma residueRepOutside_cast (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v))
    (c : ↑(modImage S v \ D)) :
    ((residueRepOutside S v D c : ℕ) : ZMod v) = c.1 := by
  exact residueRep_cast S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

lemma residueRepOutside_injective (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    Function.Injective (residueRepOutside S v D) := by
  intro c e hce
  apply Subtype.ext
  rw [← residueRepOutside_cast S v D c,
    ← residueRepOutside_cast S v D e, hce]

lemma card_residueRepsOutside (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    (residueRepsOutside S v D).card = (modImage S v \ D).card := by
  rw [residueRepsOutside,
    card_image_of_injective _ (residueRepOutside_injective S v D)]
  simp

lemma residueRepsOutside_subset (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    residueRepsOutside S v D ⊆ S := by
  intro z hz
  simp only [residueRepsOutside, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact residueRepOutside_mem S v D c

lemma cast_not_mem_of_mem_residueRepsOutside {S : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} (hz : z ∈ residueRepsOutside S v D) :
    (z : ZMod v) ∉ D := by
  simp only [residueRepsOutside, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  rw [residueRepOutside_cast]
  exact (mem_sdiff.mp c.2).2

/-- Sums in a chosen residue set. -/
def sumsOverResidues (A B : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  (A + B).filter fun z ↦ (z : ZMod v) ∈ D

@[simp] lemma mem_sumsOverResidues {A B : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} :
    z ∈ sumsOverResidues A B v D ↔ z ∈ A + B ∧ (z : ZMod v) ∈ D := by
  simp [sumsOverResidues]

/-- Ruzsa's refined lift: besides one representative outside `D`, retain
the shifted copy of `A` and every actual sum whose residue lies in `D`.
When `D` misses all residues of `A`, these three collections are disjoint. -/
lemma card_modImage_add_add_card_add_fiber_le {A B : Finset ℕ} {u v : ℕ}
    (D : Finset (ZMod v))
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v) (hA0 : 0 ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hD : D ⊆ modImage (A + B) v)
    (hDA : Disjoint D (modImage A v)) :
    (modImage (A + B) v).card + A.card +
        (sumsOverResidues A B v D).card ≤ (A + B).card + D.card := by
  let R := residueRepsOutside (A + B) v D
  let E := shiftedBy A v
  let F := sumsOverResidues A B v D
  have hRS : R ⊆ A + B := residueRepsOutside_subset (A + B) v D
  have hES : E ⊆ A + B := shiftedBy_subset_add hvB
  have hFS : F ⊆ A + B := filter_subset _ _
  have hRE : Disjoint R E := by
    apply Disjoint.mono_left _ (residueReps_disjoint_shiftedBy hA huv hv hA0 hB0)
    intro z hz
    change z ∈ residueRepsOutside (A + B) v D at hz
    simp only [residueRepsOutside, residueReps, mem_image] at hz ⊢
    obtain ⟨c, -, rfl⟩ := hz
    exact ⟨⟨c.1, (mem_sdiff.mp c.2).1⟩, by simp,
      rfl⟩
  have hRF : Disjoint R F := by
    rw [Finset.disjoint_left]
    intro z hzR hzF
    exact (cast_not_mem_of_mem_residueRepsOutside hzR)
      (mem_sumsOverResidues.mp hzF).2
  have hEF : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro z hzE hzF
    simp only [E, shiftedBy, mem_image] at hzE
    obtain ⟨a, ha, rfl⟩ := hzE
    have haD : (a : ZMod v) ∈ D := by
      simpa using (mem_sumsOverResidues.mp hzF).2
    exact (Finset.disjoint_left.mp hDA) haD
      (mem_modImage.mpr ⟨a, ha, rfl⟩)
  have hREF : Disjoint (R ∪ E) F := by
    rw [Finset.disjoint_left]
    intro z hz hzF
    rcases mem_union.mp hz with hzR | hzE
    · exact (Finset.disjoint_left.mp hRF) hzR hzF
    · exact (Finset.disjoint_left.mp hEF) hzE hzF
  have hU : (R ∪ E) ∪ F ⊆ A + B := union_subset (union_subset hRS hES) hFS
  have hcardU := card_le_card hU
  rw [card_union_of_disjoint hREF, card_union_of_disjoint hRE,
    card_residueRepsOutside, card_shiftedBy] at hcardU
  have hsplit := card_sdiff_add_card_eq_card hD
  change (modImage (A + B) v \ D).card + D.card =
    (modImage (A + B) v).card at hsplit
  change (modImage (A + B) v).card + A.card + F.card ≤
    (A + B).card + D.card
  omega

/-- The integers of `S` whose residues belong to `D`. -/
def residueFiberSet (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  S.filter fun z ↦ (z : ZMod v) ∈ D

@[simp] lemma mem_residueFiberSet {S : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} :
    z ∈ residueFiberSet S v D ↔ z ∈ S ∧ (z : ZMod v) ∈ D := by
  simp [residueFiberSet]

lemma modImage_residueFiberSet (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) :
    modImage (residueFiberSet S v D) v = modImage S v ∩ D := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc
    have hz' := mem_residueFiberSet.mp hz
    exact mem_inter.mpr ⟨mem_modImage.mpr ⟨z, hz'.1, hzc⟩, by simpa [hzc] using hz'.2⟩
  · intro hc
    have hc' := mem_inter.mp hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc'.1
    apply mem_modImage.mpr
    exact ⟨z, mem_residueFiberSet.mpr ⟨hz, by simpa [hzc] using hc'.2⟩, hzc⟩

lemma card_modImage_le (S : Finset ℕ) (v : ℕ) :
    (modImage S v).card ≤ S.card := by
  exact card_image_le

/-- Saturating a residue set by `H` fills the coset through any occupied
residue.  The only overcount in adjoining that coset is paid for by the
corresponding integer fiber. -/
lemma card_modImage_add_card_le_saturation_add_fiber
    {S : Finset ℕ} {v : ℕ} {H : Finset (ZMod v)} {a : ZMod v}
    (h0 : (0 : ZMod v) ∈ H) (ha : a ∈ modImage S v) :
    (modImage S v).card + H.card ≤
      (modImage S v + H).card +
        (residueFiberSet S v (a +ᵥ H)).card := by
  let X := modImage S v
  let D := a +ᵥ H
  have hX : X ⊆ X + H := by
    intro x hx
    have : x + 0 ∈ X + H := Finset.add_mem_add hx h0
    simpa using this
  have hD : D ⊆ X + H := vadd_finset_subset_add ha
  have hU : X ∪ D ⊆ X + H := union_subset hX hD
  have hinter : (X ∩ D).card ≤ (residueFiberSet S v D).card := by
    rw [← modImage_residueFiberSet]
    exact card_modImage_le _ _
  have hcardU := card_le_card hU
  have hcardD : D.card = H.card := card_vadd_finset a H
  have hIE := card_union_add_card_inter X D
  change X.card + H.card ≤ (X + H).card + (residueFiberSet S v D).card
  omega

lemma disjoint_vadd_add_of_not_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X H : Finset G} {c : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hc : c ∉ X + H) :
    Disjoint (c +ᵥ H) (X + H) := by
  rw [Finset.disjoint_left]
  intro z hzD hzX
  obtain ⟨h₂, hh₂, hh₂z⟩ := mem_vadd_finset.mp hzD
  obtain ⟨x, hx, h₁, hh₁, hh₁z⟩ := mem_add.mp hzX
  change c + h₂ = z at hh₂z
  apply hc
  apply mem_add.mpr
  refine ⟨x, hx, h₁ + -h₂, hadd h₁ hh₁ (-h₂) (hneg h₂ hh₂), ?_⟩
  calc
    x + (h₁ + -h₂) = (x + h₁) + -h₂ := by abel
    _ = z + -h₂ := by rw [hh₁z]
    _ = (c + h₂) + -h₂ := by rw [hh₂z]
    _ = c := by abel

lemma disjoint_self_vadd_of_not_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {H : Finset G} {b : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hb : b ∉ H) :
    Disjoint H (b +ᵥ H) := by
  rw [Finset.disjoint_left]
  intro z hzH hzD
  obtain ⟨h, hh, hhz⟩ := mem_vadd_finset.mp hzD
  change b + h = z at hhz
  apply hb
  have : z + -h ∈ H := hadd z hzH (-h) (hneg h hh)
  convert this using 1
  rw [← hhz]
  abel

lemma residueFiberSet_add_subset_sumsOverResidues
    {A B : Finset ℕ} {v : ℕ} {H : Finset (ZMod v)} {a b c : ZMod v}
    (hc : a + b = c)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) :
    residueFiberSet A v (a +ᵥ H) + residueFiberSet B v (b +ᵥ H) ⊆
      sumsOverResidues A B v (c +ᵥ H) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_residueFiberSet.mp hx
  have hy' := mem_residueFiberSet.mp hy
  obtain ⟨h₁, hh₁, ha⟩ := mem_vadd_finset.mp hx'.2
  obtain ⟨h₂, hh₂, hb⟩ := mem_vadd_finset.mp hy'.2
  change a + h₁ = (x : ZMod v) at ha
  change b + h₂ = (y : ZMod v) at hb
  apply mem_sumsOverResidues.mpr
  constructor
  · exact Finset.add_mem_add hx'.1 hy'.1
  · apply mem_vadd_finset.mpr
    refine ⟨h₁ + h₂, hadd h₁ hh₁ h₂ hh₂, ?_⟩
    change c + (h₁ + h₂) = ((x + y : ℕ) : ZMod v)
    push_cast
    rw [← ha, ← hb, ← hc]
    abel

/-! ## Ruzsa's diameter estimate -/

/-- Ruzsa's modular diameter estimate in the normalized situation.  The
set of all elements of the two summands has integer gcd one. -/
theorem ruzsa_normalized_diameter_bound
    {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (hB : B ⊆ Icc 0 v) (huv : u ≤ v)
    (hv : 0 < v) (hA0 : 0 ∈ A) (huA : u ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hgcd : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1) :
    min (A.card + v)
      (A.card + B.card + min A.card B.card - 3) ≤ (A + B).card := by
  let _ : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let A₀ := modImage A v
  let B₀ := modImage B v
  let C₀ := A₀ + B₀
  let H := C₀.addStab
  have hA₀zero : (0 : ZMod v) ∈ A₀ := zero_mem_modImage hA0
  have hB₀zero : (0 : ZMod v) ∈ B₀ := zero_mem_modImage hB0
  have hA₀ne : A₀.Nonempty := ⟨0, hA₀zero⟩
  have hB₀ne : B₀.Nonempty := ⟨0, hB₀zero⟩
  have hC₀ne : C₀.Nonempty := by
    rw [Finset.add_nonempty]
    exact ⟨hA₀ne, hB₀ne⟩
  have hHzero : (0 : ZMod v) ∈ H := zero_mem_addStab hC₀ne
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hC₀ne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hC₀ne hx
  have hA₀C₀ : A₀ ⊆ C₀ := by
    intro a ha
    exact mem_add.mpr ⟨a, ha, 0, hB₀zero, by simp⟩
  have hB₀C₀ : B₀ ⊆ C₀ := by
    intro b hb
    exact mem_add.mpr ⟨0, hA₀zero, b, hb, by simp⟩
  have hA₀sat : A₀ ⊆ A₀ + H := by
    intro a ha
    exact mem_add.mpr ⟨a, ha, 0, hHzero, by simp⟩
  have hB₀sat : B₀ ⊆ B₀ + H := by
    intro b hb
    exact mem_add.mpr ⟨b, hb, 0, hHzero, by simp⟩
  have hA₀H_C₀ : A₀ + H ⊆ C₀ := by
    have hs := add_subset_add hA₀C₀ (subset_rfl : H ⊆ H)
    change A₀ + H ⊆ C₀ + H at hs
    simpa only [H, add_addStab] using hs
  have hB₀H_C₀ : B₀ + H ⊆ C₀ := by
    have hs := add_subset_add hB₀C₀ (subset_rfl : H ⊆ H)
    change B₀ + H ⊆ C₀ + H at hs
    simpa only [H, add_addStab] using hs
  have hB₀card : B₀.card + 1 = B.card := by
    exact card_modImage_add_one_eq hv hB hB0 hvB
  have hA₀card : A.card ≤ A₀.card + 1 := by
    by_cases hlt : u < v
    · have h := card_modImage_eq_card_of_lt hA hlt
      change A₀.card = A.card at h
      omega
    · have huv' : u = v := by omega
      subst u
      have h := card_modImage_add_one_eq hv hA hA0 huA
      change A₀.card + 1 = A.card at h
      omega
  have hC₀image : C₀ = modImage (A + B) v := by
    change modImage A v + modImage B v = modImage (A + B) v
    exact (modImage_add A B v).symm
  have hlift : C₀.card + A.card ≤ (A + B).card := by
    rw [hC₀image]
    exact card_modImage_add_add_card_le hA huv hv hA0 hB0 hvB
  have hkneser : (A₀ + H).card + (B₀ + H).card ≤ C₀.card + H.card := by
    have hk := Finset.add_kneser A₀ B₀
    change (A₀ + C₀.addStab).card + (B₀ + C₀.addStab).card ≤
      C₀.card + C₀.addStab.card at hk
    exact hk
  have hHcard : H.card ≤ v := by
    calc
      H.card ≤ (Finset.univ : Finset (ZMod v)).card := card_le_card (subset_univ H)
      _ = v := by simp [ZMod.card]
  by_cases hwhole : H.card = v
  · have hHC₀ : H ⊆ C₀ := by
      intro h hh
      exact hA₀H_C₀ (mem_add.mpr ⟨0, hA₀zero, h, hh, by simp⟩)
    have hC₀cardle : C₀.card ≤ v := by
      calc
        C₀.card ≤ (Finset.univ : Finset (ZMod v)).card :=
          card_le_card (subset_univ C₀)
        _ = v := by simp [ZMod.card]
    have hC₀card : C₀.card = v := by
      have := card_le_card hHC₀
      omega
    apply (min_le_left _ _).trans
    omega
  · have hHlt : H.card < v := by omega
    have hnotBoth : ¬ (A₀ ⊆ H ∧ B₀ ⊆ H) := by
      rintro ⟨hAH, hBH⟩
      let K : AddSubgroup (ZMod v) := AddAction.stabilizer (ZMod v) (C₀ : Set (ZMod v))
      have hHK : (H : Set (ZMod v)) = (K : Set (ZMod v)) := by
        change (↑C₀.addStab : Set (ZMod v)) = _
        exact coe_addStab hC₀ne
      have hUK : ∀ n ∈ A ∪ B, (n : ZMod v) ∈ K := by
        intro n hn
        have hnH : (n : ZMod v) ∈ H := by
          rcases mem_union.mp hn with hnA | hnB
          · exact hAH (mem_modImage.mpr ⟨n, hnA, rfl⟩)
          · exact hBH (mem_modImage.mpr ⟨n, hnB, rfl⟩)
        have hnHs : (n : ZMod v) ∈ (H : Set (ZMod v)) := hnH
        rw [hHK] at hnHs
        exact hnHs
      have hKtop := stabilizer_eq_top_of_gcd_one hgcd K hUK
      have hHuniv : H = (Finset.univ : Finset (ZMod v)) := by
        ext x
        simp only [mem_univ, iff_true]
        have hxK : x ∈ K := by rw [hKtop]; trivial
        have hxKs : x ∈ (K : Set (ZMod v)) := hxK
        rw [← hHK] at hxKs
        exact hxKs
      have : H.card = v := by simp [hHuniv, ZMod.card]
      omega
    by_cases hBH : B₀ ⊆ H
    · have hAnH : ¬ A₀ ⊆ H := fun hAH ↦ hnotBoth ⟨hAH, hBH⟩
      obtain ⟨a, haA, haH⟩ := Finset.not_subset.mp hAnH
      have hdisj : Disjoint H (a +ᵥ H) :=
        disjoint_self_vadd_of_not_mem hHadd hHneg haH
      have hHsub : H ⊆ A₀ + H := by
        intro h hh
        exact mem_add.mpr ⟨0, hA₀zero, h, hh, by simp⟩
      have hacoset : a +ᵥ H ⊆ A₀ + H := vadd_finset_subset_add haA
      have hAsat : 2 * H.card ≤ (A₀ + H).card := by
        have hc := card_le_card (union_subset hHsub hacoset)
        rw [card_union_of_disjoint hdisj, card_vadd_finset] at hc
        omega
      have hBsatEq : B₀ + H = H := by
        apply Subset.antisymm
        · intro z hz
          obtain ⟨b, hb, h, hh, rfl⟩ := mem_add.mp hz
          exact hHadd b (hBH hb) h hh
        · intro h hh
          exact mem_add.mpr ⟨0, hB₀zero, h, hh, by simp⟩
      have hC₀lower : 2 * H.card ≤ C₀.card := by
        rw [hBsatEq] at hkneser
        omega
      have hBsmall : B.card ≤ H.card + 1 := by
        have hc := card_le_card hBH
        omega
      apply (min_le_right _ _).trans
      have hm := min_le_left A.card B.card
      omega
    · obtain ⟨b', hb'B, hb'H⟩ := Finset.not_subset.mp hBH
      have hdisjBH : Disjoint H (b' +ᵥ H) :=
        disjoint_self_vadd_of_not_mem hHadd hHneg hb'H
      have hHsubB : H ⊆ B₀ + H := by
        intro h hh
        exact mem_add.mpr ⟨0, hB₀zero, h, hh, by simp⟩
      have hbcoset : b' +ᵥ H ⊆ B₀ + H := vadd_finset_subset_add hb'B
      have hBsat : 2 * H.card ≤ (B₀ + H).card := by
        have hc := card_le_card (union_subset hHsubB hbcoset)
        rw [card_union_of_disjoint hdisjBH, card_vadd_finset] at hc
        omega
      have hAproperCard : (A₀ + H).card + H.card ≤ C₀.card := by omega
      have hHpos : 0 < H.card := card_pos.mpr ⟨0, hHzero⟩
      have hnotSubset : ¬ C₀ ⊆ A₀ + H := by
        intro hs
        have hc := card_le_card hs
        omega
      obtain ⟨c, hcC, hcA⟩ := Finset.not_subset.mp hnotSubset
      have hDsubC : c +ᵥ H ⊆ C₀ := by
        have hs : c +ᵥ H ⊆ C₀ + H := vadd_finset_subset_add hcC
        change c +ᵥ H ⊆ C₀ + C₀.addStab at hs
        simpa only [add_addStab] using hs
      have hDdisjSat : Disjoint (c +ᵥ H) (A₀ + H) :=
        disjoint_vadd_add_of_not_mem hHadd hHneg hcA
      have hDdisjA : Disjoint (c +ᵥ H) A₀ :=
        hDdisjSat.mono_right hA₀sat
      obtain ⟨a, haA, b, hbB, hab⟩ := mem_add.mp hcC
      let X := a +ᵥ H
      let Y := b +ᵥ H
      let D := c +ᵥ H
      let R := residueFiberSet A v X
      let S := residueFiberSet B v Y
      let F := sumsOverResidues A B v D
      have hRne : R.Nonempty := by
        obtain ⟨x, hxA, hxa⟩ := mem_modImage.mp haA
        refine ⟨x, mem_residueFiberSet.mpr ⟨hxA, ?_⟩⟩
        apply mem_vadd_finset.mpr
        exact ⟨0, hHzero, by simpa using hxa.symm⟩
      have hSne : S.Nonempty := by
        obtain ⟨y, hyB, hyb⟩ := mem_modImage.mp hbB
        refine ⟨y, mem_residueFiberSet.mpr ⟨hyB, ?_⟩⟩
        apply mem_vadd_finset.mpr
        exact ⟨0, hHzero, by simpa using hyb.symm⟩
      have hRF : R + S ⊆ F := by
        exact residueFiberSet_add_subset_sumsOverResidues hab hHadd
      have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hRne hSne
      have hFcard : R.card + S.card ≤ F.card + 1 := by
        have hs := card_le_card hRF
        change R.card + S.card - 1 ≤ (R + S).card at hcauchy
        have hRp : 0 < R.card := card_pos.mpr hRne
        have hSp : 0 < S.card := card_pos.mpr hSne
        omega
      have hAsatFiber : A₀.card + H.card ≤ (A₀ + H).card + R.card := by
        exact card_modImage_add_card_le_saturation_add_fiber hHzero haA
      have hBsatFiber : B₀.card + H.card ≤ (B₀ + H).card + S.card := by
        exact card_modImage_add_card_le_saturation_add_fiber hHzero hbB
      have hDcard : D.card = H.card := card_vadd_finset c H
      have hDimage : D ⊆ modImage (A + B) v := by
        rw [← hC₀image]
        exact hDsubC
      have hrefined : C₀.card + A.card + F.card ≤
          (A + B).card + H.card := by
        have hr := card_modImage_add_add_card_add_fiber_le D hA huv hv hA0 hB0 hvB
          hDimage hDdisjA
        rw [← hC₀image, hDcard] at hr
        exact hr
      apply (min_le_right _ _).trans
      have hm := min_le_left A.card B.card
      omega

/-- The normalized strict Bardaji--Grynkiewicz alternative.  Failure of
three-summand growth forces an interval of the full Cauchy--Davenport
length in the sumset. -/
theorem normalized_growth_or_long_interval
    {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (hB : B ⊆ Icc 0 v) (huv : u ≤ v)
    (hv : 0 < v) (hA0 : 0 ∈ A) (huA : u ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hgcd : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1) :
    A.card + B.card + min A.card B.card ≤ (A + B).card + 3 ∨
      ∃ lo, Icc lo (lo + (A.card + B.card - 2)) ⊆ A + B := by
  by_cases hgrowth :
      A.card + B.card + min A.card B.card ≤ (A + B).card + 3
  · exact Or.inl hgrowth
  · right
    have hAne : A.Nonempty := ⟨0, hA0⟩
    have hBne : B.Nonempty := ⟨0, hB0⟩
    have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hAne hBne
    have hlow : A.card + B.card ≤ (A + B).card + 1 := by
      change A.card + B.card - 1 ≤ (A + B).card at hcauchy
      have hAp : 0 < A.card := card_pos.mpr hAne
      have hBp : 0 < B.card := card_pos.mpr hBne
      omega
    let r := (A + B).card + 1 - (A.card + B.card)
    have hsumcard : (A + B).card + 1 = A.card + B.card + r := by
      dsimp [r]
      omega
    have hr : r + 3 ≤ A.card := by
      have hm := min_le_left A.card B.card
      omega
    have hruzsa := ruzsa_normalized_diameter_bound hA hB huv hv hA0 huA hB0 hvB hgcd
    have hdiam : v + 3 ≤ B.card + A.card := by
      have hm := min_le_right A.card B.card
      omega
    have hlong := normalized_long_interval (A := B) (B := A)
      (M := v) (N := u) (r := r) huv hB hA hB0 hvB hA0 huA
      hdiam (by simpa [add_comm] using hsumcard) hr
    obtain ⟨lo, hlo⟩ := hlong
    refine ⟨lo, ?_⟩
    simpa only [add_comm (a := B.card) A.card, add_comm (a := B) A] using hlo

/-! ## Translation and division by the common gcd -/

lemma nat_int_finset_gcd (S : Finset ℕ) :
    S.gcd (fun n ↦ (n : ℤ)) =
      (((S.gcd (fun n : ℕ ↦ n) : ℕ) : ℤ)) := by
  induction S using Finset.cons_induction_on with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.gcd_cons ha, Finset.gcd_cons ha, ih]
    rw [← Int.coe_gcd]
    rfl

/-- Translate a natural finset down by `m` and divide by `d`. -/
def normalizeNat (S : Finset ℕ) (m d : ℕ) : Finset ℕ :=
  S.image fun x ↦ (x - m) / d

lemma mem_normalizeNat {S : Finset ℕ} {m d q : ℕ} :
    q ∈ normalizeNat S m d ↔ ∃ x ∈ S, (x - m) / d = q := by
  simp [normalizeNat]

lemma normalizeNat_spec {S : Finset ℕ} {m d : ℕ}
    (hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m)
    {q : ℕ} : q ∈ normalizeNat S m d ↔ ∃ x ∈ S, x = m + d * q := by
  constructor
  · intro hq
    obtain ⟨x, hx, rfl⟩ := mem_normalizeNat.mp hq
    refine ⟨x, hx, ?_⟩
    have hcancel := Nat.mul_div_cancel' (hdiv x hx)
    have hmx := hmin x hx
    omega
  · rintro ⟨x, hx, rfl⟩
    apply mem_normalizeNat.mpr
    refine ⟨m + d * q, hx, ?_⟩
    have : m + d * q - m = d * q := by omega
    rw [this]
    exact Nat.mul_div_cancel_left q hd

lemma card_normalizeNat {S : Finset ℕ} {m d : ℕ}
    (_hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m) :
    (normalizeNat S m d).card = S.card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  have hdx := Nat.mul_div_cancel' (hdiv x hx)
  have hdy := Nat.mul_div_cancel' (hdiv y hy)
  have hmx := hmin x hx
  have hmy := hmin y hy
  change (x - m) / d = (y - m) / d at hxy
  have := congrArg (fun z ↦ d * z) hxy
  rw [hdx, hdy] at this
  omega

lemma normalizeNat_subset_Icc {S : Finset ℕ} {m d M : ℕ}
    (hS : S ⊆ Icc m M) : normalizeNat S m d ⊆ Icc 0 ((M - m) / d) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := mem_normalizeNat.mp hq
  have hxI := mem_Icc.mp (hS hx)
  exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right (Nat.sub_le_sub_right hxI.2 m)⟩

lemma zero_mem_normalizeNat {S : Finset ℕ} {m d : ℕ} (hm : m ∈ S) :
    0 ∈ normalizeNat S m d := by
  apply mem_normalizeNat.mpr
  exact ⟨m, hm, by simp⟩

lemma top_mem_normalizeNat {S : Finset ℕ} {m d M : ℕ} (hM : M ∈ S) :
    (M - m) / d ∈ normalizeNat S m d := by
  apply mem_normalizeNat.mpr
  exact ⟨M, hM, rfl⟩

/-- Reconstructing the original sumset from the translated, divided
summands. -/
lemma sumset_eq_image_normalized {S T : Finset ℕ} {s t d : ℕ}
    (hd : 0 < d) (hSmin : ∀ x ∈ S, s ≤ x) (hTmin : ∀ x ∈ T, t ≤ x)
    (hSdiv : ∀ x ∈ S, d ∣ x - s) (hTdiv : ∀ x ∈ T, d ∣ x - t) :
    S + T = (normalizeNat S s d + normalizeNat T t d).image
      (fun q ↦ s + t + d * q) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    let a := (x - s) / d
    let b := (y - t) / d
    have ha : a ∈ normalizeNat S s d := mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hb : b ∈ normalizeNat T t d := mem_normalizeNat.mpr ⟨y, hy, rfl⟩
    apply mem_image.mpr
    refine ⟨a + b, Finset.add_mem_add ha hb, ?_⟩
    have hdx := Nat.mul_div_cancel' (hSdiv x hx)
    have hdy := Nat.mul_div_cancel' (hTdiv y hy)
    have hsx := hSmin x hx
    have hty := hTmin y hy
    have hxa : x = s + d * a := by dsimp [a]; omega
    have hyb : y = t + d * b := by dsimp [b]; omega
    change s + t + d * (a + b) = x + y
    rw [hxa, hyb]
    ring
  · intro hz
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hq
    obtain ⟨x, hx, hxa⟩ := (normalizeNat_spec hd hSmin hSdiv).mp ha
    obtain ⟨y, hy, hyb⟩ := (normalizeNat_spec hd hTmin hTdiv).mp hb
    apply mem_add.mpr
    refine ⟨x, hx, y, hy, ?_⟩
    rw [hxa, hyb]
    ring

lemma card_sumset_eq_card_normalized {S T : Finset ℕ} {s t d : ℕ}
    (hd : 0 < d)
    (hSmin : ∀ x ∈ S, s ≤ x) (hTmin : ∀ x ∈ T, t ≤ x)
    (hSdiv : ∀ x ∈ S, d ∣ x - s) (hTdiv : ∀ x ∈ T, d ∣ x - t) :
    (S + T).card = (normalizeNat S s d + normalizeNat T t d).card := by
  rw [sumset_eq_image_normalized hd hSmin hTmin hSdiv hTdiv,
    card_image_iff.mpr]
  intro x hx y hy hxy
  change s + t + d * x = s + t + d * y at hxy
  have hmul : d * x = d * y := Nat.add_left_cancel hxy
  exact Nat.eq_of_mul_eq_mul_left hd hmul

/-- The local arithmetic progression notation used by the final additive
alternative. -/
def natAP (a d len : ℕ) : Finset ℕ :=
  (range len).image fun j ↦ a + d * j

@[simp] lemma mem_natAP {a d len x : ℕ} :
    x ∈ natAP a d len ↔ ∃ j < len, a + d * j = x := by
  simp [natAP]

def InOneResidue (U : Finset ℕ) (d : ℕ) : Prop :=
  ∃ r : ZMod d, ∀ x ∈ U, (x : ZMod d) = r

/-- The strict additive alternative before symmetrizing the two summands,
assuming the first has no larger diameter than the second. -/
theorem growth_or_long_AP_of_diameter_le {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hdiam : S.max' hS - S.min' hS ≤ T.max' hT - T.min' hT) :
    S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨
      ∃ a d : ℕ, 0 < d ∧
        natAP a d (S.card + T.card - 1) ⊆ S + T ∧
        InOneResidue (S + T) d := by
  let s := S.min' hS
  let t := T.min' hT
  let sM := S.max' hS
  let tM := T.max' hT
  let u := sM - s
  let v := tM - t
  have hsS : s ∈ S := S.min'_mem hS
  have htT : t ∈ T := T.min'_mem hT
  have hsMS : sM ∈ S := S.max'_mem hS
  have htMT : tM ∈ T := T.max'_mem hT
  have hSmin : ∀ x ∈ S, s ≤ x := fun x hx ↦ S.min'_le x hx
  have hTmin : ∀ x ∈ T, t ≤ x := fun x hx ↦ T.min'_le x hx
  have hSmax : ∀ x ∈ S, x ≤ sM := fun x hx ↦ S.le_max' x hx
  have hTmax : ∀ x ∈ T, x ≤ tM := fun x hx ↦ T.le_max' x hx
  have huv : u ≤ v := by simpa [u, v, s, t, sM, tM] using hdiam
  by_cases hv0 : v = 0
  · have hu0 : u = 0 := by omega
    have hScard : S.card = 1 := by
      have hSeq : S = {s} := by
        ext x
        constructor
        · intro hx
          have := hSmin x hx
          have := hSmax x hx
          have hMs : sM = s := by dsimp [u] at hu0; omega
          simp only [mem_singleton]
          omega
        · intro hx
          have hxs : x = s := by simpa using hx
          simpa [hxs] using hsS
      simp [hSeq]
    have hTcard : T.card = 1 := by
      have hTeq : T = {t} := by
        ext x
        constructor
        · intro hx
          have := hTmin x hx
          have := hTmax x hx
          have hMt : tM = t := by dsimp [v] at hv0; omega
          simp only [mem_singleton]
          omega
        · intro hx
          have hxt : x = t := by simpa using hx
          simpa [hxt] using htT
      simp [hTeq]
    left
    have hsumne : (S + T).Nonempty := Finset.add_nonempty.mpr ⟨hS, hT⟩
    have : 0 < (S + T).card := card_pos.mpr hsumne
    omega
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
    let S₁ := normalizeNat S s 1
    let T₁ := normalizeNat T t 1
    let W := S₁ ∪ T₁
    let d := W.gcd (fun n : ℕ ↦ n)
    have huS₁ : u ∈ S₁ := by
      have := top_mem_normalizeNat (m := s) (d := 1) hsMS
      simpa [S₁, u, sM, s] using this
    have hvT₁ : v ∈ T₁ := by
      have := top_mem_normalizeNat (m := t) (d := 1) htMT
      simpa [T₁, v, tM, t] using this
    have hvW : v ∈ W := mem_union_right S₁ hvT₁
    have hdne : d ≠ 0 := by
      intro hd0
      have hz := (Finset.gcd_eq_zero_iff.mp hd0) v hvW
      exact hv0 hz
    have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
    have hSdiv : ∀ x ∈ S, d ∣ x - s := by
      intro x hx
      apply Finset.gcd_dvd
      apply mem_union_left T₁
      apply mem_normalizeNat.mpr
      exact ⟨x, hx, by simp⟩
    have hTdiv : ∀ x ∈ T, d ∣ x - t := by
      intro x hx
      apply Finset.gcd_dvd
      apply mem_union_right S₁
      apply mem_normalizeNat.mpr
      exact ⟨x, hx, by simp⟩
    have hdv : d ∣ v := by
      exact Finset.gcd_dvd hvW
    have hdvle : d ≤ v := Nat.le_of_dvd hvpos hdv
    have hvqpos : 0 < v / d := Nat.div_pos hdvle hdpos
    let A := normalizeNat S s d
    let B := normalizeNat T t d
    have hAint : A ⊆ Icc 0 (u / d) := by
      apply normalizeNat_subset_Icc
      intro x hx
      exact mem_Icc.mpr ⟨hSmin x hx, hSmax x hx⟩
    have hBint : B ⊆ Icc 0 (v / d) := by
      apply normalizeNat_subset_Icc
      intro x hx
      exact mem_Icc.mpr ⟨hTmin x hx, hTmax x hx⟩
    have hAzero : 0 ∈ A := zero_mem_normalizeNat hsS
    have hBzero : 0 ∈ B := zero_mem_normalizeNat htT
    have hAtop : u / d ∈ A := by
      have := top_mem_normalizeNat (m := s) (d := d) hsMS
      simpa [A, u, sM, s] using this
    have hBtop : v / d ∈ B := by
      have := top_mem_normalizeNat (m := t) (d := d) htMT
      simpa [B, v, tM, t] using this
    have hqorder : u / d ≤ v / d := Nat.div_le_div_right huv
    have hABW : A ∪ B = W.image (fun z ↦ z / d) := by
      ext q
      simp only [A, B, W, S₁, T₁, normalizeNat, mem_union, mem_image]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨x - s, Or.inl ⟨x, hx, by simp⟩, rfl⟩
        · exact ⟨y - t, Or.inr ⟨y, hy, by simp⟩, rfl⟩
      · rintro ⟨z, (⟨x, hx, hxz⟩ | ⟨y, hy, hyz⟩), rfl⟩
        · left
          refine ⟨x, hx, ?_⟩
          simpa using congrArg (fun n ↦ n / d) hxz
        · right
          refine ⟨y, hy, ?_⟩
          simpa using congrArg (fun n ↦ n / d) hyz
    have hWgcd : W.gcd (fun z ↦ z / d) = 1 := by
      exact Finset.gcd_div_id_eq_one hvW hv0
    have hABgcdNat : (A ∪ B).gcd (fun n : ℕ ↦ n) = 1 := by
      rw [hABW, Finset.gcd_image]
      change W.gcd (fun z ↦ z / d) = 1
      exact hWgcd
    have hABgcdInt : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1 := by
      rw [nat_int_finset_gcd, hABgcdNat]
      norm_num
    have hAcard : A.card = S.card := card_normalizeNat hdpos hSmin hSdiv
    have hBcard : B.card = T.card := card_normalizeNat hdpos hTmin hTdiv
    have hsumcard : (S + T).card = (A + B).card :=
      card_sumset_eq_card_normalized hdpos hSmin hTmin hSdiv hTdiv
    have halt := normalized_growth_or_long_interval hAint hBint hqorder hvqpos
      hAzero hAtop hBzero hBtop hABgcdInt
    rcases halt with hgrowth | ⟨lo, hlo⟩
    · left
      simpa only [hAcard, hBcard, ← hsumcard] using hgrowth
    · right
      let a := s + t + d * lo
      refine ⟨a, d, hdpos, ?_, ?_⟩
      · intro z hz
        obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
        have hcardS : 0 < S.card := card_pos.mpr hS
        have hcardT : 0 < T.card := card_pos.mpr hT
        have hq : lo + j ∈ A + B := by
          apply hlo
          apply mem_Icc.mpr
          constructor
          · omega
          · rw [hAcard, hBcard]
            omega
        rw [sumset_eq_image_normalized hdpos hSmin hTmin hSdiv hTdiv]
        apply mem_image.mpr
        refine ⟨lo + j, hq, ?_⟩
        dsimp [a]
        ring
      · refine ⟨((s + t : ℕ) : ZMod d), ?_⟩
        intro z hz
        rw [sumset_eq_image_normalized hdpos hSmin hTmin hSdiv hTdiv] at hz
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
        push_cast
        simp

/-- Strict Bardaji--Grynkiewicz alternative for arbitrary nonempty natural
finsets. -/
theorem growth_or_long_AP {S T : Finset ℕ} (hS : S.Nonempty) (hT : T.Nonempty) :
    S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨
      ∃ a d : ℕ, 0 < d ∧
        natAP a d (S.card + T.card - 1) ⊆ S + T ∧
        InOneResidue (S + T) d := by
  rcases le_total (S.max' hS - S.min' hS) (T.max' hT - T.min' hT) with hle | hle
  · exact growth_or_long_AP_of_diameter_le hS hT hle
  · have h := growth_or_long_AP_of_diameter_le hT hS hle
    simpa only [add_comm (a := T.card) S.card, min_comm, add_comm (a := T) S] using h
end Erdos13Additive
