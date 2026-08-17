/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.CentralSpan
import ErdosProblems.Erdos874.LayerOrdering
import ErdosProblems.Erdos874.RoughUpper
import ErdosProblems.Erdos874.Thresholds
import ErdosProblems.Erdos874.Tail
import ErdosProblems.Erdos874.LocalDensity
import ErdosProblems.Erdos874.DensityEndgame

/-!
# Extraction of the central block for Erdős Problem 874

This file carries the output of the Deshouillers--Freiman structure and
central-span arguments to the concrete ordered block used by the density
endgame.  In particular, it fixes a total extension of the increasing
enumeration of a finite set and proves that a common difference divisor gives
the quantitative `QSeparated` property.
-/

open Filter
open scoped BigOperators Pointwise Topology

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The canonical total increasing enumeration -/

/-- The increasing enumeration of `A`, extended by zero past `A.card`. -/
def orderedEntry (A : Finset ℤ) (i : ℕ) : ℤ :=
  if hi : i < A.card then A.orderEmbOfFin rfl ⟨i, hi⟩ else 0

@[simp] theorem orderedEntry_of_lt (A : Finset ℤ) {i : ℕ}
    (hi : i < A.card) :
    orderedEntry A i = A.orderEmbOfFin rfl ⟨i, hi⟩ := by
  simp [orderedEntry, hi]

theorem orderedEntry_mem (A : Finset ℤ) {i : ℕ} (hi : i < A.card) :
    orderedEntry A i ∈ A := by
  rw [orderedEntry_of_lt A hi]
  exact A.orderEmbOfFin_mem rfl _

theorem orderedEntry_strict {A : Finset ℤ} {i j : ℕ}
    (hij : i < j) (hj : j < A.card) :
    orderedEntry A i < orderedEntry A j := by
  have hi : i < A.card := hij.trans hj
  rw [orderedEntry_of_lt A hi, orderedEntry_of_lt A hj]
  exact (A.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)

/-- The first `A.card` values of `orderedEntry` enumerate `A` exactly. -/
theorem image_orderedEntry_range (A : Finset ℤ) :
    Finset.image (orderedEntry A) (Finset.range A.card) = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact orderedEntry_mem A (Finset.mem_range.mp hi)
  · intro hx
    have hxmap : x ∈
        Finset.map (A.orderEmbOfFin rfl).toEmbedding Finset.univ := by
      rw [A.map_orderEmbOfFin_univ rfl]
      exact hx
    obtain ⟨i, -, hix⟩ := Finset.mem_map.mp hxmap
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_range.mpr i.isLt, ?_⟩
    rw [orderedEntry_of_lt A i.isLt]
    exact hix

/-- All entries of a bounded set lie below the ambient endpoint. -/
theorem orderedEntry_le_ambient {N : ℕ} {A : Finset ℤ}
    (hA : IsBoundedAdmissible N A) {i : ℕ} (hi : i < A.card) :
    orderedEntry A i ≤ (N : ℤ) := by
  exact (mem_ambient.mp (hA.1 (orderedEntry_mem A hi))).2

/-- The first `n` values of the canonical enumeration are distinct. -/
theorem card_image_orderedEntry_range {A : Finset ℤ} {n : ℕ}
    (hn : n ≤ A.card) :
    (Finset.image (orderedEntry A) (Finset.range n)).card = n := by
  have hinj : Set.InjOn (orderedEntry A) (Finset.range n) := by
    intro i hi j hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hjA : j < A.card := (Finset.mem_range.mp hj).trans_le hn
      exact (orderedEntry_strict hlt hjA).ne hij
    · have hiA : i < A.card := (Finset.mem_range.mp hi).trans_le hn
      exact (orderedEntry_strict hgt hiA).ne hij.symm
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Every member of `A` has a unique rank in its canonical enumeration. -/
theorem exists_orderedEntry_eq_of_mem {A : Finset ℤ} {x : ℤ}
    (hx : x ∈ A) :
    ∃ i < A.card, orderedEntry A i = x := by
  have hx' : x ∈ Finset.image (orderedEntry A) (Finset.range A.card) := by
    simpa [image_orderedEntry_range A] using hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx'
  exact ⟨i, Finset.mem_range.mp hi, hix⟩

/-- Passing to a subset can only move a fixed zero-based rank to the right. -/
theorem orderedEntry_ambient_le_subset
    {A B : Finset ℤ} (hBA : B ⊆ A) {i : ℕ} (hi : i < B.card) :
    orderedEntry A i ≤ orderedEntry B i := by
  have hcard : B.card ≤ A.card := Finset.card_le_card hBA
  have hiA : i < A.card := hi.trans_le hcard
  by_contra hnot
  have hlt : orderedEntry B i < orderedEntry A i := lt_of_not_ge hnot
  let S : Finset ℤ :=
    Finset.image (orderedEntry B) (Finset.range (i + 1))
  let T : Finset ℤ :=
    Finset.image (orderedEntry A) (Finset.range i)
  have hST : S ⊆ T := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjle : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    have hjB : j < B.card := hjle.trans_lt hi
    have hxA : orderedEntry B j ∈ A := hBA (orderedEntry_mem B hjB)
    obtain ⟨r, hrA, hre⟩ := exists_orderedEntry_eq_of_mem hxA
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_range.mpr ?_, hre⟩
    by_contra hri
    have hir : i ≤ r := le_of_not_gt hri
    have hmono : orderedEntry A i ≤ orderedEntry A r := by
      rcases eq_or_lt_of_le hir with rfl | hir'
      · exact le_rfl
      · exact (orderedEntry_strict hir' hrA).le
    have hBjle : orderedEntry B j ≤ orderedEntry B i := by
      rcases eq_or_lt_of_le hjle with rfl | hji
      · exact le_rfl
      · exact (orderedEntry_strict hji hi).le
    rw [hre] at hmono
    omega
  have hScard : S.card = i + 1 := by
    exact card_image_orderedEntry_range (by omega)
  have hTcard : T.card = i := card_image_orderedEntry_range hiA.le
  have := Finset.card_le_card hST
  rw [hScard, hTcard] at this
  omega

/-- If `B ⊆ A`, deleting the complement moves the `i`-th member of `B` by
at most `A.card-B.card` ranks.  This is the precise reinsertion estimate for
the exceptional set. -/
theorem orderedEntry_subset_le_shifted_ambient
    {A B : Finset ℤ} (hBA : B ⊆ A) {i : ℕ} (hi : i < B.card) :
    orderedEntry B i ≤ orderedEntry A (A.card - B.card + i) := by
  have hcard : B.card ≤ A.card := Finset.card_le_card hBA
  let c : ℕ := A.card - B.card
  have hidx : c + i < A.card := by dsimp [c]; omega
  by_contra hnot
  have hlt : orderedEntry A (c + i) < orderedEntry B i := lt_of_not_ge hnot
  let S : Finset ℤ :=
    Finset.image (orderedEntry A) (Finset.range (c + i + 1))
  let T : Finset ℤ :=
    (A \ B) ∪ Finset.image (orderedEntry B) (Finset.range i)
  have hST : S ⊆ T := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjle : j ≤ c + i := by
      have := Finset.mem_range.mp hj
      omega
    have hjA : j < A.card := hjle.trans_lt hidx
    by_cases hxB : orderedEntry A j ∈ B
    · apply Finset.mem_union_right (A \ B)
      obtain ⟨r, hrB, hre⟩ := exists_orderedEntry_eq_of_mem hxB
      apply Finset.mem_image.mpr
      refine ⟨r, Finset.mem_range.mpr ?_, hre⟩
      by_contra hri
      have hir : i ≤ r := le_of_not_gt hri
      have hmono : orderedEntry B i ≤ orderedEntry B r := by
        rcases eq_or_lt_of_le hir with rfl | hir'
        · exact le_rfl
        · exact (orderedEntry_strict hir' hrB).le
      have hAjle : orderedEntry A j ≤ orderedEntry A (c + i) := by
        rcases eq_or_lt_of_le hjle with rfl | hj'
        · exact le_rfl
        · exact (orderedEntry_strict hj' hidx).le
      rw [hre] at hmono
      omega
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨orderedEntry_mem A hjA, hxB⟩
  have hScard : S.card = c + i + 1 :=
    card_image_orderedEntry_range (by omega)
  have hdiffcard : (A \ B).card = c := by
    dsimp [c]
    simp [Finset.card_sdiff, Finset.inter_eq_left.mpr hBA]
  have hinitcard :
      (Finset.image (orderedEntry B) (Finset.range i)).card = i :=
    card_image_orderedEntry_range hi.le
  have hTcard : T.card ≤ c + i := by
    calc
      T.card ≤ (A \ B).card +
          (Finset.image (orderedEntry B) (Finset.range i)).card :=
        by
          simpa [T] using (Finset.card_union_le (A \ B)
            (Finset.image (orderedEntry B) (Finset.range i)))
      _ = c + i := by rw [hdiffcard, hinitcard]
  have hle := (Finset.card_le_card hST).trans hTcard
  rw [hScard] at hle
  omega

/-! ## From one residue class to quantitative separation -/

/-- Consecutive members of a finite integer set in one residue class modulo
the positive integer `q` differ by at least `q`. -/
theorem orderedEntry_add_step_le
    {A : Finset ℤ} {q i : ℕ} (hq : 0 < q)
    (hdiv : IsDifferenceDivisor q A) (hi : i + 1 < A.card) :
    orderedEntry A i + (q : ℤ) ≤ orderedEntry A (i + 1) := by
  have hi0 : i < A.card := by omega
  have hx := orderedEntry_mem A hi0
  have hy := orderedEntry_mem A hi
  obtain ⟨z, hz⟩ := hdiv (orderedEntry A (i + 1)) hy
    (orderedEntry A i) hx
  have hlt : orderedEntry A i < orderedEntry A (i + 1) :=
    orderedEntry_strict (by omega) hi
  have hqz : orderedEntry A (i + 1) - orderedEntry A i = (q : ℤ) * z := by
    simpa [mul_comm] using hz
  have hzpos : 0 < z := by
    have hqzpos : 0 < (q : ℤ) * z := by linarith
    have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
    nlinarith
  have hqcast : (0 : ℤ) < q := by exact_mod_cast hq
  nlinarith

/-- The canonical enumeration of a set contained in one `q`-residue class is
`q`-separated. -/
theorem qSeparated_orderedEntry
    {A : Finset ℤ} {q : ℕ} (hq : 0 < q)
    (hdiv : IsDifferenceDivisor q A) :
    QSeparated (orderedEntry A) A.card q := by
  apply qSeparated_of_adjacent
  intro i hi
  exact orderedEntry_add_step_le hq hdiv hi

/-- A positive common step across all of a bounded set is controlled by the
ambient interval: the `A.card - 1` consecutive gaps already occupy that many
copies of the step.  This is the crude step estimate used before the sharper
central quadratic estimate becomes available. -/
theorem common_step_mul_card_sub_one_lt_ambient
    {N : ℕ} {A : Finset ℤ} {q : ℕ}
    (hA : IsBoundedAdmissible N A) (hq : 0 < q)
    (hdiv : IsDifferenceDivisor q A) (hcard : 2 ≤ A.card) :
    q * (A.card - 1) < N := by
  have hsep := qSeparated_orderedEntry hq hdiv
  have hgap := hsep (i := 0) (j := A.card - 1) (by omega) (by omega)
  have hfirst := mem_ambient.mp
    (hA.1 (orderedEntry_mem A (by omega : 0 < A.card)))
  have hlast := mem_ambient.mp
    (hA.1 (orderedEntry_mem A (by omega : A.card - 1 < A.card)))
  have hgap' :
      orderedEntry A 0 + ((A.card - 1 : ℕ) : ℤ) * (q : ℤ) ≤
        orderedEntry A (A.card - 1) := by
    simpa [mul_comm] using hgap
  have hnatZ : ((q * (A.card - 1) : ℕ) : ℤ) < (N : ℤ) := by
    push_cast
    nlinarith [hfirst.1, hlast.2, hgap']
  exact_mod_cast hnatZ

/-! ## Absorbing the exceptional residue classes -/

/-- Every fixed-cardinality sum of a set contained in one residue class has
the expected residue. -/
private theorem restrictedSumset_modEq_mul
    {B : Finset ℤ} {q r : ℕ} {b z : ℤ}
    (hdiv : IsDifferenceDivisor q B) (hb : b ∈ B)
    (hz : z ∈ restrictedSumset r B) :
    Int.ModEq (q : ℤ) z ((r : ℤ) * b) := by
  obtain ⟨R, hRB, hRcard, hRsum⟩ := mem_restrictedSumset.mp hz
  have hsum := Int.ModEq.sum (s := R) (f := fun x : ℤ ↦ x)
    (g := fun _x : ℤ ↦ b) (fun x hx ↦ by
      rw [Int.modEq_iff_dvd]
      rw [← neg_sub]
      exact dvd_neg.mpr (hdiv x (hRB hx) b hb))
  rw [← hRsum]
  simpa [Finset.sum_const, hRcard, nsmul_eq_mul] using hsum

/-- The elementary polynomial identity in the residue-absorption count.
The summand is the sum of the two sharp restricted-sum lower bounds after
their constant terms have been included. -/
private theorem three_mul_sum_alignment_weight_int (b : ℤ) (n : ℕ) :
    3 * ∑ r ∈ Finset.range n,
        (((r : ℤ) + 1) * (b - (r : ℤ) - 1) +
          (r : ℤ) * (b - (r : ℤ)) + 2) =
      (n : ℤ) * (3 * b * (n : ℤ) - 2 * (n : ℤ) ^ 2 + 5) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- Natural-number form of the exact weight identity used in the DF99
exceptional-residue argument. -/
private theorem three_mul_sum_alignment_weight (b : ℕ) :
    3 * ∑ r ∈ Finset.range b,
        ((r + 1) * (b - (r + 1)) + r * (b - r) + 2) =
      b * (b * b + 5) := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  calc
    3 * ∑ r ∈ Finset.range b,
          ((↑r + 1) * ↑(b - (r + 1)) + ↑r * ↑(b - r) + 2) =
        3 * ∑ r ∈ Finset.range b,
          ((↑r + 1) * ((b : ℤ) - ↑r - 1) +
            ↑r * ((b : ℤ) - ↑r) + 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      have hrb : r < b := Finset.mem_range.mp hr
      rw [Nat.cast_sub (by omega : r + 1 ≤ b), Nat.cast_sub hrb.le]
      push_cast
      ring
    _ = (b : ℤ) *
          (3 * (b : ℤ) * (b : ℤ) - 2 * (b : ℤ) ^ 2 + 5) :=
      three_mul_sum_alignment_weight_int (b : ℤ) b
    _ = (b : ℤ) * ((b : ℤ) * (b : ℤ) + 5) := by ring

/-- If one element `a` is outside the residue class occupied by `B`, the
two families

`s^B` and `a + (s-1)^B`

are disjoint subsets of `s^A`.  This is the finite heart of the first
paragraph of DF99, Theorem 3. -/
theorem two_restricted_layers_card_le_of_not_modEq
    {A B : Finset ℤ} {q s : ℕ} {a b : ℤ}
    (hBA : B ⊆ A) (ha : a ∈ A) (hb : b ∈ B)
    (hq : 0 < q) (hdiv : IsDifferenceDivisor q B)
    (hamis : ¬ Int.ModEq (q : ℤ) a b)
    (hs : 1 ≤ s) (hsB : s ≤ B.card) :
    (restrictedSumset s B).card +
        (restrictedSumset (s - 1) B).card ≤
      (restrictedSumset s A).card := by
  let X : Finset ℤ := restrictedSumset s B
  let Y : Finset ℤ := translateFinset a (restrictedSumset (s - 1) B)
  have haB : a ∉ B := by
    intro haB
    apply hamis
    rw [Int.modEq_iff_dvd, ← neg_sub]
    exact dvd_neg.mpr (hdiv a haB b hb)
  have hsingle : {a} ⊆ A \ B := by
    intro x hx
    have hxa : x = a := Finset.mem_singleton.mp hx
    subst x
    exact Finset.mem_sdiff.mpr ⟨ha, haB⟩
  have hXsub : X ⊆ restrictedSumset s A :=
    restrictedSumset_mono hBA
  have hYsub : Y ⊆ restrictedSumset s A := by
    intro z hz
    have hz' : z - a ∈ restrictedSumset (s - 1) B :=
      mem_translateFinset.mp hz
    have hadd := add_sum_mem_restrictedSumset_of_subset_sdiff
      hBA hsingle hz'
    have hcard : s - 1 + ({a} : Finset ℤ).card = s := by simp; omega
    rw [hcard] at hadd
    simpa using hadd
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    have hzXmod := restrictedSumset_modEq_mul hdiv hb hzX
    have hzY' : z - a ∈ restrictedSumset (s - 1) B :=
      mem_translateFinset.mp hzY
    have hzYmod := restrictedSumset_modEq_mul hdiv hb hzY'
    have hza : Int.ModEq (q : ℤ) z
        (a + ((s - 1 : ℕ) : ℤ) * b) := by
      have := (Int.ModEq.refl a).add hzYmod
      convert this using 1 <;> ring
    have hend : Int.ModEq (q : ℤ) ((s : ℤ) * b)
        (a + ((s - 1 : ℕ) : ℤ) * b) := hzXmod.symm.trans hza
    apply hamis
    have hsCast : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by
      rw [Nat.cast_sub hs]
      norm_num
    rw [hsCast] at hend
    have h := hend.symm.sub (Int.ModEq.refl (((s : ℤ) - 1) * b))
    convert h using 1 <;> ring
  calc
    X.card + (restrictedSumset (s - 1) B).card = X.card + Y.card := by
      rw [card_translateFinset]
    _ = (X ∪ Y).card := (Finset.card_union_of_disjoint hXY).symm
    _ ≤ (restrictedSumset s A).card :=
      Finset.card_le_card (Finset.union_subset hXsub hYsub)

/-- Summing the preceding disjoint-pair estimate over all positive layers
gives the exact cubic obstruction.  Notice that this statement has no
asymptotic notation and does not use maximality of `A`. -/
theorem cubic_bound_of_not_modEq
    {N q : ℕ} {A B : Finset ℤ} {a b : ℤ}
    (hA : IsBoundedAdmissible N A) (hBA : B ⊆ A)
    (ha : a ∈ A) (hb : b ∈ B) (hq : 0 < q)
    (hdiv : IsDifferenceDivisor q B)
    (hamis : ¬ Int.ModEq (q : ℤ) a b) :
    B.card * (B.card * B.card + 5) ≤ 3 * (B.card * N) := by
  let w : ℕ → ℕ := fun r ↦
    (r + 1) * (B.card - (r + 1)) +
      r * (B.card - r) + 2
  have hlayer : ∀ r ∈ Finset.range B.card,
      w r ≤ (restrictedSumset (r + 1) A).card := by
    intro r hr
    have hrB : r < B.card := Finset.mem_range.mp hr
    have hpair := two_restricted_layers_card_le_of_not_modEq
      hBA ha hb hq hdiv hamis (s := r + 1) (by omega) (by omega)
    have hlo₁ := card_restrictedSumset_lower_bound B (r + 1) (by omega)
    have hlo₀ := card_restrictedSumset_lower_bound B r (by omega)
    dsimp [w]
    have hsub : r + 1 - 1 = r := by omega
    rw [hsub] at hpair
    omega
  have hsumLayers :
      ∑ r ∈ Finset.range B.card, (restrictedSumset (r + 1) A).card ≤
        B.card * N := by
    have hcount := sum_card_restrictedSumset_Icc_le
      (A := A) (lo := 1) (hi := B.card) hA (by omega)
    have hrange : Finset.Icc 1 B.card =
        (Finset.range B.card).image (fun r ↦ r + 1) := by
      ext s
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hs
        exact ⟨s - 1, by omega, by omega⟩
      · rintro ⟨r, hr, rfl⟩
        omega
    rw [hrange, Finset.sum_image] at hcount
    · exact hcount
    · intro r hr t ht heq
      exact Nat.add_right_cancel heq
  have hsum : ∑ r ∈ Finset.range B.card, w r ≤ B.card * N :=
    (Finset.sum_le_sum hlayer).trans hsumLayers
  have hweight := three_mul_sum_alignment_weight B.card
  dsimp [w] at hsum
  calc
    B.card * (B.card * B.card + 5) =
        3 * ∑ r ∈ Finset.range B.card,
          ((r + 1) * (B.card - (r + 1)) +
            r * (B.card - r) + 2) := hweight.symm
    _ ≤ 3 * (B.card * N) := Nat.mul_le_mul_left 3 hsum

/-- **Exceptional-residue absorption.**  If the regular part already has
square cardinality exceeding `3N-5`, admissibility forces every exceptional
element into its residue class.  This is the exact finite substitute for the
paper's `b=(2+o(1))sqrt N` contradiction. -/
theorem isDifferenceDivisor_of_large_regular_part
    {N q : ℕ} {A B : Finset ℤ}
    (hA : IsBoundedAdmissible N A) (hBA : B ⊆ A)
    (hq : 0 < q) (hdiv : IsDifferenceDivisor q B)
    (hB : B.Nonempty) (hlarge : 3 * N < B.card * B.card + 5) :
    IsDifferenceDivisor q A := by
  have hbpos : 0 < B.card := Finset.card_pos.mpr hB
  obtain ⟨b, hb⟩ := hB
  have hall : ∀ a ∈ A, Int.ModEq (q : ℤ) a b := by
    intro a ha
    by_contra hamis
    have hcubic := cubic_bound_of_not_modEq hA hBA ha hb hq hdiv hamis
    have hstrict : 3 * (B.card * N) <
        B.card * (B.card * B.card + 5) := by
      calc
        3 * (B.card * N) = B.card * (3 * N) := by ring
        _ < B.card * (B.card * B.card + 5) :=
          Nat.mul_lt_mul_of_pos_left hlarge hbpos
    omega
  intro x hx y hy
  have hxy := (hall x hx).trans (hall y hy).symm
  rw [← neg_sub]
  exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hxy)

/-- The `10^5 N^(5/12)` exceptional set is eventually smaller than one
tenth of the square-root scale. -/
theorem eventually_exceptional_card_le_tenth_sqrt :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ) (S : LargeSetStructure N A),
      (S.exceptional.card : ℝ) ≤ Real.sqrt N / 10 := by
  have hsmall := eventually_const_mul_rpow_five_twelfths_le_sqrt
    (1000000 : ℝ) (by positivity)
  filter_upwards [hsmall] with N hN
  intro A S
  have hC := S.exceptional_card_le
  norm_num at hC hN ⊢
  linarith

/-- Under the `1.96 sqrt N` structure threshold, the regular part
eventually has square cardinality greater than `3N`.  This is the numerical
input needed by `isDifferenceDivisor_of_large_regular_part`. -/
theorem eventually_large_regular_square :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ) (S : LargeSetStructure N A),
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      3 * N < (A \ S.exceptional).card ^ 2 + 5 := by
  filter_upwards [eventually_exceptional_card_le_tenth_sqrt,
      eventually_ge_atTop 1] with N hCsmall hN
  intro A S hlarge
  have hcard :
      A.card = S.exceptional.card + (A \ S.exceptional).card := by
    rw [← Finset.card_union_of_disjoint S.exceptional_disjoint_regular,
      S.exceptional_union_regular]
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hreg : (93 / 50 : ℝ) * Real.sqrt N <
      ((A \ S.exceptional).card : ℝ) := by
    have hC := hCsmall A S
    rw [hcard] at hlarge
    push_cast at hlarge
    nlinarith
  have hregnonneg : (0 : ℝ) ≤ (A \ S.exceptional).card := by positivity
  have hbase : (0 : ℝ) ≤ (93 / 50 : ℝ) * Real.sqrt N := by positivity
  have hsqcomp := mul_self_lt_mul_self hbase hreg
  have hsq : (3 : ℝ) * N <
      ((A \ S.exceptional).card : ℝ) ^ 2 := by
    nlinarith
  have hnat : 3 * N < (A \ S.exceptional).card ^ 2 := by
    exact_mod_cast hsq
  omega

/-- For all sufficiently large structured sets, the structural step is not
merely a divisor on the regular part: it is the intrinsic gcd of all
differences of `A`. -/
theorem eventually_structure_isDifferenceGCD :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ) (S : LargeSetStructure N A),
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) →
      IsDifferenceGCD S.step A := by
  filter_upwards [eventually_large_regular_square,
      eventually_exceptional_card_le_tenth_sqrt,
      eventually_ge_atTop 1] with N hsquare hCsmall hN
  intro A S hA hlarge
  let B : Finset ℤ := A \ S.exceptional
  have hsquare' : 3 * N < B.card ^ 2 + 5 := by
    simpa [B] using hsquare A S hlarge
  have hBne : B.Nonempty := by
    by_contra hzero
    have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    have hcard : A.card = S.exceptional.card + B.card := by
      rw [← Finset.card_union_of_disjoint S.exceptional_disjoint_regular,
        S.exceptional_union_regular]
    have hC := hCsmall A S
    rw [hBempty] at hcard
    simp only [Finset.card_empty, add_zero] at hcard
    rw [hcard] at hlarge
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
    nlinarith
  have hdivB : IsDifferenceDivisor S.step B :=
    S.regular_contained.isDifferenceDivisor
  have hdivA : IsDifferenceDivisor S.step A :=
    isDifferenceDivisor_of_large_regular_part hA S.regular_subset
      S.step_pos hdivB hBne (by simpa [B, pow_two] using hsquare')
  have hlongTwo : 2 ≤ S.longLength := by
    have hp : (3 : ℝ) ≤ (S.longLength : ℝ) := by
      calc
        (3 : ℝ) ≤ 3 * (N : ℝ) ^ ((5 : ℝ) / 6) := by
          have : (1 : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 6) :=
            Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
          nlinarith
        _ ≤ S.longLength := S.longLength_ge
    have hthree : 3 ≤ S.longLength := by exact_mod_cast hp
    omega
  exact isDifferenceGCD_of_long_progression S.exceptional_subset
    S.layer_pos S.step_pos hlongTwo hdivA S.long_progression

/-! ## Transferring the regular central pair through the exceptional ranks -/

/-- Extend the increasing enumeration of a nonempty `q`-progression by
continuing with exact `q`-steps after its last member.  The extension is used
only because `central_pair_bound_simplified` has a total gap hypothesis; all
indices occurring in its endpoint sums remain inside the original set. -/
def stepExtendedEntry (B : Finset ℤ) (q i : ℕ) : ℤ :=
  if hi : i < B.card then roughEntry B i
  else roughEntry B (B.card - 1) + (q : ℤ) * (i - B.card + 1)

@[simp] theorem stepExtendedEntry_of_lt {B : Finset ℤ} {q i : ℕ}
    (hi : i < B.card) : stepExtendedEntry B q i = roughEntry B i := by
  simp [stepExtendedEntry, hi]

/-- The total extension remains `q`-separated. -/
theorem stepExtendedEntry_gap
    {B : Finset ℤ} {start : ℤ} {q M : ℕ}
    (hB : B.Nonempty) (hcontained : ContainedInAP B start q M) :
    ∀ i j : ℕ, i ≤ j →
      stepExtendedEntry B q i + (j - i : ℕ) * (q : ℤ) ≤
        stepExtendedEntry B q j := by
  intro i j hij
  have hBcard : 0 < B.card := Finset.card_pos.mpr hB
  by_cases hj : j < B.card
  · have hi : i < B.card := hij.trans_lt hj
    rw [stepExtendedEntry_of_lt hi, stepExtendedEntry_of_lt hj]
    have hgap := roughEntry_add_step_mul_le hcontained (S := B.card)
      (le_refl _) (i := i) (d := j - i) (by omega)
    have hidx : i + (j - i) = j := by omega
    rw [hidx] at hgap
    simpa [mul_comm] using hgap
  · have hjout : B.card ≤ j := le_of_not_gt hj
    simp only [stepExtendedEntry, dif_neg hj]
    by_cases hi : i < B.card
    · rw [dif_pos hi]
      have hlast := roughEntry_add_step_mul_le hcontained (S := B.card)
        (le_refl _) (i := i) (d := B.card - 1 - i) (by omega)
      have hidx : i + (B.card - 1 - i) = B.card - 1 := by omega
      rw [hidx] at hlast
      have hjiCast : ((j - i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by
        rw [Nat.cast_sub hij]
      have hlastCast : ((B.card - 1 - i : ℕ) : ℤ) =
          (B.card : ℤ) - 1 - (i : ℤ) := by
        rw [Nat.cast_sub (by omega : i ≤ B.card - 1),
          Nat.cast_sub (by omega : 1 ≤ B.card)]
        push_cast
        ring
      rw [hlastCast] at hlast
      rw [hjiCast]
      nlinarith
    · have hiout : B.card ≤ i := le_of_not_gt hi
      rw [dif_neg hi]
      have hjiCast : ((j - i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by
        rw [Nat.cast_sub hij]
      rw [hjiCast]
      ring_nf
      exact le_rfl

/-- Finite central-span transfer from the regular set `A \ C` to the full
ordered set `A`.  The exceptional-cardinality loss appears only in the rank
`u = |C| + θ + t`; the value gap itself can only shrink. -/
theorem LargeSetStructure.central_pair_after_reinsertion
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A)
    (hA : IsBoundedAdmissible N A)
    (hshortLong : 2 * S.shortLength ≤ S.longLength)
    (hqcard : S.step ≤ (A \ S.exceptional).card)
    {t : ℕ}
    (ht : t < ((A \ S.exceptional).card - S.step) / 2) :
    let B := A \ S.exceptional
    let k := (B.card - S.step) / 2
    let θ := (B.card - S.step) % 2
    let u := S.exceptional.card + θ + t
    (k : ℤ) ^ 2 + 2 * (k : ℤ) * (S.step : ℤ) < (N : ℤ) ∧
      ((t + 1 : ℕ) : ℤ) *
          (orderedEntry A (A.card - u - 1) - orderedEntry A u) <
        (S.step : ℤ) *
          ((N : ℤ) - (k : ℤ) ^ 2 +
            2 * (k : ℤ) * ((t : ℤ) + 1)) := by
  let B : Finset ℤ := A \ S.exceptional
  let k : ℕ := (B.card - S.step) / 2
  let θ : ℕ := (B.card - S.step) % 2
  let u : ℕ := S.exceptional.card + θ + t
  change S.step ≤ B.card at hqcard
  change t < k at ht
  have hBsub : B ⊆ A \ S.exceptional := by simp [B]
  have hBambient : B ⊆ ambient N := S.regular_subset.trans hA.1
  have hBpos : ∀ x ∈ B, 0 < x := by
    intro x hx
    exact (mem_ambient.mp (hBambient hx)).1
  have hBne : B.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hθlt : θ < 2 := Nat.mod_lt _ (by omega)
  have hdecomp : B.card = 2 * k + S.step + θ := by
    have hdiv := Nat.mod_add_div (B.card - S.step) 2
    dsimp [k, θ]
    omega
  have hkpos : 0 < k := Nat.zero_lt_of_lt ht
  have hused : 2 * k + S.step ≤ B.card := by omega
  have hcompare :
      ∑ i ∈ Finset.range k, roughEntry B (k + S.step + i) <
        ∑ i ∈ Finset.range (k + S.step), roughEntry B i :=
    central_layer_ordering_of_long_progression hA.2 S.exceptional_subset
      hBsub hBpos S.layer_pos S.step_pos
      (show 0 < S.longLength by
        have hshortPos : 0 < S.shortLength :=
          (Finset.card_pos.mpr hBne).trans_le S.regular_card_le_shortLength
        omega)
      S.long_progression S.regular_contained hkpos hused hshortLong
  let b : ℕ → ℤ := stepExtendedEntry B S.step
  have hbGap : ∀ i j : ℕ, i ≤ j →
      b i + (j - i : ℕ) * (S.step : ℤ) ≤ b j :=
    stepExtendedEntry_gap hBne S.regular_contained
  have hbUsed : ∀ i < 2 * k + S.step, b i = roughEntry B i := by
    intro i hi
    exact stepExtendedEntry_of_lt (hi.trans_le hused)
  have hcompare' :
      ∑ i ∈ Finset.range k, b (k + S.step + i) <
        ∑ i ∈ Finset.range (k + S.step), b i := by
    convert hcompare using 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hbUsed]
      have hi' := Finset.mem_range.mp hi
      omega
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hbUsed]
      have hi' := Finset.mem_range.mp hi
      omega
  have hlastIndex : 2 * k + S.step - 1 < B.card := by omega
  have hbN : b (2 * k + S.step - 1) ≤ (N : ℤ) := by
    rw [hbUsed _ (by omega)]
    have hm : roughEntry B (2 * k + S.step - 1) ∈ B := by
      rw [roughEntry_eq_orderEmb B hlastIndex]
      exact B.orderEmbOfFin_mem rfl _
    exact (mem_ambient.mp (hBambient hm)).2
  have hquad := central_step_quadratic_bound S.step_pos hkpos hbGap hbN hcompare'
  have hpair := central_pair_bound_simplified S.step_pos ht hbGap hbN hcompare'
  have htB : t < B.card := by omega
  have htopB : 2 * k + S.step - t - 1 < B.card := by omega
  have hAcard : A.card = S.exceptional.card + B.card := by
    dsimp [B]
    rw [← Finset.card_union_of_disjoint S.exceptional_disjoint_regular,
      S.exceptional_union_regular]
  have huIndex : u < A.card := by dsimp [u]; omega
  have htopIndex : A.card - u - 1 < A.card := by omega
  have huLower : roughEntry B t ≤ orderedEntry A u := by
    have h₁ := orderedEntry_subset_le_shifted_ambient S.regular_subset htB
    have h₂ : orderedEntry A (A.card - B.card + t) ≤ orderedEntry A u := by
      have hidx₁ : A.card - B.card + t < A.card := by omega
      rcases Nat.eq_or_lt_of_le (show A.card - B.card + t ≤ u by
        dsimp [u]; omega) with heq | hlt
      · simpa [heq]
      · exact (orderedEntry_strict hlt huIndex).le
    rw [show roughEntry B t = orderedEntry B t by
      simp [roughEntry, orderedEntry, htB]]
    exact h₁.trans h₂
  have htopUpper : orderedEntry A (A.card - u - 1) ≤
      roughEntry B (2 * k + S.step - t - 1) := by
    have hidxEq : A.card - u - 1 = 2 * k + S.step - t - 1 := by
      dsimp [u]
      omega
    rw [hidxEq]
    have h := orderedEntry_ambient_le_subset S.regular_subset htopB
    change orderedEntry A (2 * k + S.step - t - 1) ≤
      orderedEntry B (2 * k + S.step - t - 1) at h
    have heq : roughEntry B (2 * k + S.step - t - 1) =
        orderedEntry B (2 * k + S.step - t - 1) := by
      simp [roughEntry, orderedEntry, htopB]
    rw [heq]
    exact h
  have hgapTransfer :
      orderedEntry A (A.card - u - 1) - orderedEntry A u ≤
        b (2 * k + S.step - t - 1) - b t := by
    rw [hbUsed _ (by omega), hbUsed _ (by omega)]
    omega
  constructor
  · exact hquad
  · have htp : (0 : ℤ) < t + 1 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hgapTransfer htp.le
    exact hscaled.trans_lt hpair

/-! ## Eventual central-window arithmetic -/

/-- The rounded `N^(11/24)` rank used in the central-pair estimate.  A
ceiling (rather than a floor) makes the lower bound on the window literal. -/
def dfCentralWindow (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ ((11 : ℝ) / 24))

theorem dfCentralWindow_cast_ge (N : ℕ) :
    (N : ℝ) ^ ((11 : ℝ) / 24) ≤ (dfCentralWindow N : ℝ) := by
  exact Nat.le_ceil _

theorem dfCentralWindow_cast_lt_add_one (N : ℕ) :
    (dfCentralWindow N : ℝ) <
      (N : ℝ) ^ ((11 : ℝ) / 24) + 1 := by
  exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)

/-- The sharp terminal construction is within two of `2 sqrt N`. -/
theorem two_sqrt_sub_two_lt_strausLength {N : ℕ} (hN : 1 ≤ N) :
    2 * Real.sqrt N - 2 < (strausLength N : ℝ) := by
  let m : ℕ := Nat.sqrt (4 * N + 1)
  have hm2 : 2 ≤ m := by
    dsimp [m]
    rw [Nat.le_sqrt']
    nlinarith
  have hroot : 4 * N + 1 < (m + 1) * (m + 1) := by
    simpa [m] using Nat.lt_succ_sqrt (4 * N + 1)
  have hrootZ : (4 : ℝ) * N < ((m : ℝ) + 1) ^ 2 := by
    exact_mod_cast (show 4 * N < (m + 1) ^ 2 by simpa [pow_two] using
      (show 4 * N < (m + 1) * (m + 1) by omega))
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hmnonneg : (0 : ℝ) ≤ m + 1 := by positivity
  have hsnonneg : (0 : ℝ) ≤ 2 * Real.sqrt N := by positivity
  have hlt : 2 * Real.sqrt N < (m : ℝ) + 1 := by
    by_contra hn
    have hge : (m : ℝ) + 1 ≤ 2 * Real.sqrt N := le_of_not_gt hn
    have hsqle := mul_self_le_mul_self hmnonneg hge
    nlinarith
  have hq : strausLength N = m - 1 := by rfl
  rw [hq]
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hmcast]
  linarith

/-- Every maximizer eventually lies above the numerical threshold needed by
the large-set structure theorem. -/
theorem eventually_maximizer_above_structure_threshold :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A → A.card = k N →
      (49 / 25 : ℝ) * Real.sqrt N < (A.card : ℝ) := by
  filter_upwards [eventually_ge_atTop 2501] with N hN
  intro A hA hcard
  have hNpos : 1 ≤ N := by omega
  have hlower := strausLength_le_k N
  have htail := two_sqrt_sub_two_lt_strausLength hNpos
  have hsqrt : 50 < Real.sqrt N := by
    rw [Real.lt_sqrt (by norm_num)]
    exact_mod_cast (show 2500 < N by omega)
  have htailK : 2 * Real.sqrt N - 2 < (k N : ℝ) :=
    htail.trans_le (by exact_mod_cast hlower)
  rw [hcard]
  nlinarith

/-- All coarse scale comparisons needed before the final central-density
calculation hold simultaneously.  Constants are deliberately generous; the
strict exponent inequalities, not their values, are what matter. -/
theorem eventually_central_extractor_scales (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      2 * (N : ℝ) ^ ((7 : ℝ) / 12) ≤
        3 * (N : ℝ) ^ ((5 : ℝ) / 6) ∧
      (100000 + C₀ + 10) * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
        (N : ℝ) ^ ((11 : ℝ) / 24) ∧
      (4000000 + 10 * C₀) * (N : ℝ) ^ ((11 : ℝ) / 24) ≤
        Real.sqrt N := by
  have h₁ := eventually_const_mul_rpow_seven_twelfths_le_five_sixths
    2 (by positivity)
  have h₂ := eventually_const_mul_rpow_five_twelfths_le_eleven_twentyfourths
    (100000 + C₀ + 10) (by positivity)
  have h₃ := eventually_const_mul_rpow_eleven_twentyfourths_le_sqrt
    (4000000 + 10 * C₀) (by positivity)
  filter_upwards [eventually_ge_atTop 1, h₁, h₂, h₃] with N hN h₁ h₂ h₃
  have hp : 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := by positivity
  exact ⟨hN, h₁.trans (by nlinarith), h₂, h₃⟩

/-! ## Coarse finite scale extraction -/

/-- Before using the central quadratic inequality, ambient span already
forces the structural step below `3/5 sqrt N`.  Consequently the regular
half-length `k=(|A\C|-q)/2` is at least `sqrt N/2`.  This is the exact
bootstrap needed by `central_q_k_error`. -/
theorem LargeSetStructure.crude_step_and_half_regular
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A)
    (hA : IsBoundedAdmissible N A)
    (hgcd : IsDifferenceGCD S.step A)
    (hK : 2 * Real.sqrt N - 2 ≤ (A.card : ℝ))
    (hC : (S.exceptional.card : ℝ) ≤ Real.sqrt N / 10)
    (hsqrt : 10 ≤ Real.sqrt N) :
    let B := A \ S.exceptional
    let k := (B.card - S.step) / 2
    (S.step : ℝ) ≤ (3 / 5 : ℝ) * Real.sqrt N ∧
      S.step ≤ B.card ∧ Real.sqrt N / 2 ≤ (k : ℝ) := by
  let B : Finset ℤ := A \ S.exceptional
  let k : ℕ := (B.card - S.step) / 2
  have hNpos : (0 : ℝ) < N := by
    have hsqrtPos : 0 < Real.sqrt N := by linarith
    exact (Real.sqrt_pos).mp hsqrtPos
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNpos.le
  have hAcard : A.card = S.exceptional.card + B.card := by
    dsimp [B]
    rw [← Finset.card_union_of_disjoint S.exceptional_disjoint_regular,
      S.exceptional_union_regular]
  have hcardTwo : 2 ≤ A.card := by
    have hreal : (2 : ℝ) < A.card := by nlinarith
    exact_mod_cast hreal.le
  have hspan := common_step_mul_card_sub_one_lt_ambient hA S.step_pos
    hgcd.1 hcardTwo
  have hspanR : (S.step : ℝ) * (A.card - 1 : ℕ) < N := by
    exact_mod_cast hspan
  have hKminus : (5 / 3 : ℝ) * Real.sqrt N ≤
      ((A.card - 1 : ℕ) : ℝ) := by
    have hcardPos : 1 ≤ A.card := by omega
    rw [Nat.cast_sub hcardPos]
    push_cast
    nlinarith
  have hq : (S.step : ℝ) ≤ (3 / 5 : ℝ) * Real.sqrt N := by
    by_contra hn
    have hqgt : (3 / 5 : ℝ) * Real.sqrt N < S.step :=
      lt_of_not_ge hn
    have hnonneg : (0 : ℝ) ≤ S.step := by positivity
    have hprod := mul_lt_mul_of_pos_right hqgt
      (show 0 < ((A.card - 1 : ℕ) : ℝ) by
        exact_mod_cast (show 0 < A.card - 1 by omega))
    have hprodLower := mul_le_mul_of_nonneg_left hKminus
      (show 0 ≤ (3 / 5 : ℝ) * Real.sqrt N by positivity)
    nlinarith
  have hBlarge : (S.step : ℝ) ≤ (B.card : ℝ) := by
    rw [hAcard] at hK
    push_cast at hK
    nlinarith
  have hqB : S.step ≤ B.card := by exact_mod_cast hBlarge
  let θ : ℕ := (B.card - S.step) % 2
  have hθlt : θ < 2 := Nat.mod_lt _ (by omega)
  have hdecomp : B.card = 2 * k + S.step + θ := by
    have hdiv := Nat.mod_add_div (B.card - S.step) 2
    dsimp [k, θ]
    omega
  have hkhalf : Real.sqrt N / 2 ≤ (k : ℝ) := by
    rw [hAcard, hdecomp] at hK
    push_cast at hK
    have hθR : (θ : ℝ) ≤ 1 := by exact_mod_cast (show θ ≤ 1 by omega)
    nlinarith
  exact ⟨hq, hqB, hkhalf⟩

private theorem central_hole_Nk_bound
    {x k p w N : ℝ}
    (hxpos : 0 < x) (hk0 : 0 ≤ k)
    (hxSq : x ^ 2 = N) (hxp : x * p = w ^ 2)
    (hdelta : x - k < 200006 * p) (hklt : k < x) :
    N - k ^ 2 < 400012 * w ^ 2 := by
  have hdelta0 : 0 < x - k := by linarith
  have hsumPos : 0 < x + k := by linarith
  have hsum : x + k ≤ 2 * x := by linarith
  have hprod₁ := mul_lt_mul_of_pos_right hdelta hsumPos
  have hprod₂ := mul_le_mul_of_nonneg_left hsum hdelta0.le
  nlinarith

private theorem central_hole_correction_bound
    {c θ t q : ℕ} {w : ℝ}
    (hcw : (c : ℝ) ≤ w) (hθ : θ ≤ 1)
    (htup : (t : ℝ) < w + 1) (hwlarge : 100010 ≤ w) :
    ((c : ℝ) + θ + 2 * t + 1 - q) * (t + 1) < 4 * w ^ 2 := by
  have hθR : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ
  have hcoef : (c : ℝ) + θ + 2 * t + 1 - q < 3 * w + 4 := by
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have htplus : ((t + 1 : ℕ) : ℝ) < w + 2 := by
    push_cast
    linarith
  have hpoly : (3 * w + 4) * (w + 2) < 4 * w ^ 2 := by
    nlinarith [sq_nonneg (w - 6)]
  by_cases hcoef0 : 0 ≤ (c : ℝ) + θ + 2 * t + 1 - q
  · have hmul₁ := mul_lt_mul_of_pos_right hcoef
      (show 0 < w + 2 by linarith)
    have hmul₂ := mul_le_mul_of_nonneg_left htplus.le hcoef0
    simpa only [Nat.cast_add, Nat.cast_one] using
      hmul₂.trans_lt (hmul₁.trans hpoly)
  · have hneg : (c : ℝ) + θ + 2 * t + 1 - q < 0 :=
      lt_of_not_ge hcoef0
    have hmulneg := mul_neg_of_neg_of_pos hneg
      (show 0 < ((t + 1 : ℕ) : ℝ) by positivity)
    have hw2 : 0 < 4 * w ^ 2 := by positivity
    push_cast at hmulneg ⊢
    exact hmulneg.trans hw2

private theorem central_hole_finish
    {t R : ℕ} {w : ℝ}
    (hwlarge : 100010 ≤ w) (htlow : w ≤ (t : ℝ))
    (hupper : ((t + 1 : ℕ) : ℝ) * (R : ℝ) < 400016 * w ^ 2) :
    (R : ℝ) ≤ 400020 * w := by
  by_contra hn
  have hRgt : 400020 * w < (R : ℝ) := lt_of_not_ge hn
  have htlow' : w ≤ ((t + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hwpos : 0 < w := by linarith
  have hlower : 400020 * w ^ 2 <
      ((t + 1 : ℕ) : ℝ) * (R : ℝ) := by
    calc
      400020 * w ^ 2 = (400020 * w) * w := by ring
      _ ≤ (400020 * w) * ((t + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left htlow' (by positivity)
      _ < (R : ℝ) * ((t + 1 : ℕ) : ℝ) :=
        mul_lt_mul_of_pos_right hRgt (by positivity)
      _ = ((t + 1 : ℕ) : ℝ) * (R : ℝ) := by ring
  nlinarith

/-- Real-arithmetic core of the missing-step estimate.  The central-pair
inequality, the `N^(5/12)` bound on `sqrt N-k`, and the choice
`t=⌈N^(11/24)⌉` force the hole count onto the `N^(11/24)` scale. -/
theorem central_hole_count_le_scale
    {N k q c θ t T R : ℕ} {p w : ℝ}
    (hN : 0 < N)
    (hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ))
    (hsqrtp : Real.sqrt N * p = w ^ 2)
    (hdelta : Real.sqrt N - (k : ℝ) < 200006 * p)
    (hklt : (k : ℝ) < Real.sqrt N)
    (hc : (c : ℝ) ≤ 100000 * p)
    (hθ : θ ≤ 1)
    (hp : 1 ≤ p) (hpw : 100010 * p ≤ w)
    (htlow : w ≤ (t : ℝ)) (htup : (t : ℝ) < w + 1)
    (hTpos : 1 ≤ T)
    (hT : (T : ℝ) =
      2 * (k : ℝ) + q - c - θ - 2 * t)
    (hpair : ((t + 1 : ℕ) : ℝ) * ((T - 1 + R : ℕ) : ℝ) <
      (N : ℝ) - (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((t + 1 : ℕ) : ℝ)) :
    (R : ℝ) ≤ 400020 * w := by
  have hsqrtPos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hNk : (N : ℝ) - (k : ℝ) ^ 2 < 400012 * w ^ 2 :=
    central_hole_Nk_bound hsqrtPos (by positivity) hsqrtSq hsqrtp hdelta hklt
  have hwlarge : 100010 ≤ w := by nlinarith
  have hcw : (c : ℝ) ≤ w := by nlinarith
  have hcorrBound :
      ((c : ℝ) + θ + 2 * t + 1 - q) * (t + 1) < 4 * w ^ 2 :=
    central_hole_correction_bound hcw hθ htup hwlarge
  have hpair' :
      ((t + 1 : ℕ) : ℝ) * (R : ℝ) <
        (N : ℝ) - (k : ℝ) ^ 2 +
          ((c : ℝ) + θ + 2 * t + 1 - q) * (t + 1) := by
    push_cast
    have hcast : ((T - 1 + R : ℕ) : ℝ) =
        (T : ℝ) - 1 + R := by
      rw [Nat.cast_add, Nat.cast_sub hTpos]
      push_cast
      ring
    rw [hcast] at hpair
    push_cast at hpair
    have hid :
        ((t : ℝ) + 1) * ((T : ℝ) - 1 + R) =
          ((t : ℝ) + 1) * R + 2 * k * (t + 1) -
            ((c : ℝ) + θ + 2 * t + 1 - q) * (t + 1) := by
      rw [hT]
      ring
    rw [hid] at hpair
    linarith
  have hupper :
      ((t + 1 : ℕ) : ℝ) * (R : ℝ) < 400016 * w ^ 2 := by
    calc
      ((t + 1 : ℕ) : ℝ) * (R : ℝ) <
          (N : ℝ) - (k : ℝ) ^ 2 +
            ((c : ℝ) + θ + 2 * t + 1 - q) * (t + 1) := hpair'
      _ < 400012 * w ^ 2 + 4 * w ^ 2 := add_lt_add hNk hcorrBound
      _ = 400016 * w ^ 2 := by ring
  exact central_hole_finish hwlarge htlow hupper

/-! ## Consecutive central subsequences -/

/-- The `K-2u` central terms of an ordered sequence. -/
def centralBlock (a : ℕ → ℤ) (K u : ℕ) : Finset ℤ :=
  Finset.image (fun i ↦ a (u + i)) (Finset.range (K - 2 * u))

theorem card_centralBlock_of_qSeparated
    {a : ℕ → ℤ} {K q u : ℕ} (hq : 0 < q)
    (hu : 2 * u ≤ K) (hsep : QSeparated a K q) :
    (centralBlock a K u).card = K - 2 * u := by
  rw [centralBlock]
  have hinj : Set.InjOn (fun i : ℕ ↦ a (u + i))
      (Finset.range (K - 2 * u)) := by
    intro i hi j hj hij
    change a (u + i) = a (u + j) at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hjK : u + j < K := by
        have := Finset.mem_range.mp hj
        omega
      have h := hsep (i := u + i) (j := u + j) (by omega) hjK
      rw [hij] at h
      have hqcast : (0 : ℤ) < q := by exact_mod_cast hq
      push_cast at h
      nlinarith
    · have hiK : u + i < K := by
        have := Finset.mem_range.mp hi
        omega
      have h := hsep (i := u + j) (j := u + i) (by omega) hiK
      rw [hij] at h
      have hqcast : (0 : ℤ) < q := by exact_mod_cast hq
      push_cast at h
      nlinarith
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range]

theorem centralBlock_subset_of_enumerates
    {A : Finset ℤ} {a : ℕ → ℤ} {K u : ℕ}
    (henum : A = Finset.image a (Finset.range K))
    (hK : K = A.card) (hu : 2 * u ≤ K) :
    centralBlock a K u ⊆ A := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [henum]
  apply Finset.mem_image.mpr
  refine ⟨u + i, Finset.mem_range.mpr ?_, rfl⟩
  have hi' := Finset.mem_range.mp hi
  omega

/-- The central span of a `q`-separated sequence has a unique nonnegative
number of missing `q`-steps.  This elementary division lemma is the bridge
from the analytic central-span bound to the hole parameter of local density. -/
theorem exists_central_hole_count
    {a : ℕ → ℤ} {K q u : ℕ} (hq : 0 < q)
    (hcentral : 2 * u + 1 < K)
    (hsep : QSeparated a K q)
    (hdiv : (q : ℤ) ∣ a (K - u - 1) - a u) :
    ∃! R : ℕ, a (K - u - 1) - a u =
      (q : ℤ) * ((K : ℤ) - 2 * (u : ℤ) - 1 + (R : ℤ)) := by
  obtain ⟨z, hz⟩ := hdiv
  have hgap := hsep (i := u) (j := K - u - 1) (by omega) (by omega)
  have hidx : (((K - u - 1 : ℕ) : ℤ) - (u : ℤ)) =
      (K : ℤ) - 2 * (u : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hidx] at hgap
  have hqcast : (0 : ℤ) < q := by exact_mod_cast hq
  have hzbase : (K : ℤ) - 2 * (u : ℤ) - 1 ≤ z := by
    nlinarith [hz]
  let R : ℕ := Int.toNat (z - ((K : ℤ) - 2 * (u : ℤ) - 1))
  have hnonneg : 0 ≤ z - ((K : ℤ) - 2 * (u : ℤ) - 1) := by omega
  have hRcast : (R : ℤ) = z - ((K : ℤ) - 2 * (u : ℤ) - 1) := by
    exact Int.toNat_of_nonneg hnonneg
  refine ⟨R, ?_, ?_⟩
  · dsimp
    rw [hz, hRcast]
    ring
  · intro R' hR'
    rw [hz] at hR'
    have hzEq : z = (K : ℤ) - 2 * (u : ℤ) - 1 + (R' : ℤ) :=
      mul_left_cancel₀
        (by exact_mod_cast (Nat.ne_of_gt hq) : (q : ℤ) ≠ 0) hR'
    have hmul : (q : ℤ) * (R : ℤ) = (q : ℤ) * (R' : ℤ) := by
      rw [hRcast, hzEq]
      ring
    have : (R : ℤ) = (R' : ℤ) :=
      mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hq) : (q : ℤ) ≠ 0) hmul
    exact_mod_cast this.symm

/-! ## The finite ordered-block constructor -/

/-- Assemble the concrete ordered central block from the common-residue and
central-span conclusions.  The hole count is constructed (and proved unique)
rather than supplied as data. -/
theorem exists_orderedCentralBlock_of_common_difference_specified
    {N : ℕ} {A : Finset ℤ} {q u : ℕ}
    (hA : IsBoundedAdmissible N A) (hq : 0 < q)
    (hdivA : IsDifferenceDivisor q A) (hu2 : 2 ≤ u)
    (hcentral : 2 * u + 1 < A.card)
    (hqT : q ≤ A.card - 2 * u)
    (hsize : q + 3 ≤ 2 * A.card)
    (hspanDiv : (q : ℤ) ∣
      orderedEntry A (A.card - u - 1) - orderedEntry A u) :
    ∃ D : OrderedCentralBlock N A,
      D.a = orderedEntry A ∧ D.q = q ∧ D.u = u := by
  let a : ℕ → ℤ := orderedEntry A
  let T : ℕ := A.card - 2 * u
  let L : ℕ := u + sigma T q
  let θ : ℕ := theta T q
  have hsep : QSeparated a A.card q := by
    exact qSeparated_orderedEntry hq hdivA
  obtain ⟨R, hspan, -⟩ := exists_central_hole_count
    hq hcentral hsep hspanDiv
  have htheta : θ = 0 ∨ θ = 1 := by
    exact theta_eq_zero_or_one T q (by simpa [T] using hqT)
  have hTdecomp : 2 * sigma T q + q + θ = T := by
    exact two_sigma_add_q_add_theta T q (by simpa [T] using hqT)
  have hKdecomp : A.card = 2 * L + q + θ := by
    dsimp [T, L, θ] at hTdecomp ⊢
    omega
  refine ⟨{
    a := a
    q := q
    u := u
    R := R
    L := L
    θ := θ
    enumerates := ?_
    q_pos := hq
    u_ge_two := hu2
    u_le_L := by simp [L]
    central_nonempty := hcentral
    size_condition := hsize
    theta_cases := htheta
    card_decomposition := hKdecomp
    separated := hsep
    central_span := hspan
    last_le := ?_
  }, rfl, rfl, rfl⟩
  · simpa [a] using (image_orderedEntry_range A).symm
  · apply orderedEntry_le_ambient hA
    omega

/-- Existential wrapper around the fully specified ordered-block
constructor. -/
theorem exists_orderedCentralBlock_of_common_difference
    {N : ℕ} {A : Finset ℤ} {q u : ℕ}
    (hA : IsBoundedAdmissible N A) (hq : 0 < q)
    (hdivA : IsDifferenceDivisor q A) (hu2 : 2 ≤ u)
    (hcentral : 2 * u + 1 < A.card)
    (hqT : q ≤ A.card - 2 * u)
    (hsize : q + 3 ≤ 2 * A.card)
    (hspanDiv : (q : ℤ) ∣
      orderedEntry A (A.card - u - 1) - orderedEntry A u) :
    Nonempty (OrderedCentralBlock N A) := by
  obtain ⟨D, -, -, -⟩ :=
    exists_orderedCentralBlock_of_common_difference_specified hA hq hdivA
      hu2 hcentral hqT hsize hspanDiv
  exact ⟨D⟩

/-! ## Endpoint sums of the central block -/

/-- Every in-range value of an ordered-block enumeration belongs to the set
it enumerates. -/
theorem OrderedCentralBlock.entry_mem
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {i : ℕ} (hi : i < A.card) : D.a i ∈ A := by
  apply (le_of_eq D.enumerates.symm)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- The increasing enumeration stored in an ordered central block is the
canonical increasing enumeration.  This lets later quantitative estimates,
which were first proved for `orderedEntry`, rewrite directly to the block's
sequence. -/
theorem OrderedCentralBlock.entry_eq_orderedEntry
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {i : ℕ} (hi : i < A.card) : D.a i = orderedEntry A i := by
  let f : Fin A.card → ℤ := fun j ↦ D.a j
  have hfmem : ∀ j, f j ∈ A := fun j ↦ D.entry_mem j.isLt
  have hfmono : StrictMono f := by
    intro x y hxy
    have hxyNat : (x : ℕ) < (y : ℕ) := hxy
    have hgap := D.separated (i := (x : ℕ)) (j := (y : ℕ))
      hxyNat y.isLt
    have hdiff : (0 : ℤ) < (y.val : ℤ) - (x.val : ℤ) := by
      apply sub_pos.mpr
      exact_mod_cast hxyNat
    have hq : (0 : ℤ) < D.q := by exact_mod_cast D.q_pos
    dsimp [f]
    nlinarith
  have heq : f = A.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl hfmem hfmono
  have hiEq := congrFun heq ⟨i, hi⟩
  rw [orderedEntry_of_lt A hi]
  exact hiEq

/-- The lower ambient endpoint for every in-range ordered entry. -/
theorem OrderedCentralBlock.one_le_entry
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A) {i : ℕ} (hi : i < A.card) :
    (1 : ℤ) ≤ D.a i := by
  exact (mem_ambient.mp (hA.1 (D.entry_mem hi))).1

/-- The upper ambient endpoint for every in-range ordered entry. -/
theorem OrderedCentralBlock.entry_le_ambient
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A) {i : ℕ} (hi : i < A.card) :
    D.a i ≤ (N : ℤ) := by
  exact (mem_ambient.mp (hA.1 (D.entry_mem hi))).2

/-- Sum of the first `s` entries after deleting `u` entries from the left. -/
def centralInitialSum (a : ℕ → ℤ) (u s : ℕ) : ℤ :=
  ∑ i ∈ Finset.range s, a (u + i)

/-- Sum of the last `s` entries before the final `u` entries. -/
def centralTerminalSum (a : ℕ → ℤ) (K u s : ℕ) : ℤ :=
  ∑ i ∈ Finset.range s, a (K - u - 1 - i)

theorem orderedInitialSum_eq_outer_add_central
    (a : ℕ → ℤ) (u s : ℕ) :
    orderedInitialSum a (u + s) =
      orderedInitialSum a u + centralInitialSum a u s := by
  simp only [orderedInitialSum, centralInitialSum, Finset.sum_range_add]

theorem orderedTerminalSum_eq_outer_add_central
    (a : ℕ → ℤ) {K u s : ℕ} (hus : u + s ≤ K) :
    orderedTerminalSum a K (u + s) =
      orderedTerminalSum a K u + centralTerminalSum a K u s := by
  rw [orderedTerminalSum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  congr 1
  omega

theorem centralTerminalSum_eq_sum_Ico
    (a : ℕ → ℤ) {K u s : ℕ} (hs : s ≤ K - 2 * u)
    (hu : 2 * u ≤ K) :
    centralTerminalSum a K u s =
      ∑ i ∈ Finset.Ico (K - 2 * u - s) (K - 2 * u), a (u + i) := by
  let T := K - 2 * u
  have hKT : K = 2 * u + T := by dsimp [T]; omega
  have hTs : T - s + s = T := Nat.sub_add_cancel (by simpa [T] using hs)
  have hreflect := Finset.sum_range_reflect
    (fun i : ℕ ↦ a (u + (T - s + i))) s
  have hleft :
      (∑ i ∈ Finset.range s, a (K - u - 1 - i)) =
        ∑ i ∈ Finset.range s, a (u + (T - s + (s - 1 - i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    congr 1
    omega
  rw [centralTerminalSum, hleft, hreflect]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : K - 2 * u - (K - 2 * u - s) = s := by omega
  rw [hlen]

/-- Enlarging the two symmetric central endpoint blocks from `s` to `s+q`
cannot decrease their endpoint spread when
`K = 2*(u+s)+q+θ`, `θ ∈ {0,1}`.  For `θ=0` the newly added middle
blocks coincide; for `θ=1` the terminal block is the one-place right shift
of the initial block. -/
theorem OrderedCentralBlock.central_endpoint_width_mono
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A) :
    centralTerminalSum D.a A.card D.u (D.L - D.u + D.q) -
        centralInitialSum D.a D.u (D.L - D.u + D.q) ≥
      centralTerminalSum D.a A.card D.u (D.L - D.u) -
        centralInitialSum D.a D.u (D.L - D.u) := by
  let s : ℕ := D.L - D.u
  have hLs : D.L = D.u + s := by
    dsimp [s]
    have := D.u_le_L
    omega
  have hcard := D.card_decomposition
  have hnew :
      (∑ i ∈ Finset.range D.q, D.a (D.u + s + i)) ≤
        ∑ i ∈ Finset.range D.q,
          D.a (A.card - D.u - 1 - (s + i)) := by
    have hreflect := Finset.sum_range_reflect
      (fun i : ℕ ↦ D.a (A.card - D.u - 1 - (s + i))) D.q
    rw [← hreflect]
    apply Finset.sum_le_sum
    intro i hi
    have hiq := Finset.mem_range.mp hi
    rcases D.theta_cases with hθ | hθ
    · have hidx :
          A.card - D.u - 1 - (s + (D.q - 1 - i)) =
            D.u + s + i := by
        rw [hcard, hLs, hθ]
        omega
      rw [hidx]
    · have hidx :
          A.card - D.u - 1 - (s + (D.q - 1 - i)) =
            D.u + s + i + 1 := by
        rw [hcard, hLs, hθ]
        omega
      rw [hidx]
      have hj : D.u + s + i + 1 < A.card := by
        rw [hcard, hLs, hθ]
        omega
      have hgap := D.separated (i := D.u + s + i)
        (j := D.u + s + i + 1) (by omega) hj
      have hq : (0 : ℤ) < D.q := by exact_mod_cast D.q_pos
      have hdiff :
          ((D.u + s + i + 1 : ℕ) : ℤ) -
              ((D.u + s + i : ℕ) : ℤ) = 1 := by
        push_cast
        ring
      rw [hdiff] at hgap
      nlinarith
  have hterminal :
      centralTerminalSum D.a A.card D.u (s + D.q) =
        centralTerminalSum D.a A.card D.u s +
          ∑ i ∈ Finset.range D.q,
            D.a (A.card - D.u - 1 - (s + i)) := by
    simp only [centralTerminalSum, Finset.sum_range_add]
  have hinitial :
      centralInitialSum D.a D.u (s + D.q) =
        centralInitialSum D.a D.u s +
          ∑ i ∈ Finset.range D.q, D.a (D.u + s + i) := by
    simp only [centralInitialSum, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  change centralTerminalSum D.a A.card D.u (s + D.q) -
      centralInitialSum D.a D.u (s + D.q) ≥
    centralTerminalSum D.a A.card D.u s -
      centralInitialSum D.a D.u s
  rw [hterminal, hinitial]
  linarith

/-! ## Affine local density on an extracted central block -/

/-- The local-density theorem specialized to a consecutive central block of
an ordered set in one residue class.  The normalized carrier and its hole
count are constructed inside the proof; the conclusion uses the actual
endpoint sums of the original ordered sequence. -/
theorem centralBlock_hasLocalDensity
    {a : ℕ → ℤ} {K q u R s : ℕ}
    (hq : 0 < q) (hcentral : 2 * u + 1 < K)
    (hsep : QSeparated a K q)
    (hcongr : ∀ i < K, Int.ModEq (q : ℤ) (a i) (a u))
    (hspan : a (K - u - 1) - a u =
      (q : ℤ) * ((K : ℤ) - 2 * (u : ℤ) - 1 + (R : ℤ)))
    (hT : 2 * s ≤ (K - 2 * u) + q)
    (hs : 4 * R + 3 + q ≤ s) :
    HasLocalDensity (restrictedSumset s (centralBlock a K u))
      (centralInitialSum a u s) (centralTerminalSum a K u s)
      ((s : ℤ) * a u) (q : ℤ) R := by
  let T : ℕ := K - 2 * u
  let c : ℤ := a u
  let d : ℕ → ℤ := fun i ↦ (a (u + i) - c) / (q : ℤ)
  let D : Finset ℤ := (Finset.range T).image d
  have huT : u < K := by omega
  have hrecover : ∀ {i : ℕ}, i < T → (q : ℤ) * d i + c = a (u + i) := by
    intro i hi
    have hui : u + i < K := by dsimp [T] at hi; omega
    have hmod := hcongr (u + i) hui
    have hdvdneg : (q : ℤ) ∣ c - a (u + i) := Int.modEq_iff_dvd.mp hmod
    have hdvd : (q : ℤ) ∣ a (u + i) - c := by
      rw [← neg_sub]
      exact dvd_neg.mpr hdvdneg
    have hcancel := Int.ediv_mul_cancel hdvd
    dsimp [d]
    calc
      (q : ℤ) * ((a (u + i) - c) / (q : ℤ)) + c =
          ((a (u + i) - c) / (q : ℤ)) * q + c := by ring
      _ = (a (u + i) - c) + c := by rw [hcancel]
      _ = a (u + i) := by ring
  have hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j := by
    intro i j hij hj
    have hi : i < T := hij.trans hj
    have haij := hsep (i := u + i) (j := u + j) (by omega)
      (show u + j < K by dsimp [T] at hj; omega)
    rw [← hrecover hi, ← hrecover hj] at haij
    have hqcast : (0 : ℤ) < q := by exact_mod_cast hq
    push_cast at haij
    nlinarith
  have hspanNorm : d (T - 1) - d 0 = ((T - 1 + R : ℕ) : ℤ) := by
    have hTpos : 0 < T := by dsimp [T]; omega
    have htop : T - 1 < T := by omega
    have hzero : 0 < T := hTpos
    have hidx : u + (T - 1) = K - u - 1 := by dsimp [T]; omega
    have hs := hspan
    have hrec0 := hrecover hzero
    simp only [Nat.add_zero] at hrec0
    rw [← hidx, ← hrecover htop, ← hrec0] at hs
    have hTcast : ((T - 1 + R : ℕ) : ℤ) =
        (K : ℤ) - 2 * (u : ℤ) - 1 + (R : ℤ) := by
      dsimp [T]
      push_cast
      omega
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    apply mul_left_cancel₀ hq0
    rw [hTcast]
    nlinarith
  have hV : centralBlock a K u =
      D.image (fun x ↦ (q : ℤ) * x + c) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hiT := Finset.mem_range.mp hi
      apply Finset.mem_image.mpr
      refine ⟨d i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
      exact hrecover hiT
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hiT := Finset.mem_range.mp hi
      apply Finset.mem_image.mpr
      exact ⟨i, hi, (hrecover hiT).symm⟩
  have hdense := df99_localDensity_of_affine_normalization_explicit
    (D := D) (V := centralBlock a K u) (d := d) (T := T)
    (s := s) (R := R) (q := q) (a := c) (c := c)
    hq (by simpa [T] using hT) (by simpa using hs) rfl hmono hspanNorm hV
    (Int.ModEq.refl c)
  have hsT : s ≤ T := by omega
  have hlo : (∑ i ∈ Finset.range s, ((q : ℤ) * d i + c)) =
      centralInitialSum a u s := by
    rw [centralInitialSum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hrecover (by
      have hi' := Finset.mem_range.mp hi
      omega)
  have hhi : (∑ i ∈ Finset.Ico (T - s) T, ((q : ℤ) * d i + c)) =
      centralTerminalSum a K u s := by
    calc
      (∑ i ∈ Finset.Ico (T - s) T, ((q : ℤ) * d i + c)) =
          ∑ i ∈ Finset.Ico (T - s) T, a (u + i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' := Finset.mem_Ico.mp hi
            exact hrecover (by omega)
      _ = centralTerminalSum a K u s := by
        symm
        simpa [T] using centralTerminalSum_eq_sum_Ico a
          (K := K) (u := u) (s := s) (by simpa [T] using hsT) (by omega)
  simpa only [hlo, hhi, c] using hdense

/-! ## The two fixed outer supports -/

def OrderedCentralBlock.initialFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : Finset ℤ :=
  Finset.image D.a (Finset.range D.u)

def OrderedCentralBlock.terminalFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : Finset ℤ :=
  Finset.image (fun i ↦ D.a (A.card - 1 - i)) (Finset.range D.u)

theorem OrderedCentralBlock.card_initialFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : D.initialFinset.card = D.u := by
  have hcentral := D.central_nonempty
  have hinj : Set.InjOn D.a (Finset.range D.u) := by
    intro i hi j hj hij
    apply D.separated.eq_of_eq D.q_pos
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hj
      omega
    · exact hij
  rw [OrderedCentralBlock.initialFinset, Finset.card_image_iff.mpr hinj,
    Finset.card_range]

theorem OrderedCentralBlock.card_terminalFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : D.terminalFinset.card = D.u := by
  have hcentral := D.central_nonempty
  have hinj : Set.InjOn (fun i ↦ D.a (A.card - 1 - i))
      (Finset.range D.u) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have heq := D.separated.eq_of_eq D.q_pos
      (show A.card - 1 - i < A.card by omega)
      (show A.card - 1 - j < A.card by omega) hij
    omega
  rw [OrderedCentralBlock.terminalFinset,
    Finset.card_image_iff.mpr hinj, Finset.card_range]

theorem OrderedCentralBlock.initialFinset_subset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : D.initialFinset ⊆ A := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hc := D.central_nonempty
  have hm : D.a i ∈ Finset.image D.a (Finset.range A.card) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hi
    omega), rfl⟩
  exact (Finset.ext_iff.mp D.enumerates (D.a i)).mpr hm

theorem OrderedCentralBlock.terminalFinset_subset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : D.terminalFinset ⊆ A := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hm : D.a (A.card - 1 - i) ∈
      Finset.image D.a (Finset.range A.card) :=
    Finset.mem_image.mpr ⟨A.card - 1 - i, Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hi
    have hc := D.central_nonempty
    omega), rfl⟩
  exact (Finset.ext_iff.mp D.enumerates (D.a (A.card - 1 - i))).mpr hm

theorem OrderedCentralBlock.sum_initialFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) :
    ∑ x ∈ D.initialFinset, x = orderedInitialSum D.a D.u := by
  rw [OrderedCentralBlock.initialFinset, Finset.sum_image]
  · rfl
  · intro i hi j hj hij
    have hc := D.central_nonempty
    exact D.separated.eq_of_eq D.q_pos
      (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hj; omega) hij

theorem OrderedCentralBlock.sum_terminalFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) :
    ∑ x ∈ D.terminalFinset, x = orderedTerminalSum D.a A.card D.u := by
  rw [OrderedCentralBlock.terminalFinset, Finset.sum_image]
  · rfl
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hc := D.central_nonempty
    have heq := D.separated.eq_of_eq D.q_pos
      (show A.card - 1 - i < A.card by omega)
      (show A.card - 1 - j < A.card by omega) hij
    omega

theorem OrderedCentralBlock.initial_disjoint_central {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) :
    Disjoint D.initialFinset D.centralFinset := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hc := D.central_nonempty
  have heq : i = D.u + j := D.separated.eq_of_eq D.q_pos
    (by omega) (by omega) (hix.trans hjx.symm)
  omega

theorem OrderedCentralBlock.terminal_disjoint_central
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A) :
    Disjoint D.terminalFinset D.centralFinset := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hc := D.central_nonempty
  have heq : A.card - 1 - i = D.u + j := D.separated.eq_of_eq D.q_pos
    (by omega) (by omega) (hix.trans hjx.symm)
  omega

/-- Quantitative width between the first and last `s` sums of a central
block. -/
theorem central_endpoint_width
    {a : ℕ → ℤ} {K q u T s : ℕ} (hq : 0 < q)
    (hKT : K = 2 * u + T) (hsT : s ≤ T)
    (hsep : QSeparated a K q) :
    (q : ℤ) * (s : ℤ) * ((T - s : ℕ) : ℤ) ≤
      centralTerminalSum a K u s - centralInitialSum a u s := by
  have hterm : ∀ i ∈ Finset.range s,
      a (u + i) + (q : ℤ) * ((T - s : ℕ) : ℤ) ≤
        a (u + (T - s + i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h := hsep.le_gap (i := u + i) (j := u + (T - s + i))
      (by omega) (by omega)
    have hcast : ((u + (T - s + i) : ℕ) : ℤ) - ((u + i : ℕ) : ℤ) =
        ((T - s : ℕ) : ℤ) := by
      push_cast
      omega
    rw [hcast] at h
    exact h
  have hsum := Finset.sum_le_sum hterm
  have hterminal : centralTerminalSum a K u s =
      ∑ i ∈ Finset.range s, a (u + (T - s + i)) := by
    calc
      centralTerminalSum a K u s =
          ∑ i ∈ Finset.Ico (K - 2 * u - s) (K - 2 * u), a (u + i) :=
        centralTerminalSum_eq_sum_Ico a (by omega) (by omega)
      _ = ∑ i ∈ Finset.range s, a (u + (T - s + i)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hlen : K - 2 * u - (K - 2 * u - s) = s := by omega
        rw [hlen]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        omega
  rw [← hterminal] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  rw [centralInitialSum]
  nlinarith

/-! ## Construction of the concrete density-endgame data -/

/-- The two central restricted-sum layers give an orientation-free second
pigeonhole certificate.  Every field, including both endpoint divisibilities
and both full-width estimates, follows from the ordered central block. -/
theorem symmetricSecondDensityComparison_of_orderedCentralBlock
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A)
    (hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u))
    (hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u) :
    ∃ E : SymmetricSecondDensityComparison (D.q : ℤ) D.R,
      E.shiftX = orderedTerminalSum D.a A.card D.u ∧
      E.MX = centralTerminalSum D.a A.card D.u (D.L - D.u) ∧
      E.shiftY = orderedInitialSum D.a D.u ∧
      E.mY = centralInitialSum D.a D.u (D.L - D.u + D.q) := by
  let s : ℕ := D.L - D.u
  let T : ℕ := A.card - 2 * D.u
  let V : Finset ℤ := D.centralFinset
  let X : Finset ℤ := restrictedSumset s V
  let Y : Finset ℤ := restrictedSumset (s + D.q) V
  let mX : ℤ := centralInitialSum D.a D.u s
  let MX : ℤ := centralTerminalSum D.a A.card D.u s
  let mY : ℤ := centralInitialSum D.a D.u (s + D.q)
  let MY : ℤ := centralTerminalSum D.a A.card D.u (s + D.q)
  let shiftX : ℤ := orderedTerminalSum D.a A.card D.u
  let shiftY : ℤ := orderedInitialSum D.a D.u
  have hcard := D.card_decomposition
  have htheta := D.theta_cases
  have huL := D.u_le_L
  have hKT : A.card = 2 * D.u + T := by dsimp [T]; omega
  have hTform : T = 2 * s + D.q + D.θ := by
    dsimp [T, s]
    omega
  have hqpos : 0 < D.q := D.q_pos
  have hsT : s ≤ T := by omega
  have hsqT : s + D.q ≤ T := by omega
  have hVeq : V = centralBlock D.a A.card D.u := rfl
  have hdensityX : HasLocalDensity X mX MX
      ((s : ℤ) * D.a D.u) (D.q : ℤ) D.R := by
    dsimp [X, mX, MX]
    rw [hVeq]
    apply centralBlock_hasLocalDensity hqpos D.central_nonempty D.separated
      hcongr D.central_span
    · omega
    · simpa [s] using hlocal
  have hdensityY : HasLocalDensity Y mY MY
      (((s + D.q : ℕ) : ℤ) * D.a D.u) (D.q : ℤ) D.R := by
    dsimp [Y, mY, MY]
    rw [hVeq]
    apply centralBlock_hasLocalDensity hqpos D.central_nonempty D.separated
      hcongr D.central_span
    · omega
    · simpa [s] using (show 4 * D.R + 3 + D.q ≤ s + D.q by omega)
  have hsumMod : ∀ n : ℕ, n ≤ T →
      Int.ModEq (D.q : ℤ) (centralInitialSum D.a D.u n)
        ((n : ℤ) * D.a D.u) := by
    intro n hn
    have h := Int.ModEq.sum (s := Finset.range n)
      (f := fun i : ℕ ↦ D.a (D.u + i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (D.u + i) (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [centralInitialSum, Finset.sum_const, nsmul_eq_mul] using h
  have hterminalMod : ∀ n : ℕ, n ≤ T →
      Int.ModEq (D.q : ℤ) (centralTerminalSum D.a A.card D.u n)
        ((n : ℤ) * D.a D.u) := by
    intro n hn
    have h := Int.ModEq.sum (s := Finset.range n)
      (f := fun i : ℕ ↦ D.a (A.card - D.u - 1 - i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (A.card - D.u - 1 - i) (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [centralTerminalSum, Finset.sum_const, nsmul_eq_mul] using h
  have hshiftY : Int.ModEq (D.q : ℤ) shiftY
      ((D.u : ℤ) * D.a D.u) := by
    have h := Int.ModEq.sum (s := Finset.range D.u)
      (f := fun i : ℕ ↦ D.a i) (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr i (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [shiftY, orderedInitialSum, Finset.sum_const, nsmul_eq_mul] using h
  have hshiftX : Int.ModEq (D.q : ℤ) shiftX
      ((D.u : ℤ) * D.a D.u) := by
    have h := Int.ModEq.sum (s := Finset.range D.u)
      (f := fun i : ℕ ↦ D.a (A.card - 1 - i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (A.card - 1 - i) (by
        have hi' := Finset.mem_range.mp hi
        have hc := D.central_nonempty
        omega))
    simpa [shiftX, orderedTerminalSum, Finset.sum_const, nsmul_eq_mul] using h
  have hmXmod : Int.ModEq (D.q : ℤ) mX ((s : ℤ) * D.a D.u) := by
    simpa [mX] using hsumMod s hsT
  have hMXmod : Int.ModEq (D.q : ℤ) MX ((s : ℤ) * D.a D.u) := by
    simpa [MX] using hterminalMod s hsT
  have hmYmod : Int.ModEq (D.q : ℤ) mY
      (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
    simpa [mY] using hsumMod (s + D.q) hsqT
  have hMYmod : Int.ModEq (D.q : ℤ) MY
      (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
    simpa [MY] using hterminalMod (s + D.q) hsqT
  have hdrop : Int.ModEq (D.q : ℤ)
      (((s + D.q : ℕ) : ℤ) * D.a D.u) ((s : ℤ) * D.a D.u) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(D.a D.u), ?_⟩
    push_cast
    ring
  have hcrossX : Int.ModEq (D.q : ℤ)
      (shiftY + mY - shiftX) ((s : ℤ) * D.a D.u) := by
    have hraw := (hshiftY.add hmYmod).sub hshiftX
    have hraw' : Int.ModEq (D.q : ℤ) (shiftY + mY - shiftX)
        (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
      convert hraw using 1 <;> push_cast <;> ring
    exact hraw'.trans hdrop
  have hcrossY : Int.ModEq (D.q : ℤ)
      (shiftX + mX - shiftY)
      (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
    have hraw := (hshiftX.add hmXmod).sub hshiftY
    have hraw' : Int.ModEq (D.q : ℤ) (shiftX + mX - shiftY)
        ((s : ℤ) * D.a D.u) := by
      convert hraw using 1 <;> push_cast <;> ring
    exact hraw'.trans hdrop.symm
  have hforwardMod : Int.ModEq (D.q : ℤ)
      (shiftX + MX) (shiftY + mY) := by
    have hl := hshiftX.add hMXmod
    have hr := hshiftY.add hmYmod
    apply hl.trans
    apply (Int.ModEq.trans ?_ hr.symm)
    rw [Int.modEq_iff_dvd]
    refine ⟨D.a D.u, ?_⟩
    push_cast
    ring
  have hreverseMod : Int.ModEq (D.q : ℤ)
      (shiftY + MY) (shiftX + mX) := by
    have hl := hshiftY.add hMYmod
    have hr := hshiftX.add hmXmod
    apply hl.trans
    apply (Int.ModEq.trans ?_ hr.symm)
    rw [Int.modEq_iff_dvd]
    refine ⟨-(D.a D.u), ?_⟩
    push_cast
    ring
  have hforwardDiv : (D.q : ℤ) ∣
      (shiftX + MX) - (shiftY + mY) := by
    rw [← neg_sub]
    exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hforwardMod)
  have hreverseDiv : (D.q : ℤ) ∣
      (shiftY + MY) - (shiftX + mX) := by
    rw [← neg_sub]
    exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hreverseMod)
  have width_of (n : ℕ) (hn : n ≤ T)
      (hR : 2 * D.R ≤ n * (T - n)) :
      centralInitialSum D.a D.u n + (D.q : ℤ) * (2 * D.R : ℕ) ≤
        centralTerminalSum D.a A.card D.u n := by
    have hwidth := central_endpoint_width (a := D.a) (K := A.card)
      (q := D.q) (u := D.u) (T := T) (s := n)
      hqpos hKT hn D.separated
    have hprodZ : ((2 * D.R : ℕ) : ℤ) ≤
        (n : ℤ) * ((T - n : ℕ) : ℤ) := by exact_mod_cast hR
    have hqZ : (0 : ℤ) < D.q := by exact_mod_cast hqpos
    have hscaled := mul_le_mul_of_nonneg_left hprodZ hqZ.le
    push_cast at hscaled
    nlinarith
  have hprodX : 2 * D.R ≤ s * (T - s) := by
    have hRle : 2 * D.R ≤ s := by dsimp [s] at hlocal ⊢; omega
    have hfactor : 1 ≤ T - s := by omega
    nlinarith
  have hprodY : 2 * D.R ≤ (s + D.q) * (T - (s + D.q)) := by
    have hRle : 2 * D.R ≤ s + D.q := by dsimp [s] at hlocal ⊢; omega
    have hfactor : 1 ≤ T - (s + D.q) := by
      rcases htheta with hθ | hθ <;> omega
    nlinarith
  have hXwidth : mX + (D.q : ℤ) * (2 * D.R : ℕ) ≤ MX := by
    simpa [mX, MX] using width_of s hsT hprodX
  have hYwidth : mY + (D.q : ℤ) * (2 * D.R : ℕ) ≤ MY := by
    simpa [mY, MY] using width_of (s + D.q) hsqT hprodY
  have hdisjoint : Disjoint (translateFinset shiftX X)
      (translateFinset shiftY Y) := by
    have h0 := translated_restrictedSumsets_disjoint_of_admissible
      (A := A) (V := V) (B := D.terminalFinset) (C := D.initialFinset)
      (r := s) (s := s + D.q) hA.2 D.centralFinset_subset
      D.terminalFinset_subset D.initialFinset_subset
      D.terminal_disjoint_central D.initial_disjoint_central
      (by rw [D.card_terminalFinset]; omega)
      (by rw [D.card_initialFinset]; omega)
      (by rw [D.card_terminalFinset, D.card_initialFinset]; omega)
    rw [D.sum_terminalFinset, D.sum_initialFinset] at h0
    exact h0
  refine ⟨{
    X := X
    Y := Y
    mX := mX
    MX := MX
    mY := mY
    MY := MY
    residueX := (s : ℤ) * D.a D.u
    residueY := ((s + D.q : ℕ) : ℤ) * D.a D.u
    shiftX := shiftX
    shiftY := shiftY
    densityX := hdensityX
    densityY := hdensityY
    cross_residueX := hcrossX
    cross_residueY := hcrossY
    least_residueX := hmXmod
    least_residueY := hmYmod
    X_has_full_block := hXwidth
    Y_has_full_block := hYwidth
    forward_endpoint_difference_divisible := hforwardDiv
    reverse_endpoint_difference_divisible := hreverseDiv
    translated_layers_disjoint := hdisjoint
  }, rfl, rfl, rfl, ?_⟩
  congr 1

/-- Complete orientation-free density data.  This is the strongest
unconditional finite certificate furnished by the central block: its public
endgame theorem returns the forward density endgame or the explicit reverse
pigeonhole branch. -/
theorem symmetricDensityEndgameData_of_orderedCentralBlock
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A)
    (hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u))
    (hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u) :
    Nonempty (SymmetricDensityEndgameData N A) := by
  obtain ⟨second, hshiftX, hMX, hshiftY, hmY⟩ :=
    symmetricSecondDensityComparison_of_orderedCentralBlock
      D hA hcongr hlocal
  let s : ℕ := D.L - D.u
  have hLs : D.L = D.u + s := by dsimp [s]; omega
  refine ⟨{
    toOrderedCentralBlock := D
    second := second
    second_left_eq := ?_
    second_right_eq := ?_
  }⟩
  · rw [hshiftX, hMX]
    change orderedTerminalSum D.a A.card D.u +
        centralTerminalSum D.a A.card D.u s =
      orderedTerminalSum D.a A.card D.L
    have hus : D.u + s ≤ A.card := by
      rw [← hLs]
      have hcard := D.card_decomposition
      omega
    rw [← orderedTerminalSum_eq_outer_add_central D.a hus, ← hLs]
  · rw [hshiftY, hmY]
    change orderedInitialSum D.a D.u +
        centralInitialSum D.a D.u (s + D.q) =
      orderedInitialSum D.a (D.L + D.q)
    rw [← orderedInitialSum_eq_outer_add_central]
    have hind : D.u + (s + D.q) = D.L + D.q := by omega
    rw [hind]

/-- The exact eventual output of the structure/central-span extractor.  The
two final inequalities are precisely the hypotheses consumed by the local
density and endpoint-orientation modules. -/
structure ExtractedCentralBlock (N : ℕ) (A : Finset ℤ) : Type
    extends OrderedCentralBlock N A where
  congruent : ∀ i < A.card, Int.ModEq (q : ℤ) (a i) (a u)
  local_room : 4 * R + 3 + q ≤ L - u
  orientation_scale :
    (N : ℤ) - 1 + 2 * ((2 * (R : ℤ) - 1) * (q : ℤ)) <
      2 * (q : ℤ) * ((L - u : ℕ) : ℤ) *
        (((A.card - 2 * u) - (L - u) : ℕ) : ℤ)

/-- Once the central block and the ordered comparison of its two relevant
layers have been extracted, every remaining field of `DensityEndgameData` is
forced.  In particular, both local-density assertions, all congruences, the
full-width condition, support disjointness, and the raw endpoint identities
are proved here. -/
theorem densityEndgameData_of_orderedCentralBlock
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A)
    (hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u))
    (hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u)
    (hleft :
      orderedTerminalSum D.a A.card D.u +
          centralInitialSum D.a D.u (D.L - D.u) ≤
        orderedInitialSum D.a D.u +
          centralInitialSum D.a D.u (D.L - D.u + D.q)) :
    Nonempty (DensityEndgameData N A) := by
  let s : ℕ := D.L - D.u
  let T : ℕ := A.card - 2 * D.u
  let V : Finset ℤ := D.centralFinset
  let X : Finset ℤ := restrictedSumset s V
  let Y : Finset ℤ := restrictedSumset (s + D.q) V
  let mX : ℤ := centralInitialSum D.a D.u s
  let MX : ℤ := centralTerminalSum D.a A.card D.u s
  let mY : ℤ := centralInitialSum D.a D.u (s + D.q)
  let MY : ℤ := centralTerminalSum D.a A.card D.u (s + D.q)
  let shiftX : ℤ := orderedTerminalSum D.a A.card D.u
  let shiftY : ℤ := orderedInitialSum D.a D.u
  have hcard := D.card_decomposition
  have htheta := D.theta_cases
  have huL := D.u_le_L
  have hLs : D.L = D.u + s := by dsimp [s]; omega
  have hKT : A.card = 2 * D.u + T := by dsimp [T]; omega
  have hTform : T = 2 * s + D.q + D.θ := by
    dsimp [T, s]
    omega
  have hspos : 0 < s := by
    dsimp [s] at hlocal ⊢
    omega
  have hqpos : 0 < D.q := D.q_pos
  have hsT : s ≤ T := by omega
  have hsqT : s + D.q ≤ T := by omega
  have hVeq : V = centralBlock D.a A.card D.u := rfl
  have hdensityX : HasLocalDensity X mX MX
      ((s : ℤ) * D.a D.u) (D.q : ℤ) D.R := by
    dsimp [X, mX, MX]
    rw [hVeq]
    apply centralBlock_hasLocalDensity hqpos D.central_nonempty D.separated
      hcongr D.central_span
    · omega
    · simpa [s] using hlocal
  have hdensityY : HasLocalDensity Y mY MY
      (((s + D.q : ℕ) : ℤ) * D.a D.u) (D.q : ℤ) D.R := by
    dsimp [Y, mY, MY]
    rw [hVeq]
    apply centralBlock_hasLocalDensity hqpos D.central_nonempty D.separated
      hcongr D.central_span
    · omega
    · simpa [s] using (show 4 * D.R + 3 + D.q ≤ s + D.q by omega)
  have hsumMod : ∀ n : ℕ, n ≤ T →
      Int.ModEq (D.q : ℤ) (centralInitialSum D.a D.u n)
        ((n : ℤ) * D.a D.u) := by
    intro n hn
    have h := Int.ModEq.sum (s := Finset.range n)
      (f := fun i : ℕ ↦ D.a (D.u + i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (D.u + i) (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [centralInitialSum, Finset.sum_const, nsmul_eq_mul] using h
  have hterminalMod : ∀ n : ℕ, n ≤ T →
      Int.ModEq (D.q : ℤ) (centralTerminalSum D.a A.card D.u n)
        ((n : ℤ) * D.a D.u) := by
    intro n hn
    have h := Int.ModEq.sum (s := Finset.range n)
      (f := fun i : ℕ ↦ D.a (A.card - D.u - 1 - i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (A.card - D.u - 1 - i) (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [centralTerminalSum, Finset.sum_const, nsmul_eq_mul] using h
  have hshiftY : Int.ModEq (D.q : ℤ) shiftY
      ((D.u : ℤ) * D.a D.u) := by
    have h := Int.ModEq.sum (s := Finset.range D.u)
      (f := fun i : ℕ ↦ D.a i) (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr i (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [shiftY, orderedInitialSum, Finset.sum_const, nsmul_eq_mul] using h
  have hshiftX : Int.ModEq (D.q : ℤ) shiftX
      ((D.u : ℤ) * D.a D.u) := by
    have h := Int.ModEq.sum (s := Finset.range D.u)
      (f := fun i : ℕ ↦ D.a (A.card - 1 - i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (A.card - 1 - i) (by
        have hi' := Finset.mem_range.mp hi
        have hc := D.central_nonempty
        omega))
    simpa [shiftX, orderedTerminalSum, Finset.sum_const, nsmul_eq_mul] using h
  have hmXmod : Int.ModEq (D.q : ℤ) mX ((s : ℤ) * D.a D.u) := by
    simpa [mX] using hsumMod s hsT
  have hMXmod : Int.ModEq (D.q : ℤ) MX ((s : ℤ) * D.a D.u) := by
    simpa [MX] using hterminalMod s hsT
  have hmYmod : Int.ModEq (D.q : ℤ) mY
      (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
    simpa [mY] using hsumMod (s + D.q) hsqT
  have hdrop : Int.ModEq (D.q : ℤ)
      (((s + D.q : ℕ) : ℤ) * D.a D.u) ((s : ℤ) * D.a D.u) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(D.a D.u), ?_⟩
    push_cast
    ring
  have hstart : Int.ModEq (D.q : ℤ)
      (shiftY + mY - shiftX) ((s : ℤ) * D.a D.u) := by
    have hraw := (hshiftY.add hmYmod).sub hshiftX
    have hraw' : Int.ModEq (D.q : ℤ) (shiftY + mY - shiftX)
        (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
      convert hraw using 1 <;> push_cast <;> ring
    exact hraw'.trans hdrop
  have hleftMod : Int.ModEq (D.q : ℤ) (shiftX + MX)
      (((D.u + s : ℕ) : ℤ) * D.a D.u) := by
    convert hshiftX.add hMXmod using 1 <;> push_cast <;> ring
  have hrightMod : Int.ModEq (D.q : ℤ) (shiftY + mY)
      (((D.u + s + D.q : ℕ) : ℤ) * D.a D.u) := by
    convert hshiftY.add hmYmod using 1 <;> push_cast <;> ring
  have hLRmod : Int.ModEq (D.q : ℤ) (shiftX + MX) (shiftY + mY) := by
    apply hleftMod.trans
    apply (Int.ModEq.trans ?_ hrightMod.symm)
    rw [Int.modEq_iff_dvd]
    refine ⟨D.a D.u, ?_⟩
    push_cast
    ring
  have hendpointDiv : (D.q : ℤ) ∣ (shiftX + MX) - (shiftY + mY) := by
    rw [← neg_sub]
    exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hLRmod)
  have hwidth := central_endpoint_width (a := D.a) (K := A.card)
    (q := D.q) (u := D.u) (T := T) (s := s + D.q)
    hqpos hKT hsqT D.separated
  have hprod : 2 * D.R ≤ (s + D.q) * (T - (s + D.q)) := by
    have hRle : 2 * D.R ≤ s + D.q := by omega
    have hfactor : 1 ≤ T - (s + D.q) := by
      rcases htheta with hθ | hθ <;> omega
    nlinarith
  have hYwidth : mY + (D.q : ℤ) * (2 * D.R : ℕ) ≤ MY := by
    dsimp [mY, MY]
    have hprodZ : ((2 * D.R : ℕ) : ℤ) ≤
        ((s + D.q : ℕ) : ℤ) * ((T - (s + D.q) : ℕ) : ℤ) := by
      exact_mod_cast hprod
    have hqZ : (0 : ℤ) < D.q := by exact_mod_cast hqpos
    have hscaled := mul_le_mul_of_nonneg_left hprodZ hqZ.le
    push_cast at hscaled
    calc
      centralInitialSum D.a D.u (s + D.q) +
            (D.q : ℤ) * (2 * D.R : ℕ) ≤
          centralInitialSum D.a D.u (s + D.q) +
            (D.q : ℤ) * (((s + D.q : ℕ) : ℤ) *
              ((T - (s + D.q) : ℕ) : ℤ)) := by gcongr
      _ = centralInitialSum D.a D.u (s + D.q) +
            (D.q : ℤ) * ((s + D.q : ℕ) : ℤ) *
              ((T - (s + D.q) : ℕ) : ℤ) := by ring
      _ ≤ centralTerminalSum D.a A.card D.u (s + D.q) := by linarith
  have hdisjoint : Disjoint (translateFinset shiftX X)
      (translateFinset shiftY Y) := by
    have h0 := translated_restrictedSumsets_disjoint_of_admissible
      (A := A) (V := V) (B := D.terminalFinset) (C := D.initialFinset)
      (r := s) (s := s + D.q) hA.2 D.centralFinset_subset
      D.terminalFinset_subset D.initialFinset_subset
      D.terminal_disjoint_central D.initial_disjoint_central
      (by rw [D.card_terminalFinset]; omega)
      (by rw [D.card_initialFinset]; omega)
      (by rw [D.card_terminalFinset, D.card_initialFinset]; omega)
    rw [D.sum_terminalFinset, D.sum_initialFinset] at h0
    exact h0
  let second : SecondDensityComparison (D.q : ℤ) D.R := {
    X := X
    Y := Y
    mX := mX
    MX := MX
    mY := mY
    MY := MY
    residueX := (s : ℤ) * D.a D.u
    residueY := ((s + D.q : ℕ) : ℤ) * D.a D.u
    shiftX := shiftX
    shiftY := shiftY
    densityX := hdensityX
    densityY := hdensityY
    start_residueX := hstart
    least_residueY := hmYmod
    left_endpoints_ordered := by simpa [shiftX, shiftY, mX, mY, s] using hleft
    Y_has_full_block := hYwidth
    endpoint_difference_divisible := hendpointDiv
    translated_layers_disjoint := hdisjoint
  }
  refine ⟨{
    toOrderedCentralBlock := D
    second := second
    second_left_eq := ?_
    second_right_eq := ?_
  }⟩
  · dsimp [second, shiftX, MX]
    rw [← orderedTerminalSum_eq_outer_add_central D.a (by omega), ← hLs]
  · dsimp [second, shiftY, mY]
    rw [← orderedInitialSum_eq_outer_add_central]
    have hind : D.u + (s + D.q) = D.L + D.q := by omega
    rw [hind]

/-! ## Eventual extraction for maximizing sets -/

private theorem central_T_formula
    {K C b k q θ t u T : ℕ}
    (hK : K = C + b) (hb : b = 2 * k + q + θ)
    (hu : u = C + θ + t) (hT : T = K - 2 * u)
    (hsmall : C + θ + 2 * t < 2 * k) :
    T = 2 * k + q - C - θ - 2 * t := by
  omega

private theorem central_T_formula_real
    {T k q C θ t : ℕ}
    (hT : T = 2 * k + q - C - θ - 2 * t)
    (hsmall : C + θ + 2 * t < 2 * k) :
    (T : ℝ) = 2 * (k : ℝ) + q - C - θ - 2 * t := by
  rw [hT]
  have hCθ : C + θ ≤ 2 * k + q := by omega
  have ht : 2 * t ≤ 2 * k + q - C - θ := by omega
  have hC : C ≤ 2 * k + q := by omega
  have hθ : θ ≤ 2 * k + q - C := by omega
  rw [Nat.cast_sub ht, Nat.cast_sub hθ, Nat.cast_sub hC]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

private theorem int_cancel_positive_factor
    {q x y : ℤ} (hq : 0 < q) (h : q * x < q * y) : x < y :=
  (Int.mul_lt_mul_left hq).mp h

private theorem central_T_pos
    {K u T : ℕ} (hK : K = 2 * u + T) (hcentral : 2 * u + 1 < K) :
    1 ≤ T := by
  omega

private theorem central_trim_decomposition
    {K L q θ u TD s : ℕ}
    (hcard : K = 2 * L + q + θ) (hu : u ≤ L)
    (hTD : TD = K - 2 * u) (hs : s = L - u) :
    K = 2 * u + TD ∧ TD = 2 * s + q + θ := by
  omega

private theorem int_central_pair_to_real
    {t T R N k : ℕ} (hT : 1 ≤ T)
    (h : ((t + 1 : ℕ) : ℤ) * ((T : ℤ) - 1 + (R : ℤ)) <
      (N : ℤ) - (k : ℤ) ^ 2 +
        2 * (k : ℤ) * ((t + 1 : ℕ) : ℤ)) :
    ((t + 1 : ℕ) : ℝ) * ((T - 1 + R : ℕ) : ℝ) <
      (N : ℝ) - (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((t + 1 : ℕ) : ℝ) := by
  simp only [Nat.cast_add, Nat.cast_sub hT, Nat.cast_one]
  exact_mod_cast h

private theorem central_sqrt_scale_identity
    {N : ℕ} (hN : 0 < N) :
    Real.sqrt N * (N : ℝ) ^ ((5 : ℝ) / 12) =
      ((N : ℝ) ^ ((11 : ℝ) / 24)) ^ 2 := by
  have hratio := sqrt_mul_five_twelfths_div_eleven_twentyfourths hN
  have hw0 : (N : ℝ) ^ ((11 : ℝ) / 24) ≠ 0 := by positivity
  rw [div_eq_iff hw0] at hratio
  simpa [pow_two] using hratio

/-- Construction and central-pair normalization isolated from the eventual
filter wrapper so that the finite proof has its own elaboration budget. -/
private theorem exists_central_block_core
    {N : ℕ} {A : Finset ℤ} {q u k t : ℕ}
    (hA : IsBoundedAdmissible N A) (hq : 0 < q)
    (hdiv : IsDifferenceDivisor q A) (hu2 : 2 ≤ u)
    (hcentral : 2 * u + 1 < A.card)
    (hqT : q ≤ A.card - 2 * u) (hsize : q + 3 ≤ 2 * A.card)
    (hpair : ((t + 1 : ℕ) : ℤ) *
        (orderedEntry A (A.card - u - 1) - orderedEntry A u) <
      (q : ℤ) * ((N : ℤ) - (k : ℤ) ^ 2 +
        2 * (k : ℤ) * ((t + 1 : ℕ) : ℤ))) :
    ∃ (D : OrderedCentralBlock N A) (T : ℕ),
      D.q = q ∧ D.u = u ∧ T = A.card - 2 * u ∧
      A.card = 2 * u + T ∧
      ((t + 1 : ℕ) : ℝ) * ((T - 1 + D.R : ℕ) : ℝ) <
        (N : ℝ) - (k : ℝ) ^ 2 +
          2 * (k : ℝ) * ((t + 1 : ℕ) : ℝ) := by
  have hspanDiv : (q : ℤ) ∣
      orderedEntry A (A.card - u - 1) - orderedEntry A u := by
    apply hdiv
    · exact orderedEntry_mem A (by omega)
    · exact orderedEntry_mem A (by omega)
  obtain ⟨D, ha, hqD, huD⟩ :=
    exists_orderedCentralBlock_of_common_difference_specified hA hq hdiv
      hu2 hcentral hqT hsize hspanDiv
  let T : ℕ := A.card - 2 * u
  have hKT : A.card = 2 * u + T := by dsimp [T]; omega
  have hspan := D.central_span
  rw [ha, hqD, huD] at hspan
  rw [hspan] at hpair
  have hpairReducedZ :
      ((t + 1 : ℕ) : ℤ) *
          ((T : ℤ) - 1 + (D.R : ℤ)) <
        (N : ℤ) - (k : ℤ) ^ 2 +
          2 * (k : ℤ) * ((t + 1 : ℕ) : ℤ) := by
    have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
    have hTcast : (A.card : ℤ) - 2 * (u : ℤ) - 1 =
        (T : ℤ) - 1 := by
      rw [hKT]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hTcast] at hpair
    change ((t + 1 : ℕ) : ℤ) *
        ((q : ℤ) * ((T : ℤ) - 1 + (D.R : ℤ))) <
      (q : ℤ) * ((N : ℤ) - (k : ℤ) ^ 2 +
        2 * (k : ℤ) * ((t + 1 : ℕ) : ℤ)) at hpair
    apply int_cancel_positive_factor hqZ
    calc
      (q : ℤ) * (((t + 1 : ℕ) : ℤ) *
          ((T : ℤ) - 1 + (D.R : ℤ))) =
        ((t + 1 : ℕ) : ℤ) *
          ((q : ℤ) * ((T : ℤ) - 1 + (D.R : ℤ))) := by ring
      _ < _ := hpair
  refine ⟨D, T, hqD, huD, rfl, hKT, ?_⟩
  exact int_central_pair_to_real (central_T_pos hKT hcentral) hpairReducedZ

/-- The final numerical-threshold and residue bookkeeping, isolated from the
eventual filter wrapper so that the dependent threshold application is checked
in a small finite context. -/
private theorem extractedCentralBlock_of_bounds
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A) (hNpos : 1 ≤ N)
    (hKlower : 2 * Real.sqrt N - 2 ≤ (A.card : ℝ))
    (hdivD : IsDifferenceDivisor D.q A)
    (huBoundD : (D.u : ℝ) ≤
      3 * (N : ℝ) ^ ((11 : ℝ) / 24))
    (hqBoundD : (D.q : ℝ) ≤
      300009 * (N : ℝ) ^ ((5 : ℝ) / 12))
    (hRbound : (D.R : ℝ) ≤
      400020 * (N : ℝ) ^ ((11 : ℝ) / 24))
    (horientN : ∀ {K u q R s T theta : ℕ},
      2 * Real.sqrt N - 2 ≤ (K : ℝ) →
      (u : ℝ) ≤ 3 * (N : ℝ) ^ ((11 : ℝ) / 24) →
      (q : ℝ) ≤ 300009 * (N : ℝ) ^ ((5 : ℝ) / 12) →
      (R : ℝ) ≤ 400020 * (N : ℝ) ^ ((11 : ℝ) / 24) →
      K = 2 * u + T → T = 2 * s + q + theta → theta ≤ 1 → 1 ≤ q →
      4 * (R + q) + 3 + q ≤ s ∧
        N - 1 + 2 * ((2 * R - 1) * q) < 2 * q * s * (T - s)) :
    Nonempty (ExtractedCentralBlock N A) := by
  let s : ℕ := D.L - D.u
  let TD : ℕ := A.card - 2 * D.u
  obtain ⟨hKTD, hTDs⟩ := central_trim_decomposition D.card_decomposition
    D.u_le_L (by rfl : TD = A.card - 2 * D.u)
      (by rfl : s = D.L - D.u)
  have hθD : D.θ ≤ 1 := by rcases D.theta_cases with h | h <;> omega
  obtain ⟨hlocalStrong, hgapNat⟩ := horientN hKlower huBoundD hqBoundD
    hRbound hKTD hTDs hθD D.q_pos
  have hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u := by
    dsimp [s] at hlocalStrong ⊢
    omega
  have hgapSigned := central_orientation_signed_gap_int hNpos hgapNat
  have hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u) := by
    intro i hi
    have huA : D.u < A.card := by omega
    have hd := hdivD (D.a i) (D.entry_mem hi)
      (D.a D.u) (D.entry_mem huA)
    rw [Int.modEq_iff_dvd]
    rw [← neg_sub]
    exact dvd_neg.mpr hd
  refine ⟨{
    toOrderedCentralBlock := D
    congruent := hcongr
    local_room := hlocal
    orientation_scale := ?_
  }⟩
  simpa [s, TD] using hgapSigned

/-- The structure theorem, residue absorption, central-pair estimate, and
all numerical thresholds assemble to the exact block consumed by endpoint
orientation. -/
theorem eventually_extractedCentralBlock
    (hstructure : HasEventuallyLargeSetStructure) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A → A.card = k N →
        Nonempty (ExtractedCentralBlock N A) := by
  obtain ⟨N₀, hN₀⟩ := hstructure
  have hscale := eventually_central_extractor_scales 0 (by norm_num)
  have horient := eventually_central_orientation_thresholds
  filter_upwards [eventually_ge_atTop N₀,
      eventually_ge_atTop 10000,
      eventually_maximizer_above_structure_threshold,
      eventually_structure_isDifferenceGCD,
      eventually_exceptional_card_le_tenth_sqrt,
      hscale, horient] with N hNstruct hNlarge hmax hgcdEvent hCsmall
        hscaleN horientN
  intro A hA hcard
  have hNpos : 1 ≤ N := by omega
  have hlarge := hmax A hA hcard
  obtain ⟨S⟩ := hN₀ N hNstruct A hA hlarge
  have hgcd : IsDifferenceGCD S.step A := hgcdEvent A S hA hlarge
  have hKlower : 2 * Real.sqrt N - 2 ≤ (A.card : ℝ) := by
    have htail := two_sqrt_sub_two_lt_strausLength hNpos
    have hkLower := strausLength_le_k N
    rw [hcard]
    exact htail.le.trans (by exact_mod_cast hkLower)
  have hsqrt10 : 10 ≤ Real.sqrt N := by
    have hN100 : (100 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show 100 ≤ N by omega)
    have hsqrtSq := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ (N : ℝ))
    have hsqrt0 := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  let B : Finset ℤ := A \ S.exceptional
  let k₀ : ℕ := (B.card - S.step) / 2
  let θ₀ : ℕ := (B.card - S.step) % 2
  let t : ℕ := dfCentralWindow N
  let u : ℕ := S.exceptional.card + θ₀ + t
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  let w : ℝ := (N : ℝ) ^ ((11 : ℝ) / 24)
  have hBdecomp : B.card = 2 * k₀ + S.step + θ₀ := by
    have hdiv := Nat.mod_add_div (B.card - S.step) 2
    dsimp [k₀, θ₀]
    have hqB :=
      (S.crude_step_and_half_regular hA hgcd hKlower (hCsmall A S) hsqrt10).2.1
    change S.step ≤ B.card at hqB
    omega
  have hθ₀ : θ₀ ≤ 1 := by
    dsimp [θ₀]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hAcard : A.card = S.exceptional.card + B.card := by
    dsimp [B]
    rw [← Finset.card_union_of_disjoint S.exceptional_disjoint_regular,
      S.exceptional_union_regular]
  obtain ⟨hqCrude, hqB, hkhalf⟩ :=
    S.crude_step_and_half_regular hA hgcd hKlower (hCsmall A S) hsqrt10
  change S.step ≤ B.card at hqB
  change Real.sqrt N / 2 ≤ (k₀ : ℝ) at hkhalf
  have hpone : 1 ≤ p := by
    dsimp [p]
    exact Real.one_le_rpow (by exact_mod_cast hNpos) (by norm_num)
  have hwone : 1 ≤ w := by
    dsimp [w]
    exact Real.one_le_rpow (by exact_mod_cast hNpos) (by norm_num)
  have htlow : w ≤ (t : ℝ) := by
    simpa [t, w] using dfCentralWindow_cast_ge N
  have htup : (t : ℝ) < w + 1 := by
    simpa [t, w] using dfCentralWindow_cast_lt_add_one N
  have hCpow : (S.exceptional.card : ℝ) ≤ 100000 * p := by
    dsimp [p]
    convert S.exceptional_card_le using 1 <;> norm_num
  rcases hscaleN with ⟨-, hshortScale, hpw, hwindow⟩
  have hpw' : 100010 * p ≤ w := by
    dsimp [p, w]
    norm_num at hpw ⊢
    exact hpw
  have hwindow' : 4000000 * w ≤ Real.sqrt N := by
    simpa [w] using hwindow
  have hshortLong : 2 * S.shortLength ≤ S.longLength := by
    have hreal : (2 : ℝ) * S.shortLength ≤ S.longLength :=
      calc
        (2 : ℝ) * S.shortLength ≤
            2 * (N : ℝ) ^ ((7 : ℝ) / 12) := by
          gcongr
          exact S.shortLength_le
        _ ≤ 3 * (N : ℝ) ^ ((5 : ℝ) / 6) := hshortScale
        _ ≤ S.longLength := S.longLength_ge
    exact_mod_cast hreal
  have ht : t < k₀ := by
    have htReal : (t : ℝ) < (k₀ : ℝ) := by
      nlinarith [htup, hwindow', hkhalf]
    exact_mod_cast htReal
  have hpair := S.central_pair_after_reinsertion hA hshortLong hqB ht
  have hquadR : (k₀ : ℝ) ^ 2 +
      2 * (k₀ : ℝ) * S.step < N := by
    exact_mod_cast hpair.1
  have hnear : 2 * Real.sqrt N - 100003 * p ≤
      2 * (k₀ : ℝ) + S.step := by
    rw [hAcard, hBdecomp] at hKlower
    push_cast at hKlower
    have hθR : (θ₀ : ℝ) ≤ 1 := by exact_mod_cast hθ₀
    nlinarith
  obtain ⟨hqFine, hkFine⟩ := central_q_k_error
    (E := 100003 * p) (by positivity) hkhalf hnear hquadR
  have hqFine' : (S.step : ℝ) ≤ 300009 * p := by
    nlinarith [hqFine]
  have hklt : (k₀ : ℝ) < Real.sqrt N := by
    have hsqrtSq := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ (N : ℝ))
    nlinarith
  have huReal : (u : ℝ) ≤ 3 * w := by
    have hCw : (S.exceptional.card : ℝ) ≤ w := by
      nlinarith [hCpow, hpw']
    have hθR : (θ₀ : ℝ) ≤ 1 := by exact_mod_cast hθ₀
    have hwlarge : (2 : ℝ) ≤ w := by nlinarith [hpone, hpw']
    dsimp [u]
    push_cast
    linarith only [hCw, hθR, htup, hwlarge]
  have hutk : S.exceptional.card + θ₀ + t < k₀ := by
    change u < k₀
    have hreal : (u : ℝ) < k₀ := by
      linarith only [huReal, hwindow', hkhalf, hwone]
    exact_mod_cast hreal
  have hcentralAux : S.exceptional.card + θ₀ + 2 * t < 2 * k₀ := by
    omega
  have hu2 : 2 ≤ u := by
    have ht2 : 2 ≤ t := by
      have : (2 : ℝ) ≤ t := by
        linarith only [htlow, hpw', hpone]
      exact_mod_cast this
    dsimp [u]
    omega
  have hcentral : 2 * u + 1 < A.card := by
    dsimp [u]
    rw [hAcard, hBdecomp]
    omega
  have hqT : S.step ≤ A.card - 2 * u := by
    dsimp [u]
    rw [hAcard, hBdecomp]
    omega
  have hsize : S.step + 3 ≤ 2 * A.card := by
    have hqA : S.step ≤ A.card := hqB.trans
      (Finset.card_le_card (by
        dsimp [B]
        exact Finset.sdiff_subset))
    have hAthree : 3 ≤ A.card := by omega
    simpa [two_mul] using Nat.add_le_add hqA hAthree
  obtain ⟨D, T, hqD, huD, hTdef, hKT, hpairReduced⟩ :=
    exists_central_block_core hA S.step_pos hgcd.1 hu2 hcentral hqT hsize
      hpair.2
  have hTformNat : T = 2 * k₀ + S.step - S.exceptional.card - θ₀ - 2 * t := by
    apply central_T_formula hAcard hBdecomp
    · rfl
    · exact hTdef
    · exact hcentralAux
  have hTform : (T : ℝ) = 2 * (k₀ : ℝ) + S.step -
      S.exceptional.card - θ₀ - 2 * t := by
    exact central_T_formula_real hTformNat hcentralAux
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtp : Real.sqrt N * p = w ^ 2 := by
    dsimp [p, w]
    exact central_sqrt_scale_identity (by omega)
  have hkFine' : Real.sqrt N - (k₀ : ℝ) < 200006 * p := by
    nlinarith only [hkFine]
  have hRbound : (D.R : ℝ) ≤ 400020 * w := by
    exact central_hole_count_le_scale (N := N) (k := k₀) (q := S.step)
      (c := S.exceptional.card) (θ := θ₀) (t := t) (T := T)
      (R := D.R) (p := p) (w := w)
      (Nat.zero_lt_of_lt hNpos) hsqrtSq hsqrtp hkFine' hklt hCpow hθ₀
      hpone hpw' htlow htup (central_T_pos hKT hcentral) hTform hpairReduced
  have hqBoundD : (D.q : ℝ) ≤ 300009 * p := by
    rw [hqD]
    exact hqFine'
  have huBoundD : (D.u : ℝ) ≤ 3 * w := by
    rw [huD]
    exact huReal
  have hdivD : IsDifferenceDivisor D.q A := by
    rw [hqD]
    exact hgcd.1
  exact extractedCentralBlock_of_bounds D hA hNpos hKlower hdivD
    (by simpa [w] using huBoundD) (by simpa [p] using hqBoundD)
      (by simpa [w] using hRbound) horientN

end

end Erdos874
