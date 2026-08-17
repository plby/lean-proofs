/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.LayerSelection

/-!
# The small four-fold layer in the Deshouillers--Freiman argument

This file formalizes Proposition 2 of Deshouillers--Freiman (1995).  Starting
from the small restricted layer selected by Proposition 1, we slide windows of
length `s + 4` through the increasing enumeration of `A`, in steps of four.
After deleting the common endpoint of consecutive `s`-sum layers, these
layers are pairwise disjoint.  Complementation in a window identifies its
`s`-sum layer with its four-fold restricted-sum layer.  A second subdivision
into blocks of prescribed size `L` gives a set `B` with

`5 * |4^B| < 29 * |B|`.

The paper works for all sufficiently large `N`.  The two harmless largeness
requirements used in its estimate are recorded explicitly as `1000 ≤ s` and
`1000 ≤ (|A| - s) / 4`; no asymptotic notation is hidden in the theorem.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Consecutive blocks in an increasing enumeration -/

/-- The `len` consecutive members of `A` beginning at position `start`. -/
private def orderedBlock (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) : Finset ℤ :=
  Finset.univ.image fun j : Fin len ↦
    A.orderEmbOfFin rfl ⟨start + j, by omega⟩

private lemma orderedBlock_card (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) :
    (orderedBlock A start len h).card = len := by
  rw [orderedBlock, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext (Nat.add_left_cancel
      (congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij)))

private lemma orderedBlock_subset (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) :
    orderedBlock A start len h ⊆ A := by
  intro x hx
  simp only [orderedBlock, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨j, rfl⟩ := hx
  exact A.orderEmbOfFin_mem rfl _

private lemma mem_orderedBlock_iff (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) (x : ℤ) :
    x ∈ orderedBlock A start len h ↔
      ∃ j : Fin len,
        A.orderEmbOfFin rfl ⟨start + j, by omega⟩ = x := by
  simp [orderedBlock]

private lemma restrictedSumset_mono_smallFour {r : ℕ} {A B : Finset ℤ}
    (hAB : A ⊆ B) : restrictedSumset r A ⊆ restrictedSumset r B := by
  intro z hz
  obtain ⟨C, hCA, hcard, rfl⟩ := mem_restrictedSumset.mp hz
  exact mem_restrictedSumset.mpr ⟨C, hCA.trans hAB, hcard, rfl⟩

/-! ## Four omitted positions control the endpoints of a window layer -/

private lemma sum_orderEmbOfFin (P : Finset ℤ) (n : ℕ) (hP : P.card = n) :
    (∑ j : Fin n, P.orderEmbOfFin hP j) = ∑ x ∈ P, x := by
  calc
    (∑ j : Fin n, P.orderEmbOfFin hP j) =
        ∑ x ∈ Finset.map (P.orderEmbOfFin hP).toEmbedding Finset.univ, x := by
          symm
          simpa using
            (Finset.sum_map (s := Finset.univ)
              (e := (P.orderEmbOfFin hP).toEmbedding) (f := fun x : ℤ ↦ x))
    _ = ∑ x ∈ P, x := by rw [Finset.map_orderEmbOfFin_univ]

/-- In a consecutive block, the sum of the first four entries is at most the
sum of any four-element subset. -/
private lemma firstFour_sum_le
    (A : Finset ℤ) (start len : ℕ) (hlen : 4 ≤ len)
    (h : start + len ≤ A.card) (P : Finset ℤ)
    (hPsub : P ⊆ orderedBlock A start len h) (hPcard : P.card = 4) :
    (∑ j : Fin 4,
        A.orderEmbOfFin rfl ⟨start + j, by omega⟩) ≤ ∑ x ∈ P, x := by
  let p : Fin 4 ↪o ℤ := P.orderEmbOfFin hPcard
  have hpblock (j : Fin 4) : p j ∈ orderedBlock A start len h :=
    hPsub (P.orderEmbOfFin_mem hPcard j)
  have hex (j : Fin 4) : ∃ u : Fin len,
      A.orderEmbOfFin rfl ⟨start + u, by omega⟩ = p j :=
    (mem_orderedBlock_iff A start len h (p j)).mp (hpblock j)
  let u : Fin 4 → Fin len := fun j ↦ Classical.choose (hex j)
  have hu (j : Fin 4) :
      A.orderEmbOfFin rfl ⟨start + u j, by omega⟩ = p j :=
    Classical.choose_spec (hex j)
  have hu_strict : StrictMono u := by
    intro i j hij
    have hpij : p i < p j := p.strictMono hij
    rw [← hu i, ← hu j] at hpij
    have hidx : start + (u i).val < start + (u j).val :=
      (A.orderEmbOfFin rfl).lt_iff_lt.mp hpij
    exact Fin.mk_lt_mk.mpr (Nat.lt_of_add_lt_add_left hidx)
  have hu_lower (j : Fin 4) : j.val ≤ (u j).val := by
    have h01 : (u (0 : Fin 4)).val < (u (1 : Fin 4)).val := hu_strict (by decide)
    have h12 : (u (1 : Fin 4)).val < (u (2 : Fin 4)).val := hu_strict (by decide)
    have h23 : (u (2 : Fin 4)).val < (u (3 : Fin 4)).val := hu_strict (by decide)
    fin_cases j
    · exact Nat.zero_le _
    · change 1 ≤ (u (1 : Fin 4)).val
      omega
    · change 2 ≤ (u (2 : Fin 4)).val
      omega
    · change 3 ≤ (u (3 : Fin 4)).val
      omega
  calc
    (∑ j : Fin 4, A.orderEmbOfFin rfl ⟨start + j, by omega⟩) ≤
        ∑ j : Fin 4, p j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← hu j]
          exact (A.orderEmbOfFin rfl).monotone (by
            exact Fin.mk_le_mk.mpr (Nat.add_le_add_left (hu_lower j) start))
    _ = ∑ x ∈ P, x := sum_orderEmbOfFin P 4 hPcard

private lemma fin_val_le_of_strictMono {n m : ℕ} (u : Fin (n + 1) → Fin m)
    (hu : StrictMono u) (j : Fin (n + 1)) : j.val ≤ (u j).val := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
      simpa using! lt_of_le_of_lt ih (hu Fin.castSucc_lt_succ)

/-- The sum of the first `s` entries of a block is at most the sum of any
`s`-element subset of that block. -/
private lemma firstS_sum_le
    (A : Finset ℤ) (start s : ℕ)
    (h : start + (4 + s) ≤ A.card) (R : Finset ℤ)
    (hRsub : R ⊆ orderedBlock A start (4 + s) h) (hRcard : R.card = s) :
    (∑ j : Fin s,
        A.orderEmbOfFin rfl ⟨start + j, by omega⟩) ≤ ∑ x ∈ R, x := by
  let r : Fin s ↪o ℤ := R.orderEmbOfFin hRcard
  have hrblock (j : Fin s) : r j ∈ orderedBlock A start (4 + s) h :=
    hRsub (R.orderEmbOfFin_mem hRcard j)
  have hex (j : Fin s) : ∃ u : Fin (4 + s),
      A.orderEmbOfFin rfl ⟨start + u, by omega⟩ = r j :=
    (mem_orderedBlock_iff A start (4 + s) h (r j)).mp (hrblock j)
  let u : Fin s → Fin (4 + s) := fun j ↦ Classical.choose (hex j)
  have hu (j : Fin s) :
      A.orderEmbOfFin rfl ⟨start + u j, by omega⟩ = r j :=
    Classical.choose_spec (hex j)
  have hu_strict : StrictMono u := by
    intro i j hij
    have hrij : r i < r j := r.strictMono hij
    rw [← hu i, ← hu j] at hrij
    have hidx : start + (u i).val < start + (u j).val :=
      (A.orderEmbOfFin rfl).lt_iff_lt.mp hrij
    exact Fin.mk_lt_mk.mpr (Nat.lt_of_add_lt_add_left hidx)
  have hu_lower (j : Fin s) : j.val ≤ (u j).val := by
    by_cases hs : s = 0
    · exact Fin.elim0 (hs ▸ j)
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
      exact fin_val_le_of_strictMono u hu_strict j
  calc
    (∑ j : Fin s, A.orderEmbOfFin rfl ⟨start + j, by omega⟩) ≤
        ∑ j : Fin s, r j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← hu j]
          exact (A.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr
            (Nat.add_le_add_left (hu_lower j) start))
    _ = ∑ x ∈ R, x := sum_orderEmbOfFin R s hRcard

/-- In a consecutive block of length `s + 4`, the sum of any four-element
subset is at most the sum of the last four entries. -/
private lemma sum_le_lastFour
    (A : Finset ℤ) (start s : ℕ)
    (h : start + (4 + s) ≤ A.card) (P : Finset ℤ)
    (hPsub : P ⊆ orderedBlock A start (4 + s) h) (hPcard : P.card = 4) :
    (∑ x ∈ P, x) ≤
      ∑ j : Fin 4,
        A.orderEmbOfFin rfl ⟨start + s + j, by omega⟩ := by
  let p : Fin 4 ↪o ℤ := P.orderEmbOfFin hPcard
  have hpblock (j : Fin 4) : p j ∈ orderedBlock A start (4 + s) h :=
    hPsub (P.orderEmbOfFin_mem hPcard j)
  have hex (j : Fin 4) : ∃ u : Fin (4 + s),
      A.orderEmbOfFin rfl ⟨start + u, by omega⟩ = p j :=
    (mem_orderedBlock_iff A start (4 + s) h (p j)).mp (hpblock j)
  let u : Fin 4 → Fin (4 + s) := fun j ↦ Classical.choose (hex j)
  have hu (j : Fin 4) :
      A.orderEmbOfFin rfl ⟨start + u j, by omega⟩ = p j :=
    Classical.choose_spec (hex j)
  have hu_strict : StrictMono u := by
    intro i j hij
    have hpij : p i < p j := p.strictMono hij
    rw [← hu i, ← hu j] at hpij
    have hidx : start + (u i).val < start + (u j).val :=
      (A.orderEmbOfFin rfl).lt_iff_lt.mp hpij
    exact Fin.mk_lt_mk.mpr (Nat.lt_of_add_lt_add_left hidx)
  have hu_upper (j : Fin 4) : (u j).val ≤ s + j.val := by
    have h01 : (u (0 : Fin 4)).val < (u (1 : Fin 4)).val := hu_strict (by decide)
    have h12 : (u (1 : Fin 4)).val < (u (2 : Fin 4)).val := hu_strict (by decide)
    have h23 : (u (2 : Fin 4)).val < (u (3 : Fin 4)).val := hu_strict (by decide)
    have hlast : (u (3 : Fin 4)).val < s + 4 := by
      simpa [Nat.add_comm] using (u (3 : Fin 4)).isLt
    fin_cases j
    · change (u (0 : Fin 4)).val ≤ s
      omega
    · change (u (1 : Fin 4)).val ≤ s + 1
      omega
    · change (u (2 : Fin 4)).val ≤ s + 2
      omega
    · change (u (3 : Fin 4)).val ≤ s + 3
      omega
  calc
    (∑ x ∈ P, x) = ∑ j : Fin 4, p j := (sum_orderEmbOfFin P 4 hPcard).symm
    _ ≤ ∑ j : Fin 4,
        A.orderEmbOfFin rfl ⟨start + s + j, by omega⟩ := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← hu j]
          have hjbound := hu_upper j
          have hnat : start + (u j).val ≤ start + s + j.val := by
            omega
          exact (A.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr hnat)

private lemma sum_orderedBlock (A : Finset ℤ) (start len : ℕ)
    (h : start + len ≤ A.card) :
    (∑ x ∈ orderedBlock A start len h, x) =
      ∑ j : Fin len, A.orderEmbOfFin rfl ⟨start + j, by omega⟩ := by
  rw [orderedBlock, Finset.sum_image]
  intro i hi j hj hij
  exact Fin.ext (Nat.add_left_cancel
    (congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij)))

/-! ## Complementation of restricted layers -/

/-- In a set of size `s + 4`, taking complements identifies the `s`-fold
and four-fold restricted sum layers (up to reflection in the total sum). -/
private lemma card_restrictedSumset_eq_four_of_card
    (C : Finset ℤ) (s : ℕ) (hC : C.card = s + 4) :
    (restrictedSumset s C).card = (restrictedSumset 4 C).card := by
  let T : ℤ := ∑ x ∈ C, x
  let f : ℤ → ℤ := fun z ↦ T - z
  have hf : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    omega
  have himage : (restrictedSumset s C).image f = restrictedSumset 4 C := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨R, hRC, hRcard, hRsum⟩ := mem_restrictedSumset.mp hz
      let P := C \ R
      have hPcard : P.card = 4 := by
        dsimp [P]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRC, hC, hRcard]
        omega
      have hPsum : ∑ x ∈ P, x = f z := by
        have hsplit := Finset.sum_sdiff (f := fun x : ℤ ↦ x) hRC
        dsimp [P, f, T]
        rw [hRsum] at hsplit
        omega
      exact mem_restrictedSumset.mpr ⟨P, Finset.sdiff_subset, hPcard, hPsum⟩
    · intro hy
      obtain ⟨Q, hQC, hQcard, hQsum⟩ := mem_restrictedSumset.mp hy
      let R := C \ Q
      have hRcard : R.card = s := by
        dsimp [R]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hQC, hC, hQcard]
        omega
      have hRsum : f (∑ x ∈ R, x) = y := by
        have hsplit := Finset.sum_sdiff (f := fun x : ℤ ↦ x) hQC
        dsimp [R, f, T]
        rw [hQsum] at hsplit
        omega
      refine ⟨∑ x ∈ R, x, ?_, hRsum⟩
      exact mem_restrictedSumset.mpr ⟨R, Finset.sdiff_subset, hRcard, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ hf]

/-! ## The sliding windows and their separating boundary sums -/

private def df95Window (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) : Finset ℤ :=
  orderedBlock A (4 * l.val) (4 + s) (by
    have hl := l.isLt
    omega)

private def df95Boundary (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) : ℤ :=
  ∑ j : Fin s,
    A.orderEmbOfFin rfl ⟨4 * l.val + 4 + j, by
      have hl := l.isLt
      omega⟩

private def df95Lower (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) : ℤ :=
  ∑ j : Fin s,
    A.orderEmbOfFin rfl ⟨4 * l.val + j, by
      have hl := l.isLt
      omega⟩

private lemma df95Window_card (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) :
    (df95Window A s J hJ l).card = s + 4 := by
  unfold df95Window
  have hc := orderedBlock_card A (4 * l.val) (4 + s) (by
    have hl := l.isLt
    omega)
  omega

private lemma df95Window_subset (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) :
    df95Window A s J hJ l ⊆ A := by
  exact orderedBlock_subset _ _ _ _

private lemma window_layer_le_boundary (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) {z : ℤ}
    (hz : z ∈ restrictedSumset s (df95Window A s J hJ l)) :
    z ≤ df95Boundary A s J hJ l := by
  obtain ⟨R, hRC, hRcard, hRsum⟩ := mem_restrictedSumset.mp hz
  let C := df95Window A s J hJ l
  let P := C \ R
  have hCcard : C.card = s + 4 := df95Window_card A s J hJ l
  have hPcard : P.card = 4 := by
    dsimp [P]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRC, hCcard, hRcard]
    omega
  have hPsub : P ⊆ C := Finset.sdiff_subset
  have hfirst :
      (∑ j : Fin 4,
        A.orderEmbOfFin rfl ⟨4 * l.val + j, by
          have hl := l.isLt
          omega⟩) ≤ ∑ x ∈ P, x := by
    exact firstFour_sum_le A (4 * l.val) (4 + s) (by omega) (by
      have hl := l.isLt
      omega) P hPsub hPcard
  have hsplitP := Finset.sum_sdiff (f := fun x : ℤ ↦ x) hRC
  have hsplitC :
      (∑ x ∈ C, x) =
        (∑ j : Fin 4,
          A.orderEmbOfFin rfl ⟨4 * l.val + j, by
            have hl := l.isLt
            omega⟩) + df95Boundary A s J hJ l := by
    dsimp [C]
    unfold df95Window
    rw [sum_orderedBlock]
    simp only [df95Boundary]
    simpa [Fin.sum_univ_add, add_assoc]
  dsimp [P, C] at hsplitP hfirst
  dsimp [C] at hsplitC
  rw [hRsum] at hsplitP
  omega

private lemma lower_le_window_layer (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) {z : ℤ}
    (hz : z ∈ restrictedSumset s (df95Window A s J hJ l)) :
    df95Lower A s J hJ l ≤ z := by
  obtain ⟨R, hRC, hRcard, hRsum⟩ := mem_restrictedSumset.mp hz
  rw [← hRsum]
  unfold df95Lower df95Window at *
  exact firstS_sum_le A (4 * l.val) s (by
    have hl := l.isLt
    omega) R hRC hRcard

private lemma df95Boundary_le_lower (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) {l m : Fin J} (hlm : l < m) :
    df95Boundary A s J hJ l ≤ df95Lower A s J hJ m := by
  apply Finset.sum_le_sum
  intro j hj
  exact (A.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr (by
    have hl := l.isLt
    have hm := m.isLt
    omega))

private def trimmedWindowLayer (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) : Finset ℤ :=
  (restrictedSumset s (df95Window A s J hJ l)).erase
    (df95Boundary A s J hJ l)

private lemma trimmedWindowLayer_pairwiseDisjoint
    (A : Finset ℤ) (s J : ℕ) (hJ : 4 * J + s ≤ A.card) :
    ((Finset.univ : Finset (Fin J)) : Set (Fin J)).PairwiseDisjoint
      (trimmedWindowLayer A s J hJ) := by
  intro l hl m hm hlm
  rcases lt_or_gt_of_ne hlm with hlt | hgt
  · change Disjoint (trimmedWindowLayer A s J hJ l)
        (trimmedWindowLayer A s J hJ m)
    rw [Finset.disjoint_left]
    intro z hzl hzm
    have hzl' : z ∈ restrictedSumset s (df95Window A s J hJ l) := by
      exact Finset.mem_of_mem_erase hzl
    have hzm' : z ∈ restrictedSumset s (df95Window A s J hJ m) := by
      exact Finset.mem_of_mem_erase hzm
    have hzne : z ≠ df95Boundary A s J hJ l := (Finset.mem_erase.mp hzl).1
    have h1 := window_layer_le_boundary A s J hJ l hzl'
    have h2 := df95Boundary_le_lower A s J hJ hlt
    have h3 := lower_le_window_layer A s J hJ m hzm'
    exact hzne (by omega)
  · change Disjoint (trimmedWindowLayer A s J hJ l)
        (trimmedWindowLayer A s J hJ m)
    rw [Finset.disjoint_left]
    intro z hzl hzm
    have hzl' : z ∈ restrictedSumset s (df95Window A s J hJ l) := by
      exact Finset.mem_of_mem_erase hzl
    have hzm' : z ∈ restrictedSumset s (df95Window A s J hJ m) := by
      exact Finset.mem_of_mem_erase hzm
    have hzne : z ≠ df95Boundary A s J hJ m := (Finset.mem_erase.mp hzm).1
    have h1 := window_layer_le_boundary A s J hJ m hzm'
    have h2 := df95Boundary_le_lower A s J hJ hgt
    have h3 := lower_le_window_layer A s J hJ l hzl'
    exact hzne (by omega)

private lemma trimmedWindowLayer_subset (A : Finset ℤ) (s J : ℕ)
    (hJ : 4 * J + s ≤ A.card) (l : Fin J) :
    trimmedWindowLayer A s J hJ l ⊆ restrictedSumset s A := by
  exact (Finset.erase_subset _ _).trans
    (restrictedSumset_mono_smallFour (df95Window_subset A s J hJ l))

private lemma exists_fin_mul_le_of_sum_le {J T : ℕ} (hJ : 0 < J)
    (f : Fin J → ℕ) (hsum : ∑ i, f i ≤ T) :
  ∃ i : Fin J, J * f i ≤ T := by
  by_contra h
  have hall : ∀ i : Fin J, T < J * f i := fun i ↦
    Nat.lt_of_not_ge (fun hi ↦ h ⟨i, hi⟩)
  have hstrict : (∑ _i : Fin J, T) < ∑ i : Fin J, J * f i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hall i).le
    · exact ⟨⟨0, hJ⟩, Finset.mem_univ _, hall ⟨0, hJ⟩⟩
  have hright : (∑ i : Fin J, J * f i) = J * ∑ i : Fin J, f i := by
    rw [Finset.mul_sum]
  rw [hright] at hstrict
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hstrict
  have hscaled := Nat.mul_le_mul_left J hsum
  nlinarith

/-! ## The first pigeonhole: a short `(s+4)`-window -/

private theorem exists_small_four_window
    (A : Finset ℤ) (s : ℕ)
    (hsA : s ≤ A.card)
    (hsmall : 25 * (restrictedSumset s A).card < 36 * s * (A.card - s))
    (hsLarge : 1000 ≤ s)
    (hJLarge : 1000 ≤ (A.card - s) / 4) :
    ∃ C : Finset ℤ, C ⊆ A ∧ C.card = s + 4 ∧
      100 * (restrictedSumset 4 C).card < 577 * s := by
  let J := (A.card - s) / 4
  have hJpos : 0 < J := by omega
  have hdivle : 4 * J ≤ A.card - s := by
    simpa [J, Nat.mul_comm] using Nat.div_mul_le_self (A.card - s) 4
  have hJbound : 4 * J + s ≤ A.card := by omega
  have hdivlt : A.card - s < 4 * J + 4 := by
    have hmod := Nat.mod_lt (A.card - s) (by decide : 0 < 4)
    have hdecomp := Nat.mod_add_div (A.card - s) 4
    dsimp [J] at hdivle ⊢
    omega
  have hcoreCount :
      ∑ l : Fin J, (trimmedWindowLayer A s J hJbound l).card ≤
        (restrictedSumset s A).card := by
    exact sum_card_le_card_of_pairwiseDisjoint_subset
      (Finset.univ : Finset (Fin J)) (trimmedWindowLayer A s J hJbound)
      (restrictedSumset s A) (trimmedWindowLayer_pairwiseDisjoint A s J hJbound)
      (fun l hl ↦ trimmedWindowLayer_subset A s J hJbound l)
  have hlayers :
      ∑ l : Fin J, (restrictedSumset s (df95Window A s J hJbound l)).card ≤
        (restrictedSumset s A).card + J := by
    calc
      ∑ l : Fin J, (restrictedSumset s (df95Window A s J hJbound l)).card ≤
          ∑ l : Fin J, ((trimmedWindowLayer A s J hJbound l).card + 1) := by
            apply Finset.sum_le_sum
            intro l hl
            dsimp [trimmedWindowLayer]
            by_cases hb : df95Boundary A s J hJbound l ∈
                restrictedSumset s (df95Window A s J hJbound l)
            · rw [Finset.card_erase_of_mem hb]
              omega
            · rw [Finset.erase_eq_of_notMem hb]
              omega
      _ = (∑ l : Fin J, (trimmedWindowLayer A s J hJbound l).card) + J := by
        simp [Finset.sum_add_distrib]
      _ ≤ (restrictedSumset s A).card + J := Nat.add_le_add_right hcoreCount J
  obtain ⟨l, hl⟩ := exists_fin_mul_le_of_sum_le hJpos
    (fun l : Fin J ↦ (restrictedSumset s (df95Window A s J hJbound l)).card)
    hlayers
  let C := df95Window A s J hJbound l
  have hCsub : C ⊆ A := df95Window_subset A s J hJbound l
  have hCcard : C.card = s + 4 := df95Window_card A s J hJbound l
  have hcomp : (restrictedSumset s C).card = (restrictedSumset 4 C).card :=
    card_restrictedSumset_eq_four_of_card C s hCcard
  refine ⟨C, hCsub, hCcard, ?_⟩
  rw [← hcomp]
  have hSJ : 432 * s + 100 * J ≤ s * J := by
    dsimp [J] at hJLarge ⊢
    nlinarith
  dsimp [C] at hl ⊢
  nlinarith

/-! ## The second pigeonhole: a prescribed-size block -/

private def prescribedBlock (C : Finset ℤ) (L M : ℕ)
    (hM : L * M ≤ C.card) (m : Fin M) : Finset ℤ :=
  orderedBlock C (L * m.val) L (by
    have hm := m.isLt
    nlinarith)

private lemma prescribedBlock_card (C : Finset ℤ) (L M : ℕ)
    (hM : L * M ≤ C.card) (m : Fin M) :
    (prescribedBlock C L M hM m).card = L := by
  exact orderedBlock_card _ _ _ _

private lemma prescribedBlock_subset (C : Finset ℤ) (L M : ℕ)
    (hM : L * M ≤ C.card) (m : Fin M) :
    prescribedBlock C L M hM m ⊆ C := by
  exact orderedBlock_subset _ _ _ _

private lemma prescribedBlock_lt (C : Finset ℤ) (L M : ℕ)
    (_hL : 0 < L) (hM : L * M ≤ C.card) {m n : Fin M} (hmn : m < n)
    {x y : ℤ} (hx : x ∈ prescribedBlock C L M hM m)
    (hy : y ∈ prescribedBlock C L M hM n) : x < y := by
  obtain ⟨i, hi⟩ :=
    (mem_orderedBlock_iff C (L * m.val) L (by
      have hm := m.isLt
      nlinarith) x).mp hx
  obtain ⟨j, hj⟩ :=
    (mem_orderedBlock_iff C (L * n.val) L (by
      have hn := n.isLt
      nlinarith) y).mp hy
  rw [← hi, ← hj]
  apply (C.orderEmbOfFin rfl).strictMono
  apply Fin.mk_lt_mk.mpr
  have hi' := i.isLt
  have hj' := j.isLt
  have hmn' : m.val + 1 ≤ n.val := by omega
  have hmul := Nat.mul_le_mul_left L hmn'
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

private lemma sum_lt_sum_of_four_of_all_lt {R S : Finset ℤ}
    (hR : R.card = 4) (hS : S.card = 4)
    (h : ∀ x ∈ R, ∀ y ∈ S, x < y) :
    (∑ x ∈ R, x) < ∑ y ∈ S, y := by
  let r : Fin 4 ↪o ℤ := R.orderEmbOfFin hR
  let q : Fin 4 ↪o ℤ := S.orderEmbOfFin hS
  have hrq (i : Fin 4) : r i < q i :=
    h (r i) (R.orderEmbOfFin_mem hR i) (q i) (S.orderEmbOfFin_mem hS i)
  have hsum : (∑ i : Fin 4, r i) < ∑ i : Fin 4, q i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hrq i).le
    · exact ⟨(0 : Fin 4), Finset.mem_univ _, hrq 0⟩
  rw [sum_orderEmbOfFin R 4 hR, sum_orderEmbOfFin S 4 hS] at hsum
  exact hsum

private lemma prescribedFourLayers_pairwiseDisjoint (C : Finset ℤ) (L M : ℕ)
    (hL : 0 < L) (hM : L * M ≤ C.card) :
    ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint
      (fun m ↦ restrictedSumset 4 (prescribedBlock C L M hM m)) := by
  intro m hm n hn hmn
  change Disjoint (restrictedSumset 4 (prescribedBlock C L M hM m))
    (restrictedSumset 4 (prescribedBlock C L M hM n))
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · rw [Finset.disjoint_left]
    intro z hzm hzn
    obtain ⟨R, hRB, hRcard, hRsum⟩ := mem_restrictedSumset.mp hzm
    obtain ⟨S, hSB, hScard, hSsum⟩ := mem_restrictedSumset.mp hzn
    have hsum : (∑ x ∈ R, x) < ∑ y ∈ S, y :=
      sum_lt_sum_of_four_of_all_lt hRcard hScard (fun x hx y hy ↦
        prescribedBlock_lt C L M hL hM hlt (hRB hx) (hSB hy))
    omega
  · rw [Finset.disjoint_left]
    intro z hzm hzn
    obtain ⟨R, hRB, hRcard, hRsum⟩ := mem_restrictedSumset.mp hzm
    obtain ⟨S, hSB, hScard, hSsum⟩ := mem_restrictedSumset.mp hzn
    have hsum : (∑ y ∈ S, y) < ∑ x ∈ R, x :=
      sum_lt_sum_of_four_of_all_lt hScard hRcard (fun y hy x hx ↦
        prescribedBlock_lt C L M hL hM hgt (hSB hy) (hRB hx))
    omega

private theorem exists_prescribed_small_four_block
    (C : Finset ℤ) (s L : ℕ) (hCcard : C.card = s + 4)
    (hL : 0 < L) (hLsmall : 200 * L ≤ s)
    (hCsmall : 100 * (restrictedSumset 4 C).card < 577 * s) :
    ∃ B : Finset ℤ, B ⊆ C ∧ B.card = L ∧
      5 * (restrictedSumset 4 B).card < 29 * L := by
  let M := (s + 4) / L
  have hMpos : 0 < M := by
    apply Nat.div_pos
    · omega
    · omega
  have hMbound : L * M ≤ C.card := by
    rw [hCcard]
    simpa [M, Nat.mul_comm] using Nat.div_mul_le_self (s + 4) L
  have hcount :
      ∑ m : Fin M, (restrictedSumset 4 (prescribedBlock C L M hMbound m)).card ≤
        (restrictedSumset 4 C).card := by
    exact sum_card_le_card_of_pairwiseDisjoint_subset
      (Finset.univ : Finset (Fin M))
      (fun m ↦ restrictedSumset 4 (prescribedBlock C L M hMbound m))
      (restrictedSumset 4 C) (prescribedFourLayers_pairwiseDisjoint C L M hL hMbound)
      (fun m hm ↦ restrictedSumset_mono_smallFour
        (prescribedBlock_subset C L M hMbound m))
  obtain ⟨m, hm⟩ := exists_fin_mul_le_of_sum_le hMpos
    (fun m : Fin M ↦ (restrictedSumset 4 (prescribedBlock C L M hMbound m)).card)
    hcount
  let B := prescribedBlock C L M hMbound m
  have hBsub : B ⊆ C := prescribedBlock_subset C L M hMbound m
  have hBcard : B.card = L := prescribedBlock_card C L M hMbound m
  refine ⟨B, hBsub, hBcard, ?_⟩
  have hmod := Nat.mod_lt (s + 4) hL
  have hdecomp := Nat.mod_add_div (s + 4) L
  have hML : 577 * s ≤ 580 * (L * M) := by
    dsimp [M]
    nlinarith
  dsimp [B] at hm ⊢
  nlinarith

/-! ## DF95 Proposition 2 -/

/-- Deshouillers--Freiman Proposition 2, in an exact finite form.  The
hypothesis `hsmall` is precisely the output of their Proposition 1 (formalized
in `LayerSelection.lean`). -/
theorem exists_df95_small_four_layer
    (A : Finset ℤ) (s L : ℕ)
    (hslow : A.card / 10 ≤ s) (hshi : s ≤ 3 * A.card / 4)
    (hsmall : 25 * (restrictedSumset s A).card < 36 * s * (A.card - s))
    (hsLarge : 1000 ≤ s) (hJLarge : 1000 ≤ (A.card - s) / 4)
    (hL : 0 < L) (hLcard : 2000 * L ≤ A.card) :
    ∃ B : Finset ℤ, B ⊆ A ∧ B.card = L ∧
      5 * (restrictedSumset 4 B).card < 29 * L := by
  have hsA : s ≤ A.card := by
    have hdiv := Nat.div_mul_le_self (3 * A.card) 4
    omega
  obtain ⟨C, hCA, hCcard, hCsmall⟩ :=
    exists_small_four_window A s hsA hsmall hsLarge hJLarge
  have hLsmall : 200 * L ≤ s := by
    have hmod := Nat.mod_lt A.card (by decide : 0 < 10)
    have hdecomp := Nat.mod_add_div A.card 10
    omega
  obtain ⟨B, hBC, hBcard, hBsmall⟩ :=
    exists_prescribed_small_four_block C s L hCcard hL hLsmall hCsmall
  exact ⟨B, hBC.trans hCA, hBcard, hBsmall⟩

end

end Erdos874
