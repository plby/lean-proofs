/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.LevMultipleAddition

/-!
# Normalizing integer summands for Lev's theorem

This file supplies the bridge from arbitrary nonempty integer finsets to the
normalized natural-number theorem in `LevMultipleAddition`.
-/

open Finset Nat
open scoped Pointwise BigOperators

namespace Erdos186.CFP.LevNormalization

open Erdos13Additive
open LevMultipleAddition

/-- The integral diameter of a nonempty integer finset. -/
def intDiameter (S : Finset ℤ) (hS : S.Nonempty) : ℕ :=
  (S.max' hS - S.min' hS).toNat

/-- Source-faithful primitivity: no modulus at least two divides every
pairwise difference. -/
def IntPrimitive (S : Finset ℤ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ x ∈ S, ∃ y ∈ S, ¬ (d : ℤ) ∣ x - y

/-- Translate a nonempty integer finset to start at zero, then view it in
the natural numbers. -/
noncomputable def normalizeInt (S : Finset ℤ) (hS : S.Nonempty) : Finset ℕ :=
  S.image fun x ↦ (x - S.min' hS).toNat

lemma cast_normalized_value {S : Finset ℤ} (hS : S.Nonempty)
    {x : ℤ} (hx : x ∈ S) :
    (((x - S.min' hS).toNat : ℕ) : ℤ) = x - S.min' hS := by
  rw [Int.toNat_of_nonneg]
  exact sub_nonneg.mpr (Finset.min'_le S x hx)

@[simp] lemma card_normalizeInt (S : Finset ℤ) (hS : S.Nonempty) :
    (normalizeInt S hS).card = S.card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hxy
  rw [cast_normalized_value hS hx, cast_normalized_value hS hy] at hcast
  omega

lemma zero_mem_normalizeInt (S : Finset ℤ) (hS : S.Nonempty) :
    0 ∈ normalizeInt S hS := by
  apply mem_image.mpr
  refine ⟨S.min' hS, Finset.min'_mem S hS, ?_⟩
  simp

lemma diameter_mem_normalizeInt (S : Finset ℤ) (hS : S.Nonempty) :
    intDiameter S hS ∈ normalizeInt S hS := by
  apply mem_image.mpr
  exact ⟨S.max' hS, Finset.max'_mem S hS, rfl⟩

lemma normalizeInt_subset_Icc (S : Finset ℤ) (hS : S.Nonempty) :
    normalizeInt S hS ⊆ Icc 0 (intDiameter S hS) := by
  intro n hn
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
  simp only [mem_Icc, zero_le, true_and]
  apply Int.toNat_le_toNat
  exact sub_le_sub_right (Finset.le_max' S x hx) _

/-- Primitivity is precisely the gcd-one condition after normalization. -/
theorem gcd_normalizeInt_eq_one {S : Finset ℤ} (hS : S.Nonempty)
    (hprim : IntPrimitive S) :
    (normalizeInt S hS).gcd (fun n ↦ (n : ℤ)) = 1 := by
  let N := normalizeInt S hS
  let g : ℤ := N.gcd (fun n ↦ (n : ℤ))
  have hg0 : 0 ≤ g := by
    simpa [g] using (Int.finsetGcd_nonneg (s := N) (f := fun n : ℕ ↦ (n : ℤ)))
  by_contra hg1
  have hg1g : g ≠ 1 := by simpa [g, N] using hg1
  have hcases : g = 0 ∨ 2 ≤ g := by omega
  rcases hcases with hg | hg
  · obtain ⟨x, hx, y, hy, hxy⟩ := hprim 2 (by omega)
    have hxN : (x - S.min' hS).toNat ∈ N :=
      mem_image.mpr ⟨x, hx, rfl⟩
    have hyN : (y - S.min' hS).toNat ∈ N :=
      mem_image.mpr ⟨y, hy, rfl⟩
    have hxd := Finset.gcd_dvd (f := fun n : ℕ ↦ (n : ℤ)) hxN
    have hyd := Finset.gcd_dvd (f := fun n : ℕ ↦ (n : ℤ)) hyN
    change g ∣ (((x - S.min' hS).toNat : ℕ) : ℤ) at hxd
    change g ∣ (((y - S.min' hS).toNat : ℕ) : ℤ) at hyd
    rw [hg] at hxd hyd
    have hxzero : x - S.min' hS = 0 := by
      rw [← cast_normalized_value hS hx]
      simpa using hxd
    have hyzero : y - S.min' hS = 0 := by
      rw [← cast_normalized_value hS hy]
      simpa using hyd
    apply hxy
    use 0
    omega
  · let d := g.toNat
    have hd : 2 ≤ d := by
      rw [← Int.ofNat_le]
      simpa [d, Int.toNat_of_nonneg hg0] using hg
    obtain ⟨x, hx, y, hy, hxy⟩ := hprim d hd
    have hxN : (x - S.min' hS).toNat ∈ N :=
      mem_image.mpr ⟨x, hx, rfl⟩
    have hyN : (y - S.min' hS).toNat ∈ N :=
      mem_image.mpr ⟨y, hy, rfl⟩
    have hxd := Finset.gcd_dvd (f := fun n : ℕ ↦ (n : ℤ)) hxN
    have hyd := Finset.gcd_dvd (f := fun n : ℕ ↦ (n : ℤ)) hyN
    change g ∣ (((x - S.min' hS).toNat : ℕ) : ℤ) at hxd
    change g ∣ (((y - S.min' hS).toNat : ℕ) : ℤ) at hyd
    have hdcast : (d : ℤ) = g := by
      simp [d, Int.toNat_of_nonneg hg0]
    rw [cast_normalized_value hS hx, ← hdcast] at hxd
    rw [cast_normalized_value hS hy, ← hdcast] at hyd
    apply hxy
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hxd hyd

/-- A normalized set lying in `[0,L]` loses at most its two identified
endpoints on reduction modulo `L`. -/
lemma card_pred_le_card_modImage {S : Finset ℕ} {L : ℕ}
    (_hL : 0 < L) (hS : S ⊆ Icc 0 L) :
    S.card - 1 ≤ (modImage S L).card := by
  by_cases hLS : L ∈ S
  · have hinj : Set.InjOn (fun x : ℕ ↦ (x : ZMod L)) (S.erase L) :=
      (natCast_injOn_Ico (v := L)).mono (erase_top_subset_Ico hS)
    have hcard : (S.erase L).card = S.card - 1 := card_erase_of_mem hLS
    calc
      S.card - 1 = (S.erase L).card := hcard.symm
      _ = (modImage (S.erase L) L).card := (card_image_iff.mpr hinj).symm
      _ ≤ (modImage S L).card := by
        apply card_le_card
        intro c hc
        obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
        exact mem_modImage.mpr ⟨x, mem_of_mem_erase hx, hxc⟩
  · have hinj : Set.InjOn (fun x : ℕ ↦ (x : ZMod L)) S := by
      apply (natCast_injOn_Ico (v := L)).mono
      intro x hx
      have hxI := mem_Icc.mp (hS hx)
      exact mem_Ico.mpr ⟨hxI.1, lt_of_le_of_ne hxI.2 (Ne.symm (by
        intro h
        exact hLS (h ▸ hx)))⟩
    have hc : (modImage S L).card = S.card := card_image_iff.mpr hinj
    omega

/-! ## Sumset cardinality under independent normalization -/

def castNatSet (S : Finset ℕ) : Finset ℤ :=
  Finset.image (fun n : ℕ ↦ (n : ℤ)) S

def translateInt (S : Finset ℤ) (a : ℤ) : Finset ℤ :=
  S.image fun x ↦ x + a

@[simp] lemma card_castNatSet (S : Finset ℕ) : (castNatSet S).card = S.card := by
  exact Finset.card_image_of_injective S Int.ofNat_injective

@[simp] lemma card_translateInt (S : Finset ℤ) (a : ℤ) :
    (translateInt S a).card = S.card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact add_right_cancel h

lemma castNatSet_add (A B : Finset ℕ) :
    castNatSet (A + B) = castNatSet A + castNatSet B := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hnz⟩ := mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hn
    apply Finset.mem_add.mpr
    refine ⟨(a : ℤ), mem_image.mpr ⟨a, ha, rfl⟩,
      (b : ℤ), mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    simpa using hnz
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨a + b, Finset.add_mem_add ha hb, by simp⟩

lemma translateInt_add (A B : Finset ℤ) (a b : ℤ) :
    translateInt A a + translateInt B b = translateInt (A + B) (a + b) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    apply mem_image.mpr
    refine ⟨u + v, Finset.add_mem_add hu hv, by ring⟩
  · intro hz
    obtain ⟨w, hw, hwz⟩ := mem_image.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hw
    apply Finset.mem_add.mpr
    refine ⟨u + a, mem_image.mpr ⟨u, hu, rfl⟩,
      v + b, mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [← hwz]
    ring

lemma castNatSet_normalizeInt (S : Finset ℤ) (hS : S.Nonempty) :
    castNatSet (normalizeInt S hS) =
      translateInt S (-S.min' hS) := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hnz⟩ := mem_image.mp hz
    obtain ⟨x, hx, hxn⟩ := mem_image.mp hn
    apply mem_image.mpr
    refine ⟨x, hx, ?_⟩
    rw [← hnz, ← hxn]
    rw [cast_normalized_value hS hx]
    ring
  · intro hz
    obtain ⟨x, hx, hxz⟩ := mem_image.mp hz
    apply mem_image.mpr
    refine ⟨(x - S.min' hS).toNat,
      mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    rw [cast_normalized_value hS hx]
    simpa only [sub_eq_add_neg] using hxz

noncomputable def normalizeIntList :
    (As : List (Finset ℤ)) →
      (∀ A ∈ As, A.Nonempty) → List (Finset ℕ)
  | [], _ => []
  | A :: As, h =>
      normalizeInt A (h A (by simp)) ::
        normalizeIntList As (fun B hB ↦ h B (by simp [hB]))

noncomputable def normalizeShift :
    (As : List (Finset ℤ)) →
      (∀ A ∈ As, A.Nonempty) → ℤ
  | [], _ => 0
  | A :: As, h =>
      -A.min' (h A (by simp)) +
        normalizeShift As (fun B hB ↦ h B (by simp [hB]))

@[simp] lemma normalizeIntList_nil
    (h : ∀ A ∈ ([] : List (Finset ℤ)), A.Nonempty) :
    normalizeIntList [] h = [] := rfl

@[simp] lemma normalizeIntList_cons (A : Finset ℤ) (As : List (Finset ℤ))
    (h : ∀ B ∈ A :: As, B.Nonempty) :
    normalizeIntList (A :: As) h =
      normalizeInt A (h A (by simp)) ::
        normalizeIntList As (fun B hB ↦ h B (by simp [hB])) := rfl

@[simp] lemma normalizeShift_nil
    (h : ∀ A ∈ ([] : List (Finset ℤ)), A.Nonempty) :
    normalizeShift [] h = 0 := rfl

@[simp] lemma normalizeShift_cons (A : Finset ℤ) (As : List (Finset ℤ))
    (h : ∀ B ∈ A :: As, B.Nonempty) :
    normalizeShift (A :: As) h =
      -A.min' (h A (by simp)) +
        normalizeShift As (fun B hB ↦ h B (by simp [hB])) := rfl

lemma castNatSet_listSumset (As : List (Finset ℕ)) :
    castNatSet (listSumset As) = listSumset (As.map castNatSet) := by
  induction As with
  | nil =>
      ext z
      simp [castNatSet, listSumset]
  | cons A As ih =>
      simp only [listSumset_cons, List.map_cons, castNatSet_add, ih]

theorem castNatSet_listSumset_normalizeIntList
    (As : List (Finset ℤ)) (hAs : ∀ A ∈ As, A.Nonempty) :
    castNatSet (listSumset (normalizeIntList As hAs)) =
      translateInt (listSumset As) (normalizeShift As hAs) := by
  induction As with
  | nil =>
      ext z
      simp [castNatSet, translateInt, listSumset]
  | cons A As ih =>
      have hA : A.Nonempty := hAs A (by simp)
      have htail : ∀ B ∈ As, B.Nonempty :=
        fun B hB ↦ hAs B (by simp [hB])
      rw [normalizeIntList_cons, listSumset_cons, castNatSet_add,
        castNatSet_normalizeInt, ih htail, translateInt_add]
      rfl

@[simp] theorem card_listSumset_normalizeIntList
    (As : List (Finset ℤ)) (hAs : ∀ A ∈ As, A.Nonempty) :
    (listSumset (normalizeIntList As hAs)).card = (listSumset As).card := by
  have h := congrArg Finset.card
    (castNatSet_listSumset_normalizeIntList As hAs)
  simpa using h

@[simp] theorem length_normalizeIntList
    (As : List (Finset ℤ)) (hAs : ∀ A ∈ As, A.Nonempty) :
    (normalizeIntList As hAs).length = As.length := by
  induction As with
  | nil => rfl
  | cons A As ih =>
      simp only [normalizeIntList_cons, List.length_cons]
      rw [ih]

theorem zero_mem_of_mem_normalizeIntList
    (As : List (Finset ℤ)) (hAs : ∀ A ∈ As, A.Nonempty) :
    ∀ N ∈ normalizeIntList As hAs, 0 ∈ N := by
  induction As with
  | nil => simp
  | cons A As ih =>
      intro N hN
      simp only [normalizeIntList_cons, List.mem_cons] at hN
      rcases hN with rfl | hN
      · exact zero_mem_normalizeInt A (hAs A (by simp))
      · exact ih (fun B hB ↦ hAs B (by simp [hB])) N hN

lemma intDiameter_eq_sub (S : Finset ℤ) (hS : S.Nonempty) :
    (intDiameter S hS : ℤ) = S.max' hS - S.min' hS := by
  rw [intDiameter, Int.toNat_of_nonneg]
  exact sub_nonneg.mpr
    (Finset.min'_le S _ (Finset.max'_mem S hS))

lemma intDiameter_pos_of_primitive {S : Finset ℤ} (hS : S.Nonempty)
    (hprim : IntPrimitive S) : 0 < intDiameter S hS := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hprim 2 (by omega)
  have hxmin := Finset.min'_le S x hx
  have hxmax := Finset.le_max' S x hx
  have hymin := Finset.min'_le S y hy
  have hymax := Finset.le_max' S y hy
  have hdiam := intDiameter_eq_sub S hS
  by_contra hn
  have : intDiameter S hS = 0 := by omega
  have hxyEq : x = y := by omega
  subst y
  apply hxy
  simp

theorem sum_card_modImage_normalizeIntList_ge
    (As : List (Finset ℤ)) (hAs : ∀ A ∈ As, A.Nonempty)
    {L n : ℕ} (hL : 0 < L)
    (hdiam : ∀ A (hA : A ∈ As), intDiameter A (hAs A hA) ≤ L)
    (hcard : ∀ A ∈ As, n ≤ A.card) :
    As.length * (n - 1) ≤
      ((normalizeIntList As hAs).map fun N ↦ (modImage N L).card).sum := by
  induction As with
  | nil => simp
  | cons A As ih =>
      have hA : A.Nonempty := hAs A (by simp)
      have htail : ∀ B ∈ As, B.Nonempty :=
        fun B hB ↦ hAs B (by simp [hB])
      have hsub : normalizeInt A hA ⊆ Icc 0 L := by
        intro x hx
        have hxI := mem_Icc.mp (normalizeInt_subset_Icc A hA hx)
        exact mem_Icc.mpr ⟨hxI.1,
          hxI.2.trans (hdiam A (by simp))⟩
      have hmod := card_pred_le_card_modImage hL hsub
      have hhead : n - 1 ≤ (modImage (normalizeInt A hA) L).card := by
        rw [card_normalizeInt] at hmod
        exact (Nat.sub_le_sub_right (hcard A (by simp)) 1).trans hmod
      have htailBound := ih htail
        (fun B hB ↦ hdiam B (by simp [hB]))
        (fun B hB ↦ hcard B (by simp [hB]))
      simp only [normalizeIntList_cons, List.map_cons, List.sum_cons,
        List.length_cons, Nat.succ_mul]
      omega

/-! ## The arbitrary-integer one-step theorem -/

/-- Source-shaped one-step consequence of Lev's theorem.  The last summand
`A` has maximal diameter, every summand has at least `n` elements, and `A`
is primitive. -/
theorem lev1997_increment_int {A : Finset ℤ} (As : List (Finset ℤ))
    {n : ℕ} (hn : 2 ≤ n) (hA : A.Nonempty)
    (hAs : ∀ B ∈ As, B.Nonempty)
    (hprim : IntPrimitive A)
    (hdiam : ∀ B (hB : B ∈ As),
      intDiameter B (hAs B hB) ≤ intDiameter A hA)
    (hcardA : n ≤ A.card)
    (hcards : ∀ B ∈ As, n ≤ B.card) :
    (listSumset As).card +
        min (intDiameter A hA) ((As.length + 1) * (n - 2) + 1) ≤
      (listSumset As + A).card := by
  let L := intDiameter A hA
  let NA := normalizeInt A hA
  let NAs := normalizeIntList As hAs
  have hL : 0 < L := intDiameter_pos_of_primitive hA hprim
  have hNA0 : 0 ∈ NA := zero_mem_normalizeInt A hA
  have hNAL : L ∈ NA := diameter_mem_normalizeInt A hA
  have hgcd : NA.gcd (fun m ↦ (m : ℤ)) = 1 :=
    gcd_normalizeInt_eq_one hA hprim
  have hNAs0 : ∀ B ∈ NAs, 0 ∈ B :=
    zero_mem_of_mem_normalizeIntList As hAs
  have hcore := lev1997_increment NAs hL hNA0 hNAL hgcd hNAs0
  have hNAlength : NAs.length = As.length := length_normalizeIntList As hAs
  have hNAsResidue : As.length * (n - 1) ≤
      (NAs.map fun B ↦ (modImage B L).card).sum := by
    exact sum_card_modImage_normalizeIntList_ge As hAs hL hdiam hcards
  have hNAsub : NA ⊆ Icc 0 L := normalizeInt_subset_Icc A hA
  have hNAmod0 := card_pred_le_card_modImage hL hNAsub
  have hNAmod : n - 1 ≤ (modImage NA L).card := by
    rw [card_normalizeInt] at hNAmod0
    exact (Nat.sub_le_sub_right hcardA 1).trans hNAmod0
  have hresidue : (As.length + 1) * (n - 1) ≤
      (modImage NA L).card +
        (NAs.map fun B ↦ (modImage B L).card).sum := by
    rw [Nat.add_mul, one_mul]
    simpa [add_comm] using Nat.add_le_add hNAmod hNAsResidue
  have hnrel : n - 1 = (n - 2) + 1 := by omega
  rw [hnrel, Nat.mul_add, Nat.mul_one] at hresidue
  have htarget : (As.length + 1) * (n - 2) + 1 ≤
      (modImage NA L).card +
        (NAs.map fun B ↦ (modImage B L).card).sum -
        (NAs.length + 1) + 1 := by
    rw [hNAlength]
    omega
  have hmin : min L ((As.length + 1) * (n - 2) + 1) ≤
      min L ((modImage NA L).card +
        (NAs.map fun B ↦ (modImage B L).card).sum -
        (NAs.length + 1) + 1) := min_le_min_left L htarget
  have hprev : (listSumset NAs).card = (listSumset As).card :=
    card_listSumset_normalizeIntList As hAs
  have hAll : ∀ B ∈ A :: As, B.Nonempty := by
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hA
    · exact hAs B hB
  have htotal0 := card_listSumset_normalizeIntList (A :: As) hAll
  have htotal : (listSumset NAs + NA).card = (listSumset As + A).card := by
    have hnormCons : normalizeIntList (A :: As) hAll = NA :: NAs := by
      simp only [normalizeIntList_cons]
      rfl
    rw [hnormCons, listSumset_cons, listSumset_cons] at htotal0
    simpa only [add_comm] using htotal0
  rw [← hprev, ← htotal]
  exact (Nat.add_le_add_left hmin (listSumset NAs).card).trans hcore

/-! ## Ordered telescoping -/

/-- Diameter with the empty case assigned value zero. -/
noncomputable def finsetDiameter (A : Finset ℤ) : ℕ :=
  if hA : A.Nonempty then intDiameter A hA else 0

lemma finsetDiameter_eq {A : Finset ℤ} (hA : A.Nonempty) :
    finsetDiameter A = intDiameter A hA := by
  simp [finsetDiameter, hA]

/-- The sum of Lev's successive increments, starting with index `r`. -/
noncomputable def levWeightSumFrom (n r : ℕ) : List (Finset ℤ) → ℕ
  | [] => 0
  | A :: As =>
      min (finsetDiameter A) ((r + 1) * (n - 2) + 1) +
        levWeightSumFrom n (r + 1) As

noncomputable def levWeightSum (n : ℕ) (As : List (Finset ℤ)) : ℕ :=
  levWeightSumFrom n 0 As

lemma levWeightSumFrom_ofFn {k : ℕ} (n r : ℕ)
    (S : Fin k → Finset ℤ) :
    levWeightSumFrom n r (List.ofFn S) =
      ∑ i : Fin k,
        min (finsetDiameter (S i)) ((r + i.val + 1) * (n - 2) + 1) := by
  induction k generalizing r with
  | zero => simp [levWeightSumFrom]
  | succ k ih =>
      rw [List.ofFn_succ, levWeightSumFrom, Fin.sum_univ_succ]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hidx : r + 1 + i.val + 1 = r + i.succ.val + 1 := by
        simp only [Fin.val_succ]
        omega
      rw [hidx]

lemma levWeightSum_ofFn {k : ℕ} (n : ℕ) (S : Fin k → Finset ℤ) :
    levWeightSum n (List.ofFn S) =
      ∑ i : Fin k,
        min (finsetDiameter (S i)) ((i.val + 1) * (n - 2) + 1) := by
  simpa [levWeightSum] using levWeightSumFrom_ofFn n 0 S

lemma levWeightSumFrom_append_singleton (n r : ℕ)
    (As : List (Finset ℤ)) (A : Finset ℤ) :
    levWeightSumFrom n r (As ++ [A]) =
      levWeightSumFrom n r As +
        min (finsetDiameter A) ((r + As.length + 1) * (n - 2) + 1) := by
  induction As generalizing r with
  | nil => simp [levWeightSumFrom]
  | cons B Bs ih =>
      simp only [List.cons_append, levWeightSumFrom, List.length_cons]
      rw [ih]
      have hidx : r + 1 + Bs.length + 1 = r + (Bs.length + 1) + 1 := by omega
      rw [hidx]
      simp only [Nat.add_assoc]

lemma levWeightSum_append_singleton (n : ℕ)
    (As : List (Finset ℤ)) (A : Finset ℤ) :
    levWeightSum n (As ++ [A]) =
      levWeightSum n As +
        min (finsetDiameter A) ((As.length + 1) * (n - 2) + 1) := by
  simpa [levWeightSum] using levWeightSumFrom_append_singleton n 0 As A

/-- Telescoped ordered form of Lev's theorem.  Earlier list entries have
no larger diameter than later entries. -/
theorem lev1997_ordered_growth (As : List (Finset ℤ)) {n : ℕ}
    (hn : 2 ≤ n)
    (hne : ∀ A ∈ As, A.Nonempty)
    (hcard : ∀ A ∈ As, n ≤ A.card)
    (hprim : ∀ A ∈ As, IntPrimitive A)
    (hmono : As.Pairwise fun A B ↦ finsetDiameter A ≤ finsetDiameter B) :
    1 + levWeightSum n As ≤ (listSumset As).card := by
  induction As using List.reverseRecOn with
  | nil => simp [levWeightSum, levWeightSumFrom, listSumset]
  | append_singleton As A ih =>
      have hA : A.Nonempty := hne A (by simp)
      have hneAs : ∀ B ∈ As, B.Nonempty :=
        fun B hB ↦ hne B (by simp [hB])
      have hcardAs : ∀ B ∈ As, n ≤ B.card :=
        fun B hB ↦ hcard B (by simp [hB])
      have hprimAs : ∀ B ∈ As, IntPrimitive B :=
        fun B hB ↦ hprim B (by simp [hB])
      have hmonoParts := List.pairwise_append.mp hmono
      have hmonoAs : As.Pairwise fun B C ↦ finsetDiameter B ≤ finsetDiameter C :=
        hmonoParts.1
      have ih' := ih hneAs hcardAs hprimAs hmonoAs
      have hdiam : ∀ B (hB : B ∈ As),
          intDiameter B (hneAs B hB) ≤ intDiameter A hA := by
        intro B hB
        rw [← finsetDiameter_eq (hneAs B hB), ← finsetDiameter_eq hA]
        exact hmonoParts.2.2 B hB A (by simp)
      have hstep := lev1997_increment_int As hn hA hneAs
        (hprim A (by simp)) hdiam (hcard A (by simp)) hcardAs
      rw [levWeightSum_append_singleton, listSumset_append, listSumset_singleton]
      rw [finsetDiameter_eq hA]
      omega

/-- Fin-indexed form of the telescoped Lev bound. -/
theorem lev1997_ordered_growth_fin {k n : ℕ} (S : Fin k → Finset ℤ)
    (hn : 2 ≤ n)
    (hne : ∀ i, (S i).Nonempty)
    (hcard : ∀ i, n ≤ (S i).card)
    (hprim : ∀ i, IntPrimitive (S i))
    (hmono : ∀ ⦃i j : Fin k⦄, i < j →
      intDiameter (S i) (hne i) ≤ intDiameter (S j) (hne j)) :
    1 + ∑ i : Fin k,
        min (intDiameter (S i) (hne i)) ((i.val + 1) * (n - 2) + 1) ≤
      (listSumset (List.ofFn S)).card := by
  have hne' : ∀ A ∈ List.ofFn S, A.Nonempty :=
    List.forall_mem_ofFn_iff.mpr hne
  have hcard' : ∀ A ∈ List.ofFn S, n ≤ A.card :=
    List.forall_mem_ofFn_iff.mpr hcard
  have hprim' : ∀ A ∈ List.ofFn S, IntPrimitive A :=
    List.forall_mem_ofFn_iff.mpr hprim
  have hmono' : (List.ofFn S).Pairwise
      (fun A B ↦ finsetDiameter A ≤ finsetDiameter B) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    rw [finsetDiameter_eq (hne i), finsetDiameter_eq (hne j)]
    exact hmono hij
  have hgrowth := lev1997_ordered_growth (List.ofFn S) hn hne' hcard' hprim' hmono'
  rw [levWeightSum_ofFn] at hgrowth
  calc
    1 + ∑ i : Fin k,
        min (intDiameter (S i) (hne i)) ((i.val + 1) * (n - 2) + 1) =
        1 + ∑ i : Fin k,
          min (finsetDiameter (S i)) ((i.val + 1) * (n - 2) + 1) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            rw [finsetDiameter_eq (hne i)]
    _ ≤ (listSumset (List.ofFn S)).card := hgrowth

end Erdos186.CFP.LevNormalization
