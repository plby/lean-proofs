/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Counting combinatorial lines in finite Hales--Jewett cubes

This module supplies the exact finite counts used in the sparse-line selection
argument of Reiher--Rödl--Sales.  It deliberately separates raw line words
from proper combinatorial lines: a raw word is a function to `Option A`, and a
proper line is one whose `none` (moving-coordinate) set is nonempty.
-/

namespace Erdos847LineCounting

open Function Set
open Combinatorics

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {A : Type u} [Fintype A]

/-- Evaluation on a combinatorial line is injective when the alphabet has at least two letters. -/
lemma line_apply_injective [Nontrivial A] {n : ℕ} (l : Line A (Fin n)) :
    Function.Injective l := by
  intro a b hab
  obtain ⟨j, hj⟩ := l.proper
  have h := congrFun hab j
  simpa [Line.coe_apply, hj] using h

/-- Two values of a nontrivial alphabet determine a line as a function. -/
lemma line_eq_of_apply_eq_apply [Nontrivial A] {n : ℕ} {l m : Line A (Fin n)} {a b : A}
    (hab : a ≠ b) (ha : l a = m a) (hb : l b = m b) : l = m := by
  ext j
  have haj := congrFun ha j
  have hbj := congrFun hb j
  cases hl : l.idxFun j <;> cases hm : m.idxFun j <;>
    simp_all [Line.coe_apply]

/-- Two distinct cube points lie on at most one combinatorial line. -/
lemma line_eq_of_two_points [Nontrivial A] {n : ℕ} {l m : Line A (Fin n)}
    {a b c d : A} (hpts : l a ≠ l b) (ha : l a = m c) (hb : l b = m d) : l = m := by
  have hab : a ≠ b := fun h ↦ hpts (by simp [h])
  obtain ⟨j, hj⟩ := l.proper
  have hc : c = a := by
    have hca := congrFun ha j
    cases hm : m.idxFun j with
    | none => simpa [Line.coe_apply, hj, hm] using hca.symm
    | some z =>
        have hdb := congrFun hb j
        simp only [Line.coe_apply, hj, hm, Option.getD_none, Option.getD_some] at hca hdb
        exact (hab (hca.trans hdb.symm)).elim
  have hd : d = b := by
    have hdb := congrFun hb j
    cases hm : m.idxFun j with
    | none => simpa [Line.coe_apply, hj, hm] using hdb.symm
    | some z =>
        have hca := congrFun ha j
        simp only [Line.coe_apply, hj, hm, Option.getD_none, Option.getD_some] at hca hdb
        exact (hab (hca.trans hdb.symm)).elim
  apply line_eq_of_apply_eq_apply hab
  · simpa [hc] using ha
  · simpa [hd] using hb

/-- The cube vertices lying on a combinatorial line. -/
def linePoints {n : ℕ} (l : Line A (Fin n)) : Set (Fin n → A) := Set.range l

@[simp] lemma mem_linePoints {n : ℕ} (l : Line A (Fin n)) (x : Fin n → A) :
    x ∈ linePoints l ↔ ∃ a, l a = x := Iff.rfl

/-- Set-theoretic form: two distinct common vertices determine the line uniquely. -/
lemma line_eq_of_two_mem_points [Nontrivial A] {n : ℕ} {l m : Line A (Fin n)}
    {x y : Fin n → A} (hxy : x ≠ y)
    (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, rfl⟩
  rcases hyl with ⟨b, hby⟩
  rcases hxm with ⟨c, hca⟩
  rcases hym with ⟨d, hdy⟩
  apply line_eq_of_two_points (l := l) (m := m) (a := a) (b := b) (c := c) (d := d)
  · intro hab
    exact hxy (hab.trans hby)
  · exact hca.symm
  · exact hby.trans hdy.symm

/-- Moving coordinates of a proper Mathlib combinatorial line. -/
def movingSet {I : Type*} [Fintype I] (l : Line A I) : Finset I :=
  Finset.univ.filter fun j ↦ l.idxFun j = none

@[simp] lemma mem_movingSet {I : Type*} [Fintype I] (l : Line A I) (j : I) :
    j ∈ movingSet l ↔ l.idxFun j = none := by
  simp [movingSet]

/-- A raw line word. `none` means a moving coordinate and `some a` a fixed letter. -/
abbrev RawLine (A : Type u) (n : ℕ) := Fin n → Option A

/-- Moving coordinates of a raw line word. -/
def rawMovingSet {n : ℕ} (f : RawLine A n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ f j = none

@[simp] lemma mem_rawMovingSet {n : ℕ} (f : RawLine A n) (j : Fin n) :
    j ∈ rawMovingSet f ↔ f j = none := by
  simp [rawMovingSet]

lemma rawMovingSet_idxFun {n : ℕ} (l : Line A (Fin n)) :
    rawMovingSet l.idxFun = movingSet l := by
  ext j
  simp [rawMovingSet, movingSet]

/-- All proper combinatorial lines, stratified by moving-support cardinality. -/
noncomputable def lineStratum (n i : ℕ) : Finset (Line A (Fin n)) := by
  letI : Fintype (Line A (Fin n)) :=
    Fintype.ofInjective Line.idxFun (by
      intro l m h
      cases l
      cases m
      simp_all)
  exact Finset.univ.filter fun l ↦ (movingSet l).card = i

@[simp] lemma mem_lineStratum {n i : ℕ} {l : Line A (Fin n)} :
    l ∈ lineStratum (A := A) n i ↔ (movingSet l).card = i := by
  simp [lineStratum]

/-- An `i`-element coordinate support, represented as an element of a finite powerset slice. -/
abbrev Support (n i : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard i)

/-- The fixed letters on the complement of a support. -/
abbrev FixedWord (S : Finset (Fin n)) := ({j : Fin n // j ∉ S} → A)

/-- A support together with all fixed letters is the canonical code for a line. -/
abbrev LineCode (A : Type u) [Fintype A] (n i : ℕ) :=
  Σ S : Support n i, FixedWord (A := A) S.1

lemma support_card (S : Support n i) : S.1.card = i :=
  (Finset.mem_powersetCard.mp S.2).2

lemma fixedWord_card (S : Finset (Fin n)) :
    Fintype.card (FixedWord (A := A) S) = Fintype.card A ^ (n - S.card) := by
  rw [Fintype.card_congr (Equiv.refl _)]
  simp only [FixedWord, Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  simp

lemma support_type_card (n i : ℕ) :
    Fintype.card (Support n i) = Nat.choose n i := by
  simp [Support]

lemma lineCode_card (n i : ℕ) :
    Fintype.card (LineCode A n i) = Nat.choose n i * Fintype.card A ^ (n - i) := by
  rw [Fintype.card_sigma]
  simp_rw [fixedWord_card, support_card]
  rw [Finset.sum_const]
  simp [support_type_card]

/-- Decode a canonical support/fixed-word code into a proper combinatorial line. -/
def lineOfCode {n i : ℕ} (hi : 0 < i) (c : LineCode A n i) : Line A (Fin n) where
  idxFun j := if h : j ∈ c.1.1 then none else some (c.2 ⟨j, h⟩)
  proper := by
    have hcard : c.1.1.card = i := support_card c.1
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (hcard.symm ▸ hi)
    exact ⟨j, dif_pos hj⟩

@[simp] lemma lineOfCode_idxFun_none_iff {n i : ℕ} (hi : 0 < i) (c : LineCode A n i)
    (j : Fin n) : (lineOfCode hi c).idxFun j = none ↔ j ∈ c.1.1 := by
  simp [lineOfCode]

lemma movingSet_lineOfCode {n i : ℕ} (hi : 0 < i) (c : LineCode A n i) :
    movingSet (lineOfCode hi c) = c.1.1 := by
  ext j
  simp [lineOfCode]

lemma lineOfCode_injective {n i : ℕ} (hi : 0 < i) :
    Function.Injective (lineOfCode (A := A) (n := n) hi) := by
  rintro ⟨S, w⟩ ⟨T, v⟩ hline
  have hSTval : S.1 = T.1 := by
    rw [← movingSet_lineOfCode hi ⟨S, w⟩, ← movingSet_lineOfCode hi ⟨T, v⟩, hline]
  have hST : S = T := Subtype.ext hSTval
  subst T
  congr 1
  funext j
  have hidx := congrArg (fun l : Line A (Fin n) ↦ l.idxFun j.1) hline
  simp only [lineOfCode, j.2, dite_false, Option.some.injEq] at hidx
  exact hidx

/-- A coordinate outside the moving support carries a fixed letter. -/
lemma idxFun_isSome_of_not_mem_movingSet {n : ℕ} (l : Line A (Fin n))
    (j : {j : Fin n // j ∉ movingSet l}) : (l.idxFun j.1).isSome := by
  cases h : l.idxFun j.1 with
  | none => exact (j.2 ((mem_movingSet l j.1).2 h)).elim
  | some a => simp

/-- The fixed letter of a line at a coordinate outside its moving support. -/
def fixedLetter {n : ℕ} (l : Line A (Fin n)) (j : {j : Fin n // j ∉ movingSet l}) : A :=
  (l.idxFun j.1).get (idxFun_isSome_of_not_mem_movingSet l j)

@[simp] lemma fixedLetter_spec {n : ℕ} (l : Line A (Fin n))
    (j : {j : Fin n // j ∉ movingSet l}) : l.idxFun j.1 = some (fixedLetter l j) := by
  exact (Option.coe_get (idxFun_isSome_of_not_mem_movingSet l j)).symm

/-- Encode a line in the `i`th stratum by its moving support and fixed word. -/
def codeOfStratum {n i : ℕ} (l : ↥(lineStratum (A := A) n i)) : LineCode A n i :=
  ⟨⟨movingSet l.1, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (mem_lineStratum.mp l.2)⟩⟩,
    fixedLetter l.1⟩

lemma lineOfCode_codeOfStratum {n i : ℕ} (hi : 0 < i)
    (l : ↥(lineStratum (A := A) n i)) : lineOfCode hi (codeOfStratum l) = l.1 := by
  apply Line.ext
  funext j
  by_cases hj : j ∈ movingSet l.1
  · have hnone := (mem_movingSet l.1 j).mp hj
    simp [lineOfCode, codeOfStratum, hj, hnone]
  · have hsome := fixedLetter_spec l.1 ⟨j, hj⟩
    simp [lineOfCode, codeOfStratum, hj, hsome]

/-- Exact number of proper combinatorial lines with `i` moving coordinates. -/
theorem card_lineStratum {n i : ℕ} (hi : 0 < i) :
    (lineStratum (A := A) n i).card =
      Nat.choose n i * Fintype.card A ^ (n - i) := by
  let f := lineOfCode (A := A) (n := n) hi
  have himage : (Finset.univ : Finset (LineCode A n i)).image f = lineStratum (A := A) n i := by
    ext l
    constructor
    · intro hl
      rcases Finset.mem_image.mp hl with ⟨c, -, rfl⟩
      exact mem_lineStratum.mpr (by rw [movingSet_lineOfCode, support_card])
    · intro hl
      let l' : ↥(lineStratum (A := A) n i) := ⟨l, hl⟩
      exact Finset.mem_image.mpr ⟨codeOfStratum l', Finset.mem_univ _,
        lineOfCode_codeOfStratum hi l'⟩
  rw [← himage, Finset.card_image_of_injective _ (lineOfCode_injective hi),
    Finset.card_univ, lineCode_card]

/-- Lines in a support stratum which contain a specified cube point. -/
noncomputable def linesThrough {n : ℕ} (x : Fin n → A) (i : ℕ) :
    Finset (Line A (Fin n)) :=
  (lineStratum (A := A) n i).filter fun l ↦ ∃ a, l a = x

@[simp] lemma mem_linesThrough {n i : ℕ} {x : Fin n → A} {l : Line A (Fin n)} :
    l ∈ linesThrough x i ↔ (movingSet l).card = i ∧ ∃ a, l a = x := by
  simp [linesThrough]

lemma line_eq_of_movingSet_eq_of_point {n : ℕ} {x : Fin n → A}
    {l m : Line A (Fin n)} (hS : movingSet l = movingSet m)
    (hl : ∃ a, l a = x) (hm : ∃ b, m b = x) : l = m := by
  rcases hl with ⟨a, ha⟩
  rcases hm with ⟨b, hb⟩
  apply Line.ext
  funext j
  have hnone : l.idxFun j = none ↔ m.idxFun j = none := by
    rw [← mem_movingSet, ← mem_movingSet, hS]
  cases hlopt : l.idxFun j with
  | none => exact (hnone.mp hlopt).symm
  | some c =>
      cases hmopt : m.idxFun j with
      | none => exact ((Option.some_ne_none c) (hlopt.symm.trans (hnone.mpr hmopt))).elim
      | some d =>
          have hc := congrFun ha j
          have hd := congrFun hb j
          simp only [Line.coe_apply, hlopt, hmopt, Option.getD_some] at hc hd
          exact congrArg some (hc.trans hd.symm)

lemma movingSet_injectiveOn_linesThrough {n i : ℕ} (x : Fin n → A) :
    Set.InjOn movingSet (linesThrough x i : Set (Line A (Fin n))) := by
  intro l hl m hm hS
  exact line_eq_of_movingSet_eq_of_point hS (mem_linesThrough.mp hl).2 (mem_linesThrough.mp hm).2

/-- A fixed cube point lies on at most `choose n i` lines with support size `i`. -/
theorem card_linesThrough_le (x : Fin n → A) (i : ℕ) :
    (linesThrough x i).card ≤ Nat.choose n i := by
  calc
    (linesThrough x i).card = ((linesThrough x i).image movingSet).card :=
      (Finset.card_image_of_injOn (movingSet_injectiveOn_linesThrough x)).symm
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard i).card := Finset.card_le_card (by
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨l, hl, rfl⟩
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (mem_linesThrough.mp hl).1⟩)
    _ = Nat.choose n i := by simp

/-! ## Subcube and extension multiplicities

An `m`-dimensional coordinate subcube is canonically encoded by its `m` moving coordinates and
one fixed letter on every complementary coordinate.  This representation avoids the `|A|^m`
overcount caused by representing a subcube by an arbitrary ambient point.
-/

/-- Canonical codes for `m`-dimensional coordinate subcubes of `A^(Fin n)`. -/
abbrev SubcubeCode (A : Type u) [Fintype A] (n m : ℕ) := LineCode A n m

/-- Exact number of `m`-dimensional coordinate subcubes. -/
theorem card_subcubeCode (n m : ℕ) :
    Fintype.card (SubcubeCode A n m) =
      Nat.choose n m * Fintype.card A ^ (n - m) :=
  lineCode_card n m

/-- The candidate `m`-coordinate supports which extend the moving support of `l`. -/
noncomputable def extensionSupports {n : ℕ} (l : Line A (Fin n)) (m : ℕ) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard m).filter (movingSet l ⊆ ·)

@[simp] lemma mem_extensionSupports {n m : ℕ} {l : Line A (Fin n)}
    {M : Finset (Fin n)} :
    M ∈ extensionSupports l m ↔ M ⊆ Finset.univ ∧ M.card = m ∧ movingSet l ⊆ M := by
  simp [extensionSupports, and_assoc]

/-- A support of size `i` has exactly `choose (n-i) (m-i)` extensions of size `m`. -/
theorem card_extensionSupports {n i m : ℕ} (l : Line A (Fin n))
    (hi : (movingSet l).card = i) (him : i ≤ m) :
    (extensionSupports l m).card = Nat.choose (n - i) (m - i) := by
  rw [extensionSupports,
    Finset.card_filter_powersetCard_subset (movingSet l) Finset.univ m
      (Finset.subset_univ _) (hi.symm ▸ him)]
  simp [hi]

/-- A canonical subcube contains a line when it moves on every moving coordinate of the line and
agrees with the line's fixed letters outside the subcube support. -/
def SubcubeContainsLine {n m : ℕ} (Q : SubcubeCode A n m) (l : Line A (Fin n)) : Prop :=
  movingSet l ⊆ Q.1.1 ∧
    ∀ j : {j : Fin n // j ∉ Q.1.1}, l.idxFun j.1 = some (Q.2 j)

/-- All canonical `m`-subcubes containing a given line. -/
noncomputable def subcubesContaining {n : ℕ} (l : Line A (Fin n)) (m : ℕ) :
    Finset (SubcubeCode A n m) :=
  Finset.univ.filter fun Q ↦ SubcubeContainsLine Q l

@[simp] lemma mem_subcubesContaining {n m : ℕ} {l : Line A (Fin n)}
    {Q : SubcubeCode A n m} :
    Q ∈ subcubesContaining l m ↔ SubcubeContainsLine Q l := by
  simp [subcubesContaining]

/-- Projection to the moving-coordinate support of a canonical subcube. -/
def subcubeSupport {n m : ℕ} (Q : SubcubeCode A n m) : Finset (Fin n) := Q.1.1

lemma subcubeSupport_injectiveOn_containing {n m : ℕ} (l : Line A (Fin n)) :
    Set.InjOn subcubeSupport (subcubesContaining l m : Set (SubcubeCode A n m)) := by
  rintro ⟨M, w⟩ hQ ⟨N, v⟩ hR hMN
  have hMN' : M = N := Subtype.ext hMN
  subst N
  congr 1
  funext j
  have hw := (mem_subcubesContaining.mp hQ).2 j
  have hv := (mem_subcubesContaining.mp hR).2 j
  exact Option.some.inj (hw.symm.trans hv)

/-- The unique canonical subcube with support `M` which contains `l`. -/
def subcubeOfExtension {n m : ℕ} (l : Line A (Fin n)) (M : Support n m)
    (hSM : movingSet l ⊆ M.1) : SubcubeCode A n m :=
  ⟨M, fun j ↦ fixedLetter l ⟨j.1, fun hj ↦ j.2 (hSM hj)⟩⟩

lemma subcubeOfExtension_contains {n m : ℕ} (l : Line A (Fin n)) (M : Support n m)
    (hSM : movingSet l ⊆ M.1) : SubcubeContainsLine (subcubeOfExtension l M hSM) l := by
  refine ⟨hSM, ?_⟩
  intro j
  exact fixedLetter_spec l ⟨j.1, fun hj ↦ j.2 (hSM hj)⟩

/-- Exact line--subcube incidence multiplicity from RRS Claim 3.8. -/
theorem card_subcubesContaining {n i m : ℕ} (l : Line A (Fin n))
    (hi : (movingSet l).card = i) (him : i ≤ m) :
    (subcubesContaining l m).card = Nat.choose (n - i) (m - i) := by
  have himage : (subcubesContaining l m).image subcubeSupport = extensionSupports l m := by
    ext M
    constructor
    · intro hM
      rcases Finset.mem_image.mp hM with ⟨Q, hQ, rfl⟩
      exact mem_extensionSupports.mpr
        ⟨Finset.subset_univ _, support_card Q.1, (mem_subcubesContaining.mp hQ).1⟩
    · intro hM
      have hdata := mem_extensionSupports.mp hM
      let MS : Support n m :=
        ⟨M, Finset.mem_powersetCard.mpr ⟨hdata.1, hdata.2.1⟩⟩
      let Q : SubcubeCode A n m := subcubeOfExtension l MS hdata.2.2
      exact Finset.mem_image.mpr
        ⟨Q, mem_subcubesContaining.mpr (subcubeOfExtension_contains l MS hdata.2.2), rfl⟩
  calc
    (subcubesContaining l m).card =
        ((subcubesContaining l m).image subcubeSupport).card :=
      (Finset.card_image_of_injOn (subcubeSupport_injectiveOn_containing l)).symm
    _ = (extensionSupports l m).card := congrArg Finset.card himage
    _ = Nat.choose (n - i) (m - i) := card_extensionSupports l hi him

/-- The binomial double-counting identity behind the line/subcube incidence argument. -/
lemma choose_subcube_incidence (n m i : ℕ) (him : i ≤ m) :
    Nat.choose n m * Nat.choose m i =
      Nat.choose n i * Nat.choose (n - i) (m - i) :=
  Nat.choose_mul him

end Erdos847LineCounting
