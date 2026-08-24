/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 606.
https://www.erdosproblems.com/forum/thread/606

Informal authors:
- Paul Erdős
- Peter Salamon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos606.md
-/
import ErdosProblems.Erdos606.PlanarIncidence

/-!
# Erdős Problem 606: possible numbers of determined lines

For a finite set `P` of points in the real affine plane, `lineCount P` is the
number of affine lines containing at least two points of `P`.  The main theorem
`erdos_606` gives the eventual Erdős--Salamon classification of all possible
values.

Mathematical sources:

* P. Salamon and P. Erdős, *The solution to a problem of Grünbaum*,
  Canadian Mathematical Bulletin 31 (1988), 129--138.
* P. Erdős, *On a problem of Grunbaum*, Canadian Mathematical Bulletin 15
  (1972), 23--25.
* J. Beck, *On the lattice property of the plane and some problems of Dirac,
  Motzkin and Erdős in combinatorial geometry*, Combinatorica 3 (1983),
  281--297.

The detailed reconstruction and Leanization plan is `tex/606.tex`.
-/

open scoped BigOperators
open Finset

namespace Erdos606

noncomputable section

/-- The real affine plane. -/
abbrev Point := Fin 2 → ℝ

/-- The affine line through two points.  It is a singleton when the points
coincide; all uses in `pointPairs` are non-diagonal. -/
def lineThrough (p q : Point) : AffineSubspace ℝ Point :=
  affineSpan ℝ ({p, q} : Set Point)

lemma lineThrough_comm (p q : Point) : lineThrough p q = lineThrough q p := by
  simp only [lineThrough, Set.pair_comm]

/-- The line through an unordered pair. -/
def lineOfPair : Sym2 Point → AffineSubspace ℝ Point :=
  Sym2.lift ⟨lineThrough, lineThrough_comm⟩

@[simp]
lemma lineOfPair_mk (p q : Point) : lineOfPair s(p, q) = lineThrough p q := by
  rfl

/-- Unordered pairs of distinct points of `P`. -/
def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.sym2.filter fun e ↦ ¬ e.IsDiag

/-- The distinct affine lines determined by `P`. -/
def determinedLines (P : Finset Point) : Finset (AffineSubspace ℝ Point) := by
  classical
  exact (pointPairs P).image lineOfPair

/-- Number of distinct affine lines containing at least two points of `P`. -/
def lineCount (P : Finset Point) : ℕ :=
  (determinedLines P).card

/-- `m` is a possible number of lines determined by `n` distinct real planar
points. -/
def PossibleLineCount (n m : ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧ lineCount P = m

/-- No three distinct points of `P` lie on one affine line. -/
def GeneralPosition (P : Finset Point) : Prop :=
  ∀ ⦃p q r : Point⦄, p ∈ P → q ∈ P → r ∈ P →
    p ≠ q → r ≠ p → r ≠ q → r ∉ lineThrough p q

lemma left_mem_lineThrough (p q : Point) : p ∈ lineThrough p q := by
  exact subset_affineSpan ℝ ({p, q} : Set Point) (by simp)

lemma right_mem_lineThrough (p q : Point) : q ∈ lineThrough p q := by
  exact subset_affineSpan ℝ ({p, q} : Set Point) (by simp)

@[simp]
lemma mk_mem_pointPairs (P : Finset Point) (p q : Point) :
    s(p, q) ∈ pointPairs P ↔ p ∈ P ∧ q ∈ P ∧ p ≠ q := by
  classical
  simp only [pointPairs, mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.mk_isDiag_iff]
  tauto

/-- The points of `P` lying on `L`. -/
def pointsOnLine (P : Finset Point) (L : AffineSubspace ℝ Point) : Finset Point := by
  classical
  exact P.filter fun p ↦ p ∈ L

/-- The unordered point-pairs of `P` whose line is `L`. -/
def pairFiber (P : Finset Point) (L : AffineSubspace ℝ Point) : Finset (Sym2 Point) := by
  classical
  exact (pointPairs P).filter fun e ↦ lineOfPair e = L

@[simp]
lemma mem_pointsOnLine {P : Finset Point} {L : AffineSubspace ℝ Point} {p : Point} :
    p ∈ pointsOnLine P L ↔ p ∈ P ∧ p ∈ L := by
  simp [pointsOnLine]

lemma lineThrough_eq_of_mem_of_mem_of_ne {p q r s : Point}
    (hp : p ∈ lineThrough r s) (hq : q ∈ lineThrough r s) (hpq : p ≠ q) :
    lineThrough p q = lineThrough r s := by
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hpq

lemma lineOfPair_eq_iff_mem {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines P) {p q : Point} (hpq : p ≠ q) :
    lineOfPair s(p, q) = L ↔ p ∈ L ∧ q ∈ L := by
  classical
  constructor
  · intro h
    rw [← h]
    exact ⟨left_mem_lineThrough p q, right_mem_lineThrough p q⟩
  · rintro ⟨hp, hq⟩
    rw [determinedLines, mem_image] at hL
    obtain ⟨e, he, rfl⟩ := hL
    rcases e with ⟨r, s⟩
    rw [lineOfPair_mk] at hp hq ⊢
    exact lineThrough_eq_of_mem_of_mem_of_ne hp hq hpq

lemma pairFiber_eq_pointPairs {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines P) :
    pairFiber P L = pointPairs (pointsOnLine P L) := by
  classical
  ext e
  rcases e with ⟨p, q⟩
  simp only [pairFiber, mem_filter, mk_mem_pointPairs]
  constructor
  · rintro ⟨⟨hp, hq, hpq⟩, heq⟩
    have hm := (lineOfPair_eq_iff_mem hL hpq).mp heq
    exact ⟨mem_pointsOnLine.mpr ⟨hp, hm.1⟩,
      mem_pointsOnLine.mpr ⟨hq, hm.2⟩, hpq⟩
  · rintro ⟨hp', hq', hpq⟩
    rcases mem_pointsOnLine.mp hp' with ⟨hp, hpL⟩
    rcases mem_pointsOnLine.mp hq' with ⟨hq, hqL⟩
    exact ⟨⟨hp, hq, hpq⟩, (lineOfPair_eq_iff_mem hL hpq).mpr ⟨hpL, hqL⟩⟩

lemma pointPairs_card (P : Finset Point) :
    (pointPairs P).card = P.card.choose 2 := by
  classical
  have hcard :
      (P.sym2.filter fun e ↦ ¬ e.IsDiag).card =
        (P.powersetCard 2).card := by
    refine Finset.card_bij (fun x _ ↦ P.filter fun y ↦ y ∈ x) ?_ ?_ ?_
    · simp +contextual [Finset.mem_powersetCard, Finset.subset_iff]
      intro a ha₁ ha₂
      rcases a with ⟨x, y⟩
      simp_all +decide [Sym2.IsDiag]
      rw [show {z ∈ P | z = x ∨ z = y} = {x, y} by ext; aesop]
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      aesop
    · simp +contextual [Finset.ext_iff, Sym2.forall]
      grind
    · simp +decide [Finset.mem_powersetCard, Finset.subset_iff]
      intro s hs hs'
      obtain ⟨x, y, hxy⟩ := Finset.card_eq_two.mp hs'
      use s(x, y)
      aesop
  rw [pointPairs, hcard, Finset.card_powersetCard]

lemma pairFiber_card {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines P) :
    (pairFiber P L).card = (pointsOnLine P L).card.choose 2 := by
  rw [pairFiber_eq_pointPairs hL, pointPairs_card]

lemma lineCount_le_choose (P : Finset Point) :
    lineCount P ≤ P.card.choose 2 := by
  classical
  rw [lineCount, determinedLines, ← pointPairs_card]
  exact Finset.card_image_le

/-- Partitioning unordered point-pairs according to their determined line. -/
lemma pair_count_sum (P : Finset Point) :
    P.card.choose 2 = ∑ L ∈ determinedLines P, (pointsOnLine P L).card.choose 2 := by
  classical
  rw [← pointPairs_card]
  calc
    (pointPairs P).card =
        ∑ L ∈ (pointPairs P).image lineOfPair, (pairFiber P L).card := by
      simpa only [pairFiber] using
        (Finset.card_eq_sum_card_image lineOfPair (pointPairs P))
    _ = ∑ L ∈ determinedLines P, (pointsOnLine P L).card.choose 2 := by
      rw [determinedLines]
      apply sum_congr rfl
      intro L hL
      exact pairFiber_card (by simpa [determinedLines] using hL)

lemma two_le_pointsOnLine_card {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines P) : 2 ≤ (pointsOnLine P L).card := by
  classical
  rw [determinedLines, mem_image] at hL
  obtain ⟨e, he, rfl⟩ := hL
  rcases e with ⟨p, q⟩
  rw [mk_mem_pointPairs] at he
  rcases he with ⟨hp, hq, hpq⟩
  have hsub : ({p, q} : Finset Point) ⊆ pointsOnLine P (lineThrough p q) := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · simp [hp, left_mem_lineThrough]
    · simp [hq, right_mem_lineThrough]
  have hc := Finset.card_le_card hsub
  simpa [hpq] using hc

/-- The pair defect is a sum of the losses contributed by the determined
lines.  A line with `r` selected points contributes `choose r 2 - 1`. -/
lemma pair_defect_identity (P : Finset Point) :
    P.card.choose 2 - lineCount P =
      ∑ L ∈ determinedLines P, ((pointsOnLine P L).card.choose 2 - 1) := by
  classical
  rw [lineCount, pair_count_sum]
  calc
    (∑ L ∈ determinedLines P, (pointsOnLine P L).card.choose 2) -
          (determinedLines P).card =
        (∑ L ∈ determinedLines P, (pointsOnLine P L).card.choose 2) -
          (∑ _L ∈ determinedLines P, 1) := by simp
    _ = ∑ L ∈ determinedLines P, ((pointsOnLine P L).card.choose 2 - 1) := by
      symm
      apply Finset.sum_tsub_distrib
      intro L hL
      have hr := two_le_pointsOnLine_card hL
      have hc : 1 ≤ (pointsOnLine P L).card.choose 2 := by
        calc
          1 = (2 : ℕ).choose 2 := by norm_num
          _ ≤ (pointsOnLine P L).card.choose 2 := Nat.choose_le_choose 2 hr
      exact hc

lemma choose_two_sub_one_cases {r : ℕ} (hr : 2 ≤ r) :
    r.choose 2 - 1 = 0 ∨ r.choose 2 - 1 = 2 ∨ 5 ≤ r.choose 2 - 1 := by
  rcases eq_or_ne r 2 with rfl | hr2
  · simp
  have hr3 : 3 ≤ r := by omega
  rcases eq_or_ne r 3 with rfl | hr3ne
  · norm_num
  right
  right
  have hr4 : 4 ≤ r := by omega
  have hc : 6 ≤ r.choose 2 := by
    calc
      6 = (4 : ℕ).choose 2 := by decide
      _ ≤ r.choose 2 := Nat.choose_le_choose 2 hr4
  omega

lemma sum_choose_losses_ne_one_three {s : Finset α} {f : α → ℕ}
    (hf : ∀ x ∈ s, f x = 0 ∨ f x = 2 ∨ 5 ≤ f x) :
    (∑ x ∈ s, f x) ≠ 1 ∧ (∑ x ∈ s, f x) ≠ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (by simp)
      have hrest := ih (by
        intro x hx
        exact hf x (by simp [hx]))
      simp only [sum_insert ha]
      omega

lemma pair_defect_ne_one_three (P : Finset Point) :
    P.card.choose 2 - lineCount P ≠ 1 ∧
      P.card.choose 2 - lineCount P ≠ 3 := by
  rw [pair_defect_identity]
  apply sum_choose_losses_ne_one_three
  intro L hL
  exact choose_two_sub_one_cases (two_le_pointsOnLine_card hL)

lemma top_gap_one {P : Finset Point} (hcard : 2 ≤ P.card) :
    lineCount P ≠ P.card.choose 2 - 1 := by
  intro h
  have hc : 1 ≤ P.card.choose 2 := by
    calc
      1 = (2 : ℕ).choose 2 := by norm_num
      _ ≤ P.card.choose 2 := Nat.choose_le_choose 2 hcard
  have hle := lineCount_le_choose P
  have hdef : P.card.choose 2 - lineCount P = 1 := by omega
  exact (pair_defect_ne_one_three P).1 hdef

lemma top_gap_three {P : Finset Point} (hcard : 3 ≤ P.card) :
    lineCount P ≠ P.card.choose 2 - 3 := by
  intro h
  have hc : 3 ≤ P.card.choose 2 := by
    calc
      3 = (3 : ℕ).choose 2 := by norm_num
      _ ≤ P.card.choose 2 := Nat.choose_le_choose 2 hcard
  have hle := lineCount_le_choose P
  have hdef : P.card.choose 2 - lineCount P = 3 := by omega
  exact (pair_defect_ne_one_three P).2 hdef

lemma lineOfPair_injOn_of_generalPosition {P : Finset Point}
    (hP : GeneralPosition P) :
    Set.InjOn lineOfPair (pointPairs P) := by
  classical
  intro e he f hf hef
  rcases e with ⟨p, q⟩
  rcases f with ⟨r, s⟩
  change s(p, q) ∈ pointPairs P at he
  change s(r, s) ∈ pointPairs P at hf
  simp only [pointPairs, mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.mk_isDiag_iff, not_false_eq_true, and_self] at he hf
  rcases he with ⟨⟨hp, hq⟩, hpq⟩
  rcases hf with ⟨⟨hr, hs⟩, hrs⟩
  simp only [lineOfPair_mk] at hef
  apply Sym2.eq_iff.mpr
  by_cases hrp : r = p
  · subst r
    by_cases hsq : s = q
    · exact Or.inl ⟨rfl, hsq.symm⟩
    · have hsp : s ≠ p := by
        intro h
        apply hrs
        simpa [h] using rfl
      have hsmem : s ∈ lineThrough p q := by
        rw [hef]
        exact right_mem_lineThrough p s
      exact (hP hp hq hs hpq hsp hsq hsmem).elim
  · by_cases hrq : r = q
    · subst r
      by_cases hsp : s = p
      · exact Or.inr ⟨hsp.symm, rfl⟩
      · have hsq : s ≠ q := by
          intro h
          apply hrs
          simpa [h] using rfl
        have hsmem : s ∈ lineThrough p q := by
          rw [hef]
          exact right_mem_lineThrough q s
        exact (hP hp hq hs hpq hsp hsq hsmem).elim
    · have hrmem : r ∈ lineThrough p q := by
        rw [hef]
        exact left_mem_lineThrough r s
      exact (hP hp hq hr hpq hrp hrq hrmem).elim

lemma lineCount_eq_choose_of_generalPosition {P : Finset Point}
    (hP : GeneralPosition P) :
    lineCount P = P.card.choose 2 := by
  classical
  rw [lineCount, determinedLines,
    Finset.card_image_iff.mpr (lineOfPair_injOn_of_generalPosition hP),
    pointPairs_card]

/-! ### Explicit general-position configurations -/

/-- A point of the standard parabola. -/
def parabolaPoint (x : ℝ) : Point := ![x, x ^ 2]

@[simp]
lemma parabolaPoint_apply_zero (x : ℝ) : parabolaPoint x 0 = x := by
  simp [parabolaPoint]

@[simp]
lemma parabolaPoint_apply_one (x : ℝ) : parabolaPoint x 1 = x ^ 2 := by
  simp [parabolaPoint]

lemma parabolaPoint_injective : Function.Injective parabolaPoint := by
  intro x y h
  have := congrFun h 0
  simpa using this

lemma parabola_mem_line {x y z : ℝ}
    (h : parabolaPoint z ∈ lineThrough (parabolaPoint x) (parabolaPoint y)) :
    z = x ∨ z = y := by
  rw [lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq] at h
  obtain ⟨t, ht⟩ := h
  have hx := congrFun ht 0
  have hy := congrFun ht 1
  simp [parabolaPoint, AffineMap.lineMap_apply_module] at hx hy
  have hx' : t * (y - x) = z - x := by linarith
  have hy' : t * (y ^ 2 - x ^ 2) = z ^ 2 - x ^ 2 := by linarith
  have hxmul := congrArg (fun u : ℝ ↦ u * (x + y)) hx'
  have hfactor : (z - x) * (z - y) = 0 := by
    nlinarith [hxmul, hy']
  rcases mul_eq_zero.mp hfactor with hzx | hzy
  · exact Or.inl (sub_eq_zero.mp hzx)
  · exact Or.inr (sub_eq_zero.mp hzy)

/-- A named natural-number parametrization, packaged so that finset cardinality
lemmas see a single injective map. -/
def natParabolaPoint (i : ℕ) : Point := parabolaPoint (i : ℝ)

lemma natParabolaPoint_injective : Function.Injective natParabolaPoint := by
  intro i j h
  exact_mod_cast parabolaPoint_injective h

/-- `n` explicitly indexed points on a parabola. -/
def parabolaFinset (n : ℕ) : Finset Point := by
  classical
  exact (Finset.range n).image natParabolaPoint

lemma parabolaFinset_card (n : ℕ) : (parabolaFinset n).card = n := by
  classical
  rw [parabolaFinset]
  exact (Finset.card_image_of_injective (Finset.range n) natParabolaPoint_injective).trans
    (Finset.card_range n)

lemma parabolaFinset_generalPosition (n : ℕ) : GeneralPosition (parabolaFinset n) := by
  classical
  intro p q r hp hq hr hpq hrp hrq hrline
  rw [parabolaFinset, mem_image] at hp hq hr
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  obtain ⟨z, hz, rfl⟩ := hr
  change parabolaPoint (z : ℝ) ∈
    lineThrough (parabolaPoint (x : ℝ)) (parabolaPoint (y : ℝ)) at hrline
  rcases parabola_mem_line hrline with hzx | hzy
  · exact hrp (congrArg natParabolaPoint (Nat.cast_injective hzx))
  · exact hrq (congrArg natParabolaPoint (Nat.cast_injective hzy))

lemma possibleLineCount_choose (n : ℕ) : PossibleLineCount n (n.choose 2) := by
  refine ⟨parabolaFinset n, parabolaFinset_card n, ?_⟩
  rw [lineCount_eq_choose_of_generalPosition (parabolaFinset_generalPosition n),
    parabolaFinset_card]

/-! ### A configuration with one collinear triple -/

/-- Coordinate determinant for three planar points. -/
def collinearityDet (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

lemma collinearityDet_eq_zero_of_mem {p q r : Point}
    (h : r ∈ lineThrough p q) : collinearityDet p q r = 0 := by
  rw [lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [← ht]
  simp [collinearityDet, AffineMap.lineMap_apply_module]
  ring

/-- The three special points lie on the horizontal axis. -/
def specialPoint (c : ℕ) : Point := ![(c : ℝ), 0]

/-- All other points are far out on the parabola. -/
def farParabolaPoint (i : ℕ) : Point := parabolaPoint ((i : ℝ) + 10)

lemma specialPoint_injective : Function.Injective specialPoint := by
  intro i j h
  have hx := congrFun h 0
  simp [specialPoint] at hx
  exact_mod_cast hx

lemma farParabolaPoint_injective : Function.Injective farParabolaPoint := by
  intro i j h
  have hx := congrFun h 0
  simp [farParabolaPoint] at hx
  exact_mod_cast hx

lemma specialPoint_ne_farParabolaPoint (c i : ℕ) :
    specialPoint c ≠ farParabolaPoint i := by
  intro h
  have hy := congrFun h 1
  simp [specialPoint, farParabolaPoint, parabolaPoint] at hy
  have hpos : 0 < (i : ℝ) + 10 := by positivity
  nlinarith [sq_pos_of_pos hpos]

lemma no_special_special_far {c d i : ℕ} (hcd : c ≠ d)
    (h : farParabolaPoint i ∈ lineThrough (specialPoint c) (specialPoint d)) : False := by
  have hdet := collinearityDet_eq_zero_of_mem h
  simp [collinearityDet, specialPoint, farParabolaPoint, parabolaPoint] at hdet
  have hcast : (c : ℝ) ≠ (d : ℝ) := by exact_mod_cast hcd
  have hpos : 0 < (i : ℝ) + 10 := by positivity
  rcases hdet with hdet | hdet
  · exact hcast (by linarith)
  · linarith

lemma no_special_far_special {c d i : ℕ} (hcd : c ≠ d)
    (h : specialPoint d ∈ lineThrough (specialPoint c) (farParabolaPoint i)) : False := by
  have hdet := collinearityDet_eq_zero_of_mem h
  simp [collinearityDet, specialPoint, farParabolaPoint, parabolaPoint] at hdet
  have hcast : (c : ℝ) ≠ (d : ℝ) := by exact_mod_cast hcd
  have hpos : 0 < (i : ℝ) + 10 := by positivity
  rcases hdet with hdet | hdet
  · linarith
  · exact hcast (by linarith)

lemma no_special_far_far {c i j : ℕ} (hc : c < 3) (hij : i ≠ j)
    (h : farParabolaPoint j ∈ lineThrough (specialPoint c) (farParabolaPoint i)) : False := by
  have hdet := collinearityDet_eq_zero_of_mem h
  simp [collinearityDet, specialPoint, farParabolaPoint, parabolaPoint] at hdet
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hi : (10 : ℝ) ≤ (i : ℝ) + 10 := by linarith
  have hj : (10 : ℝ) ≤ (j : ℝ) + 10 := by linarith
  have hc' : (c : ℝ) ≤ 2 := by exact_mod_cast (by omega : c ≤ 2)
  have hne : (i : ℝ) + 10 ≠ (j : ℝ) + 10 := by
    intro h
    apply hij
    exact_mod_cast (show (i : ℝ) = (j : ℝ) by linarith)
  have hlarge : (c : ℝ) * (((i : ℝ) + 10) + ((j : ℝ) + 10)) <
      ((i : ℝ) + 10) * ((j : ℝ) + 10) := by nlinarith
  apply hne
  nlinarith

lemma no_far_far_special {c i j : ℕ} (hc : c < 3) (hij : i ≠ j)
    (h : specialPoint c ∈ lineThrough (farParabolaPoint i) (farParabolaPoint j)) : False := by
  have hdet := collinearityDet_eq_zero_of_mem h
  simp [collinearityDet, specialPoint, farParabolaPoint, parabolaPoint] at hdet
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hi : (10 : ℝ) ≤ (i : ℝ) + 10 := by linarith
  have hj : (10 : ℝ) ≤ (j : ℝ) + 10 := by linarith
  have hc' : (c : ℝ) ≤ 2 := by exact_mod_cast (by omega : c ≤ 2)
  have hne : (i : ℝ) + 10 ≠ (j : ℝ) + 10 := by
    intro h
    apply hij
    exact_mod_cast (show (i : ℝ) = (j : ℝ) by linarith)
  have hlarge : (c : ℝ) * (((i : ℝ) + 10) + ((j : ℝ) + 10)) <
      ((i : ℝ) + 10) * ((j : ℝ) + 10) := by nlinarith
  apply hne
  nlinarith

/-- The distinguished horizontal triple. -/
def specialFinset : Finset Point := by
  classical
  exact (Finset.range 3).image specialPoint

/-- The remote parabolic part. -/
def farParabolaFinset (t : ℕ) : Finset Point := by
  classical
  exact (Finset.range t).image farParabolaPoint

/-- Three horizontal points together with `t` remote parabola points. -/
def oneTripleFinset (t : ℕ) : Finset Point := by
  classical
  exact specialFinset ∪ farParabolaFinset t

@[simp]
lemma specialPoint_mem_specialFinset {c : ℕ} :
    specialPoint c ∈ specialFinset ↔ c < 3 := by
  classical
  simp only [specialFinset, mem_image, mem_range]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hdc' : d = c := specialPoint_injective hdc
    simpa [hdc'] using hd
  · intro hc
    exact ⟨c, hc, rfl⟩

lemma specialFinset_card : specialFinset.card = 3 := by
  classical
  rw [specialFinset, Finset.card_image_of_injective _ specialPoint_injective]
  simp

lemma farParabolaFinset_card (t : ℕ) : (farParabolaFinset t).card = t := by
  classical
  rw [farParabolaFinset,
    Finset.card_image_of_injective _ farParabolaPoint_injective]
  simp

lemma special_far_disjoint (t : ℕ) :
    Disjoint specialFinset (farParabolaFinset t) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [specialFinset, mem_image] at hp
  rw [farParabolaFinset, mem_image] at hq
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨i, hi, heq⟩ := hq
  exact specialPoint_ne_farParabolaPoint c i heq.symm

lemma oneTripleFinset_card (t : ℕ) : (oneTripleFinset t).card = t + 3 := by
  classical
  rw [oneTripleFinset, Finset.card_union_of_disjoint (special_far_disjoint t),
    specialFinset_card, farParabolaFinset_card]
  omega

/-- Every collinear triple in `P` belongs to `H`. -/
def OnlyCollinearTriple (P H : Finset Point) : Prop :=
  ∀ {p q r : Point}, p ∈ P → q ∈ P → r ∈ P →
    p ≠ q → r ≠ p → r ≠ q → r ∈ lineThrough p q →
      p ∈ H ∧ q ∈ H ∧ r ∈ H

lemma oneTriple_only (t : ℕ) :
    OnlyCollinearTriple (oneTripleFinset t) specialFinset := by
  classical
  intro p q r hp hq hr hpq hrp hrq hrline
  simp only [oneTripleFinset, mem_union, specialFinset, farParabolaFinset,
    mem_image, mem_range] at hp hq hr
  rcases hp with ⟨c, hc, rfl⟩ | ⟨i, hi, rfl⟩
  · rcases hq with ⟨d, hd, rfl⟩ | ⟨j, hj, rfl⟩
    · rcases hr with ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩
      · exact ⟨specialPoint_mem_specialFinset.mpr hc,
          specialPoint_mem_specialFinset.mpr hd,
          specialPoint_mem_specialFinset.mpr he⟩
      · exact (no_special_special_far
          (fun hcd ↦ hpq (congrArg specialPoint hcd)) hrline).elim
    · rcases hr with ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩
      · exact (no_special_far_special
          (fun hce ↦ hrp (congrArg specialPoint hce.symm)) hrline).elim
      · exact (no_special_far_far hc
          (fun hjk ↦ hrq (congrArg farParabolaPoint hjk.symm)) hrline).elim
  · rcases hq with ⟨d, hd, rfl⟩ | ⟨j, hj, rfl⟩
    · rcases hr with ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩
      · rw [lineThrough_comm] at hrline
        exact (no_special_far_special
          (fun hde ↦ hrq (congrArg specialPoint hde.symm)) hrline).elim
      · rw [lineThrough_comm] at hrline
        exact (no_special_far_far hd
          (fun hik ↦ hrp (congrArg farParabolaPoint hik.symm)) hrline).elim
    · rcases hr with ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩
      · exact (no_far_far_special he
          (fun hij ↦ hpq (congrArg farParabolaPoint hij)) hrline).elim
      · change parabolaPoint ((k : ℝ) + 10) ∈
          lineThrough (parabolaPoint ((i : ℝ) + 10))
            (parabolaPoint ((j : ℝ) + 10)) at hrline
        rcases parabola_mem_line hrline with hki | hkj
        · have hki' : (k : ℝ) = (i : ℝ) := by linarith
          have hnat : k = i := Nat.cast_injective hki'
          exact (hrp (congrArg farParabolaPoint hnat)).elim
        · have hkj' : (k : ℝ) = (j : ℝ) := by linarith
          have hnat : k = j := Nat.cast_injective hkj'
          exact (hrq (congrArg farParabolaPoint hnat)).elim

/-- The horizontal line supporting the distinguished triple. -/
def specialAxis : AffineSubspace ℝ Point :=
  lineThrough (specialPoint 0) (specialPoint 1)

lemma specialPoint_mem_specialAxis (c : ℕ) : specialPoint c ∈ specialAxis := by
  rw [specialAxis, lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨(c : ℝ), ?_⟩
  ext j
  fin_cases j <;> simp [specialPoint, AffineMap.lineMap_apply_module]

lemma specialFinset_subset_specialAxis :
    ↑specialFinset ⊆ (specialAxis : Set Point) := by
  intro p hp
  change p ∈ specialFinset at hp
  rw [specialFinset, mem_image] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  exact specialPoint_mem_specialAxis c

lemma specialAxis_mem_determinedLines (t : ℕ) :
    specialAxis ∈ determinedLines (oneTripleFinset t) := by
  classical
  rw [determinedLines, mem_image]
  refine ⟨s(specialPoint 0, specialPoint 1), ?_, ?_⟩
  · rw [mk_mem_pointPairs]
    refine ⟨?_, ?_, ?_⟩
    · simp [oneTripleFinset]
    · simp [oneTripleFinset]
    · exact specialPoint_injective.ne (by decide)
  · rfl

lemma pointsOnSpecialAxis (t : ℕ) :
    pointsOnLine (oneTripleFinset t) specialAxis = specialFinset := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_pointsOnLine.mp hp with ⟨hpP, hpaxis⟩
    rw [oneTripleFinset, mem_union] at hpP
    rcases hpP with hpS | hpF
    · exact hpS
    · rw [farParabolaFinset, mem_image] at hpF
      obtain ⟨i, hi, rfl⟩ := hpF
      exact (no_special_special_far (by decide) hpaxis).elim
  · intro hp
    apply mem_pointsOnLine.mpr
    exact ⟨by simp [oneTripleFinset, hp], specialFinset_subset_specialAxis hp⟩

lemma line_eq_specialAxis_of_special {p q : Point}
    (hp : p ∈ specialFinset) (hq : q ∈ specialFinset) (hpq : p ≠ q) :
    lineThrough p q = specialAxis := by
  exact lineThrough_eq_of_mem_of_mem_of_ne
    (specialFinset_subset_specialAxis hp) (specialFinset_subset_specialAxis hq) hpq

lemma pointsOnLine_card_eq_two_of_ne_axis {t : ℕ} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines (oneTripleFinset t)) (hne : L ≠ specialAxis) :
    (pointsOnLine (oneTripleFinset t) L).card = 2 := by
  have hlo := two_le_pointsOnLine_card hL
  have hhi : (pointsOnLine (oneTripleFinset t) L).card ≤ 2 := by
    by_contra hnot
    have hthree : 2 < (pointsOnLine (oneTripleFinset t) L).card := by omega
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
      Finset.two_lt_card_iff.mp hthree
    rcases mem_pointsOnLine.mp hp with ⟨hpP, hpL⟩
    rcases mem_pointsOnLine.mp hq with ⟨hqP, hqL⟩
    rcases mem_pointsOnLine.mp hr with ⟨hrP, hrL⟩
    have hpqline : lineThrough p q = L :=
      (lineOfPair_eq_iff_mem hL hpq).mpr ⟨hpL, hqL⟩
    have hrline : r ∈ lineThrough p q := by simpa [hpqline] using hrL
    rcases oneTriple_only t hpP hqP hrP hpq hpr.symm hqr.symm hrline with
      ⟨hpS, hqS, hrS⟩
    apply hne
    rw [← hpqline]
    exact line_eq_specialAxis_of_special hpS hqS hpq
  omega

lemma oneTriple_pair_defect (t : ℕ) :
    (oneTripleFinset t).card.choose 2 - lineCount (oneTripleFinset t) = 2 := by
  rw [pair_defect_identity]
  classical
  rw [Finset.sum_eq_single specialAxis]
  · rw [pointsOnSpecialAxis, specialFinset_card]
    decide
  · intro L hL hne
    rw [pointsOnLine_card_eq_two_of_ne_axis hL hne]
    decide
  · intro hnot
    exact (hnot (specialAxis_mem_determinedLines t)).elim

lemma possibleLineCount_choose_sub_two {n : ℕ} (hn : 3 ≤ n) :
    PossibleLineCount n (n.choose 2 - 2) := by
  let t := n - 3
  have hcard : (oneTripleFinset t).card = n := by
    rw [oneTripleFinset_card]
    dsimp [t]
    omega
  refine ⟨oneTripleFinset t, hcard, ?_⟩
  have hdef := oneTriple_pair_defect t
  have hle := lineCount_le_choose (oneTripleFinset t)
  rw [hcard] at hdef hle
  have hchoose : 2 ≤ n.choose 2 := by
    calc
      2 ≤ (3 : ℕ).choose 2 := by decide
      _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn
  omega

/-! ### Collinear and near-pencil configurations -/

/-- `n` distinct points on the horizontal axis. -/
def axisFinset (n : ℕ) : Finset Point := by
  classical
  exact (Finset.range n).image specialPoint

lemma axisFinset_card (n : ℕ) : (axisFinset n).card = n := by
  classical
  rw [axisFinset, Finset.card_image_of_injective _ specialPoint_injective]
  simp

lemma axisFinset_subset_axis (n : ℕ) :
    ↑(axisFinset n) ⊆ (specialAxis : Set Point) := by
  intro p hp
  change p ∈ axisFinset n at hp
  rw [axisFinset, mem_image] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  exact specialPoint_mem_specialAxis c

lemma determinedLines_axisFinset {n : ℕ} (hn : 2 ≤ n) :
    determinedLines (axisFinset n) = {specialAxis} := by
  classical
  ext L
  constructor
  · intro hL
    rw [determinedLines, mem_image] at hL
    obtain ⟨e, he, rfl⟩ := hL
    rcases e with ⟨p, q⟩
    rw [mk_mem_pointPairs] at he
    rcases he with ⟨hp, hq, hpq⟩
    simp only [mem_singleton]
    exact lineThrough_eq_of_mem_of_mem_of_ne
      (axisFinset_subset_axis n hp) (axisFinset_subset_axis n hq) hpq
  · intro hL
    rw [mem_singleton] at hL
    subst L
    rw [determinedLines, mem_image]
    refine ⟨s(specialPoint 0, specialPoint 1), ?_, rfl⟩
    rw [mk_mem_pointPairs]
    refine ⟨?_, ?_, specialPoint_injective.ne (by decide)⟩
    · rw [axisFinset, mem_image]
      refine ⟨0, ?_, rfl⟩
      exact Finset.mem_range.mpr (lt_of_lt_of_le (by decide : 0 < 2) hn)
    · rw [axisFinset, mem_image]
      refine ⟨1, ?_, rfl⟩
      exact Finset.mem_range.mpr (by omega)

lemma lineCount_axisFinset {n : ℕ} (hn : 2 ≤ n) :
    lineCount (axisFinset n) = 1 := by
  rw [lineCount, determinedLines_axisFinset hn]
  simp

lemma possibleLineCount_one {n : ℕ} (hn : 2 ≤ n) : PossibleLineCount n 1 := by
  exact ⟨axisFinset n, axisFinset_card n, lineCount_axisFinset hn⟩

lemma pair_defect_of_unique_rich_line {P H : Finset Point}
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines P)
    (hpoints : pointsOnLine P L = H) (honly : OnlyCollinearTriple P H) :
    P.card.choose 2 - lineCount P = H.card.choose 2 - 1 := by
  rw [pair_defect_identity]
  classical
  rw [Finset.sum_eq_single L]
  · rw [hpoints]
  · intro M hM hML
    have hcard : (pointsOnLine P M).card = 2 := by
      have hlo := two_le_pointsOnLine_card hM
      have hhi : (pointsOnLine P M).card ≤ 2 := by
        by_contra hnot
        have hthree : 2 < (pointsOnLine P M).card := by omega
        obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
          Finset.two_lt_card_iff.mp hthree
        rcases mem_pointsOnLine.mp hp with ⟨hpP, hpM⟩
        rcases mem_pointsOnLine.mp hq with ⟨hqP, hqM⟩
        rcases mem_pointsOnLine.mp hr with ⟨hrP, hrM⟩
        have hpqline : lineThrough p q = M :=
          (lineOfPair_eq_iff_mem hM hpq).mpr ⟨hpM, hqM⟩
        have hrline : r ∈ lineThrough p q := by simpa [hpqline] using hrM
        rcases honly hpP hqP hrP hpq hpr.symm hqr.symm hrline with ⟨hpH, hqH, hrH⟩
        have hpL : p ∈ L := (mem_pointsOnLine.mp (hpoints.symm ▸ hpH)).2
        have hqL : q ∈ L := (mem_pointsOnLine.mp (hpoints.symm ▸ hqH)).2
        have hpqL : lineThrough p q = L :=
          (lineOfPair_eq_iff_mem hL hpq).mpr ⟨hpL, hqL⟩
        apply hML
        rw [← hpqline, ← hpqL]
      omega
    rw [hcard]
    decide
  · intro hnot
    exact (hnot hL).elim

/-- `a` collinear points and one point off their line. -/
def nearPencilFinset (a : ℕ) : Finset Point := by
  classical
  exact axisFinset a ∪ {farParabolaPoint 0}

lemma nearPencilFinset_card (a : ℕ) : (nearPencilFinset a).card = a + 1 := by
  classical
  rw [nearPencilFinset, Finset.card_union_of_disjoint]
  · rw [axisFinset_card]
    simp
  · rw [Finset.disjoint_singleton_right]
    intro h
    rw [axisFinset, mem_image] at h
    obtain ⟨c, hc, heq⟩ := h
    exact specialPoint_ne_farParabolaPoint c 0 heq

lemma pointsOnAxis_nearPencil (a : ℕ) :
    pointsOnLine (nearPencilFinset a) specialAxis = axisFinset a := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_pointsOnLine.mp hp with ⟨hpP, hpaxis⟩
    rw [nearPencilFinset, mem_union, mem_singleton] at hpP
    rcases hpP with hpA | rfl
    · exact hpA
    · exact (no_special_special_far (by decide) hpaxis).elim
  · intro hp
    exact mem_pointsOnLine.mpr
      ⟨by simp [nearPencilFinset, hp], axisFinset_subset_axis a hp⟩

lemma specialAxis_mem_nearPencilLines {a : ℕ} (ha : 2 ≤ a) :
    specialAxis ∈ determinedLines (nearPencilFinset a) := by
  classical
  rw [determinedLines, mem_image]
  refine ⟨s(specialPoint 0, specialPoint 1), ?_, rfl⟩
  rw [mk_mem_pointPairs]
  refine ⟨?_, ?_, specialPoint_injective.ne (by decide)⟩
  · simp only [nearPencilFinset, mem_union, mem_singleton]
    left
    rw [axisFinset, mem_image]
    refine ⟨0, ?_, rfl⟩
    exact Finset.mem_range.mpr (lt_of_lt_of_le (by decide : 0 < 2) ha)
  · simp only [nearPencilFinset, mem_union, mem_singleton]
    left
    rw [axisFinset, mem_image]
    refine ⟨1, ?_, rfl⟩
    exact Finset.mem_range.mpr (by omega)

lemma nearPencil_only (a : ℕ) :
    OnlyCollinearTriple (nearPencilFinset a) (axisFinset a) := by
  classical
  intro p q r hp hq hr hpq hrp hrq hrline
  simp only [nearPencilFinset, mem_union, mem_singleton, axisFinset, mem_image,
    mem_range] at hp hq hr
  rcases hp with ⟨c, hc, rfl⟩ | rfl
  · rcases hq with ⟨d, hd, rfl⟩ | rfl
    · rcases hr with ⟨e, he, rfl⟩ | rfl
      · refine ⟨?_, ?_, ?_⟩
        · rw [axisFinset, mem_image]
          exact ⟨c, Finset.mem_range.mpr hc, rfl⟩
        · rw [axisFinset, mem_image]
          exact ⟨d, Finset.mem_range.mpr hd, rfl⟩
        · rw [axisFinset, mem_image]
          exact ⟨e, Finset.mem_range.mpr he, rfl⟩
      · exact (no_special_special_far
          (fun hcd ↦ hpq (congrArg specialPoint hcd)) hrline).elim
    · rcases hr with ⟨e, he, rfl⟩ | rfl
      · exact (no_special_far_special
          (fun hce ↦ hrp (congrArg specialPoint hce.symm)) hrline).elim
      · exact (hrq rfl).elim
  · rcases hq with ⟨d, hd, rfl⟩ | rfl
    · rcases hr with ⟨e, he, rfl⟩ | rfl
      · rw [lineThrough_comm] at hrline
        exact (no_special_far_special
          (fun hde ↦ hrq (congrArg specialPoint hde.symm)) hrline).elim
      · exact (hrp rfl).elim
    · exact (hpq rfl).elim

lemma lineCount_nearPencil {a : ℕ} (ha : 2 ≤ a) :
    lineCount (nearPencilFinset a) = a + 1 := by
  have hdef := pair_defect_of_unique_rich_line
    (specialAxis_mem_nearPencilLines ha) (pointsOnAxis_nearPencil a)
    (nearPencil_only a)
  rw [nearPencilFinset_card, axisFinset_card] at hdef
  have hle := lineCount_le_choose (nearPencilFinset a)
  rw [nearPencilFinset_card] at hle
  have hchoose : 1 ≤ a.choose 2 := by
    calc
      1 = (2 : ℕ).choose 2 := by decide
      _ ≤ a.choose 2 := Nat.choose_le_choose 2 ha
  have hpascal : (a + 1).choose 2 = a + a.choose 2 := by
    calc
      (a + 1).choose 2 = a.choose 1 + a.choose 2 := Nat.choose_succ_succ' a 1
      _ = a + a.choose 2 := by rw [Nat.choose_one_right]
  rw [hpascal] at hdef
  omega

lemma possibleLineCount_self {n : ℕ} (hn : 3 ≤ n) : PossibleLineCount n n := by
  let a := n - 1
  have ha : 2 ≤ a := by dsimp [a]; omega
  refine ⟨nearPencilFinset a, ?_, ?_⟩
  · rw [nearPencilFinset_card]
    dsimp [a]
    omega
  · rw [lineCount_nearPencil ha]
    dsimp [a]
    omega

/-! ### A vertical transversal for finitely many nonvertical lines -/

abbrev xCoord (p : Point) : ℝ := p 0
abbrev yCoord (p : Point) : ℝ := p 1

/-- Slope of the line represented by an unordered pair.  It is used only for
pairs with distinct first coordinates. -/
def pairSlope : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦ (yCoord q - yCoord p) / (xCoord q - xCoord p), by
    intro p q
    dsimp
    rw [show yCoord p - yCoord q = -(yCoord q - yCoord p) by ring,
      show xCoord p - xCoord q = -(xCoord q - xCoord p) by ring,
      neg_div_neg_eq]⟩

/-- Intercept of the line represented by an unordered nonvertical pair. -/
def pairIntercept : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦
    (yCoord p * xCoord q - yCoord q * xCoord p) / (xCoord q - xCoord p), by
    intro p q
    dsimp
    rw [show yCoord q * xCoord p - yCoord p * xCoord q =
        -(yCoord p * xCoord q - yCoord q * xCoord p) by ring,
      show xCoord p - xCoord q = -(xCoord q - xCoord p) by ring,
      neg_div_neg_eq]⟩

@[simp]
lemma pairSlope_mk (p q : Point) :
    pairSlope s(p, q) = (yCoord q - yCoord p) / (xCoord q - xCoord p) := rfl

@[simp]
lemma pairIntercept_mk (p q : Point) :
    pairIntercept s(p, q) =
      (yCoord p * xCoord q - yCoord q * xCoord p) / (xCoord q - xCoord p) := rfl

def graphValue (e : Sym2 Point) (c : ℝ) : ℝ :=
  pairSlope e * c + pairIntercept e

def verticalPoint (c y : ℝ) : Point := ![c, y]

def pairHole (c : ℝ) (e : Sym2 Point) : Point :=
  verticalPoint c (graphValue e c)

lemma endpoint_satisfies_graph {p q : Point} (hx : xCoord p ≠ xCoord q) :
    yCoord p = graphValue s(p, q) (xCoord p) := by
  simp only [graphValue, pairSlope_mk, pairIntercept_mk]
  field_simp
  ring

lemma pairHole_mem_line {p q : Point} (hx : xCoord p ≠ xCoord q) (c : ℝ) :
    pairHole c s(p, q) ∈ lineThrough p q := by
  rw [lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨(c - xCoord p) / (xCoord q - xCoord p), ?_⟩
  ext j
  fin_cases j
  · simp [pairHole, verticalPoint, graphValue, pairSlope, pairIntercept,
      AffineMap.lineMap_apply_module]
    field_simp
    ring
  · simp [pairHole, verticalPoint, graphValue, pairSlope, pairIntercept,
      AffineMap.lineMap_apply_module]
    field_simp
    ring

lemma mem_lineThrough_iff_graph {p q r : Point} (hx : xCoord p ≠ xCoord q) :
    r ∈ lineThrough p q ↔ yCoord r = graphValue s(p, q) (xCoord r) := by
  constructor
  · intro h
    have hdet := collinearityDet_eq_zero_of_mem h
    simp only [collinearityDet] at hdet
    simp only [graphValue, pairSlope_mk, pairIntercept_mk]
    field_simp
    nlinarith
  · intro hgraph
    rw [lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(xCoord r - xCoord p) / (xCoord q - xCoord p), ?_⟩
    ext j
    fin_cases j
    · simp [AffineMap.lineMap_apply_module]
      field_simp
      ring
    · simp [AffineMap.lineMap_apply_module]
      simp only [graphValue, pairSlope_mk, pairIntercept_mk] at hgraph
      field_simp at hgraph ⊢
      nlinarith

lemma lineThrough_eq_iff_slope_intercept {p q r s : Point}
    (hpq : xCoord p ≠ xCoord q) (hrs : xCoord r ≠ xCoord s) :
    lineThrough p q = lineThrough r s ↔
      pairSlope s(p, q) = pairSlope s(r, s) ∧
      pairIntercept s(p, q) = pairIntercept s(r, s) := by
  constructor
  · intro hline
    have hpR : p ∈ lineThrough r s := by rw [← hline]; exact left_mem_lineThrough p q
    have hqR : q ∈ lineThrough r s := by rw [← hline]; exact right_mem_lineThrough p q
    have hpE := (mem_lineThrough_iff_graph hpq).mp (left_mem_lineThrough p q)
    have hqE := (mem_lineThrough_iff_graph hpq).mp (right_mem_lineThrough p q)
    have hpF := (mem_lineThrough_iff_graph hrs).mp hpR
    have hqF := (mem_lineThrough_iff_graph hrs).mp hqR
    change yCoord p = pairSlope s(p, q) * xCoord p + pairIntercept s(p, q) at hpE
    change yCoord q = pairSlope s(p, q) * xCoord q + pairIntercept s(p, q) at hqE
    change yCoord p = pairSlope s(r, s) * xCoord p + pairIntercept s(r, s) at hpF
    change yCoord q = pairSlope s(r, s) * xCoord q + pairIntercept s(r, s) at hqF
    have hprod :
        (pairSlope s(p, q) - pairSlope s(r, s)) * (xCoord p - xCoord q) = 0 := by
      nlinarith
    have hslope : pairSlope s(p, q) = pairSlope s(r, s) := by
      rcases mul_eq_zero.mp hprod with hzero | hzero
      · linarith
      · exact (hpq (by linarith)).elim
    refine ⟨hslope, ?_⟩
    rw [hslope] at hpE
    linarith
  · rintro ⟨hslope, hintercept⟩
    apply lineThrough_eq_of_mem_of_mem_of_ne
    · apply (mem_lineThrough_iff_graph hrs).mpr
      have hp := (mem_lineThrough_iff_graph hpq).mp (left_mem_lineThrough p q)
      simpa [graphValue, hslope, hintercept] using hp
    · apply (mem_lineThrough_iff_graph hrs).mpr
      have hq := (mem_lineThrough_iff_graph hpq).mp (right_mem_lineThrough p q)
      simpa [graphValue, hslope, hintercept] using hq
    · intro h
      apply hpq
      exact congrArg xCoord h

/-- First coordinate is injective on the selected off-line points. -/
def XInjective (Q : Finset Point) : Prop := Set.InjOn xCoord Q

def crossingX (e f : Sym2 Point) : ℝ :=
  if pairSlope e = pairSlope f then 0
  else (pairIntercept f - pairIntercept e) / (pairSlope e - pairSlope f)

def badTransversalSet (Q : Finset Point) : Finset ℝ := by
  classical
  exact ((pointPairs Q).product (pointPairs Q)).image (fun ef ↦ crossingX ef.1 ef.2) ∪
    Q.image xCoord

lemma exists_good_transversal (Q : Finset Point) :
    ∃ c : ℝ, c ∉ badTransversalSet Q := by
  classical
  exact Infinite.exists_notMem_finset (badTransversalSet Q)

lemma good_transversal_ne_x {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q) {p : Point} (hp : p ∈ Q) : c ≠ xCoord p := by
  intro h
  apply hc
  rw [badTransversalSet, mem_union]
  right
  rw [mem_image]
  exact ⟨p, hp, h.symm⟩

lemma good_transversal_graph_eq_imp_line_eq {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q) {e f : Sym2 Point}
    (he : e ∈ pointPairs Q) (hf : f ∈ pointPairs Q)
    (hgraph : graphValue e c = graphValue f c) : lineOfPair e = lineOfPair f := by
  rcases e with ⟨p, q⟩
  rcases f with ⟨r, s⟩
  have he0 : s(p, q) ∈ pointPairs Q := he
  have hf0 : s(r, s) ∈ pointPairs Q := hf
  rw [mk_mem_pointPairs] at he hf
  rcases he with ⟨hp, hq, hpq⟩
  rcases hf with ⟨hr, hs, hrs⟩
  have hxpq : xCoord p ≠ xCoord q := fun h ↦ hpq (hQ hp hq h)
  have hxrs : xCoord r ≠ xCoord s := fun h ↦ hrs (hQ hr hs h)
  rw [lineOfPair_mk, lineOfPair_mk]
  apply (lineThrough_eq_iff_slope_intercept hxpq hxrs).mpr
  change pairSlope s(p, q) * c + pairIntercept s(p, q) =
    pairSlope s(r, s) * c + pairIntercept s(r, s) at hgraph
  by_cases hm : pairSlope s(p, q) = pairSlope s(r, s)
  · refine ⟨hm, ?_⟩
    rw [hm] at hgraph
    linarith
  · exfalso
    apply hc
    have hcross : c = crossingX s(p, q) s(r, s) := by
      rw [crossingX, if_neg hm]
      apply (eq_div_iff (sub_ne_zero.mpr hm)).mpr
      nlinarith [hgraph]
    rw [badTransversalSet, mem_union]
    left
    rw [mem_image]
    exact ⟨(s(p, q), s(r, s)), by simp [hp, hq, hpq, hr, hs, hrs], hcross.symm⟩

lemma pairHole_eq_iff_line_eq {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q) {e f : Sym2 Point}
    (he : e ∈ pointPairs Q) (hf : f ∈ pointPairs Q) :
    pairHole c e = pairHole c f ↔ lineOfPair e = lineOfPair f := by
  constructor
  · intro h
    have hy := congrFun h 1
    simp only [pairHole, verticalPoint] at hy
    exact good_transversal_graph_eq_imp_line_eq hQ hc he hf hy
  · intro hline
    rcases e with ⟨p, q⟩
    rcases f with ⟨r, s⟩
    rw [mk_mem_pointPairs] at he hf
    rcases he with ⟨hp, hq, hpq⟩
    rcases hf with ⟨hr, hs, hrs⟩
    have hxpq : xCoord p ≠ xCoord q := fun h ↦ hpq (hQ hp hq h)
    have hxrs : xCoord r ≠ xCoord s := fun h ↦ hrs (hQ hr hs h)
    rw [lineOfPair_mk, lineOfPair_mk] at hline
    rcases (lineThrough_eq_iff_slope_intercept hxpq hxrs).mp hline with ⟨hm, hb⟩
    ext j
    fin_cases j
    · rfl
    · simp [pairHole, verticalPoint, graphValue, hm, hb]

/-- A representative point-pair for a determined line. -/
noncomputable def linePairRep (Q : Finset Point) (L : AffineSubspace ℝ Point) : Sym2 Point :=
  by
    classical
    exact if h : ∃ e ∈ pointPairs Q, lineOfPair e = L then Classical.choose h else s(0, 0)

lemma linePairRep_spec {Q : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines Q) :
    linePairRep Q L ∈ pointPairs Q ∧ lineOfPair (linePairRep Q L) = L := by
  classical
  have hex : ∃ e ∈ pointPairs Q, lineOfPair e = L := by
    rw [determinedLines, mem_image] at hL
    simpa only [and_assoc] using hL
  rw [linePairRep, dif_pos hex]
  exact ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2⟩

/-- The point where a determined line meets the chosen vertical transversal. -/
def lineHole (Q : Finset Point) (c : ℝ) (L : AffineSubspace ℝ Point) : Point :=
  pairHole c (linePairRep Q L)

lemma pairHole_mem_lineOfPair {Q : Finset Point} (hQ : XInjective Q)
    {e : Sym2 Point} (he : e ∈ pointPairs Q) (c : ℝ) :
    pairHole c e ∈ lineOfPair e := by
  induction e using Sym2.inductionOn with
  | _ p q =>
      rw [mk_mem_pointPairs] at he
      rcases he with ⟨hp, hq, hpq⟩
      have hx : xCoord p ≠ xCoord q := fun h ↦ hpq (hQ hp hq h)
      exact pairHole_mem_line hx c

lemma lineHole_mem {Q : Finset Point} (hQ : XInjective Q)
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines Q) (c : ℝ) :
    lineHole Q c L ∈ L := by
  have hm := pairHole_mem_lineOfPair hQ (linePairRep_spec hL).1 c
  rw [(linePairRep_spec hL).2] at hm
  exact hm

@[simp]
lemma lineHole_xCoord (Q : Finset Point) (c : ℝ) (L : AffineSubspace ℝ Point) :
    xCoord (lineHole Q c L) = c := by
  simp [lineHole, pairHole, verticalPoint]

lemma lineHole_injOn {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q) :
    Set.InjOn (lineHole Q c) (determinedLines Q) := by
  intro L hL M hM hhole
  have hrepL := (linePairRep_spec hL).1
  have hrepM := (linePairRep_spec hM).1
  have hpairs : lineOfPair (linePairRep Q L) = lineOfPair (linePairRep Q M) :=
    (pairHole_eq_iff_line_eq hQ hc hrepL hrepM).mp hhole
  rw [(linePairRep_spec hL).2, (linePairRep_spec hM).2] at hpairs
  exact hpairs

lemma lineHole_not_mem_off {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q) {L : AffineSubspace ℝ Point} :
    lineHole Q c L ∉ Q := by
  intro hmem
  exact good_transversal_ne_x hc hmem (lineHole_xCoord Q c L).symm

def allHoleY (Q : Finset Point) (c : ℝ) : Finset ℝ := by
  classical
  exact (determinedLines Q).image fun L ↦ yCoord (lineHole Q c L)

lemma allHoleY_card {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q) :
    (allHoleY Q c).card = lineCount Q := by
  classical
  rw [allHoleY, lineCount, Finset.card_image_iff]
  intro L hL M hM hy
  apply lineHole_injOn hQ hc hL hM
  ext j
  fin_cases j
  · simp
  · exact hy

lemma exists_fillerY (Q : Finset Point) (c : ℝ) (f : ℕ) :
    ∃ F : Finset ℝ, F.card = f ∧ Disjoint F (allHoleY Q c) := by
  classical
  obtain ⟨T, hsub, hcard⟩ := Infinite.exists_superset_card_eq (allHoleY Q c)
    ((allHoleY Q c).card + f) (by omega)
  refine ⟨T \ allHoleY Q c, ?_, disjoint_sdiff_self_left⟩
  rw [Finset.card_sdiff_of_subset hsub, hcard]
  omega

def selectedHolePoints (Q : Finset Point) (c : ℝ)
    (S : Finset (AffineSubspace ℝ Point)) : Finset Point := by
  classical
  exact S.image (lineHole Q c)

def fillerPoints (c : ℝ) (F : Finset ℝ) : Finset Point := by
  classical
  exact F.image (verticalPoint c)

def basePoints (Q : Finset Point) (c : ℝ)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ) : Finset Point :=
  selectedHolePoints Q c S ∪ fillerPoints c F

def bandConstruction (Q : Finset Point) (c : ℝ)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ) : Finset Point :=
  basePoints Q c S F ∪ Q

lemma verticalPoint_injective (c : ℝ) : Function.Injective (verticalPoint c) := by
  intro y z h
  have hy := congrFun h 1
  simpa [verticalPoint] using hy

lemma selectedHolePoints_card {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q) :
    (selectedHolePoints Q c S).card = S.card := by
  classical
  rw [selectedHolePoints, Finset.card_image_iff]
  exact (lineHole_injOn hQ hc).mono hS

lemma fillerPoints_card (c : ℝ) (F : Finset ℝ) :
    (fillerPoints c F).card = F.card := by
  classical
  rw [fillerPoints, Finset.card_image_of_injective _ (verticalPoint_injective c)]

lemma selected_filler_disjoint {Q : Finset Point} {c : ℝ}
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c)) :
    Disjoint (selectedHolePoints Q c S) (fillerPoints c F) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpS hpF
  rw [selectedHolePoints, mem_image] at hpS
  rw [fillerPoints, mem_image] at hpF
  obtain ⟨L, hLS, rfl⟩ := hpS
  obtain ⟨y, hyF, heq⟩ := hpF
  have hyHole : yCoord (lineHole Q c L) ∈ allHoleY Q c := by
    rw [allHoleY, mem_image]
    exact ⟨L, hS hLS, rfl⟩
  have hyEq : y = yCoord (lineHole Q c L) := by
    have := congrFun heq 1
    simpa [verticalPoint] using this
  exact Finset.disjoint_left.mp hF hyF (hyEq ▸ hyHole)

lemma basePoints_card {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c)) :
    (basePoints Q c S F).card = S.card + F.card := by
  classical
  rw [basePoints, Finset.card_union_of_disjoint (selected_filler_disjoint hS hF),
    selectedHolePoints_card hQ hc hS, fillerPoints_card]

lemma basePoint_xCoord {Q : Finset Point} {c : ℝ}
    {S : Finset (AffineSubspace ℝ Point)} {F : Finset ℝ}
    {p : Point} (hp : p ∈ basePoints Q c S F) : xCoord p = c := by
  classical
  rw [basePoints, mem_union] at hp
  rcases hp with hp | hp
  · rw [selectedHolePoints, mem_image] at hp
    obtain ⟨L, hL, rfl⟩ := hp
    exact lineHole_xCoord Q c L
  · rw [fillerPoints, mem_image] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    simp [verticalPoint]

lemma base_off_disjoint {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ) :
    Disjoint (basePoints Q c S F) Q := by
  classical
  rw [Finset.disjoint_left]
  intro p hpB hpQ
  exact good_transversal_ne_x hc hpQ (basePoint_xCoord hpB).symm

lemma bandConstruction_card {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c)) :
    (bandConstruction Q c S F).card = S.card + F.card + Q.card := by
  classical
  rw [bandConstruction, Finset.card_union_of_disjoint (base_off_disjoint hc S F),
    basePoints_card hQ hc hS hF]

def verticalAxis (c : ℝ) : AffineSubspace ℝ Point :=
  lineThrough (verticalPoint c 0) (verticalPoint c 1)

lemma mem_verticalAxis_iff {c : ℝ} {p : Point} :
    p ∈ verticalAxis c ↔ xCoord p = c := by
  rw [verticalAxis, lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    simp [verticalPoint, AffineMap.lineMap_apply_module]
    ring
  · intro hx
    change p 0 = c at hx
    refine ⟨yCoord p, ?_⟩
    ext j
    fin_cases j
    · simp [verticalPoint, AffineMap.lineMap_apply_module]
      nlinarith
    · simp [verticalPoint, AffineMap.lineMap_apply_module]

lemma pointsOnVerticalAxis {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ) :
    pointsOnLine (bandConstruction Q c S F) (verticalAxis c) = basePoints Q c S F := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_pointsOnLine.mp hp with ⟨hpP, hpaxis⟩
    rw [bandConstruction, mem_union] at hpP
    rcases hpP with hpB | hpQ
    · exact hpB
    · exact (good_transversal_ne_x hc hpQ (mem_verticalAxis_iff.mp hpaxis).symm).elim
  · intro hp
    apply mem_pointsOnLine.mpr
    exact ⟨by simp [bandConstruction, hp],
      mem_verticalAxis_iff.mpr (basePoint_xCoord hp)⟩

lemma verticalAxis_mem_determinedLines {Q : Finset Point} {c : ℝ}
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ)
    (hbase : 2 ≤ (basePoints Q c S F).card) :
    verticalAxis c ∈ determinedLines (bandConstruction Q c S F) := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (basePoints Q c S F).card)
  rw [determinedLines, mem_image]
  refine ⟨s(p, q), ?_, ?_⟩
  · rw [mk_mem_pointPairs]
    exact ⟨by simp [bandConstruction, hp], by simp [bandConstruction, hq], hpq⟩
  · exact lineThrough_eq_of_mem_of_mem_of_ne
      (mem_verticalAxis_iff.mpr (basePoint_xCoord hp))
      (mem_verticalAxis_iff.mpr (basePoint_xCoord hq)) hpq

lemma mem_offLine_iff_eq_lineHole {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines Q)
    {p : Point} (hpx : xCoord p = c) :
    p ∈ L ↔ p = lineHole Q c L := by
  have hhole := lineHole_mem hQ hL c
  constructor
  · intro hpL
    have hrep := linePairRep_spec hL
    induction e : linePairRep Q L using Sym2.inductionOn with
    | _ a b =>
        have he : s(a, b) ∈ pointPairs Q := by simpa [e] using hrep.1
        rw [mk_mem_pointPairs] at he
        rcases he with ⟨ha, hb, hab⟩
        have hx : xCoord a ≠ xCoord b := fun h ↦ hab (hQ ha hb h)
        have hline : lineThrough a b = L := by simpa [e] using hrep.2
        have hpgraph : yCoord p = graphValue s(a, b) c := by
          have := (mem_lineThrough_iff_graph hx).mp (hline ▸ hpL)
          simpa [hpx] using this
        have hhgraph : yCoord (lineHole Q c L) = graphValue s(a, b) c := by
          simp [lineHole, e, pairHole, verticalPoint]
        ext j
        fin_cases j
        · simpa [lineHole_xCoord] using hpx
        · exact hpgraph.trans hhgraph.symm
  · rintro rfl
    exact hhole

lemma lineHole_mem_base_iff {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c))
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines Q) :
    lineHole Q c L ∈ basePoints Q c S F ↔ L ∈ S := by
  classical
  constructor
  · intro hmem
    rw [basePoints, mem_union] at hmem
    rcases hmem with hsel | hfill
    · rw [selectedHolePoints, mem_image] at hsel
      obtain ⟨M, hMS, heq⟩ := hsel
      have hML : M = L := lineHole_injOn hQ hc (hS hMS) hL heq
      simpa [hML] using hMS
    · rw [fillerPoints, mem_image] at hfill
      obtain ⟨y, hyF, heq⟩ := hfill
      have hyEq : y = yCoord (lineHole Q c L) := by
        have := congrFun heq 1
        simpa [verticalPoint] using this
      have hyHole : yCoord (lineHole Q c L) ∈ allHoleY Q c := by
        rw [allHoleY, mem_image]
        exact ⟨L, hL, rfl⟩
      exact (Finset.disjoint_left.mp hF hyF (hyEq ▸ hyHole)).elim
  · intro hLS
    rw [basePoints, mem_union]
    left
    rw [selectedHolePoints, mem_image]
    exact ⟨L, hLS, rfl⟩

lemma pointsOnOffLine_of_selected {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c))
    {L : AffineSubspace ℝ Point} (hL : L ∈ S) :
    pointsOnLine (bandConstruction Q c S F) L =
      insert (lineHole Q c L) (pointsOnLine Q L) := by
  classical
  have hLQ := hS hL
  ext p
  constructor
  · intro hp
    rcases mem_pointsOnLine.mp hp with ⟨hpP, hpL⟩
    rw [bandConstruction, mem_union] at hpP
    rcases hpP with hpB | hpQ
    · rw [mem_insert]
      left
      exact (mem_offLine_iff_eq_lineHole hQ hLQ (basePoint_xCoord hpB)).mp hpL
    · rw [mem_insert]
      right
      exact mem_pointsOnLine.mpr ⟨hpQ, hpL⟩
  · intro hp
    rw [mem_insert] at hp
    apply mem_pointsOnLine.mpr
    rcases hp with rfl | hpQ
    · exact ⟨by simp [bandConstruction, (lineHole_mem_base_iff hQ hc hS hF hLQ).mpr hL],
        lineHole_mem hQ hLQ c⟩
    · rcases mem_pointsOnLine.mp hpQ with ⟨hpQ', hpL⟩
      exact ⟨by simp [bandConstruction, hpQ'], hpL⟩

lemma pointsOnOffLine_of_not_selected {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c))
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines Q) (hLS : L ∉ S) :
    pointsOnLine (bandConstruction Q c S F) L = pointsOnLine Q L := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_pointsOnLine.mp hp with ⟨hpP, hpL⟩
    rw [bandConstruction, mem_union] at hpP
    rcases hpP with hpB | hpQ
    · have heq := (mem_offLine_iff_eq_lineHole hQ hL (basePoint_xCoord hpB)).mp hpL
      subst p
      exact (hLS ((lineHole_mem_base_iff hQ hc hS hF hL).mp hpB)).elim
    · exact mem_pointsOnLine.mpr ⟨hpQ, hpL⟩
  · intro hp
    rcases mem_pointsOnLine.mp hp with ⟨hpQ, hpL⟩
    exact mem_pointsOnLine.mpr ⟨by simp [bandConstruction, hpQ], hpL⟩

lemma determinedLines_mono {Q P : Finset Point} (hQP : Q ⊆ P) :
    determinedLines Q ⊆ determinedLines P := by
  classical
  intro L hL
  rw [determinedLines, mem_image] at hL ⊢
  obtain ⟨e, he, rfl⟩ := hL
  refine ⟨e, ?_, rfl⟩
  rcases e with ⟨p, q⟩
  rw [mk_mem_pointPairs] at he ⊢
  exact ⟨hQP he.1, hQP he.2.1, he.2.2⟩

lemma offLines_subset_construction (Q : Finset Point) (c : ℝ)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ) :
    determinedLines Q ⊆ determinedLines (bandConstruction Q c S F) := by
  apply determinedLines_mono
  intro p hp
  simp [bandConstruction, hp]

lemma rich_line_vertical_or_off {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ)
    {M : AffineSubspace ℝ Point}
    (hM : M ∈ determinedLines (bandConstruction Q c S F))
    (hrich : 3 ≤ (pointsOnLine (bandConstruction Q c S F) M).card) :
    M = verticalAxis c ∨ M ∈ determinedLines Q := by
  classical
  have hthree : 2 < (pointsOnLine (bandConstruction Q c S F) M).card := by omega
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hthree
  rcases mem_pointsOnLine.mp hp with ⟨hpP, hpM⟩
  rcases mem_pointsOnLine.mp hq with ⟨hqP, hqM⟩
  rcases mem_pointsOnLine.mp hr with ⟨hrP, hrM⟩
  rw [bandConstruction, mem_union] at hpP hqP hrP
  have line_eq_of {a b : Point} (ha : a ∈ M) (hb : b ∈ M) (hab : a ≠ b) :
      lineThrough a b = M := (lineOfPair_eq_iff_mem hM hab).mpr ⟨ha, hb⟩
  have off_line_of {a b : Point} (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b)
      (haM : a ∈ M) (hbM : b ∈ M) : M ∈ determinedLines Q := by
    rw [determinedLines, mem_image]
    refine ⟨s(a, b), ?_, ?_⟩
    · rw [mk_mem_pointPairs]
      exact ⟨ha, hb, hab⟩
    · simpa using line_eq_of haM hbM hab
  have vertical_of {a b : Point} (ha : a ∈ basePoints Q c S F)
      (hb : b ∈ basePoints Q c S F) (hab : a ≠ b)
      (haM : a ∈ M) (hbM : b ∈ M) : M = verticalAxis c := by
    rw [← line_eq_of haM hbM hab]
    exact lineThrough_eq_of_mem_of_mem_of_ne
      (mem_verticalAxis_iff.mpr (basePoint_xCoord ha))
      (mem_verticalAxis_iff.mpr (basePoint_xCoord hb)) hab
  rcases hpP with hpB | hpQ
  · rcases hqP with hqB | hqQ
    · exact Or.inl (vertical_of hpB hqB hpq hpM hqM)
    · rcases hrP with hrB | hrQ
      · exact Or.inl (vertical_of hpB hrB hpr hpM hrM)
      · exact Or.inr (off_line_of hqQ hrQ hqr hqM hrM)
  · rcases hqP with hqB | hqQ
    · rcases hrP with hrB | hrQ
      · exact Or.inl (vertical_of hqB hrB hqr hqM hrM)
      · exact Or.inr (off_line_of hpQ hrQ hpr hpM hrM)
    · exact Or.inr (off_line_of hpQ hqQ hpq hpM hqM)

lemma verticalAxis_not_mem_offLines {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q) : verticalAxis c ∉ determinedLines Q := by
  classical
  intro haxis
  rw [determinedLines, mem_image] at haxis
  obtain ⟨e, he, hline⟩ := haxis
  rcases e with ⟨p, q⟩
  rw [mk_mem_pointPairs] at he
  rcases he with ⟨hp, hq, hpq⟩
  have hpaxis : p ∈ verticalAxis c := by
    rw [← hline]
    exact left_mem_lineThrough p q
  exact good_transversal_ne_x hc hp (mem_verticalAxis_iff.mp hpaxis).symm

lemma extraLine_card_eq_two {Q : Finset Point} {c : ℝ}
    (hc : c ∉ badTransversalSet Q)
    (S : Finset (AffineSubspace ℝ Point)) (F : Finset ℝ)
    {M : AffineSubspace ℝ Point}
    (hM : M ∈ determinedLines (bandConstruction Q c S F))
    (hneAxis : M ≠ verticalAxis c) (hMoff : M ∉ determinedLines Q) :
    (pointsOnLine (bandConstruction Q c S F) M).card = 2 := by
  have hlo := two_le_pointsOnLine_card hM
  have hhi : (pointsOnLine (bandConstruction Q c S F) M).card ≤ 2 := by
    by_contra hnot
    have hrich : 3 ≤ (pointsOnLine (bandConstruction Q c S F) M).card := by omega
    rcases rich_line_vertical_or_off hc S F hM hrich with haxis | hoff
    · exact hneAxis haxis
    · exact hMoff hoff
  omega

def bandLineLoss (Q : Finset Point) (S : Finset (AffineSubspace ℝ Point))
    (L : AffineSubspace ℝ Point) : ℕ := by
  classical
  exact ((pointsOnLine Q L).card + if L ∈ S then 1 else 0).choose 2 - 1

lemma offLine_loss_eq {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c))
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines Q) :
    (pointsOnLine (bandConstruction Q c S F) L).card.choose 2 - 1 =
      bandLineLoss Q S L := by
  classical
  by_cases hLS : L ∈ S
  · rw [pointsOnOffLine_of_selected hQ hc hS hF hLS,
      Finset.card_insert_of_notMem]
    · simp [bandLineLoss, hLS]
    · intro hmem
      exact lineHole_not_mem_off hc (mem_pointsOnLine.mp hmem).1
  · rw [pointsOnOffLine_of_not_selected hQ hc hS hF hL hLS]
    simp [bandLineLoss, hLS]

lemma bandConstruction_defect {Q : Finset Point} (hQ : XInjective Q)
    {c : ℝ} (hc : c ∉ badTransversalSet Q)
    {S : Finset (AffineSubspace ℝ Point)} (hS : S ⊆ determinedLines Q)
    {F : Finset ℝ} (hF : Disjoint F (allHoleY Q c))
    (hbase : 2 ≤ (basePoints Q c S F).card) :
    (bandConstruction Q c S F).card.choose 2 - lineCount (bandConstruction Q c S F) =
      (basePoints Q c S F).card.choose 2 - 1 +
        ∑ L ∈ determinedLines Q, bandLineLoss Q S L := by
  classical
  rw [pair_defect_identity]
  let loss := fun L : AffineSubspace ℝ Point ↦
    (pointsOnLine (bandConstruction Q c S F) L).card.choose 2 - 1
  have haxis : verticalAxis c ∈ determinedLines (bandConstruction Q c S F) :=
    verticalAxis_mem_determinedLines S F hbase
  have haxisoff : verticalAxis c ∉ determinedLines Q := verticalAxis_not_mem_offLines hc
  have hoffsub : determinedLines Q ⊆
      (determinedLines (bandConstruction Q c S F)).erase (verticalAxis c) := by
    intro L hL
    rw [mem_erase]
    exact ⟨fun h ↦ haxisoff (h ▸ hL), offLines_subset_construction Q c S F hL⟩
  have hsumextra :
      ∑ L ∈ (determinedLines (bandConstruction Q c S F)).erase (verticalAxis c), loss L =
        ∑ L ∈ determinedLines Q, loss L := by
    symm
    apply Finset.sum_subset hoffsub
    intro M hMbig hMsmall
    rw [mem_erase] at hMbig
    have hcard := extraLine_card_eq_two hc S F hMbig.2 hMbig.1 hMsmall
    simp [loss, hcard]
  calc
    (∑ L ∈ determinedLines (bandConstruction Q c S F), loss L) =
        loss (verticalAxis c) +
          ∑ L ∈ (determinedLines (bandConstruction Q c S F)).erase (verticalAxis c),
            loss L := (Finset.add_sum_erase _ _ haxis).symm
    _ = loss (verticalAxis c) + ∑ L ∈ determinedLines Q, loss L := by
      rw [hsumextra]
    _ = (basePoints Q c S F).card.choose 2 - 1 +
          ∑ L ∈ determinedLines Q, loss L := by
      rw [show loss (verticalAxis c) = (basePoints Q c S F).card.choose 2 - 1 by
        simp only [loss]
        rw [pointsOnVerticalAxis hc S F]]
    _ = (basePoints Q c S F).card.choose 2 - 1 +
          ∑ L ∈ determinedLines Q, bandLineLoss Q S L := by
      congr 1
      apply sum_congr rfl
      intro L hL
      exact offLine_loss_eq hQ hc hS hF hL

lemma parabolaFinset_xInjective (k : ℕ) : XInjective (parabolaFinset k) := by
  classical
  intro p hp q hq hx
  change p ∈ parabolaFinset k at hp
  change q ∈ parabolaFinset k at hq
  rw [parabolaFinset, mem_image] at hp hq
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨j, hj, rfl⟩ := hq
  have hij : (i : ℝ) = (j : ℝ) := by
    simpa [natParabolaPoint, parabolaPoint] using hx
  exact congrArg natParabolaPoint (Nat.cast_injective hij)

lemma pointsOnLine_card_eq_two_of_generalPosition {Q : Finset Point}
    (hQ : GeneralPosition Q) {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines Q) : (pointsOnLine Q L).card = 2 := by
  have hlo := two_le_pointsOnLine_card hL
  have hhi : (pointsOnLine Q L).card ≤ 2 := by
    by_contra hnot
    have hthree : 2 < (pointsOnLine Q L).card := by omega
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hthree
    rcases mem_pointsOnLine.mp hp with ⟨hpQ, hpL⟩
    rcases mem_pointsOnLine.mp hq with ⟨hqQ, hqL⟩
    rcases mem_pointsOnLine.mp hr with ⟨hrQ, hrL⟩
    have hpqline : lineThrough p q = L :=
      (lineOfPair_eq_iff_mem hL hpq).mpr ⟨hpL, hqL⟩
    exact hQ hpQ hqQ hrQ hpq hpr.symm hqr.symm (by simpa [hpqline] using hrL)
  omega

lemma even_bandLineLoss_of_mem {k : ℕ} {S : Finset (AffineSubspace ℝ Point)}
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines (parabolaFinset k))
    (hLS : L ∈ S) : bandLineLoss (parabolaFinset k) S L = 2 := by
  classical
  rw [bandLineLoss, pointsOnLine_card_eq_two_of_generalPosition
    (parabolaFinset_generalPosition k) hL]
  simp [hLS]

lemma even_bandLineLoss_of_not_mem {k : ℕ} {S : Finset (AffineSubspace ℝ Point)}
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines (parabolaFinset k))
    (hLS : L ∉ S) : bandLineLoss (parabolaFinset k) S L = 0 := by
  classical
  rw [bandLineLoss, pointsOnLine_card_eq_two_of_generalPosition
    (parabolaFinset_generalPosition k) hL]
  simp [hLS]

lemma even_bandLoss_sum {k : ℕ} {S : Finset (AffineSubspace ℝ Point)}
    (hS : S ⊆ determinedLines (parabolaFinset k)) :
    ∑ L ∈ determinedLines (parabolaFinset k), bandLineLoss (parabolaFinset k) S L =
      2 * S.card := by
  classical
  calc
    (∑ L ∈ determinedLines (parabolaFinset k), bandLineLoss (parabolaFinset k) S L) =
        ∑ L ∈ determinedLines (parabolaFinset k), if L ∈ S then 2 else 0 := by
      apply sum_congr rfl
      intro L hL
      by_cases hLS : L ∈ S
      · simp [hLS, even_bandLineLoss_of_mem hL hLS]
      · simp [hLS, even_bandLineLoss_of_not_mem hL hLS]
    _ = ∑ L ∈ S, if L ∈ S then 2 else 0 := by
      symm
      apply Finset.sum_subset hS
      intro L hL hLS
      simp [hLS]
    _ = 2 * S.card := by simp [mul_comm]

lemma choose_two_add (a k : ℕ) :
    (a + k).choose 2 = a.choose 2 + a * k + k.choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hak : ((a + k) + 1).choose 2 = (a + k) + (a + k).choose 2 := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]
      have hk : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]
      rw [show a + (k + 1) = (a + k) + 1 by omega, hak, ih, hk,
        Nat.mul_add, Nat.mul_one]
      omega

lemma exists_even_band_configuration (a k s : ℕ) (ha : 2 ≤ a)
    (hsPairs : s ≤ k.choose 2) (hsBase : s ≤ a) :
    ∃ P : Finset Point, P.card = a + k ∧
      lineCount P = a * k + k.choose 2 + 1 - 2 * s := by
  classical
  let Q := parabolaFinset k
  have hQx : XInjective Q := parabolaFinset_xInjective k
  have hDcard : (determinedLines Q).card = k.choose 2 := by
    change lineCount Q = k.choose 2
    rw [lineCount_eq_choose_of_generalPosition (parabolaFinset_generalPosition k),
      parabolaFinset_card]
  have hsD : s ≤ (determinedLines Q).card := by simpa [hDcard] using hsPairs
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hsD
  obtain ⟨c, hc⟩ := exists_good_transversal Q
  obtain ⟨F, hFcard, hF⟩ := exists_fillerY Q c (a - s)
  have hbasecard : (basePoints Q c S F).card = a := by
    rw [basePoints_card hQx hc hS hF, hScard, hFcard]
    omega
  have hPcard : (bandConstruction Q c S F).card = a + k := by
    rw [bandConstruction_card hQx hc hS hF, hScard, hFcard]
    change s + (a - s) + (parabolaFinset k).card = a + k
    rw [parabolaFinset_card]
    omega
  refine ⟨bandConstruction Q c S F, hPcard, ?_⟩
  have hdef := bandConstruction_defect hQx hc hS hF (by omega : 2 ≤ (basePoints Q c S F).card)
  rw [hPcard, hbasecard, even_bandLoss_sum hS, hScard] at hdef
  have htotal := choose_two_add a k
  have hchooseA : 1 ≤ a.choose 2 := by
    calc
      1 = (2 : ℕ).choose 2 := by decide
      _ ≤ a.choose 2 := Nat.choose_le_choose 2 ha
  have htarget : 2 * s ≤ a * k + k.choose 2 + 1 := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp at hsPairs
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have haMul : a ≤ a * k := Nat.le_mul_of_pos_right a hkpos
      omega
  have hle := lineCount_le_choose (bandConstruction Q c S F)
  rw [hPcard, htotal] at hle
  rw [htotal] at hdef
  omega

lemma oneTripleFinset_xInjective (t : ℕ) : XInjective (oneTripleFinset t) := by
  classical
  intro p hp q hq hx
  change p ∈ oneTripleFinset t at hp
  change q ∈ oneTripleFinset t at hq
  simp only [oneTripleFinset, mem_union, specialFinset, farParabolaFinset,
    mem_image, mem_range] at hp hq
  rcases hp with ⟨c, hc, rfl⟩ | ⟨i, hi, rfl⟩
  · rcases hq with ⟨d, hd, rfl⟩ | ⟨j, hj, rfl⟩
    · have hcd : (c : ℝ) = (d : ℝ) := by simpa [specialPoint] using hx
      exact congrArg specialPoint (Nat.cast_injective hcd)
    · exfalso
      have hc' : (c : ℝ) ≤ 2 := by exact_mod_cast (by omega : c ≤ 2)
      have hj' : (0 : ℝ) ≤ (j : ℝ) := by positivity
      simp [specialPoint, farParabolaPoint, parabolaPoint] at hx
      linarith
  · rcases hq with ⟨d, hd, rfl⟩ | ⟨j, hj, rfl⟩
    · exfalso
      have hd' : (d : ℝ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
      have hi' : (0 : ℝ) ≤ (i : ℝ) := by positivity
      simp [specialPoint, farParabolaPoint, parabolaPoint] at hx
      linarith
    · have hij : i = j := by
        simpa [farParabolaPoint, parabolaPoint] using hx
      exact congrArg farParabolaPoint hij

lemma lineCount_oneTripleFinset (t : ℕ) :
    lineCount (oneTripleFinset t) = (t + 3).choose 2 - 2 := by
  have hdef := oneTriple_pair_defect t
  rw [oneTripleFinset_card] at hdef
  have hle := lineCount_le_choose (oneTripleFinset t)
  rw [oneTripleFinset_card] at hle
  have hchoose : 2 ≤ (t + 3).choose 2 := by
    calc
      2 ≤ (3 : ℕ).choose 2 := by decide
      _ ≤ (t + 3).choose 2 := Nat.choose_le_choose 2 (by omega)
  omega

lemma odd_axis_bandLineLoss {t : ℕ} {S : Finset (AffineSubspace ℝ Point)}
    (haxis : specialAxis ∈ S) :
    bandLineLoss (oneTripleFinset t) S specialAxis = 5 := by
  classical
  rw [bandLineLoss, pointsOnSpecialAxis, specialFinset_card]
  simp [haxis, Nat.choose]

lemma odd_other_bandLineLoss_of_mem {t : ℕ} {S : Finset (AffineSubspace ℝ Point)}
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines (oneTripleFinset t))
    (hne : L ≠ specialAxis) (hLS : L ∈ S) :
    bandLineLoss (oneTripleFinset t) S L = 2 := by
  classical
  rw [bandLineLoss, pointsOnLine_card_eq_two_of_ne_axis hL hne]
  simp [hLS]

lemma odd_other_bandLineLoss_of_not_mem {t : ℕ} {S : Finset (AffineSubspace ℝ Point)}
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines (oneTripleFinset t))
    (hne : L ≠ specialAxis) (hLS : L ∉ S) :
    bandLineLoss (oneTripleFinset t) S L = 0 := by
  classical
  rw [bandLineLoss, pointsOnLine_card_eq_two_of_ne_axis hL hne]
  simp [hLS]

def addSpecialAxis (T : Finset (AffineSubspace ℝ Point)) :
    Finset (AffineSubspace ℝ Point) := by
  classical
  exact insert specialAxis T

def eraseSpecialAxis (D : Finset (AffineSubspace ℝ Point)) :
    Finset (AffineSubspace ℝ Point) := by
  classical
  exact D.erase specialAxis

lemma odd_bandLoss_sum {t : ℕ} {T : Finset (AffineSubspace ℝ Point)}
    (hT : T ⊆ eraseSpecialAxis (determinedLines (oneTripleFinset t))) :
    ∑ L ∈ determinedLines (oneTripleFinset t),
        bandLineLoss (oneTripleFinset t) (addSpecialAxis T) L = 5 + 2 * T.card := by
  classical
  let D := determinedLines (oneTripleFinset t)
  have haxisD : specialAxis ∈ D := specialAxis_mem_determinedLines t
  have haxisT : specialAxis ∉ T := by
    intro h
    exact (Finset.mem_erase.mp (show specialAxis ∈ D.erase specialAxis by
      simpa [eraseSpecialAxis, D] using hT h)).1 rfl
  have hrest :
      ∑ L ∈ D.erase specialAxis,
          bandLineLoss (oneTripleFinset t) (addSpecialAxis T) L = 2 * T.card := by
    calc
      (∑ L ∈ D.erase specialAxis,
          bandLineLoss (oneTripleFinset t) (addSpecialAxis T) L) =
          ∑ L ∈ D.erase specialAxis, if L ∈ T then 2 else 0 := by
        apply sum_congr rfl
        intro L hL
        have hLD := (Finset.mem_erase.mp hL).2
        have hne := (Finset.mem_erase.mp hL).1
        by_cases hLT : L ∈ T
        · have hLS : L ∈ addSpecialAxis T := by simp [addSpecialAxis, hLT]
          simp [hLT, odd_other_bandLineLoss_of_mem hLD hne hLS]
        · have hLS : L ∉ addSpecialAxis T := by simp [addSpecialAxis, hne, hLT]
          simp [hLT, odd_other_bandLineLoss_of_not_mem hLD hne hLS]
      _ = ∑ L ∈ T, if L ∈ T then 2 else 0 := by
        symm
        apply Finset.sum_subset hT
        intro L hL hLT
        simp [hLT]
      _ = 2 * T.card := by simp [mul_comm]
  calc
    (∑ L ∈ D, bandLineLoss (oneTripleFinset t) (addSpecialAxis T) L) =
        bandLineLoss (oneTripleFinset t) (addSpecialAxis T) specialAxis +
          ∑ L ∈ D.erase specialAxis,
            bandLineLoss (oneTripleFinset t) (addSpecialAxis T) L :=
      (Finset.add_sum_erase _ _ haxisD).symm
    _ = 5 + 2 * T.card := by
      rw [odd_axis_bandLineLoss (by simp [addSpecialAxis]), hrest]

lemma exists_odd_band_configuration (a k s : ℕ) (ha : 2 ≤ a) (hk : 3 ≤ k)
    (hsPairs : s ≤ k.choose 2 - 3) (hsBase : s + 1 ≤ a) :
    ∃ P : Finset Point, P.card = a + k ∧
      lineCount P = a * k + k.choose 2 + 1 - 5 - 2 * s := by
  classical
  let t := k - 3
  let Q := oneTripleFinset t
  have ht : t + 3 = k := by dsimp [t]; omega
  have hQcard : Q.card = k := by
    dsimp [Q]
    rw [oneTripleFinset_card, ht]
  have hQx : XInjective Q := oneTripleFinset_xInjective t
  have haxisD : specialAxis ∈ determinedLines Q := by
    dsimp [Q]
    exact specialAxis_mem_determinedLines t
  have hchooseK : 3 ≤ k.choose 2 := by
    calc
      3 = (3 : ℕ).choose 2 := by decide
      _ ≤ k.choose 2 := Nat.choose_le_choose 2 hk
  have hDcard : (determinedLines Q).card = k.choose 2 - 2 := by
    change lineCount Q = k.choose 2 - 2
    dsimp [Q]
    rw [lineCount_oneTripleFinset, ht]
  have hEraseCard : (eraseSpecialAxis (determinedLines Q)).card = k.choose 2 - 3 := by
    rw [eraseSpecialAxis, Finset.card_erase_of_mem haxisD, hDcard]
    omega
  have hsErase : s ≤ (eraseSpecialAxis (determinedLines Q)).card := by
    simpa [hEraseCard] using hsPairs
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hsErase
  let S := addSpecialAxis T
  have haxisT : specialAxis ∉ T := by
    intro h
    have := hT h
    rw [eraseSpecialAxis, Finset.mem_erase] at this
    exact this.1 rfl
  have hScard : S.card = s + 1 := by
    dsimp [S, addSpecialAxis]
    rw [Finset.card_insert_of_notMem haxisT, hTcard]
  have hS : S ⊆ determinedLines Q := by
    intro L hL
    dsimp [S, addSpecialAxis] at hL
    rw [Finset.mem_insert] at hL
    rcases hL with rfl | hLT
    · exact haxisD
    · have := hT hLT
      rw [eraseSpecialAxis, Finset.mem_erase] at this
      exact this.2
  obtain ⟨c, hc⟩ := exists_good_transversal Q
  obtain ⟨F, hFcard, hF⟩ := exists_fillerY Q c (a - (s + 1))
  have hbasecard : (basePoints Q c S F).card = a := by
    rw [basePoints_card hQx hc hS hF, hScard, hFcard]
    omega
  have hPcard : (bandConstruction Q c S F).card = a + k := by
    rw [bandConstruction_card hQx hc hS hF, hScard, hFcard, hQcard]
    omega
  refine ⟨bandConstruction Q c S F, hPcard, ?_⟩
  have hdef := bandConstruction_defect hQx hc hS hF (by omega : 2 ≤ (basePoints Q c S F).card)
  have hloss : ∑ L ∈ determinedLines Q, bandLineLoss Q S L = 5 + 2 * s := by
    dsimp [Q, S]
    rw [odd_bandLoss_sum hT, hTcard]
  rw [hPcard, hbasecard, hloss] at hdef
  have htotal := choose_two_add a k
  have hchooseA : 1 ≤ a.choose 2 := by
    calc
      1 = (2 : ℕ).choose 2 := by decide
      _ ≤ a.choose 2 := Nat.choose_le_choose 2 ha
  have hmul : 3 * a ≤ a * k := by
    simpa [mul_comm] using Nat.mul_le_mul_left a hk
  have htarget : 5 + 2 * s ≤ a * k + k.choose 2 + 1 := by omega
  have hle := lineCount_le_choose (bandConstruction Q c S F)
  rw [hPcard, htotal] at hle
  rw [htotal] at hdef
  omega

/-- Upper endpoint of the `k`th Erdős--Salamon band. -/
def Mmax (n k : ℕ) : ℕ :=
  k * (n - k) + k.choose 2 + 1

/-- Kelly--Moser lower endpoint of the `k`th band. -/
def Mmin (n k : ℕ) : ℕ :=
  k * (n - k) - k.choose 2 + 1

/-- The transition index `⌊√(n+2)⌋`. -/
def transitionIndex (n : ℕ) : ℕ :=
  Nat.sqrt (n + 2)

/-- Values in a complete low band. -/
def BandValue (n k m : ℕ) : Prop :=
  Mmin n k ≤ m ∧ m ≤ Mmax n k ∧
    m ≠ Mmax n k - 1 ∧ m ≠ Mmax n k - 3

/-- Bottom of the terminal interval in the five Erdős--Salamon cases. -/
def continuumBottom (n : ℕ) : ℕ :=
  let K := transitionIndex n
  if K * K = n + 2 ∨ K * K = n + 1 then
    Mmax n (K - 1) - 2
  else if K * K = n ∨ K * K + 1 = n then
    Mmax n (K - 1)
  else
    Mmin n K

/-- The explicit eventual spectrum described by Erdős and Salamon. -/
def ClassifiedValue (n m : ℕ) : Prop :=
  (∃ k < transitionIndex n, BandValue n k m) ∨
  (continuumBottom n ≤ m ∧ m ≤ n.choose 2 - 4) ∨
  m = n.choose 2 - 2 ∨ m = n.choose 2

lemma Mmax_zero (n : ℕ) : Mmax n 0 = 1 := by simp [Mmax]

lemma Mmin_zero (n : ℕ) : Mmin n 0 = 1 := by simp [Mmin]

lemma Mmax_one (n : ℕ) (hn : 1 ≤ n) : Mmax n 1 = n := by
  simp [Mmax]
  omega

lemma Mmin_one (n : ℕ) (hn : 1 ≤ n) : Mmin n 1 = n := by
  simp [Mmin]
  omega

lemma Mmax_two (n : ℕ) (hn : 2 ≤ n) : Mmax n 2 = 2 * n - 2 := by
  norm_num [Mmax, Nat.choose_two_right]
  omega

lemma Mmin_two (n : ℕ) (hn : 3 ≤ n) : Mmin n 2 = 2 * n - 4 := by
  norm_num [Mmin, Nat.choose_two_right]
  rw [Nat.mul_sub_left_distrib]
  omega

lemma possible_Mmax_sub_even {n k s : ℕ} (hkn : k ≤ n)
    (ha : 2 ≤ n - k) (hsPairs : s ≤ k.choose 2) (hsBase : s ≤ n - k) :
    PossibleLineCount n (Mmax n k - 2 * s) := by
  obtain ⟨P, hPcard, hPline⟩ :=
    exists_even_band_configuration (n - k) k s ha hsPairs hsBase
  refine ⟨P, ?_, ?_⟩
  · omega
  · rw [hPline]
    simp only [Mmax]
    rw [mul_comm k (n - k)]

lemma possible_Mmax_sub_odd {n k s : ℕ} (hkn : k ≤ n)
    (ha : 2 ≤ n - k) (hk : 3 ≤ k)
    (hsPairs : s ≤ k.choose 2 - 3) (hsBase : s + 1 ≤ n - k) :
    PossibleLineCount n (Mmax n k - 5 - 2 * s) := by
  obtain ⟨P, hPcard, hPline⟩ :=
    exists_odd_band_configuration (n - k) k s ha hk hsPairs hsBase
  refine ⟨P, ?_, ?_⟩
  · omega
  · rw [hPline]
    simp only [Mmax]
    rw [mul_comm k (n - k)]

lemma full_band_possible {n k m : ℕ} (hkn : k ≤ n) (ha2 : 2 ≤ n - k)
    (hfull : k.choose 2 ≤ n - k) (hm : BandValue n k m) :
    PossibleLineCount n m := by
  rcases hm with ⟨hmin, hmax, hgap1, hgap3⟩
  let a := n - k
  let C := k.choose 2
  let top := Mmax n k
  let d := top - m
  have hprod : C ≤ a * k := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [C]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      exact hfull.trans (Nat.le_mul_of_pos_right a hkpos)
  have htop : top = a * k + C + 1 := by
    simp [top, Mmax, a, C, mul_comm]
  have hbottom : Mmin n k = a * k - C + 1 := by
    simp [Mmin, a, C, mul_comm]
  have hdadd : d + m = top := by dsimp [d]; omega
  have hdle : d ≤ 2 * C := by
    rw [hbottom] at hmin
    omega
  obtain ⟨r, hdr | hdr⟩ := Nat.even_or_odd' d
  · have hrC : r ≤ C := by omega
    have hra : r ≤ a := hrC.trans hfull
    have hmform : m = top - 2 * r := by omega
    rw [hmform]
    exact possible_Mmax_sub_even hkn ha2 hrC hra
  · have hrC : r ≤ C := by omega
    have hr2 : 2 ≤ r := by
      by_contra hr
      have hrle : r ≤ 1 := by omega
      interval_cases r
      · have hm1 : m = top - 1 := by omega
        exact hgap1 hm1
      · have hm3 : m = top - 3 := by omega
        exact hgap3 hm3
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hkle : k ≤ 2 := by omega
      have hCle : C ≤ 1 := by
        calc
          C = k.choose 2 := rfl
          _ ≤ (2 : ℕ).choose 2 := Nat.choose_le_choose 2 hkle
          _ = 1 := by decide
      omega
    let s := r - 2
    have hsform : r = s + 2 := by dsimp [s]; omega
    have hsPairs : s ≤ C - 3 := by omega
    have hsBase : s + 1 ≤ a := by omega
    have hmform : m = top - 5 - 2 * s := by omega
    rw [hmform]
    exact possible_Mmax_sub_odd hkn ha2 hk3 hsPairs hsBase

lemma partial_band_possible {n k m : ℕ} (hkn : k ≤ n) (ha2 : 2 ≤ n - k)
    (hpartial : n - k < k.choose 2)
    (hlower : Mmax n k - 2 * (n - k) ≤ m) (hupper : m ≤ Mmax n k)
    (hgap1 : m ≠ Mmax n k - 1) (hgap3 : m ≠ Mmax n k - 3) :
    PossibleLineCount n m := by
  let a := n - k
  let C := k.choose 2
  let top := Mmax n k
  let d := top - m
  have hdadd : d + m = top := by dsimp [d]; omega
  have hdle : d ≤ 2 * a := by omega
  have hk3 : 3 ≤ k := by
    have hC3 : 3 ≤ C := by omega
    by_contra hk
    have hkle : k ≤ 2 := by omega
    have hCle : C ≤ 1 := by
      calc
        C = k.choose 2 := rfl
        _ ≤ (2 : ℕ).choose 2 := Nat.choose_le_choose 2 hkle
        _ = 1 := by decide
    omega
  obtain ⟨r, hdr | hdr⟩ := Nat.even_or_odd' d
  · have hra : r ≤ a := by omega
    have hrC : r ≤ C := by omega
    have hmform : m = top - 2 * r := by omega
    rw [hmform]
    exact possible_Mmax_sub_even hkn ha2 hrC hra
  · have hra : r ≤ a := by omega
    have hr2 : 2 ≤ r := by
      by_contra hr
      have hrle : r ≤ 1 := by omega
      interval_cases r
      · exact hgap1 (by omega)
      · exact hgap3 (by omega)
    let s := r - 2
    have hsform : r = s + 2 := by dsimp [s]; omega
    have hsPairs : s ≤ C - 3 := by omega
    have hsBase : s + 1 ≤ a := by omega
    have hmform : m = top - 5 - 2 * s := by omega
    rw [hmform]
    exact possible_Mmax_sub_odd hkn ha2 hk3 hsPairs hsBase

lemma Mmax_succ {n k : ℕ} (hk : k < n) :
    Mmax n (k + 1) = Mmax n k + (n - k - 1) := by
  let a := n - k - 1
  have hn : n = k + 1 + a := by dsimp [a]; omega
  rw [hn]
  have hsub0 : k + 1 + a - k = a + 1 := by omega
  have hsub1 : k + 1 + a - (k + 1) = a := by omega
  have hsub2 : k + 1 + a - k - 1 = a := by omega
  simp only [Mmax]
  rw [hsub0, hsub1, show a + 1 - 1 = a by omega,
    Nat.choose_succ_succ', Nat.choose_one_right]
  ring

lemma two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rw [mul_comm 2, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self k)]

lemma Mmax_pred_sub_Mmin {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hchoose : k.choose 2 ≤ k * (n - k)) :
    Mmax n (k - 1) - Mmin n k = k * k - n := by
  let a := n - k
  let C := k.choose 2
  have hkform : k = (k - 1) + 1 := by omega
  have hnform : n = k + a := by dsimp [a]; omega
  have hsub : n - (k - 1) = a + 1 := by dsimp [a]; omega
  have hC : C = (k - 1).choose 2 + (k - 1) := by
    dsimp [C]
    conv_lhs => rw [hkform]
    rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm]
  have hprev : Mmax n (k - 1) = (k - 1) * a + C + 1 := by
    rw [Mmax, hsub, hC]
    ring
  have hmin : Mmin n k = k * a - C + 1 := by
    simp [Mmin, a, C]
  have hka : k * a = (k - 1) * a + a := by
    conv_lhs => rw [hkform]
    ring
  have hkk : k * k = 2 * C + k := by
    have ht := two_mul_choose_two k
    dsimp [C]
    rw [show k * k = k * (k - 1) + k by
      nth_rewrite 1 [hkform]; ring]
    omega
  have hchoose' : C ≤ (k - 1) * a + a := by
    change C ≤ k * a at hchoose
    rwa [hka] at hchoose
  have hleft : Mmax n (k - 1) - Mmin n k = 2 * C - a := by
    rw [hprev, hmin, hka]
    omega
  have hright : k * k - n = 2 * C - a := by
    rw [hnform, hkk]
    omega
  exact hleft.trans hright.symm

lemma Mmax_pred_add_n_eq_Mmin_add_sq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hchoose : k.choose 2 ≤ k * (n - k)) :
    Mmax n (k - 1) + n = Mmin n k + k * k := by
  let a := n - k
  let C := k.choose 2
  have hkform : k = (k - 1) + 1 := by omega
  have hnform : n = k + a := by dsimp [a]; omega
  have hsub : n - (k - 1) = a + 1 := by dsimp [a]; omega
  have hC : C = (k - 1).choose 2 + (k - 1) := by
    dsimp [C]
    conv_lhs => rw [hkform]
    rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm]
  have hprev : Mmax n (k - 1) = (k - 1) * a + C + 1 := by
    rw [Mmax, hsub, hC]
    ring
  have hmin : Mmin n k = k * a - C + 1 := by
    simp [Mmin, a, C]
  have hka : k * a = (k - 1) * a + a := by
    conv_lhs => rw [hkform]
    ring
  have hkk : k * k = 2 * C + k := by
    have ht := two_mul_choose_two k
    dsimp [C]
    rw [show k * k = k * (k - 1) + k by
      nth_rewrite 1 [hkform]; ring]
    omega
  have hchoose' : C ≤ (k - 1) * a + a := by
    change C ≤ k * a at hchoose
    rwa [hka] at hchoose
  rw [hprev, hmin, hnform, hka, hkk]
  omega

lemma transitionIndex_sq_le (n : ℕ) :
    transitionIndex n * transitionIndex n ≤ n + 2 := by
  exact Nat.sqrt_le (n + 2)

lemma transitionIndex_next_sq_gt (n : ℕ) :
    n + 2 < (transitionIndex n + 1) * (transitionIndex n + 1) := by
  exact Nat.lt_succ_sqrt (n + 2)

lemma transitionIndex_ge_ten {n : ℕ} (hn : 100 ≤ n) :
    10 ≤ transitionIndex n := by
  simp only [transitionIndex, Nat.le_sqrt]
  norm_num
  omega

lemma twice_transitionIndex_add_two_le {n : ℕ} (hn : 100 ≤ n) :
    2 * transitionIndex n + 2 ≤ n := by
  have hK := transitionIndex_ge_ten hn
  have hs := transitionIndex_sq_le n
  nlinarith

lemma transitionIndex_le_n {n : ℕ} (hn : 100 ≤ n) : transitionIndex n ≤ n := by
  have h := twice_transitionIndex_add_two_le hn
  omega

lemma transitionIndex_full {n : ℕ} (hn : 100 ≤ n) :
    (transitionIndex n).choose 2 ≤ n - transitionIndex n := by
  let K := transitionIndex n
  have hK : 10 ≤ K := transitionIndex_ge_ten hn
  have hs : K * K ≤ n + 2 := transitionIndex_sq_le n
  have htwice : 2 * K.choose 2 = K * (K - 1) := two_mul_choose_two K
  have hnK : K ≤ n := transitionIndex_le_n hn
  have hgap : 2 * K + 2 ≤ n := twice_transitionIndex_add_two_le hn
  have hpred : K - 1 + 1 = K := by omega
  have hkmul : K * (K - 1) + K = K * K := by
    calc
      K * (K - 1) + K = K * (K - 1) + K * 1 := by rw [mul_one]
      _ = K * ((K - 1) + 1) := by rw [Nat.mul_add]
      _ = K * K := by rw [hpred]
  have hsub : n - K + K = n := Nat.sub_add_cancel hnK
  have hdouble : 2 * (n - K) + 2 * K = 2 * n := by omega
  have htwicele : 2 * K.choose 2 ≤ 2 * (n - K) := by
    rw [htwice]
    nlinarith
  change K.choose 2 ≤ n - K
  exact Nat.le_of_mul_le_mul_left htwicele (by norm_num)

lemma index_le_transition_full {n k : ℕ} (hn : 100 ≤ n)
    (hk : k ≤ transitionIndex n) : k.choose 2 ≤ n - k := by
  have hchoose := Nat.choose_le_choose 2 hk
  exact hchoose.trans <| (transitionIndex_full hn).trans (Nat.sub_le_sub_left hk n)

lemma transitionIndex_gap_two {n : ℕ} (hn : 100 ≤ n) :
    2 ≤ n - transitionIndex n := by
  have h := twice_transitionIndex_add_two_le hn
  omega

lemma continuum_base_possible {n m : ℕ} (hn : 100 ≤ n)
    (hlow : continuumBottom n ≤ m)
    (hhigh : m ≤ Mmax n (transitionIndex n) - 4) :
    PossibleLineCount n m := by
  let K := transitionIndex n
  change m ≤ Mmax n K - 4 at hhigh
  have hK : 10 ≤ K := transitionIndex_ge_ten hn
  have hKn : K ≤ n := transitionIndex_le_n hn
  have ha2 : 2 ≤ n - K := transitionIndex_gap_two hn
  have hfull : K.choose 2 ≤ n - K := transitionIndex_full hn
  have hprod : K.choose 2 ≤ K * (n - K) := by
    exact hfull.trans (Nat.le_mul_of_pos_left (n - K) (by omega))
  have hendpoint : Mmax n (K - 1) + n = Mmin n K + K * K :=
    Mmax_pred_add_n_eq_Mmin_add_sq (by omega) hKn hprod
  have hprevKn : K - 1 ≤ n := by omega
  have hprevBase : 1 ≤ n - (K - 1) := by omega
  have hprevPairs : 1 ≤ (K - 1).choose 2 := by
    norm_num [Nat.one_le_iff_ne_zero, Nat.choose_eq_zero_iff]
    omega
  have hprevTop : PossibleLineCount n (Mmax n (K - 1)) := by
    simpa using (possible_Mmax_sub_even (n := n) (k := K - 1) (s := 0)
      hprevKn (by omega) (by omega) (by omega))
  have hprevTwo : PossibleLineCount n (Mmax n (K - 1) - 2) := by
    simpa using (possible_Mmax_sub_even (n := n) (k := K - 1) (s := 1)
      hprevKn (by omega) hprevPairs hprevBase)
  have htop4 : 4 ≤ Mmax n K := by
    have hmul : 10 * 2 ≤ K * (n - K) := Nat.mul_le_mul hK ha2
    simp only [Mmax]
    omega
  have hcurrent (hmin : Mmin n K ≤ m) : PossibleLineCount n m := by
    apply full_band_possible hKn ha2 hfull
    refine ⟨hmin, ?_, ?_, ?_⟩ <;> omega
  by_cases hp2 : K * K = n + 2
  · have hb : continuumBottom n = Mmax n (K - 1) - 2 := by
      simp [continuumBottom, K, hp2]
    apply hcurrent
    rw [hb] at hlow
    omega
  by_cases hp1 : K * K = n + 1
  · have hb : continuumBottom n = Mmax n (K - 1) - 2 := by
      simp [continuumBottom, K, hp1]
    rw [hb] at hlow
    by_cases hm : Mmin n K ≤ m
    · exact hcurrent hm
    · have : m = Mmax n (K - 1) - 2 := by omega
      rwa [this]
  by_cases hz : K * K = n
  · have hb : continuumBottom n = Mmax n (K - 1) := by
      simp [continuumBottom, K, hp2, hp1, hz]
    apply hcurrent
    rw [hb] at hlow
    omega
  by_cases hm1 : K * K + 1 = n
  · have hb : continuumBottom n = Mmax n (K - 1) := by
      simp [continuumBottom, K, hp2, hp1, hz, hm1]
    rw [hb] at hlow
    by_cases hm : Mmin n K ≤ m
    · exact hcurrent hm
    · have : m = Mmax n (K - 1) := by omega
      rwa [this]
  · have hb : continuumBottom n = Mmin n K := by
      simp [continuumBottom, K, hp2, hp1, hz, hm1]
    exact hcurrent (by rwa [← hb])

lemma continuum_step_possible {n j : ℕ} (hn : 100 ≤ n)
    (hKj : transitionIndex n ≤ j) (hj : j + 1 ≤ n - 3)
    (hprevious : ∀ m, continuumBottom n ≤ m → m ≤ Mmax n j - 4 →
      PossibleLineCount n m) :
    ∀ m, continuumBottom n ≤ m → m ≤ Mmax n (j + 1) - 4 →
      PossibleLineCount n m := by
  intro m hbottom htop
  by_cases hold : m ≤ Mmax n j - 4
  · exact hprevious m hbottom hold
  let k := j + 1
  let a := n - k
  change m ≤ Mmax n k - 4 at htop
  have hkform : k = j + 1 := rfl
  have hkn : k ≤ n := by dsimp [k]; omega
  have ha3 : 3 ≤ a := by dsimp [a, k]; omega
  have ha2 : 2 ≤ n - k := by change 2 ≤ a; omega
  have hjn : j < n := by omega
  have hsucc : Mmax n k = Mmax n j + a := by
    have haeq : n - j - 1 = a := by dsimp [a, k]; omega
    rw [hkform, Mmax_succ hjn, haeq]
  have hKnext : transitionIndex n + 1 ≤ k := by dsimp [k]; omega
  have hsqrt := transitionIndex_next_sq_gt n
  have hsquare : n + 3 ≤ k * k := by
    have hmul := Nat.mul_le_mul hKnext hKnext
    nlinarith
  have hold4 : 4 ≤ Mmax n j := by
    have hj10 : 10 ≤ j := (transitionIndex_ge_ten hn).trans hKj
    have hbase4 : 4 ≤ n - j := by omega
    have hmul : 10 * 4 ≤ j * (n - j) := Nat.mul_le_mul hj10 hbase4
    simp only [Mmax]
    omega
  have hnew4 : 4 ≤ Mmax n k := by
    have hk2 : 2 ≤ k := by
      exact (show 2 ≤ transitionIndex n + 1 by
        have := transitionIndex_ge_ten hn
        omega).trans hKnext
    have hbase3 : 3 ≤ n - k := by change 3 ≤ a; exact ha3
    have hmul : 2 * 3 ≤ k * (n - k) := Nat.mul_le_mul hk2 hbase3
    simp only [Mmax]
    omega
  have hmnear : Mmax n j - 3 ≤ m := by omega
  have hmupper : m ≤ Mmax n k := by omega
  have hgap1 : m ≠ Mmax n k - 1 := by omega
  have hgap3 : m ≠ Mmax n k - 3 := by omega
  by_cases hfull : k.choose 2 ≤ n - k
  · have hprod : k.choose 2 ≤ k * (n - k) :=
      hfull.trans (Nat.le_mul_of_pos_left (n - k) (by omega))
    have hendpoint : Mmax n j + n = Mmin n k + k * k := by
      simpa [k] using
        (Mmax_pred_add_n_eq_Mmin_add_sq (n := n) (k := k) (by omega) hkn hprod)
    apply full_band_possible hkn ha2 hfull
    refine ⟨?_, hmupper, hgap1, hgap3⟩
    omega
  · have hpartial : n - k < k.choose 2 := by omega
    apply partial_band_possible hkn ha2 hpartial
    · rw [hsucc]
      dsimp [a] at ha3
      omega
    · exact hmupper
    · exact hgap1
    · exact hgap3

lemma continuum_through_band {n j : ℕ} (hn : 100 ≤ n)
    (hKj : transitionIndex n ≤ j) (hjn : j ≤ n - 3) :
    ∀ m, continuumBottom n ≤ m → m ≤ Mmax n j - 4 →
      PossibleLineCount n m := by
  induction j, hKj using Nat.le_induction with
  | base =>
      exact fun m hlow hhigh => continuum_base_possible hn hlow hhigh
  | succ j hKj ih =>
      exact continuum_step_possible hn hKj hjn (ih (by omega))

lemma Mmax_n_sub_three {n : ℕ} (hn : 3 ≤ n) :
    Mmax n (n - 3) = n.choose 2 - 2 := by
  have hnform : n = (n - 3) + 3 := by omega
  have hsub : n - (n - 3) = 3 := by omega
  have hchoose := choose_two_add (n - 3) 3
  rw [← hnform] at hchoose
  norm_num at hchoose
  simp only [Mmax, hsub]
  omega

lemma Mmax_n_sub_two {n : ℕ} (hn : 2 ≤ n) :
    Mmax n (n - 2) = n.choose 2 := by
  have hnform : n = (n - 2) + 2 := by omega
  have hsub : n - (n - 2) = 2 := by omega
  have hchoose := choose_two_add (n - 2) 2
  rw [← hnform] at hchoose
  norm_num at hchoose
  simp only [Mmax, hsub]
  omega

lemma terminal_interval_possible {n m : ℕ} (hn : 100 ≤ n)
    (hlow : continuumBottom n ≤ m) (hhigh : m ≤ n.choose 2 - 4) :
    PossibleLineCount n m := by
  have hKtop : transitionIndex n ≤ n - 3 := by
    have h := twice_transitionIndex_add_two_le hn
    omega
  have hchoose6 : 6 ≤ n.choose 2 := by
    have hc := Nat.choose_le_choose 2 (show 4 ≤ n by omega)
    norm_num at hc
    exact hc
  have hband := continuum_through_band hn hKtop (le_rfl : n - 3 ≤ n - 3)
  by_cases hm : m ≤ n.choose 2 - 6
  · apply hband m hlow
    rw [Mmax_n_sub_three (by omega)]
    omega
  have hkn : n - 2 ≤ n := by omega
  have ha2 : 2 ≤ n - (n - 2) := by omega
  have hk3 : 3 ≤ n - 2 := by omega
  have hpair2 : 2 ≤ (n - 2).choose 2 := by
    have hc := Nat.choose_le_choose 2 (show 3 ≤ n - 2 by omega)
    norm_num at hc
    omega
  have htop : Mmax n (n - 2) = n.choose 2 := Mmax_n_sub_two (by omega)
  have hcases : m = n.choose 2 - 5 ∨ m = n.choose 2 - 4 := by omega
  rcases hcases with rfl | rfl
  · simpa [htop] using
      (possible_Mmax_sub_odd (n := n) (k := n - 2) (s := 0)
        hkn ha2 hk3 (by omega) (by omega))
  · simpa [htop] using
      (possible_Mmax_sub_even (n := n) (k := n - 2) (s := 2)
        hkn ha2 hpair2 (by omega))

lemma classifiedValue_possible {n m : ℕ} (hn : 100 ≤ n)
    (hm : ClassifiedValue n m) : PossibleLineCount n m := by
  rcases hm with ⟨k, hk, hband⟩ | hterminal | htopTwo | htop
  · have hkK : k ≤ transitionIndex n := by omega
    have hkn : k ≤ n := hkK.trans (transitionIndex_le_n hn)
    have ha2 : 2 ≤ n - k := by
      have hgap := transitionIndex_gap_two hn
      omega
    exact full_band_possible hkn ha2 (index_le_transition_full hn hkK) hband
  · exact terminal_interval_possible hn hterminal.1 hterminal.2
  · rw [htopTwo]
    exact possibleLineCount_choose_sub_two (by omega)
  · rw [htop]
    exact possibleLineCount_choose n

/-- Maximum number of selected points on a determined line. -/
def maxLineSize (P : Finset Point) : ℕ :=
  (determinedLines P).sup fun L ↦ (pointsOnLine P L).card

lemma determinedLines_nonempty {P : Finset Point} (hP : 2 ≤ P.card) :
    (determinedLines P).Nonempty := by
  classical
  have hpairs : (pointPairs P).Nonempty := by
    rw [← Finset.card_pos, pointPairs_card]
    have hc := Nat.choose_le_choose 2 hP
    norm_num at hc ⊢
    omega
  rw [determinedLines]
  exact hpairs.image lineOfPair

lemma exists_richest_line {P : Finset Point} (hP : 2 ≤ P.card) :
    ∃ L ∈ determinedLines P, (pointsOnLine P L).card = maxLineSize P := by
  classical
  obtain ⟨L, hL, hmax⟩ :=
    Finset.exists_mem_eq_sup (determinedLines P) (determinedLines_nonempty hP)
      (fun J ↦ (pointsOnLine P J).card)
  exact ⟨L, hL, hmax.symm⟩

lemma pointsOnLine_card_le_max {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines P) :
    (pointsOnLine P L).card ≤ maxLineSize P := by
  exact Finset.le_sup (s := determinedLines P)
    (f := fun J ↦ (pointsOnLine P J).card) hL

/-! ### Representatives for the incidence estimate -/

lemma exists_representative_of_mem {P : Finset Point}
    {L : AffineSubspace ℝ Point} (hL : L ∈ determinedLines P) :
    ∃ l : PlanarIncidence.LineIndex,
      l.1 ∈ P ∧ l.2 ∈ P ∧ PlanarIncidence.ValidLine l ∧
        PlanarIncidence.lineSupport l = L := by
  classical
  rw [determinedLines, Finset.mem_image] at hL
  obtain ⟨e, he, rfl⟩ := hL
  rcases e with ⟨p, q⟩
  rw [mk_mem_pointPairs] at he
  exact ⟨(p, q), he.1, he.2.1, he.2.2, rfl⟩

/-- A chosen ordered pair spanning each determined affine line. -/
noncomputable def determinedLineRepresentative (P : Finset Point)
    (L : ↥(determinedLines P)) : PlanarIncidence.LineIndex :=
  Classical.choose (exists_representative_of_mem L.property)

lemma determinedLineRepresentative_spec (P : Finset Point)
    (L : ↥(determinedLines P)) :
    (determinedLineRepresentative P L).1 ∈ P ∧
      (determinedLineRepresentative P L).2 ∈ P ∧
      PlanarIncidence.ValidLine (determinedLineRepresentative P L) ∧
      PlanarIncidence.lineSupport (determinedLineRepresentative P L) = L.1 :=
  Classical.choose_spec (exists_representative_of_mem L.property)

lemma determinedLineRepresentative_injective (P : Finset Point) :
    Function.Injective (determinedLineRepresentative P) := by
  intro L M h
  apply Subtype.ext
  rw [← (determinedLineRepresentative_spec P L).2.2.2,
    ← (determinedLineRepresentative_spec P M).2.2.2, h]

/-- The chosen ordered-pair representatives of all determined lines. -/
noncomputable def representativeLines (P : Finset Point) :
    Finset PlanarIncidence.LineIndex :=
  (determinedLines P).attach.image (determinedLineRepresentative P)

lemma mem_representativeLines_iff {P : Finset Point}
    {l : PlanarIncidence.LineIndex} :
    l ∈ representativeLines P ↔
      ∃ L : ↥(determinedLines P), determinedLineRepresentative P L = l := by
  classical
  simp [representativeLines]

lemma card_representativeLines (P : Finset Point) :
    (representativeLines P).card = lineCount P := by
  classical
  rw [representativeLines, Finset.card_image_iff.mpr
    (determinedLineRepresentative_injective P).injOn]
  simp [lineCount]

lemma representative_valid {P : Finset Point}
    {l : PlanarIncidence.LineIndex} (hl : l ∈ representativeLines P) :
    PlanarIncidence.ValidLine l := by
  obtain ⟨L, rfl⟩ := mem_representativeLines_iff.mp hl
  exact (determinedLineRepresentative_spec P L).2.2.1

lemma representative_supports_distinct (P : Finset Point) :
    PlanarIncidence.DistinctSupports (representativeLines P) := by
  intro l hl m hm heq
  obtain ⟨L, rfl⟩ := mem_representativeLines_iff.mp hl
  obtain ⟨M, hM⟩ := mem_representativeLines_iff.mp hm
  rw [← hM] at heq ⊢
  have hLM : L = M := by
    apply Subtype.ext
    rw [← (determinedLineRepresentative_spec P L).2.2.2,
      ← (determinedLineRepresentative_spec P M).2.2.2, heq]
  rw [hLM]

lemma representative_points_eq (P : Finset Point)
    (L : ↥(determinedLines P)) :
    PlanarIncidence.pointsOnLine P (determinedLineRepresentative P L) =
      pointsOnLine P L.1 := by
  classical
  ext x
  rw [PlanarIncidence.mem_pointsOnLine_iff, mem_pointsOnLine,
    PlanarIncidence.onLine_iff_mem_support,
    (determinedLineRepresentative_spec P L).2.2.2]

lemma representative_two_le {P : Finset Point}
    {l : PlanarIncidence.LineIndex} (hl : l ∈ representativeLines P) :
    2 ≤ (PlanarIncidence.pointsOnLine P l).card := by
  obtain ⟨L, rfl⟩ := mem_representativeLines_iff.mp hl
  rw [representative_points_eq]
  exact two_le_pointsOnLine_card L.property

lemma representative_card_le_max {P : Finset Point}
    {l : PlanarIncidence.LineIndex} (hl : l ∈ representativeLines P) :
    (PlanarIncidence.pointsOnLine P l).card ≤ maxLineSize P := by
  obtain ⟨L, rfl⟩ := mem_representativeLines_iff.mp hl
  rw [representative_points_eq]
  exact pointsOnLine_card_le_max L.property

lemma representative_pair_count (P : Finset Point) :
    ∑ l ∈ representativeLines P,
        (PlanarIncidence.pointsOnLine P l).card.choose 2 = P.card.choose 2 := by
  classical
  rw [representativeLines]
  rw [Finset.sum_image]
  · simp only [representative_points_eq]
    exact (Finset.sum_attach (determinedLines P)
      (fun L ↦ (pointsOnLine P L).card.choose 2)).trans
        (pair_count_sum P).symm
  · intro L hL M hM h
    exact determinedLineRepresentative_injective P h

/-- Points off a fixed determined line. -/
def offLinePoints (P : Finset Point) (L : AffineSubspace ℝ Point) : Finset Point :=
  P \ pointsOnLine P L

lemma pointsOnLine_subset (P : Finset Point) (L : AffineSubspace ℝ Point) :
    pointsOnLine P L ⊆ P := by
  intro p hp
  exact (mem_pointsOnLine.mp hp).1

lemma offLinePoints_card (P : Finset Point) (L : AffineSubspace ℝ Point) :
    (offLinePoints P L).card = P.card - (pointsOnLine P L).card := by
  rw [offLinePoints, Finset.card_sdiff]
  have hinter : pointsOnLine P L ∩ P = pointsOnLine P L := by
    exact Finset.inter_eq_left.mpr (pointsOnLine_subset P L)
  rw [hinter]

lemma pointsOnLine_card_le_off_add_one {P : Finset Point}
    {L J : AffineSubspace ℝ Point} (hL : L ∈ determinedLines P)
    (hJ : J ∈ determinedLines P) (hne : J ≠ L) :
    (pointsOnLine P J).card ≤
      (pointsOnLine (offLinePoints P L) J).card + 1 := by
  classical
  let A := pointsOnLine P L
  let Q := offLinePoints P L
  let B := pointsOnLine A J
  have hB : B.card ≤ 1 := by
    by_contra h
    have htwo : 1 < B.card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp htwo
    have hp' := mem_pointsOnLine.mp hp
    have hq' := mem_pointsOnLine.mp hq
    have hpA := mem_pointsOnLine.mp hp'.1
    have hqA := mem_pointsOnLine.mp hq'.1
    have hpJ : p ∈ J := hp'.2
    have hqJ : q ∈ J := hq'.2
    have hpL : p ∈ L := hpA.2
    have hqL : q ∈ L := hqA.2
    have hlineJ : lineOfPair s(p, q) = J :=
      (lineOfPair_eq_iff_mem hJ hpq).mpr ⟨hpJ, hqJ⟩
    have hlineL : lineOfPair s(p, q) = L :=
      (lineOfPair_eq_iff_mem hL hpq).mpr ⟨hpL, hqL⟩
    exact hne (hlineJ.symm.trans hlineL)
  have hsub : pointsOnLine P J ⊆ pointsOnLine Q J ∪ B := by
    intro p hp
    have hp' := mem_pointsOnLine.mp hp
    by_cases hpA : p ∈ A
    · rw [mem_union]
      right
      exact mem_pointsOnLine.mpr ⟨hpA, hp'.2⟩
    · rw [mem_union]
      left
      exact mem_pointsOnLine.mpr ⟨by
        dsimp [Q, offLinePoints]
        simp only [mem_sdiff]
        exact ⟨hp'.1, hpA⟩, hp'.2⟩
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (pointsOnLine Q J) B
  change (pointsOnLine P J).card ≤ (pointsOnLine Q J).card + 1
  omega

lemma choose_succ_sub_one_le_twice {q : ℕ} (hq : 1 ≤ q) :
    (q + 1).choose 2 - 1 ≤ 2 * q.choose 2 := by
  rcases eq_or_ne q 1 with rfl | hq1
  · norm_num
  rcases eq_or_ne q 2 with rfl | hq2
  · norm_num
  have hq3 : 3 ≤ q := by omega
  have hqchoose : q ≤ q.choose 2 := by
    have htwice := two_mul_choose_two q
    have hpred : 2 ≤ q - 1 := by omega
    have hmul : 2 * q ≤ q * (q - 1) := by
      rw [mul_comm 2 q]
      exact Nat.mul_le_mul_left q hpred
    rw [← htwice] at hmul
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  rw [show (q + 1).choose 2 = q.choose 2 + q by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm]]
  omega

lemma line_loss_le_twice_off_pairs {P : Finset Point}
    {L J : AffineSubspace ℝ Point} (hL : L ∈ determinedLines P)
    (hJ : J ∈ determinedLines P) (hne : J ≠ L) :
    (pointsOnLine P J).card.choose 2 - 1 ≤
      2 * (pointsOnLine (offLinePoints P L) J).card.choose 2 := by
  let r := (pointsOnLine P J).card
  let q := (pointsOnLine (offLinePoints P L) J).card
  have hr2 : 2 ≤ r := two_le_pointsOnLine_card hJ
  have hrq : r ≤ q + 1 := pointsOnLine_card_le_off_add_one hL hJ hne
  have hq1 : 1 ≤ q := by omega
  have hc : r.choose 2 ≤ (q + 1).choose 2 := Nat.choose_le_choose 2 hrq
  exact (Nat.sub_le_sub_right hc 1).trans (choose_succ_sub_one_le_twice hq1)

lemma choose_pointsOnLine_eq_zero_of_not_determined {Q P : Finset Point}
    (hQP : Q ⊆ P) {J : AffineSubspace ℝ Point}
    (hJ : J ∈ determinedLines P) (hnot : J ∉ determinedLines Q) :
    (pointsOnLine Q J).card.choose 2 = 0 := by
  classical
  by_contra hzero
  have htwo : 1 < (pointsOnLine Q J).card := by
    by_contra h
    have hle : (pointsOnLine Q J).card ≤ 1 := by omega
    interval_cases (pointsOnLine Q J).card <;> simp_all
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp htwo
  have hp' := mem_pointsOnLine.mp hp
  have hq' := mem_pointsOnLine.mp hq
  have heq : lineOfPair s(p, q) = J :=
    (lineOfPair_eq_iff_mem hJ hpq).mpr ⟨hp'.2, hq'.2⟩
  apply hnot
  rw [determinedLines, mem_image]
  exact ⟨s(p, q), (mk_mem_pointPairs Q p q).mpr ⟨hp'.1, hq'.1, hpq⟩, heq⟩

lemma sum_choose_pointsOnLine_over_super {Q P : Finset Point} (hQP : Q ⊆ P) :
    ∑ J ∈ determinedLines P, (pointsOnLine Q J).card.choose 2 = Q.card.choose 2 := by
  classical
  have hmono : determinedLines Q ⊆ determinedLines P := determinedLines_mono hQP
  calc
    ∑ J ∈ determinedLines P, (pointsOnLine Q J).card.choose 2 =
        ∑ J ∈ determinedLines Q, (pointsOnLine Q J).card.choose 2 := by
      symm
      exact Finset.sum_subset hmono (by
        intro J hJP hJQ
        exact choose_pointsOnLine_eq_zero_of_not_determined hQP hJP hJQ)
    _ = Q.card.choose 2 := (pair_count_sum Q).symm

lemma pair_defect_le_fixed_line {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hL : L ∈ determinedLines P) :
    P.card.choose 2 - lineCount P ≤
      (pointsOnLine P L).card.choose 2 - 1 +
        2 * (offLinePoints P L).card.choose 2 := by
  classical
  let D := determinedLines P
  let loss := fun J : AffineSubspace ℝ Point ↦
    (pointsOnLine P J).card.choose 2 - 1
  let offPairs := fun J : AffineSubspace ℝ Point ↦
    (pointsOnLine (offLinePoints P L) J).card.choose 2
  have herase : ∑ J ∈ D.erase L, loss J ≤ ∑ J ∈ D.erase L, 2 * offPairs J := by
    apply Finset.sum_le_sum
    intro J hJ
    have hJD : J ∈ D := (Finset.mem_erase.mp hJ).2
    have hne : J ≠ L := (Finset.mem_erase.mp hJ).1
    exact line_loss_le_twice_off_pairs hL hJD hne
  have hsubset : D.erase L ⊆ D := Finset.erase_subset L D
  have hextend : ∑ J ∈ D.erase L, 2 * offPairs J ≤ ∑ J ∈ D, 2 * offPairs J :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
  have hoffsum : ∑ J ∈ D, offPairs J = (offLinePoints P L).card.choose 2 := by
    apply sum_choose_pointsOnLine_over_super
    intro p hp
    exact (Finset.mem_sdiff.mp hp).1
  have hfactor : (∑ J ∈ D, 2 * offPairs J) = 2 * (offLinePoints P L).card.choose 2 := by
    calc
      (∑ J ∈ D, 2 * offPairs J) = 2 * ∑ J ∈ D, offPairs J := by
        exact (Finset.mul_sum D offPairs 2).symm
      _ = 2 * (offLinePoints P L).card.choose 2 := by rw [hoffsum]
  have hrest : ∑ J ∈ D.erase L, loss J ≤ 2 * (offLinePoints P L).card.choose 2 :=
    herase.trans (hextend.trans_eq hfactor)
  rw [pair_defect_identity]
  change (∑ J ∈ D, loss J) ≤
    loss L + 2 * (offLinePoints P L).card.choose 2
  calc
    (∑ J ∈ D, loss J) = (∑ J ∈ D.erase L, loss J) + loss L :=
      (Finset.sum_erase_add D loss hL).symm
    _ ≤ 2 * (offLinePoints P L).card.choose 2 + loss L :=
      Nat.add_le_add_right hrest (loss L)
    _ = loss L + 2 * (offLinePoints P L).card.choose 2 := Nat.add_comm _ _

lemma Mmax_complement {n r : ℕ} (hrn : r ≤ n) :
    Mmax n (n - r) = n.choose 2 - r.choose 2 + 1 := by
  let k := n - r
  change Mmax n k = n.choose 2 - r.choose 2 + 1
  have hnform : n = r + k := by dsimp [k]; omega
  have hsub : n - k = r := by dsimp [k]; omega
  have hchoose := choose_two_add r k
  rw [← hnform] at hchoose
  have hrchoose : r.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hrn
  have hdiff : n.choose 2 - r.choose 2 = r * k + k.choose 2 := by omega
  rw [Mmax, hsub, hdiff]
  ring

lemma fixed_line_band_bounds {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hP : 2 ≤ P.card) (hL : L ∈ determinedLines P) :
    let k := P.card - (pointsOnLine P L).card
    Mmin P.card k ≤ lineCount P ∧ lineCount P ≤ Mmax P.card k := by
  let n := P.card
  let r := (pointsOnLine P L).card
  let k := n - r
  have hrn : r ≤ n := by
    exact Finset.card_le_card (pointsOnLine_subset P L)
  have hnform : n = r + k := by dsimp [k]; omega
  have hsub : n - k = r := by dsimp [k]; omega
  have hoff : (offLinePoints P L).card = k := by
    rw [offLinePoints_card]
  have hchoose := choose_two_add r k
  rw [← hnform] at hchoose
  have hlinele : lineCount P ≤ n.choose 2 := by
    simpa [n] using lineCount_le_choose P
  have hdefeq := pair_defect_identity P
  have hdefupper := pair_defect_le_fixed_line hL
  change n.choose 2 - lineCount P =
    (∑ J ∈ determinedLines P, ((pointsOnLine P J).card.choose 2 - 1)) at hdefeq
  change n.choose 2 - lineCount P ≤ r.choose 2 - 1 +
    2 * (offLinePoints P L).card.choose 2 at hdefupper
  rw [hoff] at hdefupper
  have hdefadd : n.choose 2 - lineCount P + lineCount P = n.choose 2 :=
    Nat.sub_add_cancel hlinele
  have hactualadd :
      (∑ J ∈ determinedLines P, ((pointsOnLine P J).card.choose 2 - 1)) +
          lineCount P = n.choose 2 := by
    rw [← hdefeq]
    exact hdefadd
  have hr2 : 2 ≤ r := two_le_pointsOnLine_card hL
  have hrchoose1 : 1 ≤ r.choose 2 := by
    calc
      1 = (2 : ℕ).choose 2 := by norm_num
      _ ≤ r.choose 2 := Nat.choose_le_choose 2 hr2
  have hdeflower : r.choose 2 - 1 ≤ n.choose 2 - lineCount P := by
    rw [hdefeq]
    exact Finset.single_le_sum
      (f := fun J ↦ (pointsOnLine P J).card.choose 2 - 1)
      (fun _ _ ↦ Nat.zero_le _) hL
  have hupper : lineCount P ≤ Mmax n k := by
    rw [Mmax_complement hrn]
    omega
  have hlower : Mmin n k ≤ lineCount P := by
    by_cases hprod : k.choose 2 ≤ k * r
    · have hmin : Mmin n k = k * r - k.choose 2 + 1 := by
        simp only [Mmin, hsub]
      have hprodSplit : k * r - k.choose 2 + k.choose 2 = k * r :=
        Nat.sub_add_cancel hprod
      have hrSplit : r.choose 2 - 1 + 1 = r.choose 2 :=
        Nat.sub_add_cancel hrchoose1
      have hmul : r * k = k * r := Nat.mul_comm r k
      have hsum :
          (r.choose 2 - 1 + 2 * k.choose 2) +
              (k * r - k.choose 2 + 1) = n.choose 2 := by
        rw [hchoose]
        omega
      have hsumle :
          (∑ J ∈ determinedLines P, ((pointsOnLine P J).card.choose 2 - 1)) ≤
            r.choose 2 - 1 + 2 * k.choose 2 := by
        rw [← hdefeq]
        exact hdefupper
      rw [hmin]
      have htotaleq :
          (r.choose 2 - 1 + 2 * k.choose 2) +
              (k * r - k.choose 2 + 1) =
            (∑ J ∈ determinedLines P, ((pointsOnLine P J).card.choose 2 - 1)) +
              lineCount P := hsum.trans hactualadd.symm
      have hineq :
          (∑ J ∈ determinedLines P, ((pointsOnLine P J).card.choose 2 - 1)) +
              (k * r - k.choose 2 + 1) ≤
            (∑ J ∈ determinedLines P, ((pointsOnLine P J).card.choose 2 - 1)) +
              lineCount P := by
        calc
          _ ≤ (r.choose 2 - 1 + 2 * k.choose 2) +
                (k * r - k.choose 2 + 1) :=
            Nat.add_le_add_right hsumle _
          _ = _ := htotaleq
      exact Nat.le_of_add_le_add_left hineq
    · have hnonempty := determinedLines_nonempty hP
      have hpositive : 1 ≤ lineCount P := by
        rw [lineCount, Finset.one_le_card]
        exact hnonempty
      have hmin : Mmin n k = 1 := by
        simp only [Mmin, hsub]
        have : k * r < k.choose 2 := by omega
        omega
      rwa [hmin]
  exact ⟨hlower, hupper⟩

lemma richest_line_band_bounds {P : Finset Point} (hP : 2 ≤ P.card) :
    let k := P.card - maxLineSize P
    Mmin P.card k ≤ lineCount P ∧ lineCount P ≤ Mmax P.card k := by
  obtain ⟨L, hL, hrich⟩ := exists_richest_line hP
  simpa [hrich] using fixed_line_band_bounds hP hL

lemma fixed_line_band_gaps {P : Finset Point} {L : AffineSubspace ℝ Point}
    (hP : 2 ≤ P.card) (hL : L ∈ determinedLines P) :
    let k := P.card - (pointsOnLine P L).card
    lineCount P ≠ Mmax P.card k - 1 ∧ lineCount P ≠ Mmax P.card k - 3 := by
  classical
  let n := P.card
  let r := (pointsOnLine P L).card
  let k := n - r
  let loss := fun J : AffineSubspace ℝ Point ↦
    (pointsOnLine P J).card.choose 2 - 1
  let rest := ∑ J ∈ (determinedLines P).erase L, loss J
  have hrn : r ≤ n := Finset.card_le_card (pointsOnLine_subset P L)
  have hr2 : 2 ≤ r := two_le_pointsOnLine_card hL
  have hrchoose1 : 1 ≤ r.choose 2 := by
    calc
      1 = (2 : ℕ).choose 2 := by norm_num
      _ ≤ r.choose 2 := Nat.choose_le_choose 2 hr2
  have hlinele : lineCount P ≤ n.choose 2 := by
    simpa [n] using lineCount_le_choose P
  have hdefadd : n.choose 2 - lineCount P + lineCount P = n.choose 2 :=
    Nat.sub_add_cancel hlinele
  have hdefeq := pair_defect_identity P
  change n.choose 2 - lineCount P = ∑ J ∈ determinedLines P, loss J at hdefeq
  have hsplit := Finset.sum_erase_add (determinedLines P) loss hL
  have hrestEq : n.choose 2 - lineCount P = rest + (r.choose 2 - 1) := by
    rw [hdefeq, ← hsplit]
  have hmax : Mmax n k = n.choose 2 - r.choose 2 + 1 := Mmax_complement hrn
  have hmaxadd : Mmax n k + (r.choose 2 - 1) = n.choose 2 := by
    have hrchoose : r.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hrn
    have hdiffadd : n.choose 2 - r.choose 2 + r.choose 2 = n.choose 2 :=
      Nat.sub_add_cancel hrchoose
    rw [hmax]
    omega
  have hmaxline : Mmax n k = lineCount P + rest := by
    omega
  have hdiff : Mmax n k - lineCount P = rest := by omega
  have hrestGaps : rest ≠ 1 ∧ rest ≠ 3 := by
    apply sum_choose_losses_ne_one_three
    intro J hJ
    apply choose_two_sub_one_cases
    apply two_le_pointsOnLine_card
    exact (Finset.mem_erase.mp hJ).2
  constructor
  · intro heq
    change lineCount P = Mmax n k - 1 at heq
    have hpositive : 1 ≤ lineCount P := by
      rw [lineCount, Finset.one_le_card]
      exact determinedLines_nonempty hP
    have hle : 1 ≤ Mmax n k := by omega
    have : Mmax n k - lineCount P = 1 := by
      rw [heq, Nat.sub_sub_self hle]
    exact hrestGaps.1 (by rwa [← hdiff])
  · intro heq
    change lineCount P = Mmax n k - 3 at heq
    have hpositive : 1 ≤ lineCount P := by
      rw [lineCount, Finset.one_le_card]
      exact determinedLines_nonempty hP
    have hle : 3 ≤ Mmax n k := by omega
    have : Mmax n k - lineCount P = 3 := by
      rw [heq, Nat.sub_sub_self hle]
    exact hrestGaps.2 (by rwa [← hdiff])

lemma richest_line_band_value {P : Finset Point} (hP : 2 ≤ P.card) :
    let k := P.card - maxLineSize P
    BandValue P.card k (lineCount P) := by
  obtain ⟨L, hL, hrich⟩ := exists_richest_line hP
  have hb := fixed_line_band_bounds hP hL
  have hg := fixed_line_band_gaps hP hL
  rw [hrich] at hb hg
  exact ⟨hb.1, hb.2, hg.1, hg.2⟩

lemma continuumBottom_le_Mmin_transition {n : ℕ} (hn : 100 ≤ n) :
    continuumBottom n ≤ Mmin n (transitionIndex n) := by
  let K := transitionIndex n
  change continuumBottom n ≤ Mmin n K
  have hKn : K ≤ n := transitionIndex_le_n hn
  have hfull : K.choose 2 ≤ n - K := transitionIndex_full hn
  have hprod : K.choose 2 ≤ K * (n - K) :=
    hfull.trans (Nat.le_mul_of_pos_left (n - K) (by
      have := transitionIndex_ge_ten hn
      omega))
  have hendpoint : Mmax n (K - 1) + n = Mmin n K + K * K :=
    Mmax_pred_add_n_eq_Mmin_add_sq (by
      have := transitionIndex_ge_ten hn
      omega) hKn hprod
  by_cases hp2 : K * K = n + 2
  · have hb : continuumBottom n = Mmax n (K - 1) - 2 := by
      simp [continuumBottom, K, hp2]
    rw [hb]
    omega
  by_cases hp1 : K * K = n + 1
  · have hb : continuumBottom n = Mmax n (K - 1) - 2 := by
      simp [continuumBottom, K, hp1]
    rw [hb]
    omega
  by_cases hz : K * K = n
  · have hb : continuumBottom n = Mmax n (K - 1) := by
      simp [continuumBottom, K, hp2, hp1, hz]
    rw [hb]
    omega
  by_cases hm1 : K * K + 1 = n
  · have hb : continuumBottom n = Mmax n (K - 1) := by
      simp [continuumBottom, K, hp2, hp1, hz, hm1]
    rw [hb]
    omega
  · simp [continuumBottom, K, hp2, hp1, hz, hm1]

lemma Mmin_mono_step {n k : ℕ} (hk : 3 * (k + 1) ≤ n) :
    Mmin n k ≤ Mmin n (k + 1) := by
  have hkn : k + 1 ≤ n := by omega
  have hsub0 : n - k = (n - (k + 1)) + 1 := by omega
  have hkbase : k ≤ n - k := by omega
  have hsuccbase : k + 1 ≤ n - (k + 1) := by omega
  have hCk : k.choose 2 ≤ k * (n - k) := by
    have ht := two_mul_choose_two k
    have hle : k.choose 2 ≤ k * (k - 1) := by omega
    exact hle.trans (Nat.mul_le_mul_left k (by omega))
  have hCsucc : (k + 1).choose 2 ≤ (k + 1) * (n - (k + 1)) := by
    have ht := two_mul_choose_two (k + 1)
    have hle : (k + 1).choose 2 ≤ (k + 1) * k := by
      simpa using (show (k + 1).choose 2 ≤ (k + 1) * ((k + 1) - 1) by omega)
    exact hle.trans (Nat.mul_le_mul_left (k + 1) (by omega))
  have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm]
  have hprod0 : k * (n - k) = k * (n - (k + 1)) + k := by
    rw [hsub0]
    ring
  have hprod1 : (k + 1) * (n - (k + 1)) =
      k * (n - (k + 1)) + (n - (k + 1)) := by ring
  have hleftSplit : k * (n - k) - k.choose 2 + k.choose 2 = k * (n - k) :=
    Nat.sub_add_cancel hCk
  have hrightSplit :
      (k + 1) * (n - (k + 1)) - (k + 1).choose 2 + (k + 1).choose 2 =
        (k + 1) * (n - (k + 1)) := Nat.sub_add_cancel hCsucc
  simp only [Mmin]
  omega

lemma Mmin_transition_le {n k : ℕ} (hn : 100 ≤ n)
    (hKk : transitionIndex n ≤ k) (hk : 3 * k ≤ n) :
    Mmin n (transitionIndex n) ≤ Mmin n k := by
  induction k, hKk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hKk ih =>
      exact (ih (by omega)).trans (Mmin_mono_step hk)

lemma medium_richest_line_separation {P : Finset Point} (hn : 100 ≤ P.card)
    (hK : transitionIndex P.card ≤ P.card - maxLineSize P)
    (hthird : 3 * (P.card - maxLineSize P) ≤ P.card) :
    continuumBottom P.card ≤ lineCount P := by
  have hP : 2 ≤ P.card := by omega
  have hb := richest_line_band_bounds hP
  exact (continuumBottom_le_Mmin_transition hn).trans
    ((Mmin_transition_le hn hK hthird).trans hb.1)

lemma continuumBottom_le_five_mul_transition {n : ℕ} (hn : 3 ≤ n) :
    continuumBottom n ≤ 5 * n * transitionIndex n := by
  let K := transitionIndex n
  have hKpos : 1 ≤ K := by
    dsimp [K, transitionIndex]
    exact Nat.sqrt_pos.mpr (by omega)
  have hKsq : K * K ≤ n + 2 := by
    dsimp [K, transitionIndex]
    exact Nat.sqrt_le (n + 2)
  have hsmall : n + 3 ≤ 4 * n * K := by
    have hnK : n ≤ n * K := by
      simpa using Nat.mul_le_mul_left n hKpos
    have hfour : 4 * n ≤ 4 * (n * K) := Nat.mul_le_mul_left 4 hnK
    have hnsmall : n + 3 ≤ 4 * n := by omega
    exact hnsmall.trans (by simpa [mul_assoc] using hfour)
  have hMmax : ∀ k ≤ K, Mmax n k ≤ 5 * n * K := by
    intro k hk
    have hprod : k * (n - k) ≤ K * n :=
      Nat.mul_le_mul hk (Nat.sub_le n k)
    have hchoose : k.choose 2 ≤ k * k := by
      have ht := two_mul_choose_two k
      have hpred : k * (k - 1) ≤ k * k :=
        Nat.mul_le_mul_left k (Nat.sub_le k 1)
      omega
    have hksq : k * k ≤ K * K := Nat.mul_le_mul hk hk
    have hprod' : k * (n - k) ≤ n * K := by simpa [mul_comm] using hprod
    have hchoose' : k.choose 2 ≤ n + 2 :=
      hchoose.trans (hksq.trans hKsq)
    simp only [Mmax]
    calc
      k * (n - k) + k.choose 2 + 1 ≤ n * K + (n + 2) + 1 := by omega
      _ ≤ n * K + 4 * n * K := by omega
      _ = 5 * n * K := by ring
  have hMmin : Mmin n K ≤ 5 * n * K := by
    have hprod : K * (n - K) ≤ K * n :=
      Nat.mul_le_mul_left K (Nat.sub_le n K)
    have hprod' : K * (n - K) ≤ n * K := by simpa [mul_comm] using hprod
    calc
      Mmin n K ≤ K * (n - K) + 1 := by simp [Mmin]
      _ ≤ n * K + 1 := by omega
      _ ≤ n * K + 4 * n * K := by omega
      _ = 5 * n * K := by ring
  dsimp [continuumBottom]
  split_ifs
  · exact (Nat.sub_le _ _).trans (hMmax (K - 1) (Nat.sub_le K 1))
  · exact hMmax (K - 1) (Nat.sub_le K 1)
  · exact hMmin

lemma transitionIndex_cast_le_two_rpow_half {n : ℕ} (hn : 3 ≤ n) :
    (transitionIndex n : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hKsqN := Nat.sqrt_le (n + 2)
  have hKsq : (transitionIndex n : ℝ) ^ 2 ≤ 2 * (n : ℝ) := by
    have hcast : ((Nat.sqrt (n + 2) * Nat.sqrt (n + 2) : ℕ) : ℝ) ≤ n + 2 := by
      exact_mod_cast hKsqN
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [transitionIndex]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hcast ⊢
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsqrt0 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hn0 _
  have hsqrtSq : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hK0 : (0 : ℝ) ≤ transitionIndex n := by positivity
  nlinarith [sq_nonneg ((transitionIndex n : ℝ) -
    2 * (n : ℝ) ^ ((1 : ℝ) / 2))]

lemma continuumBottom_cast_le_ten_rpow_three_halves {n : ℕ} (hn : 3 ≤ n) :
    (continuumBottom n : ℝ) ≤ 10 * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have hcontN := continuumBottom_le_five_mul_transition hn
  have hcont : (continuumBottom n : ℝ) ≤
      5 * (n : ℝ) * transitionIndex n := by exact_mod_cast hcontN
  have hK := transitionIndex_cast_le_two_rpow_half hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hcoef : 0 ≤ 5 * (n : ℝ) := mul_nonneg (by norm_num) hn0
  have hmul := mul_le_mul_of_nonneg_left hK hcoef
  calc
    _ ≤ 5 * (n : ℝ) * transitionIndex n := hcont
    _ ≤ 5 * (n : ℝ) * (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) := by
      simpa [mul_assoc] using hmul
    _ = 10 * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      have hnpos : (0 : ℝ) < n := by positivity
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
        Real.rpow_add hnpos, Real.rpow_one]
      ring

lemma continuumBottom_le_rpow_eventually :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (continuumBottom n : ℝ) ≤ (n : ℝ) ^ ((8 : ℝ) / 5) := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 10))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  rw [Filter.tendsto_atTop_atTop] at ht
  obtain ⟨n₁, hn₁⟩ := ht 10
  refine ⟨max n₁ 3, fun n hn ↦ ?_⟩
  have hlarge : (10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) :=
    hn₁ n ((le_max_left _ _).trans hn)
  have hcont := continuumBottom_cast_le_ten_rpow_three_halves
    (n := n) ((le_max_right _ _).trans hn)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmul := mul_le_mul_of_nonneg_right hlarge
    (Real.rpow_nonneg hn0 ((3 : ℝ) / 2))
  calc
    _ ≤ 10 * (n : ℝ) ^ ((3 : ℝ) / 2) := hcont
    _ ≤ (n : ℝ) ^ ((1 : ℝ) / 10) *
        (n : ℝ) ^ ((3 : ℝ) / 2) := by simpa [mul_comm] using hmul
    _ = (n : ℝ) ^ ((8 : ℝ) / 5) := by
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n by omega)
      rw [← Real.rpow_add hnpos]
      congr 2 <;> norm_num

lemma Mmin_cast_quadratic_lower {n k r : ℕ} (hn : n = r + k)
    (hthird : n < 3 * k) (hhalf : n ≤ 2 * r) :
    (n : ℝ) ^ 2 / 12 ≤ Mmin n k := by
  have hkpos : 1 ≤ k := by omega
  have hkr : k ≤ r := by omega
  have hsub : n - k = r := by omega
  have hchoose : k.choose 2 ≤ k * r := by
    have ht := two_mul_choose_two k
    have hpred : k * (k - 1) ≤ k * k :=
      Nat.mul_le_mul_left k (Nat.sub_le k 1)
    have hkk : k * k ≤ k * r := Nat.mul_le_mul_left k hkr
    omega
  let t := 2 * r - k
  have hnt : n ≤ 2 * t := by dsimp [t]; omega
  have hn3 : n ≤ 3 * k := by omega
  have hprodN := Nat.mul_le_mul hn3 hnt
  have hprod : (n : ℝ) ^ 2 ≤ 6 * (k : ℝ) * t := by
    have hc : (n : ℝ) * n ≤ (3 * k : ℕ) * (2 * t : ℕ) := by
      exact_mod_cast hprodN
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hc
    nlinarith
  have hchooseR : 2 * (k.choose 2 : ℝ) = (k : ℝ) * (k - 1) := by
    have ht := two_mul_choose_two k
    have htR := congrArg (fun z : ℕ ↦ (z : ℝ)) ht
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at htR
    rw [Nat.cast_sub hkpos] at htR
    norm_num only [Nat.cast_one] at htR
    exact htR
  have htR : (t : ℝ) = 2 * (r : ℝ) - k := by
    dsimp [t]
    rw [Nat.cast_sub (by omega : k ≤ 2 * r)]
    norm_num
  have hminR : (Mmin n k : ℝ) =
      (k : ℝ) * r - k.choose 2 + 1 := by
    rw [Mmin, hsub, Nat.cast_add, Nat.cast_sub hchoose]
    norm_num
  rw [hminR]
  rw [htR] at hprod
  ring_nf at hprod hchooseR ⊢
  nlinarith

lemma rpow_eight_fifths_le_quadratic_eventually :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) ^ ((8 : ℝ) / 5) ≤ (n : ℝ) ^ 2 / 12 := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((2 : ℝ) / 5))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop
  rw [Filter.tendsto_atTop_atTop] at ht
  obtain ⟨n₀, hn₀⟩ := ht 12
  refine ⟨max n₀ 1, fun n hn ↦ ?_⟩
  have hlarge : (12 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) :=
    hn₀ n ((le_max_left _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast
    (show 0 < n by omega)
  have hmul := mul_le_mul_of_nonneg_right hlarge
    (Real.rpow_nonneg hnpos.le ((8 : ℝ) / 5))
  have hpow : (n : ℝ) ^ ((2 : ℝ) / 5) *
      (n : ℝ) ^ ((8 : ℝ) / 5) = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_add hnpos]
    norm_num [Real.rpow_two]
  rw [hpow] at hmul
  nlinarith

/-- The high-index separation furnished by the finite Erdős--Beck incidence
estimate.  Its proof is the only asymptotic geometric part of the converse. -/
lemma large_richest_line_separation :
    ∃ n₁ : ℕ, ∀ P : Finset Point, n₁ ≤ P.card →
      P.card < 3 * (P.card - maxLineSize P) →
      continuumBottom P.card ≤ lineCount P := by
  obtain ⟨nBeck, hBeck⟩ := PlanarIncidence.many_lines_of_pair_partition
  obtain ⟨nCont, hCont⟩ := continuumBottom_le_rpow_eventually
  obtain ⟨nQuad, hQuad⟩ := rpow_eight_fifths_le_quadratic_eventually
  refine ⟨max 100 (max nBeck (max nCont nQuad)), ?_⟩
  intro P hn hthird
  have hn100 : 100 ≤ P.card := (le_max_left _ _).trans hn
  have hnAll : max nBeck (max nCont nQuad) ≤ P.card :=
    (le_max_right _ _).trans hn
  have hnBeck : nBeck ≤ P.card := (le_max_left _ _).trans hnAll
  have hnRest : max nCont nQuad ≤ P.card := (le_max_right _ _).trans hnAll
  have hnCont : nCont ≤ P.card := (le_max_left _ _).trans hnRest
  have hnQuad : nQuad ≤ P.card := (le_max_right _ _).trans hnRest
  have hP : 2 ≤ P.card := by omega
  obtain ⟨J, hJ, hJmax⟩ := exists_richest_line hP
  have hrn : maxLineSize P ≤ P.card := by
    rw [← hJmax]
    exact Finset.card_le_card (pointsOnLine_subset P J)
  have hnform : P.card = maxLineSize P + (P.card - maxLineSize P) := by omega
  have hcont := hCont P.card hnCont
  by_cases hhalf : P.card ≤ 2 * maxLineSize P
  · have hmin := Mmin_cast_quadratic_lower hnform hthird hhalf
    have hquad := hQuad P.card hnQuad
    have hband := richest_line_band_bounds hP
    have hbandR : (Mmin P.card (P.card - maxLineSize P) : ℝ) ≤ lineCount P := by
      exact_mod_cast hband.1
    have hresult : (continuumBottom P.card : ℝ) ≤ lineCount P :=
      hcont.trans (hquad.trans (hmin.trans hbandR))
    exact_mod_cast hresult
  · have hrich : ∀ l ∈ representativeLines P,
        2 * (PlanarIncidence.pointsOnLine P l).card < P.card := by
      intro l hl
      have hle := representative_card_le_max hl
      omega
    have hmany := hBeck P (representativeLines P) hnBeck
      (fun l hl ↦ representative_valid hl)
      (representative_supports_distinct P) hrich (representative_pair_count P).symm
    rw [card_representativeLines] at hmany
    have hresult : (continuumBottom P.card : ℝ) ≤ lineCount P :=
      hcont.trans (le_of_lt hmany)
    exact_mod_cast hresult

lemma possibleLineCount_classified_of_separation {n m : ℕ} (hn : 100 ≤ n)
    (hsep : ∀ P : Finset Point, P.card = n →
      n < 3 * (n - maxLineSize P) → continuumBottom n ≤ lineCount P)
    (hm : PossibleLineCount n m) : ClassifiedValue n m := by
  obtain ⟨P, hPcard, hPline⟩ := hm
  subst n
  subst m
  have hP : 2 ≤ P.card := by omega
  let k := P.card - maxLineSize P
  have hband : BandValue P.card k (lineCount P) := richest_line_band_value hP
  by_cases hk : k < transitionIndex P.card
  · left
    exact ⟨k, hk, hband⟩
  have hlow : continuumBottom P.card ≤ lineCount P := by
    by_cases hthird : 3 * k ≤ P.card
    · exact medium_richest_line_separation (by omega) (by omega) hthird
    · apply hsep P rfl
      dsimp [k] at hthird ⊢
      omega
  have hlinele : lineCount P ≤ P.card.choose 2 := lineCount_le_choose P
  by_cases hterminal : lineCount P ≤ P.card.choose 2 - 4
  · exact Or.inr (Or.inl ⟨hlow, hterminal⟩)
  have hchoose4 : 4 ≤ P.card.choose 2 := by
    have hc := Nat.choose_le_choose 2 (show 4 ≤ P.card by omega)
    norm_num [Nat.choose] at hc
    omega
  have hdef : P.card.choose 2 - lineCount P ≠ 1 ∧
      P.card.choose 2 - lineCount P ≠ 3 := pair_defect_ne_one_three P
  have hdefle : P.card.choose 2 - lineCount P ≤ 3 := by omega
  have hcases : P.card.choose 2 - lineCount P = 0 ∨
      P.card.choose 2 - lineCount P = 2 := by omega
  rcases hcases with hzero | htwo
  · right
    right
    right
    omega
  · right
    right
    left
    omega

/-- Erdős--Salamon's complete resolution of Erdős Problem 606. -/
theorem erdos_606 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      PossibleLineCount n m ↔ ClassifiedValue n m := by
  obtain ⟨n₁, hlarge⟩ := large_richest_line_separation
  refine ⟨max 100 n₁, ?_⟩
  intro n hn m
  have hn100 : 100 ≤ n := le_trans (le_max_left _ _) hn
  have hnn₁ : n₁ ≤ n := le_trans (le_max_right _ _) hn
  constructor
  · apply possibleLineCount_classified_of_separation hn100
    intro P hPcard hthird
    have hp := hlarge P (by omega : n₁ ≤ P.card) (by
      simpa [hPcard] using hthird)
    simpa [hPcard] using hp
  · exact classifiedValue_possible hn100

#print axioms erdos_606

end

end Erdos606

alias _root_.Erdos606.erdos606 := _root_.Erdos606.erdos_606
