import ErdosProblems.Erdos957.Case13Bridge

/-!
# Coordinate-free Case 3 bridge for Erdős 957

This module removes the artificial normalization of the middle neighbour to
`verticalDown`.  The source remains at `origin`, so the supporting line is still horizontal,
but the middle unit neighbour may be any point in `InOpenMiddleCone`.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957Case3General

open Erdos957Cases13 Erdos957Case13Bridge

abbrev Point := Erdos957Cases13.Point

/-- Signed area of the oriented triangle `a,b,p`. -/
def crossFrom (a b p : Point) : ℝ :=
  (b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1)

/-- On the intersection of two unit circles, signed area determines the point. -/
lemma eq_of_common_unit_of_cross_eq {a b p q : Point}
    (hab : sqDist a b = 1)
    (hap : sqDist a p = 1) (hbp : sqDist b p = 1)
    (haq : sqDist a q = 1) (hbq : sqDist b q = 1)
    (hcross : crossFrom a b p = crossFrom a b q) :
    p = q := by
  have hdotp :
      (b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2) = 1 / 2 := by
    simp only [sqDist] at hab hap hbp
    nlinarith
  have hdotq :
      (b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2) = 1 / 2 := by
    simp only [sqDist] at hab haq hbq
    nlinarith
  have hnorm : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 = 1 := by
    simp only [sqDist] at hab
    nlinarith
  have hxid :
      ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (p.1 - q.1) =
        (b.1 - a.1) *
            ((b.1 - a.1) * (p.1 - q.1) + (b.2 - a.2) * (p.2 - q.2)) -
          (b.2 - a.2) *
            ((b.1 - a.1) * (p.2 - q.2) - (b.2 - a.2) * (p.1 - q.1)) := by
    ring
  have hyid :
      ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (p.2 - q.2) =
        (b.2 - a.2) *
            ((b.1 - a.1) * (p.1 - q.1) + (b.2 - a.2) * (p.2 - q.2)) +
          (b.1 - a.1) *
            ((b.1 - a.1) * (p.2 - q.2) - (b.2 - a.2) * (p.1 - q.1)) := by
    ring
  have hcross' :
      (b.1 - a.1) * (p.2 - q.2) - (b.2 - a.2) * (p.1 - q.1) = 0 := by
    dsimp [crossFrom] at hcross
    linarith
  have hdot' :
      (b.1 - a.1) * (p.1 - q.1) + (b.2 - a.2) * (p.2 - q.2) = 0 := by
    linarith
  rw [hnorm, hdot', hcross'] at hxid hyid
  norm_num at hxid hyid
  apply Prod.ext
  · linarith
  · linarith

lemma cross_sq_eq_three_fourths_of_common_unit {a b p : Point}
    (hab : sqDist a b = 1)
    (hap : sqDist a p = 1) (hbp : sqDist b p = 1) :
    crossFrom a b p ^ 2 = 3 / 4 := by
  have hdot :
      (b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2) = 1 / 2 := by
    simp only [sqDist] at hab hap hbp
    nlinarith
  have hnormab : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 = 1 := by
    simp only [sqDist] at hab
    nlinarith
  have hnormap : (p.1 - a.1) ^ 2 + (p.2 - a.2) ^ 2 = 1 := by
    simp only [sqDist] at hap
    nlinarith
  have hid :
      ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) ^ 2 +
          crossFrom a b p ^ 2 =
        ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) *
          ((p.1 - a.1) ^ 2 + (p.2 - a.2) ^ 2) := by
    simp only [crossFrom]
    ring
  nlinarith

/-- Two unit circles in the plane have at most two intersection points. -/
lemma common_unit_eq_first_or_second {a b p q r : Point}
    (hab : sqDist a b = 1)
    (hap : sqDist a p = 1) (hbp : sqDist b p = 1)
    (haq : sqDist a q = 1) (hbq : sqDist b q = 1)
    (har : sqDist a r = 1) (hbr : sqDist b r = 1)
    (hpq : p ≠ q) :
    r = p ∨ r = q := by
  have hpc := cross_sq_eq_three_fourths_of_common_unit hab hap hbp
  have hqc := cross_sq_eq_three_fourths_of_common_unit hab haq hbq
  have hrc := cross_sq_eq_three_fourths_of_common_unit hab har hbr
  have hpqCross : crossFrom a b p ≠ crossFrom a b q := by
    intro h
    exact hpq (eq_of_common_unit_of_cross_eq hab hap hbp haq hbq h)
  have hqneg : crossFrom a b q = -crossFrom a b p := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (hqc.trans hpc.symm)) with h | h
    · exact (hpqCross h.symm).elim
    · exact h
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (hrc.trans hpc.symm)) with h | h
  · exact Or.inl (eq_of_common_unit_of_cross_eq hab har hbr hap hbp h)
  · right
    apply eq_of_common_unit_of_cross_eq hab har hbr haq hbq
    linarith

lemma sqDist_eq_one_of_centered_sub_eq {center p q r : Point}
    (hr : sqDist center r = 1)
    (h : ((p.1 - center.1, p.2 - center.2) -
          (q.1 - center.1, q.2 - center.2)) =
        (r.1 - center.1, r.2 - center.2)) :
    sqDist p q = 1 := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [sqDist] at hr ⊢
  dsimp at hx hy
  have hx' : p.1 - q.1 = r.1 - center.1 := by linarith
  have hy' : p.2 - q.2 = r.2 - center.2 := by linarith
  rw [hx', hy']
  nlinarith [sq_nonneg (center.1 - r.1), sq_nonneg (center.2 - r.2)]

/-- Every vertex of an ordered degree-six neighbour hexagon has two distinct displayed
neighbours which are also a unit from it. -/
lemma OrderedHexagonAt.exists_two_common_neighbors {A : Finset Point} {center : Point}
    (hex : OrderedHexagonAt A center) (i : Fin 6) :
    ∃ j k : Fin 6, j ≠ k ∧
      sqDist center (hex.neighbor j) = 1 ∧
      sqDist (hex.neighbor i) (hex.neighbor j) = 1 ∧
      sqDist center (hex.neighbor k) = 1 ∧
      sqDist (hex.neighbor i) (hex.neighbor k) = 1 := by
  have hunit (u : Fin 6) : sqDist center (hex.neighbor u) = 1 :=
    (mem_unitNeighbors.mp (hex.neighbor_mem u)).2
  fin_cases i
  · refine ⟨1, 5, by decide, hunit 1, ?_, hunit 5, ?_⟩
    · exact sqDist_eq_one_of_centered_sub_eq (hunit 5) hex.zero_sub_one_eq_five
    · rw [sqDist_comm]
      exact sqDist_eq_one_of_centered_sub_eq (hunit 4) hex.five_sub_zero_eq_four
  · refine ⟨0, 2, by decide, hunit 0, ?_, hunit 2, ?_⟩
    · rw [sqDist_comm]
      exact sqDist_eq_one_of_centered_sub_eq (hunit 5) hex.zero_sub_one_eq_five
    · exact sqDist_eq_one_of_centered_sub_eq (hunit 0) hex.one_sub_two_eq_zero
  · refine ⟨1, 3, by decide, hunit 1, ?_, hunit 3, ?_⟩
    · rw [sqDist_comm]
      exact sqDist_eq_one_of_centered_sub_eq (hunit 0) hex.one_sub_two_eq_zero
    · exact sqDist_eq_one_of_centered_sub_eq (hunit 1) hex.two_sub_three_eq_one
  · refine ⟨2, 4, by decide, hunit 2, ?_, hunit 4, ?_⟩
    · rw [sqDist_comm]
      exact sqDist_eq_one_of_centered_sub_eq (hunit 1) hex.two_sub_three_eq_one
    · exact sqDist_eq_one_of_centered_sub_eq (hunit 2) hex.three_sub_four_eq_two
  · refine ⟨3, 5, by decide, hunit 3, ?_, hunit 5, ?_⟩
    · rw [sqDist_comm]
      exact sqDist_eq_one_of_centered_sub_eq (hunit 2) hex.three_sub_four_eq_two
    · exact sqDist_eq_one_of_centered_sub_eq (hunit 3) hex.four_sub_five_eq_three
  · refine ⟨4, 0, by decide, hunit 4, ?_, hunit 0, ?_⟩
    · rw [sqDist_comm]
      exact sqDist_eq_one_of_centered_sub_eq (hunit 3) hex.four_sub_five_eq_three
    · exact sqDist_eq_one_of_centered_sub_eq (hunit 4) hex.five_sub_zero_eq_four

/-- Coordinate-free completion at a degree-six vertex.  The two supplied unit neighbours need
not occupy any prescribed positions in the angular enumeration. -/
lemma completion_mem_of_degree_eq_six {A : Finset Point}
    (hAsep : IsOneSeparated (A : Set Point)) {center x y : Point}
    (hdegree : degree A center = 6)
    (hx : x ∈ unitNeighbors A center) (hy : y ∈ unitNeighbors A center)
    (hxy : sqDist x y = 1) :
    (center.1 + x.1 - y.1, center.2 + x.2 - y.2) ∈ A := by
  let r : Point := (center.1 + x.1 - y.1, center.2 + x.2 - y.2)
  obtain ⟨hex⟩ := exists_orderedHexagonAt_of_degree_eq_six hAsep hdegree
  obtain ⟨i, hi⟩ := hex.neighbor_surjective x hx
  obtain ⟨j, k, hjk, hcj, hij, hck, hik⟩ :=
    Erdos957Case3General.OrderedHexagonAt.exists_two_common_neighbors hex i
  have hcenterx : sqDist center x = 1 := (mem_unitNeighbors.mp hx).2
  have hcentery : sqDist center y = 1 := (mem_unitNeighbors.mp hy).2
  have hcenterr : sqDist center r = 1 := by
    simp only [r, sqDist]
    simp only [sqDist] at hxy
    nlinarith
  have hxr : sqDist x r = 1 := by
    simp only [r, sqDist]
    simp only [sqDist] at hcentery
    nlinarith
  have hjkPoint : hex.neighbor j ≠ hex.neighbor k := by
    exact fun h ↦ hjk (hex.neighbor_injective h)
  have hr := common_unit_eq_first_or_second hcenterx
    (by simpa [hi] using hcj) (by simpa [hi] using hij)
    (by simpa [hi] using hck) (by simpa [hi] using hik)
    hcenterr (by simpa [sqDist_comm] using hxr) hjkPoint
  rcases hr with hr | hr
  · change r ∈ A
    rw [hr]
    exact (mem_unitNeighbors.mp (hex.neighbor_mem j)).1
  · change r ∈ A
    rw [hr]
    exact (mem_unitNeighbors.mp (hex.neighbor_mem k)).1

/-! ## Arbitrary-middle Case 3 transfer -/

def case3Recipients (middle secondary : Point) (middleDegree : ℕ) : Finset Point :=
  if middleDegree ≤ 4 then {middle} else {middle, secondary}

def case3Tokens (middle secondary : Point) (middleDegree : ℕ) (p : Point) : ℕ :=
  if middleDegree ≤ 4 then
    if p = middle then 2 else 0
  else if p = middle ∨ p = secondary then 1 else 0

lemma middle_ne_secondary_of_unit {middle secondary : Point}
    (h : sqDist middle secondary = 1) : middle ≠ secondary := by
  intro heq
  subst secondary
  simpa using h

/-- If the selected secondary common neighbour is strictly higher than the arbitrary middle,
the coordinate-free degree-six completion crosses the horizontal supporting line. -/
lemma secondary_degree_le_five {A : Finset Point} {middle secondary : Point}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hmiddleA : middle ∈ A)
    (hmiddleUnit : sqDist origin middle = 1)
    (hsecondarySource : sqDist origin secondary = 1)
    (hsecondaryMiddle : sqDist middle secondary = 1)
    (hsecondaryHigh : middle.2 < secondary.2) :
    degree A secondary ≤ 5 := by
  have hle := degree_le_six hAsep secondary
  by_contra hnot
  have hdegree : degree A secondary = 6 := by omega
  have hsourceNeighbor : origin ∈ unitNeighbors A secondary := by
    apply mem_unitNeighbors.mpr
    exact ⟨hsourceA, by simpa [sqDist_comm] using hsecondarySource⟩
  have hmiddleNeighbor : middle ∈ unitNeighbors A secondary := by
    apply mem_unitNeighbors.mpr
    exact ⟨hmiddleA, by simpa [sqDist_comm] using hsecondaryMiddle⟩
  have hforced := completion_mem_of_degree_eq_six hAsep hdegree
    hsourceNeighbor hmiddleNeighbor hmiddleUnit
  have hbelow := hsupport _ hforced
  dsimp [origin] at hbelow
  linarith

/-- Complete Case 3 local row for an arbitrary middle unit vector in the actual open inward
cone.  In the high-degree branch the recipients are exactly `{middle, secondary}`. -/
theorem localTransfer_of_common_neighbor
    {A hull : Finset Point} {middle secondary : Point} {middleDegree : ℕ}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3)
    (hmiddleA : middle ∈ A) (hsecondaryA : secondary ∈ A)
    (hmiddleDegree : middleDegree = degree A middle)
    (hmiddleLeFive : middleDegree ≤ 5)
    (hmiddleInterior : middle ∉ hull)
    (honeExtreme : ∀ p ∈ hull, sqDist middle p = 1 → p = origin)
    (hmiddleUnit : sqDist origin middle = 1)
    (_hmiddleCone : InOpenMiddleCone middle)
    (hsecondarySource : sqDist origin secondary = 1)
    (hsecondaryMiddle : sqDist middle secondary = 1)
    (hsecondaryHigh : middle.2 < secondary.2) :
    Nonempty (LocalTransfer A hull origin) := by
  have hmiddleBelow : middle.2 ≤ 0 := hsupport middle hmiddleA
  have hsecondaryBelow : secondary.2 ≤ 0 := hsupport secondary hsecondaryA
  have hmiddleRect := unit_point_in_sourceRectangle hmiddleUnit hmiddleBelow
  have hsecondaryRect :=
    unit_point_in_sourceRectangle hsecondarySource hsecondaryBelow
  have hsecondaryDeg := secondary_degree_le_five hAsep hsupport hsourceA hmiddleA
    hmiddleUnit hsecondarySource hsecondaryMiddle hsecondaryHigh
  have hne : middle ≠ secondary := middle_ne_secondary_of_unit hsecondaryMiddle
  refine ⟨{
    source_mem := hsourceA
    source_mem_hull := hsourceHull
    source_degree_three := hsourceDegree
    recipients := case3Recipients middle secondary middleDegree
    tokens := case3Tokens middle secondary middleDegree
    tokens_eq_zero := ?_
    tokens_pos := ?_
    total_tokens := ?_
    recipient_mem := ?_
    recipient_not_hull := ?_
    recipient_rectangle := ?_
    recipient_within_two := ?_
    recipient_capacity := ?_ }⟩
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · simp [case3Recipients, case3Tokens, hlow] at hp ⊢
      exact fun h ↦ hp (by simpa [h])
    · simp [case3Recipients, case3Tokens, hlow] at hp ⊢
      exact hp
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = middle := by simpa [case3Recipients, hlow] using hp
      subst p
      simp [case3Tokens, hlow]
    · have hpEq : p = middle ∨ p = secondary := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl <;> simp [case3Tokens, hlow, hne]
  · by_cases hlow : middleDegree ≤ 4
    · simp [case3Recipients, case3Tokens, hlow]
    · rw [show case3Recipients middle secondary middleDegree = insert middle {secondary} by
          simp [case3Recipients, hlow],
        Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
      simp [case3Tokens, hlow, hne]
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = middle := by simpa [case3Recipients, hlow] using hp
      simpa [hpEq] using hmiddleA
    · have hpEq : p = middle ∨ p = secondary := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hmiddleA
      · exact hsecondaryA
  · intro p hp hpHull
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = middle := by simpa [case3Recipients, hlow] using hp
      subst p
      exact hmiddleInterior hpHull
    · have hpEq : p = middle ∨ p = secondary := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hmiddleInterior hpHull
      · have heq := honeExtreme _ hpHull hsecondaryMiddle
        rw [heq, sqDist_self] at hsecondarySource
        norm_num at hsecondarySource
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = middle := by simpa [case3Recipients, hlow] using hp
      simpa [hpEq] using hmiddleRect
    · have hpEq : p = middle ∨ p = secondary := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hmiddleRect
      · exact hsecondaryRect
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = middle := by simpa [case3Recipients, hlow] using hp
      subst p
      exact Or.inl hmiddleUnit
    · have hpEq : p = middle ∨ p = secondary := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact Or.inl hmiddleUnit
      · exact Or.inl hsecondarySource
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = middle := by simpa [case3Recipients, hlow] using hp
      subst p
      simp [case3Tokens, hlow]
      rw [← hmiddleDegree]
      omega
    · have hpEq : p = middle ∨ p = secondary := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · simp [case3Tokens, hlow]
        rw [← hmiddleDegree]
        omega
      · simp [case3Tokens, hlow]
        omega

/-! ## Oriented right/left identification -/

/-- Two common unit neighbours on the nonnegative oriented side of a unit segment coincide. -/
lemma common_unit_eq_of_cross_nonneg {a b p q : Point}
    (hab : sqDist a b = 1)
    (hap : sqDist a p = 1) (hbp : sqDist b p = 1)
    (haq : sqDist a q = 1) (hbq : sqDist b q = 1)
    (hpSide : 0 ≤ crossFrom a b p) (hqSide : 0 ≤ crossFrom a b q) :
    p = q := by
  have hp := cross_sq_eq_three_fourths_of_common_unit hab hap hbp
  have hq := cross_sq_eq_three_fourths_of_common_unit hab haq hbq
  apply eq_of_common_unit_of_cross_eq hab hap hbp haq hbq
  nlinarith

/-- Reflected version on the nonpositive oriented side. -/
lemma common_unit_eq_of_cross_nonpos {a b p q : Point}
    (hab : sqDist a b = 1)
    (hap : sqDist a p = 1) (hbp : sqDist b p = 1)
    (haq : sqDist a q = 1) (hbq : sqDist b q = 1)
    (hpSide : crossFrom a b p ≤ 0) (hqSide : crossFrom a b q ≤ 0) :
    p = q := by
  have hp := cross_sq_eq_three_fourths_of_common_unit hab hap hbp
  have hq := cross_sq_eq_three_fourths_of_common_unit hab haq hbq
  apply eq_of_common_unit_of_cross_eq hab hap hbp haq hbq
  nlinarith

/-- The right oriented-sector condition identifies the selected common neighbour with the
already existing nonmiddle source neighbour. -/
lemma right_candidate_eq_existing {middle existing selected : Point}
    (hmiddleUnit : sqDist origin middle = 1)
    (hexistingSource : sqDist origin existing = 1)
    (hexistingMiddle : sqDist middle existing = 1)
    (hselectedSource : sqDist origin selected = 1)
    (hselectedMiddle : sqDist middle selected = 1)
    (hexistingSide : 0 ≤ crossFrom origin middle existing)
    (hselectedSide : 0 ≤ crossFrom origin middle selected) :
    existing = selected := by
  exact common_unit_eq_of_cross_nonneg hmiddleUnit hexistingSource
    (by simpa [sqDist_comm] using hexistingMiddle) hselectedSource
    (by simpa [sqDist_comm] using hselectedMiddle) hexistingSide hselectedSide

/-- The left oriented-sector condition gives the reflected identification. -/
lemma left_candidate_eq_existing {middle existing selected : Point}
    (hmiddleUnit : sqDist origin middle = 1)
    (hexistingSource : sqDist origin existing = 1)
    (hexistingMiddle : sqDist middle existing = 1)
    (hselectedSource : sqDist origin selected = 1)
    (hselectedMiddle : sqDist middle selected = 1)
    (hexistingSide : crossFrom origin middle existing ≤ 0)
    (hselectedSide : crossFrom origin middle selected ≤ 0) :
    existing = selected := by
  exact common_unit_eq_of_cross_nonpos hmiddleUnit hexistingSource
    (by simpa [sqDist_comm] using hexistingMiddle) hselectedSource
    (by simpa [sqDist_comm] using hselectedMiddle) hexistingSide hselectedSide

/-- Right-hand arbitrary-middle Case 3 transfer.  The selected secondary recipient is proved to
be the existing right source neighbour by signed-area orientation. -/
theorem right_localTransfer
    {A hull : Finset Point} {middle existing selected : Point} {middleDegree : ℕ}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3)
    (hmiddleA : middle ∈ A) (hexistingA : existing ∈ A)
    (hmiddleDegree : middleDegree = degree A middle)
    (hmiddleLeFive : middleDegree ≤ 5)
    (hmiddleInterior : middle ∉ hull)
    (honeExtreme : ∀ p ∈ hull, sqDist middle p = 1 → p = origin)
    (hmiddleUnit : sqDist origin middle = 1)
    (hmiddleCone : InOpenMiddleCone middle)
    (hexistingSource : sqDist origin existing = 1)
    (hexistingMiddle : sqDist middle existing = 1)
    (hselectedSource : sqDist origin selected = 1)
    (hselectedMiddle : sqDist middle selected = 1)
    (hexistingSide : 0 ≤ crossFrom origin middle existing)
    (hselectedSide : 0 ≤ crossFrom origin middle selected)
    (hselectedHigh : middle.2 < selected.2) :
    Nonempty (LocalTransfer A hull origin) := by
  have heq := right_candidate_eq_existing hmiddleUnit hexistingSource hexistingMiddle
    hselectedSource hselectedMiddle hexistingSide hselectedSide
  have hselectedA : selected ∈ A := heq ▸ hexistingA
  apply localTransfer_of_common_neighbor hAsep hsupport hsourceA hsourceHull hsourceDegree
    hmiddleA hselectedA hmiddleDegree hmiddleLeFive hmiddleInterior honeExtreme
    hmiddleUnit hmiddleCone hselectedSource hselectedMiddle hselectedHigh

/-- Reflected left-hand arbitrary-middle Case 3 transfer. -/
theorem left_localTransfer
    {A hull : Finset Point} {middle existing selected : Point} {middleDegree : ℕ}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3)
    (hmiddleA : middle ∈ A) (hexistingA : existing ∈ A)
    (hmiddleDegree : middleDegree = degree A middle)
    (hmiddleLeFive : middleDegree ≤ 5)
    (hmiddleInterior : middle ∉ hull)
    (honeExtreme : ∀ p ∈ hull, sqDist middle p = 1 → p = origin)
    (hmiddleUnit : sqDist origin middle = 1)
    (hmiddleCone : InOpenMiddleCone middle)
    (hexistingSource : sqDist origin existing = 1)
    (hexistingMiddle : sqDist middle existing = 1)
    (hselectedSource : sqDist origin selected = 1)
    (hselectedMiddle : sqDist middle selected = 1)
    (hexistingSide : crossFrom origin middle existing ≤ 0)
    (hselectedSide : crossFrom origin middle selected ≤ 0)
    (hselectedHigh : middle.2 < selected.2) :
    Nonempty (LocalTransfer A hull origin) := by
  have heq := left_candidate_eq_existing hmiddleUnit hexistingSource hexistingMiddle
    hselectedSource hselectedMiddle hexistingSide hselectedSide
  have hselectedA : selected ∈ A := heq ▸ hexistingA
  apply localTransfer_of_common_neighbor hAsep hsupport hsourceA hsourceHull hsourceDegree
    hmiddleA hselectedA hmiddleDegree hmiddleLeFive hmiddleInterior honeExtreme
    hmiddleUnit hmiddleCone hselectedSource hselectedMiddle hselectedHigh

end Erdos957Case3General
