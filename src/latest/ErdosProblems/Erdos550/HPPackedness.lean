import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The packedness invariant in the specialized matching lemma

The Hladký--Piguet matching algorithm has exactly two states in each regular
matching edge.  Either both sides have reached the head-neighbour threshold, or
the two current loads differ by at most the shrub order.  A saturated bin stays
saturated.  A balanced bin stays balanced by putting the larger colour class of
the next shrub on the less loaded side.
-/

namespace Erdos550

/-- Specialized packedness: threshold saturation or balanced loads. -/
def HPPacked (leftLoad rightLoad leftThreshold rightThreshold margin τ : ℝ) : Prop :=
  min leftThreshold rightThreshold - margin ≤ min leftLoad rightLoad ∨
    |leftLoad - rightLoad| ≤ τ

/-- Two nonnegative loads of total size at most `τ` can be oriented so that a
previous discrepancy at most `τ` remains at most `τ`. -/
lemma balance_two_loads
    (l r a b τ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ τ)
    (hlr : |l - r| ≤ τ) :
    (|(l + a) - (r + b)| ≤ τ) ∨
      (|(l + b) - (r + a)| ≤ τ) := by
  rw [abs_le] at hlr
  by_cases hl : l ≤ r
  · by_cases hc : b ≤ a
    · left
      rw [abs_le]
      constructor <;> nlinarith
    · right
      rw [abs_le]
      constructor <;> nlinarith
  · have hrl : r ≤ l := le_of_not_ge hl
    by_cases hc : a ≤ b
    · left
      rw [abs_le]
      constructor <;> nlinarith
    · right
      rw [abs_le]
      constructor <;> nlinarith

/-- Packedness is preserved when a small two-colour component is inserted in
the better of its two orientations. -/
lemma hpPacked_update
    (l r a b L R margin τ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ τ)
    (hpack : HPPacked l r L R margin τ) :
    HPPacked (l + a) (r + b) L R margin τ ∨
      HPPacked (l + b) (r + a) L R margin τ := by
  rcases hpack with hsat | hbal
  · left
    apply Or.inl
    exact hsat.trans (min_le_min (le_add_of_nonneg_right ha)
      (le_add_of_nonneg_right hb))
  · rcases balance_two_loads l r a b τ ha hb hab hbal with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-- In the balanced, nonsaturated case, the two free-side cardinalities differ
by at most `τ`. -/
lemma hpPacked_free_discrepancy
    (l r cap τ : ℝ) (hbal : |l - r| ≤ τ) :
    |(cap - l) - (cap - r)| ≤ τ := by
  calc
    |(cap - l) - (cap - r)| = |-(l - r)| := by congr 1 <;> ring
    _ = |l - r| := abs_neg _
    _ ≤ τ := hbal

/-- Summed supply beating summed current load by one margin per bin yields a
bin with the required local excess. -/
lemma exists_bin_with_margin
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (supply load : κ → ℝ) (margin : ℝ)
    (hsum : (∑ k, load k) + (Fintype.card κ : ℝ) * margin
      ≤ ∑ k, supply k) :
    ∃ k, load k + margin ≤ supply k := by
  by_contra h
  push_neg at h
  have hlt : (∑ k, supply k) <
      ∑ k, (load k + margin) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun k _ => h k)
  have heq :
      (∑ k, (load k + margin)) =
        (∑ k, load k) + (Fintype.card κ : ℝ) * margin := by
    simp [Finset.sum_add_distrib]
  rw [heq] at hlt
  exact (not_lt_of_ge hsum hlt).elim

/-- If two free sides differ by at most `τ` and their total is at least
`2L+τ`, then both sides contain at least `L`. -/
lemma both_sides_large_of_sum_discrepancy
    (P Q L τ : ℝ)
    (hdisc : |P - Q| ≤ τ)
    (hsum : 2 * L + τ ≤ P + Q) :
    L ≤ P ∧ L ≤ Q := by
  rw [abs_le] at hdisc
  constructor <;> nlinarith

/-- A total root-candidate count of `2L` makes at least one orientation
available. -/
lemma one_side_large_of_sum (p q L : ℝ)
    (hsum : 2 * L ≤ p + q) :
    L ≤ p ∨ L ≤ q := by
  by_contra h
  push_neg at h
  linarith

/-- In a balanced but nonsaturated bin, both sides retain a prescribed root
reserve.  `L,R` are the two head-neighbour thresholds, `l,r` the current
loads, and `err` accounts for exceptional or forbidden vertices. -/
lemma both_root_pools_of_balanced_nonsaturated
    (l r L R margin τ err p q need : ℝ)
    (hbal : |l - r| ≤ τ)
    (hnot : ¬ min L R - margin ≤ min l r)
    (hp : L - l - err ≤ p)
    (hq : R - r - err ≤ q)
    (hneed : need + τ + err ≤ margin) :
    need ≤ p ∧ need ≤ q := by
  have hmin : min l r < min L R - margin :=
    lt_of_not_ge hnot
  have hL : min L R ≤ L := min_le_left _ _
  have hR : min L R ≤ R := min_le_right _ _
  rw [abs_le] at hbal
  rcases le_total l r with hlr | hrl
  · have hminEq : min l r = l := min_eq_left hlr
    rw [hminEq] at hmin
    constructor <;> nlinarith
  · have hminEq : min l r = r := min_eq_right hrl
    rw [hminEq] at hmin
    constructor <;> nlinarith

/-- If an equal-size bin is saturated relative to the two actual head
degrees, a sufficiently large aggregate head surplus forces room on both
sides.  This is the algebraic core of the saturated case in the
Hladký--Piguet packedness argument. -/
lemma both_free_sides_of_saturated
    (cap l r p q margin need : ℝ)
    (hp : p ≤ cap) (hq : q ≤ cap)
    (hsat : min p q - margin ≤ min l r)
    (hsum : l + r + need + margin ≤ p + q) :
    need ≤ cap - l ∧ need ≤ cap - r := by
  rcases le_total p q with hpq | hqp <;>
    rcases le_total l r with hlr | hrl
  · rw [min_eq_left hpq, min_eq_left hlr] at hsat
    constructor <;> nlinarith
  · rw [min_eq_left hpq, min_eq_right hrl] at hsat
    constructor <;> nlinarith
  · rw [min_eq_right hqp, min_eq_left hlr] at hsat
    constructor <;> nlinarith
  · rw [min_eq_right hqp, min_eq_right hrl] at hsat
    constructor <;> nlinarith

/-- A balanced nonsaturated bin has room on both sides using only the local
margin.  This is the complementary half of
`both_free_sides_of_saturated`: nonsaturation puts the smaller load below the
smaller threshold minus `margin`, and balancedness puts the other load at most
`τ` above it. -/
lemma both_free_sides_of_balanced_nonsaturated
    (cap l r L R margin τ need : ℝ)
    (hLcap : L ≤ cap) (hRcap : R ≤ cap)
    (hbal : |l - r| ≤ τ)
    (hnot : ¬ min L R - margin ≤ min l r)
    (hneed : need + τ ≤ margin) :
    need ≤ cap - l ∧ need ≤ cap - r := by
  have hsmall : min l r < min L R - margin :=
    lt_of_not_ge hnot
  have hthreshold : min L R ≤ cap :=
    (min_le_left L R).trans hLcap
  rw [abs_le] at hbal
  rcases le_total l r with hlr | hrl
  · rw [min_eq_left hlr] at hsmall
    constructor <;> nlinarith
  · rw [min_eq_right hrl] at hsmall
    constructor <;> nlinarith

/-- Choose the orientation of one rooted component while preserving
packedness.  In the saturated case one may use whichever endpoint supplies
the root pool.  In the balanced nonsaturated case both endpoint root pools
are assumed available, so `balance_two_loads` chooses the orientation.  Here
`a` is the root-colour load and `b` the opposite-colour load. -/
lemma hpPacked_choose_root_orientation
    (l r a b L R margin τ rootNeed p q : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ τ)
    (hpack : HPPacked l r L R margin τ)
    (hroot : rootNeed ≤ p ∨ rootNeed ≤ q)
    (hboth :
      ¬ min L R - margin ≤ min l r →
        rootNeed ≤ p ∧ rootNeed ≤ q) :
    ∃ swap : Bool,
      rootNeed ≤ (if swap then q else p) ∧
      HPPacked
        (if swap then l + b else l + a)
        (if swap then r + a else r + b)
        L R margin τ := by
  by_cases hsat : min L R - margin ≤ min l r
  · rcases hroot with hp | hq
    · refine ⟨false, by simpa, ?_⟩
      exact Or.inl
        (hsat.trans (min_le_min
          (le_add_of_nonneg_right ha)
          (le_add_of_nonneg_right hb)))
    · refine ⟨true, by simpa, ?_⟩
      exact Or.inl
        (hsat.trans (min_le_min
          (le_add_of_nonneg_right hb)
          (le_add_of_nonneg_right ha)))
  · have hbal : |l - r| ≤ τ := hpack.resolve_left hsat
    have hpq := hboth hsat
    rcases balance_two_loads l r a b τ ha hb hab hbal with h | h
    · exact ⟨false, by simpa using! hpq.1, Or.inr (by simpa using! h)⟩
    · exact ⟨true, by simpa using! hpq.2, Or.inr (by simpa using! h)⟩

end Erdos550
