import ErdosProblems.Erdos796.C4Free
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The elementary `C₄`-free double count

This file proves the finite inequality at the heart of the
Kővári--Sós--Turán estimate.  The two vertex classes are finite sets `L` and
`R`, while `E : Finset (X × Y)` is the ambient finite edge set.
-/

namespace Erdos796

namespace Bipartite

open scoped BigOperators

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- Degree into the finite left vertex set `L` of a right vertex `y`. -/
def leftDegree (E : Finset (X × Y)) (L : Finset X) (y : Y) : ℕ :=
  (L.filter fun x => (x, y) ∈ E).card

/-- Common right neighbours in `R` of every vertex in an unordered left
vertex set `s`.  We apply this with `s.card = 2`. -/
def pairCommonNeighbors (E : Finset (X × Y)) (R : Finset Y)
    (s : Finset X) : Finset Y :=
  R.filter fun y => ∀ x ∈ s, (x, y) ∈ E

/-- The number of edges of `E` between the displayed finite vertex classes. -/
def edgeCount (E : Finset (X × Y)) (L : Finset X) (R : Finset Y) : ℕ :=
  ∑ y ∈ R, leftDegree E L y

/-- A two-element left set has at most one common right neighbour in a
`C₄`-free graph. -/
theorem card_pairCommonNeighbors_le_one {E : Finset (X × Y)} (hE : C4Free E)
    (R : Finset Y) {s : Finset X} (hs : s.card = 2) :
    (pairCommonNeighbors E R s).card ≤ 1 := by
  rcases Finset.card_eq_two.mp hs with ⟨x₁, x₂, hxx, rfl⟩
  rw [Finset.card_le_one_iff]
  intro y₁ y₂ hy₁ hy₂
  have h₁ := (Finset.mem_filter.mp hy₁).2
  have h₂ := (Finset.mem_filter.mp hy₂).2
  exact
    (hE (h₁ x₁ (by simp)) (h₂ x₁ (by simp))
      (h₁ x₂ (by simp)) (h₂ x₂ (by simp))).resolve_left hxx

/-- The sum of codegrees over unordered left pairs is bounded by the number
of such pairs. -/
theorem sum_pairCommonNeighbors_le_choose {E : Finset (X × Y)} (hE : C4Free E)
    (L : Finset X) (R : Finset Y) :
    (∑ s ∈ L.powersetCard 2, (pairCommonNeighbors E R s).card) ≤
      Nat.choose L.card 2 := by
  calc
    (∑ s ∈ L.powersetCard 2, (pairCommonNeighbors E R s).card)
        ≤ ∑ _s ∈ L.powersetCard 2, 1 := by
          apply Finset.sum_le_sum
          intro s hs
          exact card_pairCommonNeighbors_le_one hE R
            (Finset.mem_powersetCard.mp hs).2
    _ = (L.powersetCard 2).card := by simp
    _ = Nat.choose L.card 2 := Finset.card_powersetCard 2 L

/-- Exact double counting identity: unordered left pairs counted by their
common right neighbours equal pairs chosen inside each right degree. -/
theorem sum_pairCommonNeighbors_eq_sum_choose_leftDegree
    (E : Finset (X × Y)) (L : Finset X) (R : Finset Y) :
    (∑ s ∈ L.powersetCard 2, (pairCommonNeighbors E R s).card) =
      ∑ y ∈ R, Nat.choose (leftDegree E L y) 2 := by
  let rel : Finset X → Y → Prop := fun s y => ∀ x ∈ s, (x, y) ∈ E
  have hbelow (y : Y) :
      (L.powersetCard 2).bipartiteBelow rel y =
        (L.filter fun x => (x, y) ∈ E).powersetCard 2 := by
    ext s
    simp only [Finset.mem_bipartiteBelow, Finset.mem_powersetCard,
      rel]
    constructor
    · rintro ⟨⟨hsL, hscard⟩, hsE⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hsL hx, hsE x hx⟩, hscard⟩
    · rintro ⟨hs, hscard⟩
      exact ⟨⟨fun x hx => (Finset.mem_filter.mp (hs hx)).1, hscard⟩,
        fun x hx => (Finset.mem_filter.mp (hs hx)).2⟩
  calc
    (∑ s ∈ L.powersetCard 2, (pairCommonNeighbors E R s).card) =
        ∑ s ∈ L.powersetCard 2, (R.bipartiteAbove rel s).card := by
          rfl
    _ = ∑ y ∈ R, ((L.powersetCard 2).bipartiteBelow rel y).card := by
          simpa using!
            (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
              (r := rel) (s := L.powersetCard 2) (t := R))
    _ = ∑ y ∈ R, Nat.choose (leftDegree E L y) 2 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hbelow, Finset.card_powersetCard]
          rfl

/-- Degree form of the elementary `C₄`-free double count. -/
theorem sum_choose_leftDegree_le_choose {E : Finset (X × Y)} (hE : C4Free E)
    (L : Finset X) (R : Finset Y) :
    (∑ y ∈ R, Nat.choose (leftDegree E L y) 2) ≤ Nat.choose L.card 2 := by
  rw [← sum_pairCommonNeighbors_eq_sum_choose_leftDegree E L R]
  exact sum_pairCommonNeighbors_le_choose hE L R

/-- Exact conversion between the second moment of the degrees and the number
of unordered pairs they contain. -/
theorem sum_sq_leftDegree_eq
    (E : Finset (X × Y)) (L : Finset X) (R : Finset Y) :
    (∑ y ∈ R, (leftDegree E L y : ℝ) ^ 2) =
      (edgeCount E L R : ℝ) +
        2 * ∑ y ∈ R, (Nat.choose (leftDegree E L y) 2 : ℝ) := by
  have hterm (d : ℕ) :
      (d : ℝ) ^ 2 = (d : ℝ) + 2 * (Nat.choose d 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    ring
  calc
    (∑ y ∈ R, (leftDegree E L y : ℝ) ^ 2) =
        ∑ y ∈ R, ((leftDegree E L y : ℝ) +
          2 * (Nat.choose (leftDegree E L y) 2 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hterm (leftDegree E L y)
    _ = (edgeCount E L R : ℝ) +
        2 * ∑ y ∈ R, (Nat.choose (leftDegree E L y) 2 : ℝ) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
          simp [edgeCount]

/-- A quadratic edge bound, the direct Cauchy--Schwarz form of the
Kővári--Sós--Turán estimate.  Here `edgeCount E L R` counts precisely the
edges of `E` lying in `L × R`. -/
theorem edgeCount_sq_le {E : Finset (X × Y)} (hE : C4Free E)
    (L : Finset X) (R : Finset Y) :
    (edgeCount E L R : ℝ) ^ 2 ≤
      (R.card : ℝ) *
        ((edgeCount E L R : ℝ) + 2 * (Nat.choose L.card 2 : ℝ)) := by
  have hpairsNat := sum_choose_leftDegree_le_choose hE L R
  have hpairs :
      (∑ y ∈ R, (Nat.choose (leftDegree E L y) 2 : ℝ)) ≤
        (Nat.choose L.card 2 : ℝ) := by
    exact_mod_cast hpairsNat
  have hsquares :
      (∑ y ∈ R, (leftDegree E L y : ℝ) ^ 2) ≤
        (edgeCount E L R : ℝ) + 2 * (Nat.choose L.card 2 : ℝ) := by
    rw [sum_sq_leftDegree_eq E L R]
    gcongr
  calc
    (edgeCount E L R : ℝ) ^ 2 =
        (∑ y ∈ R, (leftDegree E L y : ℝ)) ^ 2 := by
          simp [edgeCount]
    _ ≤ (R.card : ℝ) * ∑ y ∈ R, (leftDegree E L y : ℝ) ^ 2 := by
          exact sq_sum_le_card_mul_sum_sq
    _ ≤ (R.card : ℝ) *
        ((edgeCount E L R : ℝ) + 2 * (Nat.choose L.card 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg R.card)

/-- Explicit square-root form of the finite Kővári--Sós--Turán bound. -/
theorem edgeCount_le_card_add_sqrt {E : Finset (X × Y)} (hE : C4Free E)
    (L : Finset X) (R : Finset Y) :
    (edgeCount E L R : ℝ) ≤
      (R.card : ℝ) +
        Real.sqrt (2 * (R.card : ℝ) * (Nat.choose L.card 2 : ℝ)) := by
  let e : ℝ := edgeCount E L R
  let r : ℝ := R.card
  let c : ℝ := Nat.choose L.card 2
  have he : 0 ≤ e := by positivity
  have hr : 0 ≤ r := by positivity
  have hc : 0 ≤ c := by positivity
  have hq : e ^ 2 ≤ r * (e + 2 * c) := by
    simpa [e, r, c] using! edgeCount_sq_le hE L R
  have hrad : 0 ≤ 2 * r * c := mul_nonneg (mul_nonneg (by norm_num) hr) hc
  have hsqrt : 0 ≤ Real.sqrt (2 * r * c) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (2 * r * c) ^ 2 = 2 * r * c :=
    Real.sq_sqrt hrad
  by_cases her : e ≤ r
  · dsimp [e, r, c] at her hsqrt
    linarith
  · have hre : r ≤ e := (lt_of_not_ge her).le
    have hshift : 0 ≤ e - r := sub_nonneg.mpr hre
    have hshift_sq : (e - r) ^ 2 ≤ 2 * r * c := by
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hre)]
    have hshift_le : e - r ≤ Real.sqrt (2 * r * c) := by
      nlinarith
    dsimp [e, r, c] at hshift_le ⊢
    linarith

end Bipartite

end Erdos796
