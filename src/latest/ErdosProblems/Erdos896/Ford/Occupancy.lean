/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# A finite occupancy lemma for Ford's uniform order statistics

For `v` balls placed in `v` linearly ordered boxes, call a placement good if
the first `j` boxes contain at most `j` balls, for every `j`.  This is the
finite-box version of the event

`ξᵢ ≥ (i - 1) / v`

for the order statistics of `v` uniform random variables.  It is the
specialization `k = v`, `u = 1` of the order-statistics estimate used in
Ford's Lemmas 11.1, 12.1, and 4.9.

The proof below is the elementary cycle-lemma proof.  A cyclic rotation of
every balanced occupancy vector has all its partial sums below the diagonal.
Consequently every placement is a rotation of a good one, and at least a
`1 / v` fraction of all placements is good.  We keep the result in the
division-free form `v ^ v ≤ v * #good`, which is useful over `ℕ`.
-/

namespace Erdos896.Ford.Occupancy

open scoped BigOperators

/-! ## The cycle lemma for balanced lists -/

/-- A list of occupancies is below the diagonal when every prefix contains
at most as many balls as boxes. -/
def BelowDiagonal (l : List ℕ) : Prop :=
  ∀ j ≤ l.length, (l.take j).sum ≤ j

/-- The score of a cut.  Maximizing this is the usual proof of the cycle
lemma: it is the partial-sum excess, shifted by the constant `l.length`. -/
private def cutScore (l : List ℕ) (j : ℕ) : ℕ :=
  (l.take j).sum + (l.length - j)

/-- The balanced (weak) cycle lemma.  If the total occupancy equals the
number of boxes, some cyclic cut has every prefix below the diagonal. -/
theorem exists_rotate_belowDiagonal (l : List ℕ) (hl : l.sum = l.length)
    (hne : l ≠ []) :
    ∃ r < l.length, BelowDiagonal (l.rotate r) := by
  let n := l.length
  have hn : 0 < n := by simpa [n] using List.length_pos_iff.mpr hne
  obtain ⟨r, hr, hrmax⟩ :=
    (Finset.range n).exists_max_image (cutScore l) ⟨0, Finset.mem_range.mpr hn⟩
  have hrlt : r < l.length := by simpa [n] using Finset.mem_range.mp hr
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  intro j hj
  have hrn : r ≤ l.length := (Finset.mem_range.mp hr).le
  rw [List.rotate_eq_drop_append_take hrn]
  by_cases hfirst : j ≤ l.length - r
  · rw [List.take_append_of_le_length]
    · have hsum : (l.take (r + j)).sum = (l.take r).sum + (l.drop r |>.take j).sum := by
        rw [List.take_add, List.sum_append]
      have hrj : r + j ≤ l.length := by omega
      have hscore : cutScore l (r + j) ≤ cutScore l r := by
        by_cases hEq : r + j = l.length
        · have hzero := hrmax 0 (Finset.mem_range.mpr hn)
          rw [hEq]
          simpa [cutScore, hl, n] using hzero
        · exact hrmax (r + j)
            (Finset.mem_range.mpr (lt_of_le_of_ne hrj hEq))
      simp only [cutScore] at hscore
      omega
    · simp [hfirst]
  · have hjle : j ≤ l.length := by
      simpa [List.length_append] using hj
    have hdropLen : (l.drop r).length = l.length - r := List.length_drop
    let t := j - (l.length - r)
    have htEq : t + (l.length - r) = j := by
      dsimp [t]
      omega
    have htr : t ≤ r := by
      dsimp [t]
      omega
    have ht : t < l.length := htr.trans_lt hrlt
    rw [List.take_append, List.take_of_length_le (by omega : (l.drop r).length ≤ j)]
    simp only [hdropLen, List.sum_append]
    change (l.drop r).sum + ((l.take r).take t).sum ≤ j
    rw [List.take_take, min_eq_left htr]
    have hscore := hrmax t (Finset.mem_range.mpr ht)
    have hsplit : (l.take r).sum + (l.drop r).sum = l.sum := by
      simpa using congrArg List.sum (l.take_append_drop r)
    simp only [cutScore] at hscore
    omega

/-! ## Occupancies of finite maps -/

/-- The number of balls sent to box `j` by a placement `f`. -/
def boxOccupancy {v : ℕ} (f : Fin v → Fin v) (j : Fin v) : ℕ :=
  (Finset.univ.filter fun i ↦ f i = j).card

/-- The ordered list of box occupancies of a placement. -/
def occupancyList {v : ℕ} (f : Fin v → Fin v) : List ℕ :=
  List.ofFn (boxOccupancy f)

@[simp]
theorem length_occupancyList {v : ℕ} (f : Fin v → Fin v) :
    (occupancyList f).length = v := by
  simp [occupancyList]

/-- Every ball is counted in exactly one box. -/
@[simp]
theorem sum_occupancyList {v : ℕ} (f : Fin v → Fin v) :
    (occupancyList f).sum = v := by
  rw [occupancyList, List.sum_ofFn]
  simpa [boxOccupancy] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin v)))
      (t := (Finset.univ : Finset (Fin v)))
      (f := f) (by simp)).symm

/-- A good placement is one whose cumulative occupancy never rises above
the diagonal.  Equivalently, its first `j` boxes contain at most `j` balls. -/
def Good {v : ℕ} (f : Fin v → Fin v) : Prop :=
  BelowDiagonal (occupancyList f)

noncomputable instance {v : ℕ} : DecidablePred (@Good v) :=
  Classical.decPred _

/-- Rotate the labels of all boxes by subtracting `r`. -/
def rotatePlacement {v : ℕ} (r : Fin v) (f : Fin v → Fin v) : Fin v → Fin v :=
  fun i ↦ f i - r

/-- Rotating box labels rotates the occupancy list by the same cut. -/
theorem occupancyList_rotatePlacement {v : ℕ} (r : Fin v) (f : Fin v → Fin v) :
    occupancyList (rotatePlacement r f) = (occupancyList f).rotate r.val := by
  let : NeZero v := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt r.isLt)⟩
  apply List.ext_get
  · simp
  · intro j hj₁ hj₂
    simp only [occupancyList, List.get_ofFn]
    rw [List.get_rotate]
    simp only [List.get_ofFn, boxOccupancy, rotatePlacement]
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hjv : j < v := by simpa using hj₁
    let jv : Fin v := ⟨j, hjv⟩
    have hsub : f i - r = jv ↔ f i = jv + r := by
      rw [Fin.sub_eq_add_neg]
      constructor
      · intro h
        calc
          f i = (f i + -r) + r := by simp [add_assoc]
          _ = jv + r := congrArg (· + r) h
      · intro h
        calc
          f i + -r = (jv + r) + -r := congrArg (· + -r) h
          _ = jv := by simp [add_assoc]
    simpa [jv, Fin.ext_iff, Fin.add_def] using hsub

/-- Every nonempty balanced placement has a cyclic relabelling which is
good.  This is the finite occupancy form of the ballot/cycle lemma. -/
theorem exists_rotatePlacement_good {v : ℕ} (hv : 0 < v) (f : Fin v → Fin v) :
    ∃ r : Fin v, Good (rotatePlacement r f) := by
  obtain ⟨r, hr, hgood⟩ := exists_rotate_belowDiagonal (occupancyList f)
    (by simp) (by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega)
  refine ⟨⟨r, by simpa using hr⟩, ?_⟩
  simpa [Good, occupancyList_rotatePlacement] using hgood

end Erdos896.Ford.Occupancy
