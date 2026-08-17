/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic

/-!
# The endpoint-counting lemma for Erdős Problem 58

This file isolates the finite counting argument in Lemma 4 of Gyárfás,
*Graphs with k odd cycle lengths*.  The geometric input is recorded by
`EndpointGeometry`: a longest odd cycle, an outside path, the shortcut paths
between its endpoints, and ordered attachments to the cycle.  The remaining
cycle-splicing output is recorded by `EndpointCountData` as explicit
families of actual odd-cycle lengths.  The theorem `endpoint_count` proves,
rather than assumes, the numerical conclusion

`ceil (p / 2) + q ≤ |oddCycleLengths G|`.

The small-cycle/sumset separation in `LengthBlock` is the cancellation step
in the paper.  Its cardinality estimate is proved below from the torsion-free
Cauchy--Davenport theorem for `ℕ`.
-/

open Set
open scoped Pointwise SimpleGraph

namespace Erdos58.EndpointCount

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The natural-number ceiling of `n / 2`. -/
def ceilHalf (n : ℕ) : ℕ := (n + 1) / 2

@[simp] lemma ceilHalf_eq_ceilDiv (n : ℕ) : ceilHalf n = n ⌈/⌉ 2 := by
  simp only [ceilHalf, Nat.ceilDiv_eq_add_pred_div]
  congr 1

/-- A longest odd cycle, represented by a Mathlib closed walk. -/
structure LongestOddCycle (G : SimpleGraph V) where
  base : V
  cycle : G.Walk base base
  isCycle : cycle.IsCycle
  odd_length : Odd cycle.length
  longest : ∀ {n : ℕ}, n ∈ oddCycleLengths G → n ≤ cycle.length

/--
The path-and-attachment geometry used in the endpoint-counting argument.

The positions `aPos 0 < ... < aPos (p-1) < bPos` express the orientation in
which the `p` neighbours of `A` precede the extra neighbour of `B`.  The
outside path and every shortcut route avoid the longest cycle.  The `q`
positions `chordPos` are the additional neighbours of `A` on the outside
path; the first edge of `S` supplies the remaining, `(q+1)`-st neighbour.
-/
structure EndpointGeometry (G : SimpleGraph V) (p q : ℕ) where
  longestCycle : LongestOddCycle G
  aVertex : V
  bVertex : V
  path : G.Walk aVertex bVertex
  path_isPath : path.IsPath
  path_positive : 0 < path.length
  path_avoids_cycle : ∀ {v : V}, v ∈ path.support → v ∉ longestCycle.cycle.support
  chordPos : Fin q → ℕ
  chordPos_strictMono : StrictMono chordPos
  chordPos_pos : ∀ i, 0 < chordPos i
  chordPos_le : ∀ i, chordPos i ≤ path.length
  chord_adj : ∀ i, G.Adj aVertex (path.getVert (chordPos i))
  routes : Fin (q + 1) → G.Walk aVertex bVertex
  routes_isPath : ∀ i, (routes i).IsPath
  routes_avoid_cycle :
    ∀ i {v : V}, v ∈ (routes i).support → v ∉ longestCycle.cycle.support
  routes_length_strictMono : StrictMono (fun i ↦ (routes i).length)
  aPos : Fin p → ℕ
  aPos_strictMono : StrictMono aPos
  bPos : ℕ
  aPos_lt_bPos : ∀ i, aPos i < bPos
  bPos_le : bPos ≤ longestCycle.cycle.length
  a_adj_cycle : ∀ i, G.Adj aVertex (longestCycle.cycle.getVert (aPos i))
  b_adj_cycle : G.Adj bVertex (longestCycle.cycle.getVert bPos)

/--
A separated length block in the endpoint proof.

There are `a` already constructed odd lengths (`small`) and all `b*c`
sums `row i + col j` are also actual odd-cycle lengths.  The strict
separation is exactly what maximality of the chosen odd cycle proves in
Gyárfás' cancellation argument.  Injectivity is stated only for the three
primitive families; collisions among sums are handled by the theorem below.
-/
structure LengthBlock (G : SimpleGraph V) (a b c : ℕ) where
  small : Fin a → ℕ
  row : Fin b → ℕ
  col : Fin c → ℕ
  small_injective : Function.Injective small
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  small_mem : ∀ i, small i ∈ oddCycleLengths G
  sum_mem : ∀ i j, row i + col j ∈ oddCycleLengths G
  separated : ∀ i j k, small i < row j + col k

/--
The cycle-splicing certificate from which a separated block follows by
maximality of the designated odd cycle.  When a small length failed to lie
below a direct-splice length, the cancellation calculation in Gyárfás'
proof produces `complement i j k`, an actual odd cycle longer than the
designated longest cycle.  Storing that actual length and the strict
implication keeps the geometric/simple-cycle obligation visible.
-/
structure SplicingBlock (G : SimpleGraph V) (L : LongestOddCycle G)
    (a b c : ℕ) where
  small : Fin a → ℕ
  row : Fin b → ℕ
  col : Fin c → ℕ
  small_injective : Function.Injective small
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  small_mem : ∀ i, small i ∈ oddCycleLengths G
  sum_mem : ∀ i j, row i + col j ∈ oddCycleLengths G
  complement : Fin a → Fin b → Fin c → ℕ
  complement_mem : ∀ i j k, complement i j k ∈ oddCycleLengths G
  complement_long_of_not_lt :
    ∀ i j k, ¬small i < row j + col k → L.cycle.length < complement i j k

namespace SplicingBlock

/-- Maximality of `L` turns the cancellation certificate into the strict
small-versus-sum separation used by the cardinality argument. -/
def toLengthBlock {a b c : ℕ} (D : SplicingBlock G L a b c) :
    LengthBlock G a b c where
  small := D.small
  row := D.row
  col := D.col
  small_injective := D.small_injective
  row_injective := D.row_injective
  col_injective := D.col_injective
  small_mem := D.small_mem
  sum_mem := D.sum_mem
  separated := by
    intro i j k
    by_contra h
    exact (not_lt_of_ge (L.longest (D.complement_mem i j k)))
      (D.complement_long_of_not_lt i j k h)

end SplicingBlock

namespace LengthBlock

def smallFinset {a b c : ℕ} (D : LengthBlock G a b c) : Finset ℕ :=
  Finset.univ.image D.small

def rowFinset {a b c : ℕ} (D : LengthBlock G a b c) : Finset ℕ :=
  Finset.univ.image D.row

def colFinset {a b c : ℕ} (D : LengthBlock G a b c) : Finset ℕ :=
  Finset.univ.image D.col

lemma card_smallFinset {a b c : ℕ} (D : LengthBlock G a b c) :
    D.smallFinset.card = a := by
  rw [smallFinset, Finset.card_image_of_injective _ D.small_injective]
  simp

lemma card_rowFinset {a b c : ℕ} (D : LengthBlock G a b c) :
    D.rowFinset.card = b := by
  rw [rowFinset, Finset.card_image_of_injective _ D.row_injective]
  simp

lemma card_colFinset {a b c : ℕ} (D : LengthBlock G a b c) :
    D.colFinset.card = c := by
  rw [colFinset, Finset.card_image_of_injective _ D.col_injective]
  simp

lemma smallFinset_disjoint_add {a b c : ℕ} (D : LengthBlock G a b c) :
    Disjoint D.smallFinset (D.rowFinset + D.colFinset) := by
  rw [Finset.disjoint_left]
  intro n hnsmall hnsum
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hnsmall
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hnsum
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
  exact (D.separated i j k).ne hxy.symm

lemma union_subset_oddCycleLengths {a b c : ℕ} (D : LengthBlock G a b c) :
    ↑(D.smallFinset ∪ (D.rowFinset + D.colFinset)) ⊆ oddCycleLengths G := by
  intro n hn
  rw [Finset.coe_union, Set.mem_union] at hn
  rcases hn with hn | hn
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact D.small_mem i
  · obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact D.sum_mem i j

end LengthBlock

/-- The separated-block count: `a` small lengths and a nonempty `b × c`
sum grid yield at least `a+b+c-1` distinct odd cycle lengths. -/
theorem lengthBlock_lower_bound [Finite V] {a b c : ℕ} (D : LengthBlock G a b c)
    (hb : 0 < b) (hc : 0 < c) :
    a + b + c - 1 ≤ (oddCycleLengths G).ncard := by
  have hrow : D.rowFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := D.card_rowFinset
    rw [h] at this
    simp_all
  have hcol : D.colFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := D.card_colFinset
    rw [h] at this
    simp_all
  have hsum : b + c - 1 ≤ (D.rowFinset + D.colFinset).card := by
    simpa [D.card_rowFinset, D.card_colFinset] using
      cauchy_davenport_add_of_linearOrder_isCancelAdd hrow hcol
  have hunion_card :
      (D.smallFinset ∪ (D.rowFinset + D.colFinset)).card =
        a + (D.rowFinset + D.colFinset).card := by
    rw [Finset.card_union_of_disjoint D.smallFinset_disjoint_add,
      D.card_smallFinset]
  have hsub := Set.ncard_le_ncard D.union_subset_oddCycleLengths
    (oddCycleLengths_finite G)
  rw [Set.ncard_coe_finset, hunion_card] at hsub
  omega

/-
Fully explicit input for the endpoint-counting conclusion.

The arc offsets are the oriented distances from the `A`-attachments to the
extra `B`-attachment, plus the two endpoint edges.  `evenArcCount` and
`oddArcCount` are therefore definitions, not arbitrary numbers.  The
`majoritySplicing` records the actual odd cycles obtained after choosing the
larger parity class.  Its `a+b=q+1` split is the partition of the shortcut
paths used in the paper; `b>0` says that the sumset row is nonempty.
-/
namespace EndpointGeometry

def arcOffset {p q : ℕ} (D : EndpointGeometry G p q) (i : Fin p) : ℕ :=
  D.bPos - D.aPos i + 2

def evenArcCount {p q : ℕ} (D : EndpointGeometry G p q) : ℕ :=
  (Finset.univ.filter fun i : Fin p ↦ Even (D.arcOffset i)).card

def oddArcCount {p q : ℕ} (D : EndpointGeometry G p q) : ℕ :=
  (Finset.univ.filter fun i : Fin p ↦ Odd (D.arcOffset i)).card

lemma evenArcCount_add_oddArcCount {p q : ℕ} (D : EndpointGeometry G p q) :
    D.evenArcCount + D.oddArcCount = p := by
  have hodd :
      (Finset.univ.filter fun i : Fin p ↦ Odd (D.arcOffset i)) =
        Finset.univ.filter fun i : Fin p ↦ ¬Even (D.arcOffset i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.not_even_iff_odd]
  rw [evenArcCount, oddArcCount, hodd]
  simpa using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin p))) (fun i ↦ Even (D.arcOffset i)))

end EndpointGeometry

structure EndpointCountData (G : SimpleGraph V) (p q : ℕ) : Type u
    extends toGeometry : EndpointGeometry G p q where
  a : ℕ
  b : ℕ
  path_partition : a + b = q + 1
  row_nonempty : 0 < b
  majoritySplicing : SplicingBlock G toGeometry.longestCycle a b
    (max toGeometry.evenArcCount toGeometry.oddArcCount)
  tailLength : ℕ
  smallRoute : Fin a → Fin (q + 1)
  smallRoute_injective : Function.Injective smallRoute
  rowRoute : Fin b → Fin (q + 1)
  rowRoute_injective : Function.Injective rowRoute
  route_classes_disjoint : ∀ i j, smallRoute i ≠ rowRoute j
  small_eq_route_cycle : ∀ i,
    majoritySplicing.small i =
      (toGeometry.routes (smallRoute i)).length - tailLength + 1
  row_eq_route_length : ∀ i,
    majoritySplicing.row i = (toGeometry.routes (rowRoute i)).length
  majorityArc :
    Fin (max toGeometry.evenArcCount toGeometry.oddArcCount) → Fin p
  majorityArc_injective : Function.Injective majorityArc
  majorityArc_parity : ∀ i,
    (toGeometry.oddArcCount ≤ toGeometry.evenArcCount →
      Even (toGeometry.arcOffset (majorityArc i))) ∧
    (toGeometry.evenArcCount < toGeometry.oddArcCount →
      Odd (toGeometry.arcOffset (majorityArc i)))
  col_eq_arc_offset : ∀ i,
    majoritySplicing.col i = toGeometry.arcOffset (majorityArc i)

private lemma max_parity_count_pos {p q : ℕ} (D : EndpointCountData G p q)
    (hp : 0 < p) :
    0 < max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
  have hpart := D.toGeometry.evenArcCount_add_oddArcCount
  omega

private lemma ceilHalf_le_max_parity_count {p q : ℕ}
    (D : EndpointCountData G p q) :
    ceilHalf p ≤ max D.toGeometry.evenArcCount D.toGeometry.oddArcCount := by
  have hpart := D.toGeometry.evenArcCount_add_oddArcCount
  simp only [ceilHalf]
  omega

/-- **Gyárfás' endpoint-counting lemma (Lemma 4, numerical conclusion).**

If `A` has `p` ordered attachments to a longest odd cycle and `q+1`
neighbours represented by the outside-path routes, while `B` has one further
cycle attachment, the certified splicings contain at least
`ceil(p/2) + q` distinct odd cycle lengths. -/
theorem endpoint_count [Finite V] {p q : ℕ} (D : EndpointCountData G p q)
    (hp : 0 < p) :
    p ⌈/⌉ 2 + q ≤ (oddCycleLengths G).ncard := by
  have hblock := lengthBlock_lower_bound D.majoritySplicing.toLengthBlock D.row_nonempty
    (max_parity_count_pos D hp)
  have hceil := ceilHalf_le_max_parity_count D
  rw [ceilHalf_eq_ceilDiv] at hceil
  have hpath := D.path_partition
  omega

end

end Erdos58.EndpointCount

#print axioms Erdos58.EndpointCount.endpoint_count
