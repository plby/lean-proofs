import ErdosProblems.Erdos593.TripleSystem.HighPairGraph
import Mathlib.Data.Finset.Card

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite completion closures below a pair-codegree threshold

For a fixed ordered pair of vertices, this module packages all third vertices
which complete that pair to an edge.  If the pair does not have codegree at
least `t`, its completion set is finite, and its cardinality is strictly below
`t`.  The resulting finite outputs are the local input required by the
finite-closure layering construction used in the low-codegree branch of the
positive-atom strategy.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {W : Type u} {D : Type v}

/-- The vertices which occur as a third vertex in some host edge containing
the ordered pair `(x, y)`.  The use of `Nonempty` deliberately hides the
choice of a witnessing host edge while retaining a proposition-valued set. -/
def thirdVertexSet (H : TripleSystem W D) (x y : W) : Set W :=
  {z | Nonempty (ThirdVertexWitness H x y z)}

@[simp]
theorem mem_thirdVertexSet_iff {H : TripleSystem W D} {x y z : W} :
    z ∈ thirdVertexSet H x y ↔ Nonempty (ThirdVertexWitness H x y z) :=
  Iff.rfl

/-- A finite family of pair completions, listed without repetitions, gives an
explicit pair-codegree witness of the same size. -/
theorem hasPairCodegreeAtLeast_of_finset_subset_thirdVertexSet
    {H : TripleSystem W D} {x y : W} {s : Finset W} {t : Nat}
    (hcard : s.card = t)
    (hsubset : (s : Set W) ⊆ thirdVertexSet H x y) :
    HasPairCodegreeAtLeast H x y t := by
  classical
  let e : (↑s : Type u) ≃ Fin t := s.equivFinOfCardEq hcard
  let third : Fin t ↪ W :=
    { toFun := fun k => (e.symm k).1
      inj' := by
        intro i j hij
        apply e.symm.injective
        apply Subtype.ext
        exact hij }
  refine ⟨PairCodegreeWitness.ofThirdVertexWitnesses third ?_⟩
  intro k
  change ThirdVertexWitness H x y ((e.symm k).1)
  exact Classical.choice (hsubset (e.symm k).property)

/-- If a pair has no `t` distinct completions, then all of its completion
vertices form a finite set. -/
theorem thirdVertexSet_finite_of_not_hasPairCodegreeAtLeast
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) :
    (thirdVertexSet H x y).Finite := by
  by_contra hinfinite
  have hinfinite' : (thirdVertexSet H x y).Infinite := hinfinite
  obtain ⟨s, hs, hcard⟩ := hinfinite'.exists_subset_card_eq t
  exact h (hasPairCodegreeAtLeast_of_finset_subset_thirdVertexSet hcard hs)

/-- The explicit finite list of all completion vertices of a pair known not
to reach the threshold `t`.  This definition depends on the low-codegree
proof only to make the finite enumeration available. -/
noncomputable def thirdVertexFinset
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) : Finset W :=
  (thirdVertexSet_finite_of_not_hasPairCodegreeAtLeast h).toFinset

theorem mem_thirdVertexFinset_iff
    {H : TripleSystem W D} {x y z : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) :
    z ∈ thirdVertexFinset h ↔ Nonempty (ThirdVertexWitness H x y z) := by
  change z ∈ (thirdVertexSet_finite_of_not_hasPairCodegreeAtLeast h).toFinset ↔ _
  rw [(thirdVertexSet_finite_of_not_hasPairCodegreeAtLeast h).mem_toFinset]
  rfl

/-- The finite completion output of a pair below threshold `t` has fewer than
`t` vertices.  This is a cardinality bound on *distinct* third vertices. -/
theorem thirdVertexFinset_card_lt
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) :
    (thirdVertexFinset h).card < t := by
  by_contra hnot
  have hle : t ≤ (thirdVertexFinset h).card := Nat.le_of_not_gt hnot
  apply h
  apply hasPairCodegreeAtLeast_mono
    (hasPairCodegreeAtLeast_of_finset_subset_thirdVertexSet rfl ?_) hle
  intro z hz
  change Nonempty (ThirdVertexWitness H x y z)
  exact (mem_thirdVertexFinset_iff h).mp hz

/-- A total finite output for an ordered pair: high pairs contribute no
low-codegree completion vertices, while every pair below threshold `t`
contributes all of its completion vertices. -/
noncomputable def lowCompletionFinset
    (H : TripleSystem W D) (t : Nat) (x y : W) : Finset W := by
  classical
  exact if h : HasPairCodegreeAtLeast H x y t then ∅ else thirdVertexFinset h

theorem lowCompletionFinset_eq_empty_of_hasPairCodegreeAtLeast
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : HasPairCodegreeAtLeast H x y t) :
    lowCompletionFinset H t x y = ∅ := by
  rw [lowCompletionFinset, dif_pos h]

theorem lowCompletionFinset_eq_thirdVertexFinset_of_not_hasPairCodegreeAtLeast
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) :
    lowCompletionFinset H t x y = thirdVertexFinset h := by
  rw [lowCompletionFinset, dif_neg h]

theorem mem_lowCompletionFinset_iff_of_not_hasPairCodegreeAtLeast
    {H : TripleSystem W D} {x y z : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) :
    z ∈ lowCompletionFinset H t x y ↔ Nonempty (ThirdVertexWitness H x y z) := by
  rw [lowCompletionFinset_eq_thirdVertexFinset_of_not_hasPairCodegreeAtLeast h]
  exact mem_thirdVertexFinset_iff h

theorem lowCompletionFinset_card_lt_of_not_hasPairCodegreeAtLeast
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ HasPairCodegreeAtLeast H x y t) :
    (lowCompletionFinset H t x y).card < t := by
  rw [lowCompletionFinset_eq_thirdVertexFinset_of_not_hasPairCodegreeAtLeast h]
  exact thirdVertexFinset_card_lt h

/-- A low pair in the high-pair graph is precisely a distinct pair for which
the finite low-completion output contains every completion. -/
theorem mem_lowCompletionFinset_of_not_highPair
    {H : TripleSystem W D} {x y z : W} {t : Nat}
    (hxy : x ≠ y) (h : ¬ HighPair H t x y)
    (hz : Nonempty (ThirdVertexWitness H x y z)) :
    z ∈ lowCompletionFinset H t x y := by
  have hlow : ¬ HasPairCodegreeAtLeast H x y t := by
    intro hcodeg
    exact h ⟨hxy, hcodeg⟩
  exact (mem_lowCompletionFinset_iff_of_not_hasPairCodegreeAtLeast hlow).mpr hz

theorem lowCompletionFinset_card_lt_of_not_highPair
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (hxy : x ≠ y) (h : ¬ HighPair H t x y) :
    (lowCompletionFinset H t x y).card < t := by
  have hlow : ¬ HasPairCodegreeAtLeast H x y t := by
    intro hcodeg
    exact h ⟨hxy, hcodeg⟩
  exact lowCompletionFinset_card_lt_of_not_hasPairCodegreeAtLeast hlow

/-- The high-pair relation is symmetric in its two endpoints. -/
theorem highPair_comm
    (H : TripleSystem W D) (t : Nat) (x y : W) :
    HighPair H t x y ↔ HighPair H t y x := by
  constructor
  · rintro ⟨hxy, hcodeg⟩
    exact ⟨hxy.symm, (hasPairCodegreeAtLeast_comm H x y t).mp hcodeg⟩
  · rintro ⟨hyx, hcodeg⟩
    exact ⟨hyx.symm, (hasPairCodegreeAtLeast_comm H y x t).mp hcodeg⟩

/-- A chosen ordering of a two-element finite set.  The ordering is arbitrary,
but its two endpoints are distinct and recover the original unordered pair. -/
structure PairEndpoints (s : Finset W) where
  left : W
  right : W
  ne : left ≠ right
  eq_pair : (s : Set W) = {left, right}

/-- Choose an ordering of a two-element finite set. -/
noncomputable def choosePairEndpoints
    (s : {s : Finset W // s.card = 2}) : PairEndpoints s.1 :=
  Classical.choice (by
  classical
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp s.2
  exact ⟨⟨x, y, hxy, by simp [hs]⟩⟩)

theorem choosePairEndpoints_ne
    (s : {s : Finset W // s.card = 2}) :
    (choosePairEndpoints s).left ≠ (choosePairEndpoints s).right :=
  (choosePairEndpoints s).ne

theorem choosePairEndpoints_eq_pair
    (s : {s : Finset W // s.card = 2}) :
    (s.1 : Set W) = {(choosePairEndpoints s).left, (choosePairEndpoints s).right} :=
  (choosePairEndpoints s).eq_pair

/-- Any displayed ordering of the same two-element set agrees with the chosen
ordering, either directly or after swapping the two endpoints. -/
theorem choosePairEndpoints_eq_or_eq_swap
    (s : {s : Finset W // s.card = 2}) {x y : W}
    (hs : (s.1 : Set W) = {x, y}) :
    ((choosePairEndpoints s).left = x ∧ (choosePairEndpoints s).right = y) ∨
      ((choosePairEndpoints s).left = y ∧ (choosePairEndpoints s).right = x) := by
  have hpairs : ({x, y} : Set W) =
      {(choosePairEndpoints s).left, (choosePairEndpoints s).right} :=
    hs.symm.trans (choosePairEndpoints_eq_pair s)
  rcases Set.pair_eq_pair_iff.mp hpairs with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨hleft.symm, hright.symm⟩
  · exact Or.inr ⟨hright.symm, hleft.symm⟩

/-- A total arity-two finite-output operator.  Its input type is exactly the
one required by `FiniteClosureCardinality.closure` and
`FiniteClosureLayeringConstruction.exists_finiteClosureLayering_of_uncountable`.
The arbitrary endpoint ordering does not affect the intended low-codegree
closure because pair-codegree and third-vertex witnesses are symmetric. -/
noncomputable def lowPairClosureFinset
    (H : TripleSystem W D) (t : Nat) :
    {s : Finset W // s.card = 2} → Finset W :=
  fun s => lowCompletionFinset H t (choosePairEndpoints s).left
    (choosePairEndpoints s).right

theorem lowPairClosureFinset_apply
    (H : TripleSystem W D) (t : Nat)
    (s : {s : Finset W // s.card = 2}) :
    lowPairClosureFinset H t s =
      lowCompletionFinset H t (choosePairEndpoints s).left
        (choosePairEndpoints s).right :=
  rfl

theorem mem_lowPairClosureFinset_of_not_highPair
    {H : TripleSystem W D} {t : Nat}
    (s : {s : Finset W // s.card = 2}) {z : W}
    (h : ¬ HighPair H t (choosePairEndpoints s).left (choosePairEndpoints s).right)
    (hz : Nonempty (ThirdVertexWitness H (choosePairEndpoints s).left
      (choosePairEndpoints s).right z)) :
    z ∈ lowPairClosureFinset H t s := by
  change z ∈ lowCompletionFinset H t (choosePairEndpoints s).left
    (choosePairEndpoints s).right
  exact mem_lowCompletionFinset_of_not_highPair (choosePairEndpoints_ne s) h hz

theorem lowPairClosureFinset_card_lt_of_not_highPair
    {H : TripleSystem W D} {t : Nat}
    (s : {s : Finset W // s.card = 2})
    (h : ¬ HighPair H t (choosePairEndpoints s).left (choosePairEndpoints s).right) :
    (lowPairClosureFinset H t s).card < t := by
  change (lowCompletionFinset H t (choosePairEndpoints s).left
    (choosePairEndpoints s).right).card < t
  exact lowCompletionFinset_card_lt_of_not_highPair (choosePairEndpoints_ne s) h

/-- The arity-two closure operator contains every completion of any displayed
low pair.  This is the order-independent form used when a triple edge supplies
the pair `{x, y}` only as an unordered finite set. -/
theorem mem_lowPairClosureFinset_of_not_highPair_of_pair
    {H : TripleSystem W D} {t : Nat}
    (s : {s : Finset W // s.card = 2}) {x y z : W}
    (hs : (s.1 : Set W) = {x, y})
    (h : ¬ HighPair H t x y)
    (hz : Nonempty (ThirdVertexWitness H x y z)) :
    z ∈ lowPairClosureFinset H t s := by
  rcases choosePairEndpoints_eq_or_eq_swap s hs with hdirect | hswap
  · apply mem_lowPairClosureFinset_of_not_highPair s
      (by simpa [hdirect.1, hdirect.2] using! h)
    simpa [hdirect.1, hdirect.2] using! hz
  · have hlowSwap : ¬ HighPair H t y x := by
      intro hyx
      exact h ((highPair_comm H t x y).mpr hyx)
    have hzSwap : Nonempty (ThirdVertexWitness H y x z) := by
      rcases hz with ⟨p⟩
      exact ⟨p.swap⟩
    apply mem_lowPairClosureFinset_of_not_highPair s
      (by simpa [hswap.1, hswap.2] using! hlowSwap)
    simpa [hswap.1, hswap.2] using! hzSwap

end TripleSystem

end Erdos593
