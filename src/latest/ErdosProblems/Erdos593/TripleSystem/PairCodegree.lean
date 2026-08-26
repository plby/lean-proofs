import ErdosProblems.Erdos593.TripleSystem.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593

universe u v

namespace TripleSystem

/-- A specified host edge completing `x` and `y` by `z`. Since a host edge
has cardinality three, the equality below forces the displayed points to be
pairwise distinct. -/
structure ThirdVertexWitness {W : Type u} {D : Type v}
    (H : TripleSystem W D) (x y z : W) where
  edge : D
  edgeSet_eq : H.edgeSet edge = {x, y, z}

private theorem ncard_triple_lt_three_of_duplicate
    {W : Type u} {x y z : W} (hdup : x = y ∨ x = z ∨ y = z) :
    ({x, y, z} : Set W).ncard < 3 := by
  rcases hdup with hxy | hxz | hyz
  · subst y
    have hle : ({x, x, z} : Set W).ncard ≤ 2 := by
      calc
        ({x, x, z} : Set W).ncard = ({x, z} : Set W).ncard := by simp
        _ ≤ ({z} : Set W).ncard + 1 := Set.ncard_insert_le x {z}
        _ = 2 := by simp
    exact Nat.lt_succ_iff.mpr hle
  · subst z
    have hle : ({x, y, x} : Set W).ncard ≤ 2 := by
      calc
        ({x, y, x} : Set W).ncard = ({y, x} : Set W).ncard := by simp
        _ = ({x, y} : Set W).ncard := by rw [Set.pair_comm y x]
        _ ≤ ({y} : Set W).ncard + 1 := Set.ncard_insert_le x {y}
        _ = 2 := by simp
    exact Nat.lt_succ_iff.mpr hle
  · subst z
    have hle : ({x, y, y} : Set W).ncard ≤ 2 := by
      calc
        ({x, y, y} : Set W).ncard = ({x, y} : Set W).ncard := by simp
        _ ≤ ({y} : Set W).ncard + 1 := Set.ncard_insert_le x {y}
        _ = 2 := by simp
    exact Nat.lt_succ_iff.mpr hle

/-- A three-element host edge cannot be displayed using duplicate vertices. -/
theorem pairwise_ne_of_edgeSet_eq_triple
    {W : Type u} {D : Type v} {H : TripleSystem W D} {e : D} {x y z : W}
    (he : H.edgeSet e = {x, y, z}) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hcard : ({x, y, z} : Set W).ncard = 3 := by
    rw [← he]
    exact H.edgeSet_ncard e
  constructor
  · intro hxy
    exact (Nat.ne_of_lt
      (ncard_triple_lt_three_of_duplicate (Or.inl hxy))) hcard
  constructor
  · intro hxz
    exact (Nat.ne_of_lt
      (ncard_triple_lt_three_of_duplicate (Or.inr (Or.inl hxz)))) hcard
  · intro hyz
    exact (Nat.ne_of_lt
      (ncard_triple_lt_three_of_duplicate (Or.inr (Or.inr hyz)))) hcard

namespace ThirdVertexWitness

variable {W : Type u} {D : Type v} {H : TripleSystem W D} {x y : W}

/-- Reorder the two distinguished endpoints of a completion witness. -/
def swap {z : W} (p : ThirdVertexWitness H x y z) :
    ThirdVertexWitness H y x z where
  edge := p.edge
  edgeSet_eq := p.edgeSet_eq.trans (Set.insert_comm x y {z})

/-- Reinterpret a completion witness with one endpoint and its completion
vertex interchanged. -/
def rotate {z : W} (p : ThirdVertexWitness H x y z) :
    ThirdVertexWitness H x z y where
  edge := p.edge
  edgeSet_eq := p.edgeSet_eq.trans
    (congrArg (Set.insert x) (Set.pair_comm y z))

theorem left_ne_right {z : W} (p : ThirdVertexWitness H x y z) : x ≠ y :=
  (pairwise_ne_of_edgeSet_eq_triple p.edgeSet_eq).1

theorem third_ne_left {z : W} (p : ThirdVertexWitness H x y z) : z ≠ x :=
  (pairwise_ne_of_edgeSet_eq_triple p.edgeSet_eq).2.1.symm

theorem third_ne_right {z : W} (p : ThirdVertexWitness H x y z) : z ≠ y :=
  (pairwise_ne_of_edgeSet_eq_triple p.edgeSet_eq).2.2.symm

end ThirdVertexWitness

/-- Explicit, distinct third vertices together with their host-edge witnesses.
`Nonempty (PairCodegreeWitness H x y t)` is the formal codegree-at-least-`t`
assertion used by the positive-atom construction. -/
structure PairCodegreeWitness {W : Type u} {D : Type v}
    (H : TripleSystem W D) (x y : W) (t : Nat) where
  third : Fin t ↪ W
  edge : Fin t → D
  edgeSet_eq : ∀ k, H.edgeSet (edge k) = {x, y, third k}

/-- The pair `(x, y)` has at least `t` distinct, explicitly witnessed
third-vertex completions. -/
def HasPairCodegreeAtLeast (H : TripleSystem W D) (x y : W) (t : Nat) : Prop :=
  Nonempty (PairCodegreeWitness H x y t)

namespace PairCodegreeWitness

variable {W : Type u} {D : Type v} {H : TripleSystem W D}
  {x y : W} {t : Nat}

/-- Extract the one-cell witness at a given completion index. -/
def thirdWitness (p : PairCodegreeWitness H x y t) (k : Fin t) :
    ThirdVertexWitness H x y (p.third k) where
  edge := p.edge k
  edgeSet_eq := p.edgeSet_eq k

/-- Assemble a pair-codegree witness from distinct third vertices and one
completion witness for each of them. -/
def ofThirdVertexWitnesses (third : Fin t ↪ W)
    (witness : ∀ k, ThirdVertexWitness H x y (third k)) :
    PairCodegreeWitness H x y t where
  third := third
  edge := fun k => (witness k).edge
  edgeSet_eq := fun k => (witness k).edgeSet_eq

/-- Reorder the two distinguished endpoints of every completion witness. -/
def swap (p : PairCodegreeWitness H x y t) : PairCodegreeWitness H y x t where
  third := p.third
  edge := p.edge
  edgeSet_eq k := (p.edgeSet_eq k).trans (Set.insert_comm x y {p.third k})

/-- Restrict a codegree witness to any smaller finite family of third
vertices. -/
def restrict (p : PairCodegreeWitness H x y t) {s : Nat} (hst : s ≤ t) :
    PairCodegreeWitness H x y s where
  third := Function.Embedding.trans (Fin.castLEEmb hst) p.third
  edge := fun k => p.edge (Fin.castLE hst k)
  edgeSet_eq := fun k => p.edgeSet_eq (Fin.castLE hst k)

theorem left_ne_right (p : PairCodegreeWitness H x y t) (ht : 0 < t) : x ≠ y :=
  ThirdVertexWitness.left_ne_right (thirdWitness p ⟨0, ht⟩)

theorem third_ne_left (p : PairCodegreeWitness H x y t) (k : Fin t) :
    p.third k ≠ x :=
  ThirdVertexWitness.third_ne_left (thirdWitness p k)

theorem third_ne_right (p : PairCodegreeWitness H x y t) (k : Fin t) :
    p.third k ≠ y :=
  ThirdVertexWitness.third_ne_right (thirdWitness p k)

end PairCodegreeWitness

/-- Pair-codegree lower bounds are monotone in the requested number of
distinct completions. -/
theorem hasPairCodegreeAtLeast_mono {W : Type u} {D : Type v}
    {H : TripleSystem W D} {x y : W} {s t : Nat}
    (h : HasPairCodegreeAtLeast H x y t) (hst : s ≤ t) :
    HasPairCodegreeAtLeast H x y s := by
  rcases h with ⟨p⟩
  exact ⟨p.restrict hst⟩

/-- Pair-codegree is symmetric in its two distinguished endpoints. -/
theorem hasPairCodegreeAtLeast_comm {W : Type u} {D : Type v}
    (H : TripleSystem W D) (x y : W) (t : Nat) :
    HasPairCodegreeAtLeast H x y t ↔ HasPairCodegreeAtLeast H y x t := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.swap⟩
  · rintro ⟨p⟩
    exact ⟨p.swap⟩

end TripleSystem

end Erdos593
