/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# Alternating finite paths

This file collects the elementary list constructions used whenever two disjoint vertex sets
are completely joined.  `alternate xs ys` reads one vertex from `xs`, then one from `ys`, and
continues in that order.  The two useful shapes are

* `xs.length = ys.length + 1`: the list starts and ends on the `xs` side;
* `xs.length = ys.length`: the list starts on the `xs` side and ends on the `ys` side.

Swapping the two arguments gives both corresponding paths starting on the other side.  The
last section packages the construction for finite sets, including exact support and length
statements.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- Interleave two lists, beginning with the first one.  If one list is exhausted, append the
remaining list.  In path applications the lengths are equal or the first list is longer by
one, so the appended remainder has length at most one. -/
def alternate {A : Type*} : List A → List A → List A
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: alternate xs ys

@[simp] lemma alternate_nil_left {A : Type*} (ys : List A) :
    alternate ([] : List A) ys = ys := rfl

@[simp] lemma alternate_nil_right {A : Type*} (xs : List A) :
    alternate xs ([] : List A) = xs := by cases xs <;> rfl

@[simp] lemma alternate_cons_cons {A : Type*} (x y : A) (xs ys : List A) :
    alternate (x :: xs) (y :: ys) = x :: y :: alternate xs ys := rfl

@[simp] lemma head?_alternate_cons_left {A : Type*} (x : A) (xs ys : List A) :
    (alternate (x :: xs) ys).head? = some x := by
  cases ys <;> rfl

@[simp] lemma mem_alternate {A : Type*} {xs ys : List A} {z : A} :
    z ∈ alternate xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [alternate, ih, or_assoc, or_left_comm]

lemma mem_alternate_left {A : Type*} {xs ys : List A} {x : A} (hx : x ∈ xs) :
    x ∈ alternate xs ys :=
  mem_alternate.mpr (Or.inl hx)

lemma mem_alternate_right {A : Type*} {xs ys : List A} {y : A} (hy : y ∈ ys) :
    y ∈ alternate xs ys :=
  mem_alternate.mpr (Or.inr hy)

@[simp] lemma length_alternate {A : Type*} (xs ys : List A) :
    (alternate xs ys).length = xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [alternate, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] lemma toFinset_alternate [DecidableEq V] (xs ys : List V) :
    (alternate xs ys).toFinset = xs.toFinset ∪ ys.toFinset := by
  ext z
  simp

/-- Interleaving merely permutes the concatenation of the two input lists. -/
lemma alternate_perm_append {A : Type*} (xs ys : List A) :
    List.Perm (alternate xs ys) (xs ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys =>
          rw [alternate_cons_cons, List.cons_append]
          exact (List.perm_cons_append_cons y (ih ys)).cons x

/-- Interleaving preserves duplicate-freeness provided the two input lists are duplicate-free
and disjoint.  No length assumption is needed for this purely set-theoretic fact. -/
lemma nodup_alternate {A : Type*} {xs ys : List A} (hxs : xs.Nodup) (hys : ys.Nodup)
    (hdisj : List.Disjoint xs ys) : (alternate xs ys).Nodup := by
  rw [(alternate_perm_append xs ys).nodup_iff]
  exact List.nodup_append.mpr ⟨hxs, hys, fun a ha b hb hab ↦ hdisj ha (hab ▸ hb)⟩

/-- Every vertex of `xs` is joined to every vertex of `ys`. -/
def CrossAdjacent (G : SimpleGraph V) (xs ys : List V) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, G.Adj x y

lemma CrossAdjacent.symm {G : SimpleGraph V} {xs ys : List V}
    (h : CrossAdjacent G xs ys) : CrossAdjacent G ys xs := by
  intro y hy x hx
  exact (h x hx y hy).symm

lemma CrossAdjacent.mono {G : SimpleGraph V} {xs ys xs' ys' : List V}
    (h : CrossAdjacent G xs ys) (hxs : ∀ x ∈ xs', x ∈ xs)
    (hys : ∀ y ∈ ys', y ∈ ys) : CrossAdjacent G xs' ys' := by
  intro x hx y hy
  exact h x (hxs x hx) y (hys y hy)

/-- Equal-sized sides give an alternating chain which starts on the first side and ends on the
second side. -/
lemma isChain_alternate_of_length_eq {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length) (hadj : CrossAdjacent G xs ys) :
    (alternate xs ys).IsChain G.Adj := by
  induction xs generalizing ys with
  | nil =>
      have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simp only [List.length_cons] at hlen; omega
          have hxy : G.Adj x y := hadj x (by simp) y (by simp)
          cases xs with
          | nil =>
              have : ys = [] := List.eq_nil_of_length_eq_zero hlen'.symm
              subst ys
              simp [alternate, hxy]
          | cons z zs =>
              have hyz : G.Adj y z := (hadj z (by simp) y (by simp)).symm
              have htail : (alternate (z :: zs) ys).IsChain G.Adj := by
                apply ih hlen'
                exact hadj.mono (by aesop) (by aesop)
              rw [alternate_cons_cons, List.isChain_cons_cons]
              refine ⟨hxy, htail.cons ?_⟩
              simpa using hyz

/-- If the first side has one extra vertex, interleaving gives an alternating chain starting
and ending on that side. -/
lemma isChain_alternate_of_length_eq_add_one {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length + 1) (hadj : CrossAdjacent G xs ys) :
    (alternate xs ys).IsChain G.Adj := by
  induction xs generalizing ys with
  | nil => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hxslen : xs.length = 0 := by simp only [List.length_cons, List.length_nil] at hlen; omega
          have : xs = [] := List.eq_nil_of_length_eq_zero hxslen
          subst xs
          simp
      | cons y ys =>
          have hlen' : xs.length = ys.length + 1 := by
            simp only [List.length_cons] at hlen
            omega
          have hxy : G.Adj x y := hadj x (by simp) y (by simp)
          cases xs with
          | nil => simp at hlen
          | cons z zs =>
              have hyz : G.Adj y z := (hadj z (by simp) y (by simp)).symm
              have htail : (alternate (z :: zs) ys).IsChain G.Adj := by
                apply ih hlen'
                exact hadj.mono (by aesop) (by aesop)
              rw [alternate_cons_cons, List.isChain_cons_cons]
              refine ⟨hxy, htail.cons ?_⟩
              simpa using hyz

/-- The equal-sized alternating chain, started from the second side instead. -/
lemma isChain_alternate_reverse_of_length_eq {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length) (hadj : CrossAdjacent G xs ys) :
    (alternate ys xs).IsChain G.Adj :=
  isChain_alternate_of_length_eq hlen.symm hadj.symm

/-- If the second side has one extra vertex, swapping the arguments gives an alternating chain
which starts and ends on the second side. -/
lemma isChain_alternate_reverse_of_length_eq_add_one {G : SimpleGraph V} {xs ys : List V}
    (hlen : ys.length = xs.length + 1) (hadj : CrossAdjacent G xs ys) :
    (alternate ys xs).IsChain G.Adj :=
  isChain_alternate_of_length_eq_add_one hlen hadj.symm

lemma alternate_ne_nil_of_left_ne_nil {A : Type*} {xs ys : List A} (hxs : xs ≠ []) :
    alternate xs ys ≠ [] := by
  cases xs <;> cases ys <;> simp_all [alternate]

lemma alternate_ne_nil_of_right_ne_nil {A : Type*} {xs ys : List A} (hys : ys ≠ []) :
    alternate xs ys ≠ [] := by
  intro h
  have : alternate xs ys = [] := h
  have := congrArg List.length this
  simp only [length_alternate, List.length_nil] at this
  have hyslen : ys.length = 0 := by omega
  exact hys (List.eq_nil_of_length_eq_zero hyslen)

/-- An admissible alternating list always begins with the first vertex of its first side. -/
lemma head?_alternate_of_left_ne_nil {A : Type*} {xs ys : List A} (hxs : xs ≠ []) :
    (alternate xs ys).head? = xs.head? := by
  cases xs with
  | nil => contradiction
  | cons x xs => simp

/-- With equal nonzero side lengths, the alternating list ends with the final vertex of the
second side. -/
lemma getLast?_alternate_of_length_eq {A : Type*} {xs ys : List A}
    (hlen : xs.length = ys.length) :
    (alternate xs ys).getLast? = ys.getLast? := by
  induction xs generalizing ys with
  | nil =>
      have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by
            simp only [List.length_cons] at hlen
            omega
          cases xs with
          | nil =>
              have : ys = [] := List.eq_nil_of_length_eq_zero hlen'.symm
              subst ys
              simp [alternate]
          | cons z zs =>
              have hys0 : ys ≠ [] := by
                intro h
                subst ys
                simp at hlen'
              calc
                (alternate (x :: z :: zs) (y :: ys)).getLast? =
                    (alternate (z :: zs) ys).getLast? := by
                  rw [alternate_cons_cons, List.getLast?_cons_cons]
                  exact List.getLast?_cons_of_ne_nil
                    (alternate_ne_nil_of_left_ne_nil (List.cons_ne_nil z zs))
                _ = ys.getLast? := ih hlen'
                _ = (y :: ys).getLast? := (List.getLast?_cons_of_ne_nil hys0).symm

/-- If the first side is larger by one, the alternating list ends with the final vertex of that
same first side. -/
lemma getLast?_alternate_of_length_eq_add_one {A : Type*} {xs ys : List A}
    (hlen : xs.length = ys.length + 1) :
    (alternate xs ys).getLast? = xs.getLast? := by
  induction xs generalizing ys with
  | nil => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hxslen : xs.length = 0 := by
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          have : xs = [] := List.eq_nil_of_length_eq_zero hxslen
          subst xs
          simp [alternate]
      | cons y ys =>
          have hlen' : xs.length = ys.length + 1 := by
            simp only [List.length_cons] at hlen
            omega
          have hxs0 : xs ≠ [] := by
            intro h
            subst xs
            simp at hlen'
          calc
            (alternate (x :: xs) (y :: ys)).getLast? =
                (alternate xs ys).getLast? := by
              rw [alternate_cons_cons, List.getLast?_cons_cons]
              exact List.getLast?_cons_of_ne_nil (alternate_ne_nil_of_left_ne_nil hxs0)
            _ = xs.getLast? := ih hlen'
            _ = (x :: xs).getLast? := (List.getLast?_cons_of_ne_nil hxs0).symm

/-- Equal side lengths and the reversed argument order give a list starting on the second side
and ending on the first. -/
lemma getLast?_alternate_reverse_of_length_eq {A : Type*} {xs ys : List A}
    (hlen : xs.length = ys.length) :
    (alternate ys xs).getLast? = xs.getLast? :=
  getLast?_alternate_of_length_eq hlen.symm

/-- When the second side is larger by one, reversing the argument order gives a list which starts
and ends on that second side. -/
lemma getLast?_alternate_reverse_of_length_eq_add_one {A : Type*} {xs ys : List A}
    (hlen : ys.length = xs.length + 1) :
    (alternate ys xs).getLast? = ys.getLast? :=
  getLast?_alternate_of_length_eq_add_one hlen

/-- Endpoint package for the equal-sized construction: it starts on the first side and ends on
the second. -/
lemma endpoints_alternate_of_length_eq {A : Type*} {xs ys : List A}
    (hlen : xs.length = ys.length) (hxs0 : xs ≠ []) :
    (alternate xs ys).head? = xs.head? ∧
      (alternate xs ys).getLast? = ys.getLast? :=
  ⟨head?_alternate_of_left_ne_nil hxs0, getLast?_alternate_of_length_eq hlen⟩

/-- Endpoint package for a first side larger by one: both endpoints lie on that first side. -/
lemma endpoints_alternate_of_length_eq_add_one {A : Type*} {xs ys : List A}
    (hlen : xs.length = ys.length + 1) :
    (alternate xs ys).head? = xs.head? ∧
      (alternate xs ys).getLast? = xs.getLast? := by
  have hxs0 : xs ≠ [] := by
    intro h
    subst xs
    simp at hlen
  exact ⟨head?_alternate_of_left_ne_nil hxs0,
    getLast?_alternate_of_length_eq_add_one hlen⟩

/-- Endpoint package for equal-sized lists started from the second side. -/
lemma endpoints_alternate_reverse_of_length_eq {A : Type*} {xs ys : List A}
    (hlen : xs.length = ys.length) (hys0 : ys ≠ []) :
    (alternate ys xs).head? = ys.head? ∧
      (alternate ys xs).getLast? = xs.getLast? :=
  ⟨head?_alternate_of_left_ne_nil hys0, getLast?_alternate_reverse_of_length_eq hlen⟩

/-- Endpoint package for a second side larger by one: after swapping the arguments, both
endpoints lie on that second side. -/
lemma endpoints_alternate_reverse_of_length_eq_add_one {A : Type*} {xs ys : List A}
    (hlen : ys.length = xs.length + 1) :
    (alternate ys xs).head? = ys.head? ∧
      (alternate ys xs).getLast? = ys.getLast? := by
  have hys0 : ys ≠ [] := by
    intro h
    subst ys
    simp at hlen
  exact ⟨head?_alternate_of_left_ne_nil hys0,
    getLast?_alternate_reverse_of_length_eq_add_one hlen⟩

/-- Equal-sized, nonempty disjoint lists in a complete bipartite pair enumerate a simple path
starting on the first side and ending on the second. -/
lemma isPath_alternate_of_length_eq {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length) (hxs0 : xs ≠ []) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hdisj : List.Disjoint xs ys) (hadj : CrossAdjacent G xs ys) :
    IsPath G (alternate xs ys) := by
  exact ⟨alternate_ne_nil_of_left_ne_nil hxs0, nodup_alternate hxs hys hdisj,
    isChain_alternate_of_length_eq hlen hadj⟩

/-- The equal-sized alternating simple path, started on the second side. -/
lemma isPath_alternate_reverse_of_length_eq {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length) (hxs0 : xs ≠ []) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hdisj : List.Disjoint xs ys) (hadj : CrossAdjacent G xs ys) :
    IsPath G (alternate ys xs) := by
  exact ⟨alternate_ne_nil_of_right_ne_nil hxs0, nodup_alternate hys hxs hdisj.symm,
    isChain_alternate_reverse_of_length_eq hlen hadj⟩

/-- A one-vertex imbalance gives a simple path starting and ending on the larger first side. -/
lemma isPath_alternate_of_length_eq_add_one {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length + 1) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hdisj : List.Disjoint xs ys) (hadj : CrossAdjacent G xs ys) :
    IsPath G (alternate xs ys) := by
  have hxs0 : xs ≠ [] := by
    intro h
    subst xs
    simp at hlen
  exact ⟨alternate_ne_nil_of_left_ne_nil hxs0, nodup_alternate hxs hys hdisj,
    isChain_alternate_of_length_eq_add_one hlen hadj⟩

/-- A one-vertex imbalance gives a simple path starting and ending on the larger second side. -/
lemma isPath_alternate_reverse_of_length_eq_add_one {G : SimpleGraph V} {xs ys : List V}
    (hlen : ys.length = xs.length + 1) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hdisj : List.Disjoint xs ys) (hadj : CrossAdjacent G xs ys) :
    IsPath G (alternate ys xs) := by
  exact isPath_alternate_of_length_eq_add_one hlen hys hxs hdisj.symm hadj.symm

section Finsets

/-- The canonical alternating enumeration of two finite sets, starting with `X`. -/
noncomputable def alternateFinsets (X Y : Finset V) : List V :=
  alternate X.toList Y.toList

/-- The canonical alternating enumeration of two finite sets, starting with `Y`. -/
noncomputable def alternateFinsetsReverse (X Y : Finset V) : List V :=
  alternate Y.toList X.toList

@[simp] lemma mem_alternateFinsets {X Y : Finset V} {z : V} :
    z ∈ alternateFinsets X Y ↔ z ∈ X ∨ z ∈ Y := by
  simp [alternateFinsets]

@[simp] lemma mem_alternateFinsetsReverse {X Y : Finset V} {z : V} :
    z ∈ alternateFinsetsReverse X Y ↔ z ∈ X ∨ z ∈ Y := by
  simp [alternateFinsetsReverse, or_comm]

@[simp] lemma toFinset_alternateFinsets [DecidableEq V] (X Y : Finset V) :
    (alternateFinsets X Y).toFinset = X ∪ Y := by
  simp [alternateFinsets]

@[simp] lemma toFinset_alternateFinsetsReverse [DecidableEq V] (X Y : Finset V) :
    (alternateFinsetsReverse X Y).toFinset = X ∪ Y := by
  simp [alternateFinsetsReverse, Finset.union_comm]

@[simp] lemma length_alternateFinsets (X Y : Finset V) :
    (alternateFinsets X Y).length = X.card + Y.card := by
  simp [alternateFinsets]

@[simp] lemma length_alternateFinsetsReverse (X Y : Finset V) :
    (alternateFinsetsReverse X Y).length = X.card + Y.card := by
  simp [alternateFinsetsReverse, Nat.add_comm]

lemma nodup_alternateFinsets {X Y : Finset V} (hdisj : Disjoint X Y) :
    (alternateFinsets X Y).Nodup := by
  apply nodup_alternate (Finset.nodup_toList X) (Finset.nodup_toList Y)
  intro z hzX hzY
  exact Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hzX) (Finset.mem_toList.mp hzY)

lemma nodup_alternateFinsetsReverse {X Y : Finset V} (hdisj : Disjoint X Y) :
    (alternateFinsetsReverse X Y).Nodup := by
  apply nodup_alternate (Finset.nodup_toList Y) (Finset.nodup_toList X)
  intro z hzY hzX
  exact Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hzX) (Finset.mem_toList.mp hzY)

/-- Equal-cardinality disjoint finite sets with all cross-edges form an alternating simple path,
provided they are nonempty. -/
lemma isPath_alternateFinsets_of_card_eq {G : SimpleGraph V} {X Y : Finset V}
    (hcard : X.card = Y.card) (hX0 : X.Nonempty) (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    IsPath G (alternateFinsets X Y) := by
  apply isPath_alternate_of_length_eq
  · simpa using hcard
  · exact hX0.toList_ne_nil
  · exact Finset.nodup_toList X
  · exact Finset.nodup_toList Y
  · intro z hzX hzY
    exact Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hzX) (Finset.mem_toList.mp hzY)
  · intro x hx y hy
    exact hadj x (Finset.mem_toList.mp hx) y (Finset.mem_toList.mp hy)

/-- The equal-cardinality path with the same support, started on `Y`. -/
lemma isPath_alternateFinsetsReverse_of_card_eq {G : SimpleGraph V} {X Y : Finset V}
    (hcard : X.card = Y.card) (hX0 : X.Nonempty) (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    IsPath G (alternateFinsetsReverse X Y) := by
  apply isPath_alternate_reverse_of_length_eq
  · simpa using hcard
  · exact hX0.toList_ne_nil
  · exact Finset.nodup_toList X
  · exact Finset.nodup_toList Y
  · intro z hzX hzY
    exact Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hzX) (Finset.mem_toList.mp hzY)
  · intro x hx y hy
    exact hadj x (Finset.mem_toList.mp hx) y (Finset.mem_toList.mp hy)

/-- If `X` has one more vertex than `Y`, their canonical enumeration is a simple path starting
and ending in `X`. -/
lemma isPath_alternateFinsets_of_card_eq_add_one {G : SimpleGraph V} {X Y : Finset V}
    (hcard : X.card = Y.card + 1) (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    IsPath G (alternateFinsets X Y) := by
  apply isPath_alternate_of_length_eq_add_one
  · simpa using hcard
  · exact Finset.nodup_toList X
  · exact Finset.nodup_toList Y
  · intro z hzX hzY
    exact Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hzX) (Finset.mem_toList.mp hzY)
  · intro x hx y hy
    exact hadj x (Finset.mem_toList.mp hx) y (Finset.mem_toList.mp hy)

/-- If `Y` has one more vertex than `X`, swapping the enumeration produces a simple path which
starts and ends in `Y`. -/
lemma isPath_alternateFinsetsReverse_of_card_eq_add_one {G : SimpleGraph V}
    {X Y : Finset V} (hcard : Y.card = X.card + 1) (hdisj : Disjoint X Y)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    IsPath G (alternateFinsetsReverse X Y) := by
  apply isPath_alternate_reverse_of_length_eq_add_one
  · simpa using hcard
  · exact Finset.nodup_toList X
  · exact Finset.nodup_toList Y
  · intro z hzX hzY
    exact Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hzX) (Finset.mem_toList.mp hzY)
  · intro x hx y hy
    exact hadj x (Finset.mem_toList.mp hx) y (Finset.mem_toList.mp hy)

end Finsets

end Erdos518
