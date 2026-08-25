import Mathlib

/-!
# Matchings between two three-element fibres

A matching is represented by its finite set of edges.  The defining predicate
says directly that the sets of edges over every left and right vertex have
cardinality at most one.
-/

namespace Erdos59

/-- Either fibre of the bipartite graph. -/
abbrev Fibre := Fin 3

/-- An edge joins a point of the left fibre to a point of the right fibre. -/
abbrev Edge := Fibre × Fibre

/-- The edges in `s` incident to the left vertex `i`. -/
def leftEdges (s : Finset Edge) (i : Fibre) : Finset Edge :=
  s.filter fun e ↦ e.1 = i

/-- The edges in `s` incident to the right vertex `j`. -/
def rightEdges (s : Finset Edge) (j : Fibre) : Finset Edge :=
  s.filter fun e ↦ e.2 = j

/-- A computable check of the three left-degree bounds. -/
private def leftCode (s : Finset Edge) : Bool :=
  decide ((leftEdges s 0).card ≤ 1) &&
    decide ((leftEdges s 1).card ≤ 1) &&
      decide ((leftEdges s 2).card ≤ 1)

/-- A computable check of the three right-degree bounds. -/
private def rightCode (s : Finset Edge) : Bool :=
  decide ((rightEdges s 0).card ≤ 1) &&
    decide ((rightEdges s 1).card ≤ 1) &&
      decide ((rightEdges s 2).card ≤ 1)

/-- Both sides of an edge set have degree at most one. -/
def IsMatching (s : Finset Edge) : Prop :=
  leftCode s && rightCode s = true

instance (s : Finset Edge) : Decidable (IsMatching s) := by
  unfold IsMatching
  exact inferInstance

/-- Matchings between two labelled three-element fibres. -/
def Matching := {s : Finset Edge // IsMatching s}

deriving instance DecidableEq for Matching
deriving instance Fintype for Matching

namespace Matching

/-- The edge set underlying a matching. -/
def edges (M : Matching) : Finset Edge :=
  M.1

/-- Construct a matching from an edge set satisfying the two degree bounds. -/
def ofEdges (s : Finset Edge) (hs : IsMatching s) : Matching :=
  ⟨s, hs⟩

@[simp] theorem edges_ofEdges (s : Finset Edge) (hs : IsMatching s) :
    (ofEdges s hs).edges = s := rfl

theorem isMatching (M : Matching) : IsMatching M.edges :=
  M.2

/-- The incidence relation associated to a matching. -/
def Rel (M : Matching) (i j : Fibre) : Prop :=
  (i, j) ∈ M.edges

instance (M : Matching) : DecidableRel M.Rel := fun i j ↦ by
  unfold Rel edges
  exact inferInstance

@[simp] theorem rel_ofEdges (s : Finset Edge) (hs : IsMatching s) (i j : Fibre) :
    (ofEdges s hs).Rel i j ↔ (i, j) ∈ s := Iff.rfl

/-- The underlying edge set determines a matching. -/
theorem edges_injective : Function.Injective edges := by
  intro M N h
  exact Subtype.ext h

/-- Extensionality in terms of the incidence relation. -/
@[ext] theorem ext {M N : Matching}
    (h : ∀ i j, M.Rel i j ↔ N.Rel i j) : M = N := by
  apply edges_injective
  ext e
  exact h e.1 e.2

theorem rel_ext_iff {M N : Matching} :
    M = N ↔ ∀ i j, M.Rel i j ↔ N.Rel i j := by
  constructor
  · rintro rfl
    simp
  · exact ext

/-- The edge-degree bound at a left vertex. -/
theorem left_degree_le_one (M : Matching) (i : Fibre) :
    (leftEdges M.edges i).card ≤ 1 := by
  have h := Bool.and_eq_true_iff.mp M.isMatching |>.1
  simp only [leftCode, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  fin_cases i
  · simpa using h.1.1
  · simpa using h.1.2
  · simpa using h.2

/-- The edge-degree bound at a right vertex. -/
theorem right_degree_le_one (M : Matching) (j : Fibre) :
    (rightEdges M.edges j).card ≤ 1 := by
  have h := Bool.and_eq_true_iff.mp M.isMatching |>.2
  simp only [rightCode, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  fin_cases j
  · simpa using h.1.1
  · simpa using h.1.2
  · simpa using h.2

/-- A left vertex has at most one partner. -/
theorem left_unique (M : Matching) {i j j' : Fibre}
    (h : M.Rel i j) (h' : M.Rel i j') : j = j' := by
  have hp : (i, j) = (i, j') :=
    Finset.card_le_one_iff.mp (M.left_degree_le_one i)
      (by simpa [leftEdges, Rel] using h)
      (by simpa [leftEdges, Rel] using h')
  exact congrArg Prod.snd hp

/-- A right vertex has at most one partner. -/
theorem right_unique (M : Matching) {i i' j : Fibre}
    (h : M.Rel i j) (h' : M.Rel i' j) : i = i' := by
  have hp : (i, j) = (i', j) :=
    Finset.card_le_one_iff.mp (M.right_degree_le_one j)
      (by simpa [rightEdges, Rel] using h)
      (by simpa [rightEdges, Rel] using h')
  exact congrArg Prod.fst hp

/-- The possible right partners of `i`. -/
def rights (M : Matching) (i : Fibre) : Finset Fibre :=
  (leftEdges M.edges i).image Prod.snd

/-- The possible left partners of `j`. -/
def lefts (M : Matching) (j : Fibre) : Finset Fibre :=
  (rightEdges M.edges j).image Prod.fst

@[simp] theorem mem_rights (M : Matching) (i j : Fibre) :
    j ∈ M.rights i ↔ M.Rel i j := by
  simp [rights, leftEdges, Rel]

@[simp] theorem mem_lefts (M : Matching) (i j : Fibre) :
    i ∈ M.lefts j ↔ M.Rel i j := by
  simp [lefts, rightEdges, Rel]

theorem rights_card_le_one (M : Matching) (i : Fibre) :
    (M.rights i).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro j j' hj hj'
  exact M.left_unique (M.mem_rights i j |>.mp hj) (M.mem_rights i j' |>.mp hj')

theorem lefts_card_le_one (M : Matching) (j : Fibre) :
    (M.lefts j).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i i' hi hi'
  exact M.right_unique (M.mem_lefts i j |>.mp hi) (M.mem_lefts i' j |>.mp hi')

/-- An incident edge recovers the complete right-partner fibre. -/
theorem rights_eq_singleton_of_rel (M : Matching) {i j : Fibre}
    (h : M.Rel i j) : M.rights i = {j} := by
  ext j'
  simp only [mem_rights, Finset.mem_singleton]
  constructor
  · intro h'
    exact M.left_unique h' h
  · rintro rfl
    exact h

/-- An incident edge recovers the complete left-partner fibre. -/
theorem lefts_eq_singleton_of_rel (M : Matching) {i j : Fibre}
    (h : M.Rel i j) : M.lefts j = {i} := by
  ext i'
  simp only [mem_lefts, Finset.mem_singleton]
  constructor
  · intro h'
    exact M.right_unique h' h
  · rintro rfl
    exact h

/-- Recovery of an edge from its singleton right-partner fibre. -/
theorem rel_iff_rights_eq_singleton (M : Matching) (i j : Fibre) :
    M.Rel i j ↔ M.rights i = {j} := by
  constructor
  · exact M.rights_eq_singleton_of_rel
  · intro h
    have : j ∈ M.rights i := by simp [h]
    exact (M.mem_rights i j).mp this

/-- Recovery of an edge from its singleton left-partner fibre. -/
theorem rel_iff_lefts_eq_singleton (M : Matching) (i j : Fibre) :
    M.Rel i j ↔ M.lefts j = {i} := by
  constructor
  · exact M.lefts_eq_singleton_of_rel
  · intro h
    have : i ∈ M.lefts j := by simp [h]
    exact (M.mem_lefts i j).mp this

end Matching

end Erdos59
