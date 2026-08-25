/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-
Released under the Apache License 2.0.
These region lemmas adapt the Jordan curve formalization already included
in this repository.
-/

/-
Informal proof: Ryuji Maehara, "The Jordan curve theorem via the Brouwer
fixed point theorem", American Mathematical Monthly 91 (1984), 641–643.
Original formalization: rkirov/jordan_pick, commit
b141748187099368d1b564de5fc6601026255378, vendored in
Wikipedia.JordanCurveTheorem.Core.
-/

import Wikipedia.JordanCurveTheorem.Core

/-!
# The inside and outside of a Jordan curve

For an arbitrary planar set, `inside` and `outside` collect the bounded and
unbounded components of its complement. For the image of a continuous injection
of the circle, each is a single nonempty open path connected component, and both
have the curve as their frontier.

The proof uses the existing Maehara argument and its proved planar Brouwer fixed
point theorem; no geometric theorem is left as a hypothesis.
-/

namespace JordanCurveTheorem

open Bornology Function Metric Set

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The unit circle in the Euclidean plane. -/
abbrev UnitCircle := sphere (0 : Plane) 1

/-- Points in bounded connected components of the complement of `J`. -/
def inside (J : Set Plane) : Set Plane :=
  {x | x ∈ Jᶜ ∧ IsBounded (connectedComponentIn Jᶜ x)}

/-- Points in unbounded connected components of the complement of `J`. -/
def outside (J : Set Plane) : Set Plane :=
  {x | x ∈ Jᶜ ∧ ¬ IsBounded (connectedComponentIn Jᶜ x)}

variable {J : Set Plane} {x : Plane}

theorem inside_subset_compl : inside J ⊆ Jᶜ := fun _ hx => hx.1

theorem outside_subset_compl : outside J ⊆ Jᶜ := fun _ hx => hx.1

/-- The bounded and unbounded parts partition the complement. -/
theorem inside_union_outside (J : Set Plane) : inside J ∪ outside J = Jᶜ := by
  ext x
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    by_cases hb : IsBounded (connectedComponentIn Jᶜ x)
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr ⟨hx, hb⟩

theorem disjoint_inside_outside (J : Set Plane) : Disjoint (inside J) (outside J) := by
  rw [Set.disjoint_left]
  exact fun _ hx hy => hy.2 hx.2

theorem connectedComponentIn_subset_inside (hx : x ∈ inside J) :
    connectedComponentIn Jᶜ x ⊆ inside J := by
  intro y hy
  refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hx.2

theorem connectedComponentIn_subset_outside (hx : x ∈ outside J) :
    connectedComponentIn Jᶜ x ⊆ outside J := by
  intro y hy
  refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hx.2

variable {r : UnitCircle → Plane}

theorem inside_nonempty (hcont : Continuous r) (hinj : Injective r) :
    (inside (range r)).Nonempty := by
  obtain ⟨x, hx, hb⟩ :=
    JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT hcont hinj
  exact ⟨x, hx, hb⟩

theorem outside_nonempty (hcont : Continuous r) : (outside (range r)).Nonempty := by
  obtain ⟨x, hx, hb⟩ := JordanCurve.exists_unbounded_component r hcont
  exact ⟨x, hx, hb⟩

theorem isOpen_inside (hcont : Continuous r) : IsOpen (inside (range r)) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨connectedComponentIn (range r)ᶜ x, connectedComponentIn_subset_inside hx,
    JordanCurve.isOpen_component r hcont x, mem_connectedComponentIn hx.1⟩

theorem isOpen_outside (hcont : Continuous r) : IsOpen (outside (range r)) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨connectedComponentIn (range r)ᶜ x, connectedComponentIn_subset_outside hx,
    JordanCurve.isOpen_component r hcont x, mem_connectedComponentIn hx.1⟩

/-- Every point of the inside has the whole inside as its component. -/
theorem connectedComponentIn_eq_inside (hcont : Continuous r) (hinj : Injective r)
    (hx : x ∈ inside (range r)) :
    connectedComponentIn (range r)ᶜ x = inside (range r) := by
  refine (connectedComponentIn_subset_inside hx).antisymm ?_
  intro y hy
  have heq := JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT
    hcont hinj y hy.1 x hx.1 hy.2 hx.2
  rw [← heq]
  exact mem_connectedComponentIn hy.1

/-- Every point of the outside has the whole outside as its component. -/
theorem connectedComponentIn_eq_outside (hcont : Continuous r)
    (hx : x ∈ outside (range r)) :
    connectedComponentIn (range r)ᶜ x = outside (range r) := by
  refine (connectedComponentIn_subset_outside hx).antisymm ?_
  intro y hy
  have heq := JordanCurve.unbounded_component_unique r hcont hy.2 hx.2
  rw [← heq]
  exact mem_connectedComponentIn hy.1

theorem isPathConnected_inside (hcont : Continuous r) (hinj : Injective r) :
    IsPathConnected (inside (range r)) := by
  obtain ⟨x, hx⟩ := inside_nonempty hcont hinj
  rw [← connectedComponentIn_eq_inside hcont hinj hx]
  exact JordanCurve.isPathConnected_component r hcont hx.1

theorem isPathConnected_outside (hcont : Continuous r) :
    IsPathConnected (outside (range r)) := by
  obtain ⟨x, hx⟩ := outside_nonempty hcont
  rw [← connectedComponentIn_eq_outside hcont hx]
  exact JordanCurve.isPathConnected_component r hcont hx.1

theorem isBounded_inside (hcont : Continuous r) (hinj : Injective r) :
    IsBounded (inside (range r)) := by
  obtain ⟨x, hx⟩ := inside_nonempty hcont hinj
  rw [← connectedComponentIn_eq_inside hcont hinj hx]
  exact hx.2

theorem not_isBounded_outside (hcont : Continuous r) :
    ¬ IsBounded (outside (range r)) := by
  obtain ⟨x, hx⟩ := outside_nonempty hcont
  rw [← connectedComponentIn_eq_outside hcont hx]
  exact hx.2

theorem frontier_inside (hcont : Continuous r) (hinj : Injective r) :
    frontier (inside (range r)) = range r := by
  obtain ⟨x, hx⟩ := inside_nonempty hcont hinj
  obtain ⟨y, hy⟩ := outside_nonempty hcont
  rw [← connectedComponentIn_eq_inside hcont hinj hx]
  refine JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hcont hinj
    hx.1 ⟨y, hy.1, ?_⟩
  intro heq
  exact hy.2 (heq.symm ▸ hx.2)

theorem frontier_outside (hcont : Continuous r) (hinj : Injective r) :
    frontier (outside (range r)) = range r := by
  obtain ⟨x, hx⟩ := outside_nonempty hcont
  obtain ⟨y, hy⟩ := inside_nonempty hcont hinj
  rw [← connectedComponentIn_eq_outside hcont hx]
  refine JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hcont hinj
    hx.1 ⟨y, hy.1, ?_⟩
  intro heq
  exact hx.2 (heq ▸ hy.2)

/-- No point of the complement belongs to a third component. -/
theorem connectedComponentIn_eq_inside_or_outside (hcont : Continuous r) (hinj : Injective r)
    (hx : x ∈ (range r)ᶜ) :
    connectedComponentIn (range r)ᶜ x = inside (range r) ∨
      connectedComponentIn (range r)ᶜ x = outside (range r) := by
  by_cases hb : IsBounded (connectedComponentIn (range r)ᶜ x)
  · exact Or.inl (connectedComponentIn_eq_inside hcont hinj ⟨hx, hb⟩)
  · exact Or.inr (connectedComponentIn_eq_outside hcont ⟨hx, hb⟩)

end JordanCurveTheorem
