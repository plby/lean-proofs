import Mathlib.Data.Finset.Card

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite bipartite graphs without a four-cycle

We represent a finite bipartite graph by its finite edge set `E : Finset (X × Y)`.
This keeps the counting layer independent of the heavier `SimpleGraph` API.
-/

namespace Erdos796

namespace Bipartite

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- The neighbours in `Y` of a left vertex `x`. -/
def neighbors (E : Finset (X × Y)) (x : X) : Finset Y :=
  (E.filter fun e => e.1 = x).image Prod.snd

@[simp]
theorem mem_neighbors {E : Finset (X × Y)} {x : X} {y : Y} :
    y ∈ neighbors E x ↔ (x, y) ∈ E := by
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨⟨a, b⟩, he, rfl⟩
    rcases Finset.mem_filter.mp he with ⟨hab, ha⟩
    change a = x at ha
    change (x, b) ∈ E
    exact ha ▸ hab
  · intro hxy
    apply Finset.mem_image.mpr
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨hxy, rfl⟩, rfl⟩

/-- The common neighbourhood (and hence codegree support) of two left vertices. -/
def commonNeighbors (E : Finset (X × Y)) (x₁ x₂ : X) : Finset Y :=
  neighbors E x₁ ∩ neighbors E x₂

@[simp]
theorem mem_commonNeighbors {E : Finset (X × Y)} {x₁ x₂ : X} {y : Y} :
    y ∈ commonNeighbors E x₁ x₂ ↔ (x₁, y) ∈ E ∧ (x₂, y) ∈ E := by
  simp [commonNeighbors]

/-- A finite bipartite edge set is `C4Free` if every complete `2 × 2` box is
degenerate in at least one coordinate. -/
def C4Free (E : Finset (X × Y)) : Prop :=
  ∀ ⦃x₁ x₂ : X⦄ ⦃y₁ y₂ : Y⦄,
    (x₁, y₁) ∈ E →
    (x₁, y₂) ∈ E →
    (x₂, y₁) ∈ E →
    (x₂, y₂) ∈ E →
    x₁ = x₂ ∨ y₁ = y₂

/-- In a `C4`-free edge set, two distinct left vertices cannot have two
distinct common neighbours. -/
theorem common_neighbor_unique {E : Finset (X × Y)} (hE : C4Free E)
    {x₁ x₂ : X} (hxx : x₁ ≠ x₂) {y₁ y₂ : Y}
    (hy₁ : y₁ ∈ commonNeighbors E x₁ x₂)
    (hy₂ : y₂ ∈ commonNeighbors E x₁ x₂) : y₁ = y₂ := by
  rw [mem_commonNeighbors] at hy₁ hy₂
  exact (hE hy₁.1 hy₂.1 hy₁.2 hy₂.2).resolve_left hxx

/-- Equivalently, the codegree of two distinct left vertices is at most one. -/
theorem card_commonNeighbors_le_one {E : Finset (X × Y)} (hE : C4Free E)
    {x₁ x₂ : X} (hxx : x₁ ≠ x₂) :
    (commonNeighbors E x₁ x₂).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro y₁ y₂ hy₁ hy₂
  exact common_neighbor_unique hE hxx hy₁ hy₂

omit [DecidableEq X] [DecidableEq Y] in
/-- A dual formulation used in pair counting: a fixed pair of distinct right
vertices has at most one common left vertex. -/
theorem left_vertex_unique {E : Finset (X × Y)} (hE : C4Free E)
    {y₁ y₂ : Y} (hyy : y₁ ≠ y₂) {x₁ x₂ : X}
    (hx₁y₁ : (x₁, y₁) ∈ E) (hx₁y₂ : (x₁, y₂) ∈ E)
    (hx₂y₁ : (x₂, y₁) ∈ E) (hx₂y₂ : (x₂, y₂) ∈ E) : x₁ = x₂ := by
  exact (hE hx₁y₁ hx₁y₂ hx₂y₁ hx₂y₂).resolve_right hyy

/-- The codegree-one condition exactly characterizes finite bipartite
`C4`-freeness. -/
theorem c4Free_iff_card_commonNeighbors_le_one {E : Finset (X × Y)} :
    C4Free E ↔
      ∀ ⦃x₁ x₂ : X⦄, x₁ ≠ x₂ → (commonNeighbors E x₁ x₂).card ≤ 1 := by
  constructor
  · intro hE x₁ x₂ hxx
    exact card_commonNeighbors_le_one hE hxx
  · intro hcodeg x₁ x₂ y₁ y₂ hx₁y₁ hx₁y₂ hx₂y₁ hx₂y₂
    by_cases hxx : x₁ = x₂
    · exact Or.inl hxx
    · right
      have hc := hcodeg hxx
      rw [Finset.card_le_one_iff] at hc
      apply hc
      · exact mem_commonNeighbors.mpr ⟨hx₁y₁, hx₂y₁⟩
      · exact mem_commonNeighbors.mpr ⟨hx₁y₂, hx₂y₂⟩

end Bipartite

end Erdos796
