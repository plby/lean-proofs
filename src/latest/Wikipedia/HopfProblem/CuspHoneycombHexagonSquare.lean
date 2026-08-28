import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# The common unit-square gluing relation for the hexagonal component

The same relation is used by the actual oriented toric charts and by the
explicit piecewise-linear hexagon tiles.
-/

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

abbrev Plane := Fin 2 → ℝ

/-- The literal real unit square. -/
abbrev Square := {p : Plane // ∀ i, p i ∈ Set.Icc (0 : ℝ) 1}

theorem square_isCompact : IsCompact {p : Plane | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} :=
  isCompact_pi_infinite (fun _ => isCompact_Icc)

instance square_compactSpace : CompactSpace Square :=
  isCompact_iff_compactSpace.mp square_isCompact

/-- Six squares meet along their consecutive upper edges, and all their
upper-right corners represent the common center. -/
def SquareRel (i j : Fin 6) (p q : Square) : Prop :=
  (i = j ∧ p = q) ∨
  (j = i + 1 ∧ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1) ∨
  (i = j + 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = p.1 0) ∨
  ((∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1))

theorem square_eq_of_all_one (p q : Square)
    (hp : ∀ k, p.1 k = 1) (hq : ∀ k, q.1 k = 1) : p = q := by
  apply Subtype.ext
  funext k
  exact (hp k).trans (hq k).symm

@[simp] theorem squareRel_self (i : Fin 6) (p q : Square) :
    SquareRel i i p q ↔ p = q := by
  have hne : i ≠ i + 1 := (show ∀ i : Fin 6, i ≠ i + 1 by decide) i
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨hp, hq⟩)
    · exact h
    · exact (hne h).elim
    · exact (hne h).elim
    · exact square_eq_of_all_one p q hp hq
  · exact fun h => Or.inl ⟨rfl, h⟩

@[simp] theorem squareRel_next (i : Fin 6) (p q : Square) :
    SquareRel i (i + 1) p q ↔ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1 := by
  have hne : i ≠ i + 1 := (show ∀ i : Fin 6, i ≠ i + 1 by decide) i
  have hne₂ : i ≠ (i + 1) + 1 := (show ∀ i : Fin 6, i ≠ (i + 1) + 1 by decide) i
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨hp, hq⟩)
    · exact (hne h).elim
    · exact h
    · exact (hne₂ h).elim
    · exact ⟨hp 0, hq 1, (hq 0).trans (hp 1).symm⟩
  · exact fun h => Or.inr (Or.inl ⟨rfl, h⟩)

@[simp] theorem squareRel_prev (i : Fin 6) (p q : Square) :
    SquareRel i (i + 5) p q ↔ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = p.1 0 := by
  have hne : i ≠ i + 5 := (show ∀ i : Fin 6, i ≠ i + 5 by decide) i
  have hnext : i + 5 ≠ i + 1 := (show ∀ i : Fin 6, i + 5 ≠ i + 1 by decide) i
  have hprev : i = (i + 5) + 1 := (show ∀ i : Fin 6, i = (i + 5) + 1 by decide) i
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨hp, hq⟩)
    · exact (hne h).elim
    · exact (hnext h).elim
    · exact h
    · exact ⟨hp 1, hq 0, (hq 1).trans (hp 0).symm⟩
  · exact fun h => Or.inr (Or.inr (Or.inl ⟨hprev, h⟩))

theorem squareRel_nonadjacent (i j : Fin 6) (p q : Square)
    (hij : i ≠ j) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    SquareRel i j p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) := by
  simp only [SquareRel, hij, hnext, hprev, false_and, false_or]

@[simp] theorem squareRel_add_two (i : Fin 6) (p q : Square) :
    SquareRel i (i + 2) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 2) p q
    ((show ∀ i : Fin 6, i ≠ i + 2 by decide) i)
    ((show ∀ i : Fin 6, i + 2 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 2) + 1 by decide) i)

@[simp] theorem squareRel_add_three (i : Fin 6) (p q : Square) :
    SquareRel i (i + 3) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 3) p q
    ((show ∀ i : Fin 6, i ≠ i + 3 by decide) i)
    ((show ∀ i : Fin 6, i + 3 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 3) + 1 by decide) i)

@[simp] theorem squareRel_add_four (i : Fin 6) (p q : Square) :
    SquareRel i (i + 4) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 4) p q
    ((show ∀ i : Fin 6, i ≠ i + 4 by decide) i)
    ((show ∀ i : Fin 6, i + 4 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 4) + 1 by decide) i)

end Wikipedia.HopfProblem.CuspHoneycombHexagon
