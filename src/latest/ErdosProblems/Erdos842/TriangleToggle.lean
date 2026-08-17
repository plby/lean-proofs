/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos842.CanonicalArcs
import ErdosProblems.Erdos842.Coefficient
import ErdosProblems.Erdos842.SignedCancellation

open scoped symmDiff

/-!
# The canonical triangle toggle

This file gives the concrete canonical interface to the generic directed-triangle lemmas in
`Coefficient`. A survivor has a proper nonempty restriction on every triangle. On every balanced
nonsurvivor, symmetric difference with the three occurrences of the least degenerate triangle is
a fixed-point-free, sign-reversing involution preserving the cancellation domain.
-/

namespace Erdos842.TriangleToggle

open Erdos842.Parity
open Erdos842.Coefficient

/-- Restriction of `S` to the three cyclically oriented occurrences of triangle `t`. -/
def triangleRestriction {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (t : Fin n) : Finset (Fin 3) :=
  (canonicalDirectedTriangle n triangleCoord t).restriction S

@[simp]
theorem mem_triangleRestriction {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (t : Fin n) (j : Fin 3) :
    j ∈ triangleRestriction triangleCoord S t ↔ Sum.inr (t, j) ∈ S := by
  simp [triangleRestriction, canonicalDirectedTriangle]

/-- The restriction at `t` is degenerate when it is empty or full. -/
def IsDegenerateAt {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (t : Fin n) : Prop :=
  triangleRestriction triangleCoord S t = ∅ ∨
    triangleRestriction triangleCoord S t = Finset.univ

/-- A survivor has a nonempty proper restriction on every triangle. -/
def IsSurvivor {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Prop :=
  ∀ t, ¬IsDegenerateAt triangleCoord S t

/-- The set of degenerate triangle indices. -/
noncomputable def degenerateTriangles {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Finset (Fin n) :=
  canonicalDegenerateIndices n triangleCoord S

@[simp]
theorem mem_degenerateTriangles {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (t : Fin n) :
    t ∈ degenerateTriangles triangleCoord S ↔ IsDegenerateAt triangleCoord S t := by
  simp [degenerateTriangles, IsDegenerateAt, triangleRestriction]

theorem survivor_iff_degenerateTriangles_eq_empty {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    IsSurvivor triangleCoord S ↔ degenerateTriangles triangleCoord S = ∅ := by
  simp [IsSurvivor, Finset.eq_empty_iff_forall_notMem]

/-- The least degenerate triangle of a nonsurvivor. -/
noncomputable def leastDegenerateTriangle {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (h : (degenerateTriangles triangleCoord S).Nonempty) : Fin n :=
  (degenerateTriangles triangleCoord S).min' h

theorem leastDegenerateTriangle_mem {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (h : (degenerateTriangles triangleCoord S).Nonempty) :
    IsDegenerateAt triangleCoord S (leastDegenerateTriangle triangleCoord S h) := by
  rw [← mem_degenerateTriangles]
  exact Finset.min'_mem _ _

/-- Toggle the three occurrences of the least degenerate triangle. -/
noncomputable def toggle {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Finset (CanonicalOccurrence n) :=
  toggleFirstDegenerate n triangleCoord S

/-- On a nonsurvivor, `toggle` is visibly symmetric difference with the three occurrences of the
least degenerate triangle. -/
theorem toggle_eq_symmDiff_leastDegenerate {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (h : (degenerateTriangles triangleCoord S).Nonempty) :
    toggle triangleCoord S =
      S ∆ (canonicalDirectedTriangle n triangleCoord
        (leastDegenerateTriangle triangleCoord S h)).arcSet := by
  simpa [toggle, leastDegenerateTriangle, degenerateTriangles,
    DirectedTriangle.toggle] using
      (toggleFirstDegenerate_of_nonempty n triangleCoord S h)

/-- The balanced survivor set left after the triangle cancellation. -/
noncomputable def survivors {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Finset (Finset (CanonicalOccurrence n)) :=
  canonicalSurvivors n triangleCoord

@[simp]
theorem mem_survivors {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    S ∈ survivors triangleCoord ↔
      (canonicalIndexedArcs n triangleCoord).Balanced S ∧
        IsSurvivor triangleCoord S := by
  rw [survivors, mem_canonicalSurvivors]
  exact and_congr_right fun _ ↦ (survivor_iff_degenerateTriangles_eq_empty _ _).symm

theorem survivors_subset_balancedSelections {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    survivors triangleCoord ⊆ balancedSelections (canonicalIndexedArcs n triangleCoord) := by
  intro S hS
  exact (mem_balancedSelections _ _).2 ((mem_survivors triangleCoord S).1 hS).1

/-- Concrete membership preservation on the exact cancellation domain. -/
theorem toggle_mem {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      survivors triangleCoord) :
    toggle triangleCoord S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      survivors triangleCoord := by
  exact toggleFirstDegenerate_mem_complement n triangleCoord S hS

/-- Toggling preserves balancedness on balanced nonsurvivors. -/
theorem toggle_balanced {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      survivors triangleCoord) :
    (canonicalIndexedArcs n triangleCoord).Balanced (toggle triangleCoord S) := by
  exact (mem_balancedSelections _ _).1 (Finset.mem_sdiff.mp (toggle_mem triangleCoord S hS)).1

/-- The least-degenerate-triangle toggle is involutive on balanced nonsurvivors. -/
theorem toggle_involutive {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      survivors triangleCoord) :
    toggle triangleCoord (toggle triangleCoord S) = S := by
  exact toggleFirstDegenerate_involutive n triangleCoord S hS

/-- The toggle has no fixed point on balanced nonsurvivors. -/
theorem toggle_fixedPointFree {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      survivors triangleCoord) :
    toggle triangleCoord S ≠ S := by
  exact toggleFirstDegenerate_ne n triangleCoord S hS

/-- Toggling three occurrences reverses the subset-expansion sign. -/
theorem toggle_negates {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      survivors triangleCoord) :
    selectionSign (toggle triangleCoord S) = -selectionSign S := by
  exact toggleFirstDegenerate_negates n triangleCoord S hS

/-- For each triangle choose the positive boundary endpoint of its survivor chord. -/
noncomputable def survivorChordKey {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Fin n → Fin 3 := fun t ↦
  if h : ∃ j, triangleBoundary (triangleRestriction triangleCoord S t) j = 1 then
    Classical.choose h
  else 0

theorem survivorChordKey_spec {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : IsSurvivor triangleCoord S) (t : Fin n) :
    triangleBoundary (triangleRestriction triangleCoord S t)
      (survivorChordKey triangleCoord S t) = 1 := by
  have hne : triangleRestriction triangleCoord S t ≠ ∅ := by
    intro h
    exact hS t (Or.inl h)
  have hfull : triangleRestriction triangleCoord S t ≠ Finset.univ := by
    intro h
    exact hS t (Or.inr h)
  obtain ⟨p, q, hpq, hp, hq, hrest⟩ :=
    triangleBoundary_nondegenerate (triangleRestriction triangleCoord S t) hne hfull
  have hex : ∃ j, triangleBoundary (triangleRestriction triangleCoord S t) j = 1 :=
    ⟨p, hp⟩
  simp only [survivorChordKey, dif_pos hex]
  exact Classical.choose_spec hex

end Erdos842.TriangleToggle
