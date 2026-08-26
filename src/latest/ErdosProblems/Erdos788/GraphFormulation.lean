import ErdosProblems.Erdos788.Definitions
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact graph formulation

This file proves the admissibility/independence correspondence and the exact
finite min--max identity from Section 2 of the paper.
-/

namespace Erdos788

open Finset

/-- The finite vertex type corresponding exactly to `I n`. -/
abbrev Vertex (n : ℕ) := {x : ℕ // x ∈ I n}

/-- Join two distinct elements of `I n` exactly when their sum belongs to
the palette `B`. -/
def paletteGraph (n : ℕ) (B : Finset ℕ) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel fun x y ↦ x.1 + y.1 ∈ B

@[simp]
theorem paletteGraph_adj {n : ℕ} {B : Finset ℕ} {x y : Vertex n} :
    (paletteGraph n B).Adj x y ↔ x ≠ y ∧ x.1 + y.1 ∈ B := by
  simp [paletteGraph, add_comm]

/-- Forget the proofs that the vertices lie in `I n`. -/
def forgetVertices {n : ℕ} (C : Finset (Vertex n)) : Finset ℕ :=
  C.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem card_forgetVertices {n : ℕ} (C : Finset (Vertex n)) :
    (forgetVertices C).card = C.card := by
  simp [forgetVertices]

/-- Lift a finset contained in `I n` to the finite vertex type. -/
def liftVertices {n : ℕ} (C : Finset ℕ) (hC : C ⊆ I n) :
    Finset (Vertex n) :=
  C.attach.map
    { toFun := fun x ↦ ⟨x.1, hC x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : Vertex n ↦ z.1) h }

@[simp]
theorem card_liftVertices {n : ℕ} (C : Finset ℕ) (hC : C ⊆ I n) :
    (liftVertices C hC).card = C.card := by
  simp [liftVertices]

/-- An independent vertex finset gives an admissible integer finset. -/
theorem admissible_forgetVertices {n : ℕ} {B : Finset ℕ}
    {D : Finset (Vertex n)}
    (hD : (paletteGraph n B).IsIndepSet (D : Set (Vertex n))) :
    Admissible n B (forgetVertices D) := by
  classical
  constructor
  · intro x hx
    rw [forgetVertices, mem_map] at hx
    obtain ⟨v, _hv, rfl⟩ := hx
    exact v.2
  · intro x hx y hy hxy hsum
    rw [forgetVertices, mem_map] at hx hy
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    have hvw : v ≠ w := fun e ↦ hxy (congrArg Subtype.val e)
    exact hD hv hw hvw (paletteGraph_adj.mpr ⟨hvw, hsum⟩)

/-- An admissible integer finset gives an independent vertex finset. -/
theorem isIndepSet_liftVertices {n : ℕ} {B C : Finset ℕ}
    (hC : Admissible n B C) :
    (paletteGraph n B).IsIndepSet
      (liftVertices C hC.1 : Set (Vertex n)) := by
  classical
  intro v hv w hw hvw hadj
  change v ∈ liftVertices C hC.1 at hv
  change w ∈ liftVertices C hC.1 at hw
  rw [liftVertices, mem_map] at hv hw
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hw
  have hxy : x.1 ≠ y.1 := fun e ↦ hvw (Subtype.ext e)
  exact hC.2 x.2 y.2 hxy (paletteGraph_adj.mp hadj).2

/-- The score attached to one palette in the graph formulation. -/
noncomputable def graphScore (n : ℕ) (B : Finset ℕ) : ℕ :=
  B.card + (paletteGraph n B).indepNum

/-- A threshold has the original universal property exactly when it is at
most every graph score. -/
theorem guarantees_iff_forall_le_graphScore {n t : ℕ} :
    Guarantees n t ↔
      ∀ B : Finset ℕ, B ⊆ J n → t ≤ graphScore n B := by
  constructor
  · intro h B hB
    obtain ⟨C, hC, ht⟩ := h B hB
    have hInd := isIndepSet_liftVertices hC
    have hcard : C.card ≤ (paletteGraph n B).indepNum := by
      rw [← card_liftVertices C hC.1]
      exact hInd.card_le_indepNum
    exact ht.trans (Nat.add_le_add_left hcard B.card)
  · intro h B hB
    obtain ⟨D, hD⟩ := (paletteGraph n B).exists_isNIndepSet_indepNum
    refine ⟨forgetVertices D, admissible_forgetVertices hD.isIndepSet, ?_⟩
    simpa [graphScore, hD.card_eq] using! h B hB

/-- The nonempty finite set of graph scores over all palettes in `J n`. -/
noncomputable def graphScores (n : ℕ) : Finset ℕ :=
  (J n).powerset.image (graphScore n)

theorem graphScores_nonempty (n : ℕ) : (graphScores n).Nonempty := by
  classical
  refine ⟨graphScore n ∅, ?_⟩
  exact mem_image.mpr ⟨∅, by simp, rfl⟩

/-- The right side of the finite min--max formula. -/
noncomputable def minGraphScore (n : ℕ) : ℕ :=
  (graphScores n).min' (graphScores_nonempty n)

theorem minGraphScore_le {n : ℕ} {B : Finset ℕ} (hB : B ⊆ J n) :
    minGraphScore n ≤ graphScore n B := by
  classical
  apply min'_le
  exact mem_image.mpr ⟨B, mem_powerset.mpr hB, rfl⟩

theorem exists_graphScore_eq_minGraphScore (n : ℕ) :
    ∃ B : Finset ℕ, B ⊆ J n ∧ graphScore n B = minGraphScore n := by
  classical
  have hmem := min'_mem (graphScores n) (graphScores_nonempty n)
  change minGraphScore n ∈ (J n).powerset.image (graphScore n) at hmem
  rw [mem_image] at hmem
  obtain ⟨B, hB, hscore⟩ := hmem
  exact ⟨B, mem_powerset.mp hB, hscore⟩

theorem guarantees_iff_le_minGraphScore {n t : ℕ} :
    Guarantees n t ↔ t ≤ minGraphScore n := by
  rw [guarantees_iff_forall_le_graphScore]
  constructor
  · intro h
    obtain ⟨B, hB, hscore⟩ := exists_graphScore_eq_minGraphScore n
    simpa [hscore] using! h B hB
  · intro h B hB
    exact h.trans (minGraphScore_le hB)

/-- Proposition 2.1: the largest natural guarantee is the minimum graph
score over all palettes. -/
theorem fNat_eq_minGraphScore (n : ℕ) : fNat n = minGraphScore n := by
  apply le_antisymm
  · exact guarantees_iff_le_minGraphScore.mp (fNat_guarantees n)
  · exact le_fNat (guarantees_iff_le_minGraphScore.mpr le_rfl)

/-- Integer-valued form of the exact min--max identity. -/
theorem f_eq_minGraphScore (n : ℕ) : f n = (minGraphScore n : ℤ) := by
  simp [f, fNat_eq_minGraphScore]

end Erdos788
