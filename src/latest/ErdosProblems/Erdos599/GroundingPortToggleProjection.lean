/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPortToggleBoundary

/-!
# Projecting a matching toggle without losing signed boundary information

Removing diagonal pairs from a partial matching cancels one incoming and
one outgoing incidence simultaneously. Thus the signed boundary remains
unchanged even if some traversed forward steps are identity pairs.
-/

namespace Erdos599.GroundingPortToggle

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V : Type u} {G : DWeb V} {M : V → V → Prop}

def nonDiagonal (M : V → V → Prop) : Set (V × V) := {e | M e.1 e.2 ∧ e.1 ≠ e.2}

theorem nonDiagonal_biUnique (hM : Relator.BiUnique M) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ nonDiagonal M) :=
  ⟨fun _ _ _ h h' ↦ hM.1 h.1 h'.1, fun _ _ _ h h' ↦ hM.2 h.1 h'.1⟩

/-- A present diagonal is the unique pair at both ports; deleting it
therefore changes both incidence indicators by the same amount. -/
theorem nonDiagonal_edgeBalance (hM : Relator.BiUnique M) (x : V) :
    edgeBalance (nonDiagonal M) x = edgeBalance {e : V × V | M e.1 e.2} x := by
  classical
  by_cases hxx : M x x
  · have hout : ¬ HasOutgoing (nonDiagonal M) x := by
      rintro ⟨y, hxy, hne⟩
      exact hne (hM.2 hxx hxy)
    have hin : ¬ HasIncoming (nonDiagonal M) x := by
      rintro ⟨y, hyx, hne⟩
      exact hne (hM.1 hyx hxx)
    have holdOut : HasOutgoing {e : V × V | M e.1 e.2} x := ⟨x, hxx⟩
    have holdIn : HasIncoming {e : V × V | M e.1 e.2} x := ⟨x, hxx⟩
    simp only [edgeBalance, propInt, hout, hin, holdOut, holdIn, if_false, if_true, sub_self]
  · have hout : HasOutgoing (nonDiagonal M) x ↔ ∃ y, M x y := by
      constructor
      · rintro ⟨y, hy, _⟩
        exact ⟨y, hy⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, hy, ?_⟩
        intro h
        have hxy : x = y := h
        exact hxx (hxy.symm ▸ hy)
    have hin : HasIncoming (nonDiagonal M) x ↔ ∃ y, M y x := by
      constructor
      · rintro ⟨y, hy, _⟩
        exact ⟨y, hy⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, hy, ?_⟩
        intro h
        have hyx : y = x := h
        exact hxx (hyx ▸ hy)
    change propInt (HasOutgoing (nonDiagonal M) x) -
      propInt (HasIncoming (nonDiagonal M) x) =
        propInt (∃ y, M x y) - propInt (∃ y, M y x)
    rw [hout, hin]

namespace AugmentingPath

variable (D : AugmentingPath G M)

def projectedEdges : Set (V × V) := nonDiagonal D.toggled

def insertedEdges : Set (V × V) := {e | D.forward e.1 e.2 ∧ e.1 ≠ e.2}

theorem insertedEdges_finite : D.insertedEdges.Finite :=
  D.forward_finite.subset (fun _ he ↦ he.1)

theorem projectedEdges_biUnique (hM : Relator.BiUnique M) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ D.projectedEdges) :=
  nonDiagonal_biUnique (D.toggled_biUnique hM)

theorem projectedEdges_subset : D.projectedEdges ⊆ nonDiagonal M ∪ D.insertedEdges := by
  rintro e ⟨he | he, hne⟩
  · exact Or.inl ⟨he.1, hne⟩
  · exact Or.inr ⟨he, hne⟩

theorem projectedEdges_subset_adj
    (hOld : ∀ {x y}, M x y → G.graph.Adj x y ∨ x = y) :
    D.projectedEdges ⊆ {e | G.graph.Adj e.1 e.2} := by
  rintro e ⟨he | he, hne⟩
  · exact (hOld he.1).resolve_right hne
  · exact (D.forward_adj_or_eq he).resolve_right hne

/-- The same exact balance law holds for actual nondiagonal original edges. -/
theorem projectedEdges_edgeBalance (hM : Relator.BiUnique M) (x : V) :
    edgeBalance D.projectedEdges x = edgeBalance (nonDiagonal M) x +
      propInt (x = D.first) - propInt (x = D.last) := by
  rw [projectedEdges, nonDiagonal_edgeBalance (D.toggled_biUnique hM),
    D.toggled_edgeBalance, nonDiagonal_edgeBalance hM]

/-- Apart from the free sending endpoint, every new positive boundary
vertex was already a positive boundary vertex of the old projected relation. -/
theorem projectedEdges_positive_old_or_first (hM : Relator.BiUnique M) {x : V}
    (hx : edgeBalance D.projectedEdges x = 1) :
    edgeBalance (nonDiagonal M) x = 1 ∨ x = D.first := by
  classical
  by_cases hfirst : x = D.first
  · exact Or.inr hfirst
  · have hbal := D.projectedEdges_edgeBalance hM x
    have hle : edgeBalance (nonDiagonal M) x ≤ 1 := by
      simp only [edgeBalance, propInt]
      split_ifs <;> norm_num
    by_cases hlast : x = D.last
    · simp only [hx, propInt, if_neg hfirst, if_pos hlast, add_zero] at hbal
      omega
    · simp only [hx, propInt, if_neg hfirst, if_neg hlast, add_zero, sub_zero] at hbal
      exact Or.inl hbal.symm

#print axioms insertedEdges_finite
#print axioms projectedEdges_biUnique
#print axioms projectedEdges_edgeBalance
#print axioms projectedEdges_positive_old_or_first

end AugmentingPath

#print axioms nonDiagonal_edgeBalance

end Erdos599.GroundingPortToggle
