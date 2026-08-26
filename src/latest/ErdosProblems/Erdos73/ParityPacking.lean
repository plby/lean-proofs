import ErdosProblems.Erdos73.ParityPendantOddProjection
import ErdosProblems.Erdos73.ParityPendantLift
import ErdosProblems.Erdos73.OddTerminalPaths

/-! Packing and covering for paths with nonzero Boolean parity defect. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def HasParityBreakingPathPacking (G : SimpleGraph V) (c : V → Bool) (T : Finset V) (k : ℕ) : Prop :=
  ∃ P : Fin k → GraphPath G, (∀ i, IsParityBreakingPath c T (P i)) ∧
    Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet)

def HitsParityBreakingPaths (G : SimpleGraph V) (c : V → Bool) (T X : Finset V) : Prop :=
  ∀ P : GraphPath G, IsParityBreakingPath c T P → ¬ Disjoint P.vertexSet X

theorem parityBreaking_paths_packing_or_covering (G : SimpleGraph V) (c : V → Bool)
    (T : Finset V) (k : ℕ) :
    HasParityBreakingPathPacking G c T k ∨
      ∃ X : Finset V, X.card ≤ 2 * k - 2 ∧ HitsParityBreakingPaths G c T X := by
  rcases odd_terminal_paths_packing_or_covering (parityPendantGraph G T c)
      (parityPendantTerminals T c) k with ⟨P, hP, hdis⟩ | ⟨Z, hZcard, hZ⟩
  · have hex (i : Fin k) := exists_parityBreaking_path_of_oddPendantPath (P i) (hP i)
    choose Q hQ hsub using hex
    refine Or.inl ⟨Q, hQ, ?_⟩
    have hne (i : Fin k) : (P i).source ≠ (P i).target := by
      intro he
      have hnil := (P i).isPath.nil_iff_eq.mpr he
      have hz := hnil.length_eq_zero
      have ho := (hP i).odd_length
      rw [Nat.odd_iff, hz] at ho
      contradiction
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨x, hx, hxv⟩ := mem_image.mp (hsub i hvi)
    obtain ⟨y, hy, hyv⟩ := mem_image.mp (hsub j hvj)
    have hx' := parityPendant_projection_closed (P i) (hne i) hx
    have hy' := parityPendant_projection_closed (P j) (hne j) hy
    rw [hxv] at hx'
    rw [hyv] at hy'
    exact Finset.disjoint_left.mp (hdis hij) hx' hy'
  · refine Or.inr ⟨Z.image pendantProjection, (card_image_le).trans hZcard, ?_⟩
    intro P hP hdis
    obtain ⟨D, hD, hproj⟩ := exists_oddPendantPath_of_parityBreakingPath P hP
    apply hZ D hD
    apply Finset.disjoint_left.mpr
    intro x hxD hxZ
    exact Finset.disjoint_left.mp hdis
      (hproj (mem_image.mpr ⟨x, hxD, rfl⟩)) (mem_image.mpr ⟨x, hxZ, rfl⟩)

end
end Erdos73
