import ErdosProblems.Erdos547.TwoAttachmentSeparator
import ErdosProblems.Erdos547.ParityAttachments

/-!
# A small separator with equally coloured attachment vertices
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_parity_separator {U : Type*} [Fintype U] (T : SimpleGraph U)
    [DecidableRel T.Adj] (hT : T.IsTree) (r : U) (q : ℕ) (hq : 1 ≤ q)
    (col : T.Coloring (Fin 2)) :
    ∃ Z H : Finset U, r ∈ Z ∧ Z ⊆ H ∧ (T.induce (H : Set U)).Connected ∧
      q * Z.card ≤ 6 * (Fintype.card U + q) ∧
      (∀ u ∈ H, u ∉ Z → degreeIn T H u = 2) ∧
      (∀ u ∈ Z, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z) ∧
      ∀ C : Finset U, Disjoint C Z → (T.induce (C : Set U)).Connected →
        C.card ≤ 2 * q - 1 ∧ (Z.filter (fun v ↦ 0 < degreeIn T C v)).card ≤ 2 ∧
        ∀ u ∈ Z, ∀ v ∈ Z, 0 < degreeIn T C u → 0 < degreeIn T C v → col u = col v := by
  classical
  obtain ⟨S, H, hrS, hSH, hH, hScount, hdeg, hsmall⟩ :=
    exists_two_attachment_separator T hT r q hq
  obtain ⟨Z, hSZ, hZH, hZcount, hZdeg, hclosed⟩ :=
    exists_one_colour_closed_seed_extension T ⟨hH, hT.isAcyclic.induce _⟩ hSH hdeg col
  refine ⟨Z, H, hSZ hrS, hZH, hH, ?_, hZdeg, hclosed, ?_⟩
  · have hh := Nat.mul_le_mul_left q hZcount
    nlinarith only [hh, hScount]
  · intro C hCZ hC
    refine ⟨(hsmall C (hCZ.mono_right hSZ) hC).1,
      card_cut_neighbours_le_two T hT.isAcyclic C H Z hC hH hZH hCZ
        (fun u hu hn ↦ (hZdeg u hu hn).le), ?_⟩
    intro u hu v hv hdu hdv
    exact cut_attachment_colours_equal T hT.isAcyclic col C H Z hC hH hZH hCZ hclosed
      hu hv hdu hdv

end Erdos547

#print axioms Erdos547.exists_parity_separator
