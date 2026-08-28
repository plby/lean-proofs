import ErdosProblems.Erdos577.JointFullSelection

/-! The exact diamond degrees and the score-preserving low-vertex replacement. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma FullPattern.local_data {v : Quadrilateral G} {x y z w : V} (h : FullPattern v x y z w) :
    degreeIn G x v.support = 1 ∧ degreeIn G y v.support = 2 ∧
      degreeIn G z v.support = 4 ∧ degreeIn G w v.support = 2 ∧
      edgeCount G v.support = 5 ∧ degreeIn G (v 3) v.support = 2 := by
  have hf1 : ∀ i : Fin 4, i = 0 ↔ (1 : ℕ).testBit i.val = true := by decide +kernel
  have hf6 : ∀ i : Fin 4, i = 1 ∨ i = 2 ↔ (6 : ℕ).testBit i.val = true := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v.degree_eq_mask x 1 (fun i ↦ (h.1 i).trans (hf1 i))]
    decide +kernel
  · rw [v.degree_eq_mask y 6 (fun i ↦ (h.2.1 i).trans (hf6 i))]
    decide +kernel
  · have hh : degreeIn G z v.support = v.support.card :=
      (degreeIn_eq_card_iff (G := G) z v.support).mpr (by
        intro u hu
        obtain ⟨i, rfl⟩ := (v.mem_support u).mp hu
        exact h.2.2.1 i)
    rwa [v.card_support] at hh
  · rw [v.degree_eq_mask w 6 (fun i ↦ (h.2.2.2.1 i).trans (hf6 i))]
    decide +kernel
  · rw [v.edgeCount_eq, if_pos h.2.2.2.2.1, if_neg h.2.2.2.2.2]
  · rw [v.degreeIn_eq]
    change 2 + (if G.Adj (v 3) (v 1) then 1 else 0) = 2
    rw [if_neg (fun hh ↦ h.2.2.2.2.2 hh.symm), add_zero]

lemma FullPattern.last_replacement {v : Quadrilateral G} {x y z w : V}
    (h : FullPattern v x y z w) (hy : y ∉ v.support) :
    QuadOn G (insert y (v.support.erase (v 3))) ∧
      edgeCount G (insert y (v.support.erase (v 3))) = edgeCount G v.support := by
  have hdiag : PawBlock.OnlyFirst (v.rotate 2) :=
    ⟨h.2.2.2.2.1.symm, fun hh ↦ h.2.2.2.2.2 hh.symm⟩
  have hf : ∀ i : Fin 4, i + 2 = 1 ∨ i + 2 = 2 ↔ (9 : ℕ).testBit i.val = true := by
    decide +kernel
  have hrow : ∀ i : Fin 4, G.Adj y (v.rotate 2 i) ↔ (9 : ℕ).testBit i.val = true :=
    fun i ↦ (h.2.1 (i + 2)).trans (hf i)
  have hh := TwoCore.leaf_replacement (v.rotate 2) y
    (by rwa [Quadrilateral.rotate_support]) hdiag hrow
  change QuadOn G (insert y ((v.rotate 2).support.erase (v 3))) ∧
    edgeCount G (insert y ((v.rotate 2).support.erase (v 3))) =
      edgeCount G (v.rotate 2).support at hh
  simpa only [Quadrilateral.rotate_support] using hh

end Erdos577.JointFinal
