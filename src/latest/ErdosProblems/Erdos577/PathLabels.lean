import ErdosProblems.Erdos577.MatchingData
import Mathlib.Data.Fin.Rev

/-! Reversing an actual four-vertex path preserves its support. -/

namespace Erdos577.FourPath

open Finset

variable {V : Type*} {G : SimpleGraph V}

def reverse (p : FourPath G) : FourPath G where
  vertices := Fin.revPerm.toEmbedding.trans p.vertices
  adjacent i := by
    fin_cases i
    · exact (p.adjacent 2).symm
    · exact (p.adjacent 1).symm
    · exact (p.adjacent 0).symm

@[simp] lemma reverse_apply (p : FourPath G) (i : Fin 4) :
    p.reverse.vertices i = p.vertices i.rev := rfl

lemma reverse_support [DecidableEq V] (p : FourPath G) : p.reverse.support = p.support := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨i.rev, mem_univ _, rfl⟩
  · simp only [card_support, le_refl]

end Erdos577.FourPath
