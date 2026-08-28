import ErdosProblems.Erdos577.PawModel
import ErdosProblems.Erdos577.DenseOutsideModel
import ErdosProblems.Erdos577.PathMasks

/-! The four possible cross-edge patterns in Wang's eleven-contact paw lemma. -/

namespace Erdos577.PawEleven

def exceptional (m : ℕ) : Bool := [22007, 22013, 43771, 43774].contains m

def rowPattern (i j : Fin 4) : Bool :=
  decide (if i = 0 then j ≠ 3 else if i = 1 then True else j = 0 ∨ j = 2)

lemma exceptional_rows {m : ℕ} (h : exceptional m = true) :
    ∃ r : Fin 4, ∀ i j : Fin 4, m.testBit (4 * i.val + (j + r).val) = rowPattern i j := by
  have hm : m ∈ ([22007, 22013, 43771, 43774] : List ℕ) := List.contains_iff_mem.mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨1, by decide +kernel⟩

end Erdos577.PawEleven
