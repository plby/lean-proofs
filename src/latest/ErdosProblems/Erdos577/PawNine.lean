import ErdosProblems.Erdos577.PawNineWitnesses1
import ErdosProblems.Erdos577.PawNineWitnesses2
import ErdosProblems.Erdos577.PawNineWitnesses3
import ErdosProblems.Erdos577.PawNineTransport

/-! Wang 3.4(b), including the actual universal-replacement hypothesis. -/

namespace Erdos577

open Finset

namespace PawNine

theorem finite_factor (diagonal : Fin 4) (m : Fin 65536) (hd : diagonal ≠ 0)
    (hz : DenseOutside.terminalCount m.val = 1) (ht : DenseOutside.triangleCount m.val = 9)
    (hg : HasGoodRow diagonal m.val) : LocalFactor (PawModel.graph diagonal m.val) univ := by
  fin_cases diagonal
  · exact False.elim (hd rfl)
  · exact D1.finite_factor m hz ht hg
  · exact D2.finite_factor m hz ht hg
  · exact D3.finite_factor m hz ht hg

end PawNine

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Paw.nine_triangle_universal_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hleaf : 1 ≤ degreeIn G p.leaf q.support)
    (htri : 9 ≤ contacts G p.triangle q.support) (hedges : 5 ≤ edgeCount G q.support)
    (hr : ∃ v ∈ p.triangle, ∀ w ∈ q.support, QuadOn G (insert v (q.support.erase w))) :
    LocalFactor G (p.support ∪ q.support) := by
  by_contra hn
  obtain ⟨hleaf1, htri9⟩ := p.nine_triangle_contacts q hd hn hleaf htri
  have hdiag : Unattached.diagonal q ≠ 0 := by
    intro he
    have h := Unattached.oldEdges_diagonal q
    rw [he] at h
    change 4 = edgeCount G q.support at h
    omega
  have hf := PawNine.finite_factor (Unattached.diagonal q) (PawEncoding.encoded p q) hdiag
    (by rw [PawEncoding.terminalCount_encoded]; exact hleaf1)
    (by rw [PawNine.triangleCount_encoded]; exact htri9)
    (PawNine.hasGoodRow_of_universal_replacement p q hd hr)
  have hg := hf.image (PawEncoding.modelCopy p q hd)
  rw [PawEncoding.modelCopy_image] at hg
  exact hn hg

end Erdos577
