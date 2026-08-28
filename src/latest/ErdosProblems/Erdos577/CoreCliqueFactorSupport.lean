import ErdosProblems.Erdos577.CompleteCoreExtension
import ErdosProblems.Erdos577.HighPairLeafExchange

/-! Support and replacement identities for the two complete-core equality factors. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Quadrilateral.support_four (q : Quadrilateral G) :
    q.support = {q 0, q 1, q 2, q 3} := by
  have he : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Quadrilateral.support, he]
  simp

lemma Quadrilateral.replace_low_of_highs (q : Quadrilateral G) (z : V)
    (hz : z ∉ q.support) (h0 : G.Adj z (q 0)) (h2 : G.Adj z (q 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : QuadOn G (insert z (q.support.erase (q i))) := by
  apply q.quad_replaceAt i z hz
  intro j hij
  have hindices : ∀ i j : Fin 4, (i = 1 ∨ i = 3) →
      (SimpleGraph.cycleGraph 4).Adj i j → j = 0 ∨ j = 2 := by decide +kernel
  rcases hindices i j hi hij with rfl | rfl
  · exact h0
  · exact h2

lemma core_replacement_cover (center x low h z : V) {s : Finset V} (hlow : low ∈ s) :
    ({center, x, low, h} : Finset V) ∪ insert z (s.erase low) =
      insert x ({center, h, z} ∪ s) := by
  ext v
  have hv : v = low → v ∈ s := fun he ↦ he ▸ hlow
  simp only [mem_union, mem_insert, mem_singleton, mem_erase]
  tauto

end Erdos577
