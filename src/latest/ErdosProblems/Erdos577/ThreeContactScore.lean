import ErdosProblems.Erdos577.ThreeContactLabels
import ErdosProblems.Erdos577.HighPairLeafExchange
import ErdosProblems.Erdos577.QuadDegrees

/-! Replacing the missed low vertex by a three-contact vertex gains exactly one edge. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma three_contact_replace (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hrow : ∀ j : Fin 4, G.Adj z (q j) ↔ j ≠ 3) (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    QuadOn G (insert z (q.support.erase (q i))) := by
  apply q.quad_replaceAt i z hz
  intro j hij
  apply (hrow j).mpr
  have hbits : ∀ i j : Fin 4, (i = 1 ∨ i = 3) →
      (SimpleGraph.cycleGraph 4).Adj i j → j ≠ 3 := by decide +kernel
  exact hbits i j hi hij

lemma three_contact_replace_score (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hrow : ∀ j : Fin 4, G.Adj z (q j) ↔ j ≠ 3) (hd : ¬G.Adj (q 1) (q 3)) :
    edgeCount G (insert z (q.support.erase (q 3))) = edgeCount G q.support + 1 := by
  have hmask : ∀ j : Fin 4, G.Adj z (q j) ↔ (7 : ℕ).testBit j.val = true := by
    intro j
    rw [hrow j]
    fin_cases j <;> decide
  have h3 : degreeIn G z q.support = 3 := by
    rw [q.degree_eq_mask z 7 hmask]
    decide +kernel
  have hlow : degreeIn G (q 3) q.support = 2 := by
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 2
    rw [if_neg (fun he ↦ hd he.symm)]
  have hu : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have herase := degreeIn_erase_add G z (q 3) hu
  rw [if_neg (fun he ↦ (hrow 3).mp he rfl)] at herase
  have he := edgeCount_replace G (q 3) z hu hz
  omega

end Erdos577.Quadrilateral
