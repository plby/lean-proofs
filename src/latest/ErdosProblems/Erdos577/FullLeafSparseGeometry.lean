import ErdosProblems.Erdos577.FullLeafHeavyTypes
import ErdosProblems.Erdos577.PawClique

/-! The ten-contact triangle bound and the nonexceptional sparse-leaf paw factor. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma triangle_contacts_of_eighteen {z t j : Finset V} (ht : t ⊆ z)
    (hz5 : z.card = 5) (ht3 : t.card = 3) (hj4 : j.card = 4)
    (hheavy : 18 ≤ contacts G z j) : 10 ≤ contacts G t j := by
  classical
  have hrestCard : (z \ t).card = 2 := by rw [card_sdiff_of_subset ht, hz5, ht3]
  have hrest : contacts G (z \ t) j ≤ 8 := by
    calc
      contacts G (z \ t) j ≤ ∑ _ ∈ z \ t, (4 : ℕ) :=
        sum_le_sum fun v _ ↦ (degreeIn_le_card G v j).trans_eq hj4
      _ = 8 := by simp only [sum_const, smul_eq_mul, hrestCard]
  have hsum := contacts_union_left G (show Disjoint t (z \ t) from disjoint_sdiff_self_right) j
  rw [union_sdiff_of_subset ht] at hsum
  omega

theorem paw_factor_of_one_leaf_eleven (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hleaf : degreeIn G p.leaf q.support = 1)
    (htriangle : 10 ≤ contacts G p.triangle q.support) :
    LocalFactor G (p.support ∪ q.support) := by
  have hcross : 11 ≤ contacts G p.support q.support := by
    rw [p.contacts_support, hleaf]
    omega
  rcases p.eleven_contacts q hd hleaf.ge hcross with hf | ⟨q', hq', hpattern⟩
  · exact hf
  · have hrow := hpattern.degree 0
    change degreeIn G p.leaf q'.support = 3 at hrow
    rw [hq', hleaf] at hrow
    omega

end Erdos577.FullLeafSparse
