import ErdosProblems.Erdos577.RowSaturation

/-! An included finite row is exact when it already exhausts the total degree. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.row_saturated_of_included (q : Quadrilateral G) (z : V) (mask : ℕ)
    (hsub : ∀ j : Fin 4, mask.testBit j.val = true → G.Adj z (q j))
    (hcard : degreeIn G z q.support ≤ ∑ j : Fin 4, (mask.testBit j.val).toNat) :
    ∀ j : Fin 4, G.Adj z (q j) ↔ mask.testBit j.val = true := by
  let s := univ.filter (fun j : Fin 4 ↦ G.Adj z (q j))
  let t := univ.filter (fun j : Fin 4 ↦ mask.testBit j.val = true)
  have hs : s.card = degreeIn G z q.support := by
    rw [Quadrilateral.support, degreeIn_image G z univ q q.injective]
    simp only [s, card_eq_sum_ones, sum_filter]
  have ht : t.card = ∑ j : Fin 4, (mask.testBit j.val).toNat := by
    simp only [t, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro j _
    cases mask.testBit j.val <;> rfl
  have he : t = s := eq_of_subset_of_card_le (by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _, hsub j (mem_filter.mp hj).2⟩) (by
      rw [hs, ht]
      exact hcard)
  intro j
  have hh : j ∈ s ↔ j ∈ t := he ▸ Iff.rfl
  simpa only [s, t, mem_filter, mem_univ, true_and] using hh

end Erdos577
