import ErdosProblems.Erdos577.ReplacementRowTransfer
import ErdosProblems.Erdos577.TerminalReplacements
import ErdosProblems.Erdos577.LocalPathPartition

/-! A large row disjoint from a nonempty leaf row yields a common insertion or universality. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma common_or_universal_of_three_row {s : Finset V} (hs : QuadOn G s) (x y z : V)
    (hy : y ∉ s) (hz : z ∉ s) (hx : 0 < degreeIn G x s)
    (hdis : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj y u)) (hthree : 3 ≤ degreeIn G y s)
    (hrep : ∀ u ∈ s, QuadOn G (insert z (s.erase u))) :
    CommonReplacement G x z y s ∨ ∀ u ∈ s, QuadOn G (insert y (s.erase u)) := by
  obtain ⟨d, hd⟩ := card_pos.mp hx
  obtain ⟨hds, hxd⟩ := mem_filter.mp hd
  have hdy : ¬G.Adj y d := fun he ↦ hdis d hds ⟨hxd, he⟩
  have he := degreeIn_erase_add G y d hds
  rw [if_neg hdy] at he
  have hcard : (s.erase d).card = 3 := by rw [card_erase_of_mem hds, hs.card]
  have hbound := degreeIn_le_card G y (s.erase d)
  have hexact : degreeIn G y (s.erase d) = 3 := by omega
  have hfull : ∀ u ∈ s.erase d, G.Adj y u :=
    (degreeIn_eq_card_iff y (s.erase d)).mp (hexact.trans hcard.symm)
  by_cases hzd : G.Adj z d
  · exact Or.inl ⟨d, hds, hxd, hzd, hs.replace_of_three_after_erase hy hds hexact⟩
  · apply Or.inr
    apply universal_replace_of_row_inclusion hz hy _ hrep
    intro u hu hzu
    exact hfull u (mem_erase.mpr ⟨fun heu ↦ hzd (heu ▸ hzu), hu⟩)

end Erdos577
