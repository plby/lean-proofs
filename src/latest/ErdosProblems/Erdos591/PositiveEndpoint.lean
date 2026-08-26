import ErdosProblems.Erdos591.GamePositive
import ErdosProblems.Erdos591.ExactCanonicalSequence

/-! # Schipperus's exact positive relation at omega^(omega^2) -/

open Cardinal Ordinal

namespace Erdos591

open Negative.Exact

/-- Every two-colouring at `omega^(omega^2)` has a full red copy or a blue triangle. -/
theorem schipperus_two :
    OrdinalCardinalRamsey (ω ^ (ω ^ 2) : Ordinal.{0})
      (ω ^ (ω ^ 2) : Ordinal.{0}) (3 : Cardinal.{0}) := by
  classical
  intro red blue hcompl
  by_cases hfree : blue.CliqueFree 3
  · have hmodel : (blue.comap relIso).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap
        (SimpleGraph.Embedding.comap relIso.toEquiv.toEmbedding blue).isContained hfree
    obtain ⟨S, hS, htype⟩ := Positive.Game.Payoff.triangle_free_red_set (blue.comap relIso) hmodel
    let e : G ↪o (ω ^ (ω ^ 2) : Ordinal.{0}).ToType :=
      OrderEmbedding.ofStrictMono relIso (fun _ _ h => relIso.map_rel_iff.mpr h)
    let f : S ↪o (ω ^ (ω ^ 2) : Ordinal.{0}).ToType := (OrderEmbedding.subtype S).trans e
    refine Or.inl ⟨Set.range f, ?_, ?_⟩
    · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ hxy
      have hab : a.val ≠ b.val := fun heq => hxy (congrArg e heq)
      have hnot : ¬ blue.Adj (f a) (f b) :=
        ((blue.comap relIso).compl_adj a.val b.val).mp (hS a.property b.property hab) |>.2
      rw [hcompl.eq_compl]
      exact (blue.compl_adj _ _).mpr ⟨hxy, hnot⟩
    · exact (OrderIso.ordinalType_congr f.orderIso).symm.trans htype
  · obtain ⟨s, hs⟩ := not_forall.mp hfree
    have hclique : blue.IsNClique 3 s := not_not.mp hs
    refine Or.inr ⟨(s : Set (ω ^ (ω ^ 2) : Ordinal.{0}).ToType), hclique.isClique, ?_⟩
    simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, hclique.card_eq, Nat.cast_ofNat]

#print axioms schipperus_two

end Erdos591
