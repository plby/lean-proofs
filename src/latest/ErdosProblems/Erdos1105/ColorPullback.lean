import ErdosProblems.Erdos1105.PrivateColors

namespace Erdos1105

open SimpleGraph

theorem rainbow_color_pullback {V W C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V} {S : SimpleGraph W}
    (hR : Set.InjOn (extendColor c) R.edgeSet) (f : S.Copy R) :
    Set.InjOn (extendColor (c ∘ (completeCopy (⊤ : SimpleGraph W)
      ⟨f, f.injective⟩).mapEdgeSet)) S.edgeSet := by
  let φ := completeCopy (⊤ : SimpleGraph W) ⟨f, f.injective⟩
  let c' := c ∘ φ.mapEdgeSet
  intro e he d hd hc
  apply Sym2.map.injective f.injective
  have heTop : e ∈ (⊤ : SimpleGraph W).edgeSet := edgeSet_mono le_top he
  have hdTop : d ∈ (⊤ : SimpleGraph W).edgeSet := edgeSet_mono le_top hd
  rw [extendColor_edge c' ⟨e, heTop⟩, extendColor_edge c' ⟨d, hdTop⟩] at hc
  apply hR (f.mapEdgeSet ⟨e, he⟩).property (f.mapEdgeSet ⟨d, hd⟩).property
  change extendColor c (φ.mapEdgeSet ⟨e, heTop⟩).val =
    extendColor c (φ.mapEdgeSet ⟨d, hdTop⟩).val
  rw [extendColor_edge c _, extendColor_edge c _]
  exact hc

end Erdos1105
