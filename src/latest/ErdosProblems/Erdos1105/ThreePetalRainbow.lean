import ErdosProblems.Erdos1105.ThreePetalPaths

namespace Erdos1105

open SimpleGraph

/-- A rainbow copy of three triangles sharing their center forces a
rainbow six-vertex path in the ambient complete coloring. -/
theorem rainbow_path_six_of_threePetal_copy {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V}
    (hR : Set.InjOn (extendColor c) R.edgeSet) (f : threePetalGraph.Copy R) :
    ∃ g : (pathGraph 6).Copy (⊤ : SimpleGraph V), IsRainbow g c := by
  let φ := completeCopy (⊤ : SimpleGraph (Fin 7)) ⟨f, f.injective⟩
  let c' := c ∘ φ.mapEdgeSet
  have hcolors : Set.InjOn (extendColor c') threePetalGraph.edgeSet := by
    intro e he d hd hc
    apply Sym2.map.injective f.injective
    have heTop : e ∈ (⊤ : SimpleGraph (Fin 7)).edgeSet := edgeSet_mono le_top he
    have hdTop : d ∈ (⊤ : SimpleGraph (Fin 7)).edgeSet := edgeSet_mono le_top hd
    rw [extendColor_edge c' ⟨e, heTop⟩, extendColor_edge c' ⟨d, hdTop⟩] at hc
    apply hR (f.mapEdgeSet ⟨e, he⟩).property (f.mapEdgeSet ⟨d, hd⟩).property
    change extendColor c (φ.mapEdgeSet ⟨e, heTop⟩).val =
      extendColor c (φ.mapEdgeSet ⟨d, hdTop⟩).val
    rw [extendColor_edge c _, extendColor_edge c _]
    exact hc
  obtain ⟨g, hg⟩ := rainbow_path_six_of_threePetalGraph c' hcolors
  exact ⟨φ.comp g, (rainbow_comp_iff g φ c).mpr hg⟩

end Erdos1105

#print axioms Erdos1105.rainbow_path_six_of_threePetal_copy
