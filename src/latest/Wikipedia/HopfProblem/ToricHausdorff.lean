import Wikipedia.HopfProblem.ToricSpace
import Wikipedia.HopfProblem.ToricSeparation
import Wikipedia.HopfProblem.MonomialSeparation

/-!
# Hausdorffness of the actual toric chart gluing

The integral separating characters supplied by the A₂ strip inequalities
make every overlap graph closed. Open chart embeddings then give disjoint
neighbourhoods of any two distinct points of the glued space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem chart_overlap_graph_closed (s t : Triangle) :
    IsClosed (overlapGraph (transition s t)) :=
  overlapGraph_closed (transition s t)
    (ToricSeparation.exponents s t) (ToricSeparation.exponents t s)
    (ToricSeparation.exponents_nonneg s t) (ToricSeparation.exponents_nonneg t s)
    (ToricSeparation.exponents_cancel s t)
    (ToricSeparation.exponents_pos_of_transition_neg s t)

instance t2Space : T2Space Space := by
  constructor
  intro x y hxy
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨t, w, rfl⟩ := inclusion_jointly_surjective y
  have hn : (z, w) ∈ (overlapGraph (transition s t))ᶜ := by
    intro h
    apply hxy
    exact (inclusion_eq_iff s t z w).mpr ⟨by simpa using h.1, h.2⟩
  obtain ⟨U, V, hU, hV, hz, hw, hUV⟩ :=
    isOpen_prod_iff.mp (chart_overlap_graph_closed s t).isOpen_compl z w hn
  refine ⟨inclusion s '' U, inclusion t '' V,
    (inclusion_openEmbedding s).isOpenMap _ hU,
    (inclusion_openEmbedding t).isOpenMap _ hV,
    mem_image_of_mem _ hz, mem_image_of_mem _ hw, ?_⟩
  apply Set.disjoint_left.mpr
  rintro q ⟨u, hu, hsu⟩ ⟨v, hv, htv⟩
  have he := (inclusion_eq_iff s t u v).mp (hsu.trans htv.symm)
  exact hUV (show (u, v) ∈ U ×ˢ V from ⟨hu, hv⟩) ⟨by simpa using he.1, he.2⟩

instance locallyCompactSpace : LocallyCompactSpace Space :=
  ChartedSpace.locallyCompactSpace (CoordinateSpace 3) Space

end Wikipedia.HopfProblem.ToricSpace
