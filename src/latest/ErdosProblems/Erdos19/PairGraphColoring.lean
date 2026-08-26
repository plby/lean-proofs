import ErdosProblems.Erdos19.PairColoring
import ErdosProblems.Erdos19.MatchingCoreColoring

/-! # Transporting a proper graph labeling to pair hyperedges -/

namespace Erdos19.SetHypergraph

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V]

theorem exists_edgeColoring_of_pair_labeling (H : SetHypergraph V)
    (hpair : ∀ e : H, e.1.ncard = 2) (label : H.twoGraph.EdgeLabeling C)
    (hlabel : ∀ x y z (hxy : H.twoGraph.Adj x y) (hxz : H.twoGraph.Adj x z),
      label.get x y hxy = label.get x z hxz → y = z) :
    Nonempty (H.EdgeColoring C) := by
  refine ⟨⟨fun e ↦ H.pairLabel label e (hpair e), ?_⟩⟩
  intro e f hef hinter heq
  obtain ⟨x, hxe, hxf⟩ := hinter
  obtain ⟨y, hxy, hexy⟩ := exists_pair_at (hpair e) hxe
  obtain ⟨z, hxz, hfxz⟩ := exists_pair_at (hpair f) hxf
  have hE : H.twoGraph.Adj x y := ⟨hxy, hexy ▸ e.2⟩
  have hF : H.twoGraph.Adj x z := ⟨hxz, hfxz ▸ f.2⟩
  have hget : label.get x y hE = label.get x z hF := by
    simpa only [H.pairLabel_eq_get label e (hpair e) x y hE hexy,
      H.pairLabel_eq_get label f (hpair f) x z hF hfxz] using heq
  have hyz := hlabel x y z hE hF hget
  apply hef
  apply Subtype.ext
  rw [hexy, hfxz, hyz]

theorem edgeColorable_pairs_of_matching_core (H : SetHypergraph V)
    (hpair : ∀ e : H, e.1.ncard = 2) (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ v, H.twoGraph.degree v ≤ D)
    (hcore : Vizing.HasMatchingDegreeCore H.twoGraph D) : H.EdgeColorable D := by
  classical
  obtain ⟨label, hlabel⟩ := Vizing.exists_edgeLabeling_of_matching_core H.twoGraph D hD
    hdegree hcore
  exact H.exists_edgeColoring_of_pair_labeling hpair label hlabel

#print axioms edgeColorable_pairs_of_matching_core

end Erdos19.SetHypergraph
