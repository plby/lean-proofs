import ErdosProblems.Erdos1105.EvenNoncliqueCore
import ErdosProblems.Erdos1105.EvenCliqueCore
import ErdosProblems.Erdos1105.SharpCliqueRainbow
import ErdosProblems.Erdos1105.EvenSplitBound
import ErdosProblems.Erdos1105.FullRepresentative

namespace Erdos1105

open SimpleGraph Finset

/-- Above the proposed even-path bound, every connected representative
has the pendant shape; all other saturated-core cases are excluded. -/
theorem fullRepresentative_even_pendant {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {d : ℕ} (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hq : pathFormula (Fintype.card V) (2 * d + 2) < Fintype.card C)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    PendantCliqueShape R (2 * d + 2) := by
  classical
  obtain ⟨H, hRH, hH, hmax⟩ := exists_cycle_saturated_extension (graphCone R) (2 * d + 3)
    (no_long_cycle_cone_of_path_free R (by omega) (hR.free hfree))
  have hu : H.IsUniversal none := fun v hv ↦ hRH (graphCone_universal R hv)
  let G := H.comap some
  have hcone : graphCone G = H := graphCone_comap_some H hu
  have hRG : R ≤ G := fun _ _ h ↦ hRH h
  have hGconn : G.Preconnected := hconn.mono hRG
  have hGfree : ¬pathGraph (2 * d + 2) ⊑ G :=
    path_free_of_no_long_cycle_cone G (by omega) (hcone.symm ▸ hH)
  have hGmax : ∀ J : SimpleGraph (Option V), graphCone G ≤ J →
      NoLongCycle J (2 * d + 3) → J = graphCone G := by
    simpa only [hcone] using hmax
  have heRG := card_le_card (edgeFinset_mono hRG)
  have hGhigh : pathFormula (Fintype.card V) (2 * d + 2) < G.edgeFinset.card := by
    rw [hR.card_edges] at heRG
    omega
  by_cases hclique : (graphCone G).IsClique (vertexCore (graphCone G) d : Set (Option V))
  · rcases even_clique_core_high_cases G (by omega) hn hGconn hGfree hGmax hclique hGhigh with
      hshape | ⟨hcard, hsharp⟩
    · obtain ⟨S, hS, u, huS, hpend⟩ := hshape
      exact ⟨S, hS, u, huS, fun x hx y hxy ↦ hpend x hx y (hRG hxy)⟩
    · have heq : R = G := by
        apply edgeFinset_inj.mp
        apply eq_of_subset_of_card_le (edgeFinset_mono hRG)
        rw [hsharp, hR.card_edges, even_path_linear_term _ d (by omega) (by omega)]
        rw [pathFormula_even] at hq
        have h := (le_max_right _ _).trans_lt hq
        omega
      have hrainbow : Set.InjOn (extendColor c) G.edgeSet := heq ▸ hR.rainbow
      obtain ⟨f, hf⟩ := rainbow_path_of_sharp_clique_core c G hrainbow (by omega) hn
        hGfree hclique hcard hsharp
      exact (hfree f hf).elim
  · rcases even_nonclique_core_bound_or_cover G hd hn hGconn hGfree hGmax hclique with
      hlow | ⟨A, hA, hcover⟩
    · exact (not_lt_of_ge hlow hGhigh).elim
    · have hb := even_path_vertex_cover_bound c R hR.rainbow (by omega) hn hfree A hA
        (fun x y hxy ↦ hcover x y (hRG hxy))
      rw [hR.card_edges] at hb
      exact (not_lt_of_ge hb hq).elim

end Erdos1105

#print axioms Erdos1105.fullRepresentative_even_pendant
