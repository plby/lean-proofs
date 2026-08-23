import ErdosProblems.Erdos1105.PathSixNonclique
import ErdosProblems.Erdos1105.PathSixPendant
import ErdosProblems.Erdos1105.ThreePetalCopy
import ErdosProblems.Erdos1105.EvenConnectedShape

namespace Erdos1105

open SimpleGraph Finset

/-- The remaining smallest even case, including representatives with
arbitrarily many triangle blocks attached to one root. -/
theorem connected_path_six_rainbow_bound {V C : Type*} [Fintype V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V) [DecidableRel R.Adj]
    (hR : Set.InjOn (extendColor c) R.edgeSet) (hn : 6 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hconn : R.Preconnected) : R.edgeFinset.card ≤ pathFormula (Fintype.card V) 6 := by
  classical
  by_contra! hhigh
  have hRfree : ¬pathGraph 6 ⊑ R := representative_free le_top c hR hfree
  obtain ⟨H, hRH, hH, hmax⟩ := exists_cycle_saturated_extension (graphCone R) 7
    (no_long_cycle_cone_of_path_free R (by omega) hRfree)
  have hu : H.IsUniversal none := fun v hv ↦ hRH (graphCone_universal R hv)
  let G := H.comap some
  have hcone : graphCone G = H := graphCone_comap_some H hu
  have hRG : R ≤ G := fun _ _ h ↦ hRH h
  have hGconn : G.Preconnected := hconn.mono hRG
  have hGfree : ¬pathGraph 6 ⊑ G :=
    path_free_of_no_long_cycle_cone G (by omega) (hcone.symm ▸ hH)
  have hGmax : ∀ J : SimpleGraph (Option V), graphCone G ≤ J →
      NoLongCycle J 7 → J = graphCone G := by simpa only [hcone] using hmax
  have heRG := card_le_card (edgeFinset_mono hRG)
  have hGhigh : pathFormula (Fintype.card V) 6 < G.edgeFinset.card := by omega
  by_cases hclique : (graphCone G).IsClique (vertexCore (graphCone G) 2 : Set (Option V))
  · rcases even_clique_core_high_cases G (d := 2) (by omega) hn hGconn hGfree hGmax
      hclique hGhigh with hshape | ⟨hcard, hsharp⟩
    · have hRshape : PendantCliqueShape R 6 := by
        obtain ⟨S, hS, u, huS, hpend⟩ := hshape
        exact ⟨S, hS, u, huS, fun x hx y hxy ↦ hpend x hx y (hRG hxy)⟩
      exact not_lt_of_ge (path_six_pendant_rainbow_bound c R hR hn hfree hRshape) hhigh
    · have heq : R = G := by
        apply edgeFinset_inj.mp
        apply eq_of_subset_of_card_le (edgeFinset_mono hRG)
        rw [hsharp, even_path_linear_term _ 2 (by omega) (by omega)]
        have h := (le_max_right _ _).trans_lt hhigh
        norm_num [pathFormula, Nat.choose] at h ⊢
        omega
      have hrainbow : Set.InjOn (extendColor c) G.edgeSet := heq ▸ hR
      obtain ⟨f, hf⟩ := rainbow_path_of_sharp_clique_core c G hrainbow (by omega) hn
        hGfree hclique hcard hsharp
      exact hfree f hf
  · rcases path_six_nonclique_cover_or_root G hGconn hGfree hGmax hclique with
      ⟨A, hA, hcover⟩ | ⟨u, hroot⟩
    · have hb := even_path_vertex_cover_bound c R hR (l := 2) (by omega) hn hfree A hA
        (fun x y hxy ↦ hcover x y (hRG hxy))
      exact not_lt_of_ge hb hhigh
    · have hrootR : ∀ w, ∀ p : R.Walk u w, p.IsPath → p.length ≤ 2 := by
        intro w p hp
        have h := hroot w (p.mapLe hRG) (hp.mapLe hRG)
        simpa only [Walk.length_mapLe] using h
      have hb := rooted_two_rainbow_edge_bound c R hR hconn u hrootR hfree
      have h := (le_max_right _ _).trans_lt hhigh
      norm_num [pathFormula, Nat.choose] at h
      omega

theorem connected_path_six_color_bound {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hn : 6 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    Fintype.card C ≤ pathFormula (Fintype.card V) 6 := by
  classical
  rw [← hR.card_edges]
  exact connected_path_six_rainbow_bound c R hR.rainbow hn hfree hconn

end Erdos1105

#print axioms Erdos1105.connected_path_six_color_bound
