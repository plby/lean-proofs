import ErdosProblems.Erdos1105.ConnectedOddRainbow

namespace Erdos1105

open SimpleGraph

/-- The sharp odd-path color bound whenever the coloring has a connected
full representative. The induction preserves that connectivity when it
deletes a vertex with no private colors. -/
theorem connected_odd_color_bound {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    Fintype.card C ≤ pathFormula (Fintype.card V) k := by
  classical
  induction hsize : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rw [← hsize]
    by_contra! hq
    obtain ⟨hnlarge, v, _, Q, hQ, hconnQ⟩ :=
      connected_high_colors_odd_reduction c hk hodd hn hfree hq R hR hconn
    have hcard : Fintype.card {w // w ≠ v} = Fintype.card V - 1 := by
      simp [Fintype.card_subtype_compl (fun w : V ↦ w = v)]
    have hn' : k ≤ Fintype.card {w // w ≠ v} := by rw [hcard]; omega
    have hlt : Fintype.card {w // w ≠ v} < n := by rw [hcard, ← hsize]; omega
    have hind : Fintype.card C ≤ pathFormula (Fintype.card {w // w ≠ v}) k :=
      ih _ hlt (restrictVertexColoring c v) hn' (restrictVertexColoring_free c v hfree)
        Q hQ hconnQ rfl
    have hm := pathFormula_mono (show Fintype.card {w // w ≠ v} ≤ Fintype.card V by
      rw [hcard]; omega) k
    exact (not_lt_of_ge (hind.trans hm)) hq

end Erdos1105

#print axioms Erdos1105.connected_odd_color_bound
