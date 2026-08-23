import ErdosProblems.Erdos1105.EvenConnectedShape
import ErdosProblems.Erdos1105.EvenPendant

namespace Erdos1105

open SimpleGraph

/-- The connected-representative bound for every even path of order at
least eight. The six-vertex case is handled separately. -/
theorem connected_even_large_color_bound {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {d : ℕ} (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    Fintype.card C ≤ pathFormula (Fintype.card V) (2 * d + 2) := by
  classical
  induction hsize : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rw [← hsize]
    by_contra! hq
    obtain ⟨hnlarge, v, Q, hQ, hconnQ⟩ := connected_even_pendant_reduction c hd hn hq
      (fun Q hQ hconnQ ↦ fullRepresentative_even_pendant c hd hn hfree hq Q hQ hconnQ) R hR hconn
    have hcard : Fintype.card {w // w ≠ v} = Fintype.card V - 1 := by
      simp [Fintype.card_subtype_compl (fun w : V ↦ w = v)]
    have hn' : 2 * d + 2 ≤ Fintype.card {w // w ≠ v} := by rw [hcard]; omega
    have hlt : Fintype.card {w // w ≠ v} < n := by rw [hcard, ← hsize]; omega
    have hind : Fintype.card C ≤ pathFormula (Fintype.card {w // w ≠ v}) (2 * d + 2) :=
      ih _ hlt (restrictVertexColoring c v) hn' (restrictVertexColoring_free c v hfree)
        Q hQ hconnQ rfl
    have hm := pathFormula_mono (show Fintype.card {w // w ≠ v} ≤ Fintype.card V by
      rw [hcard]; omega) (2 * d + 2)
    exact (not_lt_of_ge (hind.trans hm)) hq

end Erdos1105

#print axioms Erdos1105.connected_even_large_color_bound
