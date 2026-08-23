import ErdosProblems.Erdos1105.DisconnectedReduction

universe u v

namespace Erdos1105

open SimpleGraph

/-- It suffices to prove the path bound for colorings having a connected
full representative. The bridge decomposition and a color-preserving
vertex-deletion induction handle every other coloring. -/
theorem path_color_bound_of_connected {k : ℕ} (hk : 5 ≤ k) {C : Type v} [Fintype C]
    (hconnected : ∀ {W : Type u} [Fintype W],
      ∀ (c : (⊤ : SimpleGraph W).edgeSet → C), k ≤ Fintype.card W →
      (∀ f : (pathGraph k).Copy (⊤ : SimpleGraph W), ¬IsRainbow f c) →
      ∀ R : SimpleGraph W, IsFullRepresentative c R → R.Preconnected →
        Fintype.card C ≤ pathFormula (Fintype.card W) k)
    {V : Type u} [Fintype V] (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) :
    Fintype.card C ≤ pathFormula (Fintype.card V) k := by
  classical
  induction hsize : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rw [← hsize]
    by_contra! hq
    by_cases hconn : ∃ Q : SimpleGraph V, IsFullRepresentative c Q ∧ Q.Preconnected
    · obtain ⟨Q, hQ, hQconn⟩ := hconn
      exact (not_lt_of_ge (hconnected c hn hfree Q hQ hQconn)) hq
    · have hno : ∀ Q : SimpleGraph V, IsFullRepresentative c Q → ¬Q.Preconnected :=
        fun Q hQ hQconn ↦ hconn ⟨Q, hQ, hQconn⟩
      obtain ⟨hnlarge, Q, hQ, x, hx⟩ := disconnected_high_colors_reduction c hk hn hfree R hR hno hq
      have hcard : Fintype.card {w // w ≠ x} = Fintype.card V - 1 := by
        simp [Fintype.card_subtype_compl (fun w : V ↦ w = x)]
      have hn' : k ≤ Fintype.card {w // w ≠ x} := by rw [hcard]; omega
      have hlt : Fintype.card {w // w ≠ x} < n := by rw [hcard, ← hsize]; omega
      have hind : Fintype.card C ≤ pathFormula (Fintype.card {w // w ≠ x}) k :=
        ih _ hlt (restrictVertexColoring c x) hn' (restrictVertexColoring_free c x hfree)
          (Q.induce {w | w ≠ x}) (hQ.delete_isolated hx) rfl
      have hm := pathFormula_mono (show Fintype.card {w // w ≠ x} ≤ Fintype.card V by
        rw [hcard]; omega) k
      exact (not_lt_of_ge (hind.trans hm)) hq

end Erdos1105

#print axioms Erdos1105.path_color_bound_of_connected
