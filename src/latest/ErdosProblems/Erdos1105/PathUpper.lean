import ErdosProblems.Erdos1105.ConnectedPathSix
import ErdosProblems.Erdos1105.ConnectedEvenUpper
import ErdosProblems.Erdos1105.OddPathUpper

namespace Erdos1105

open SimpleGraph

/-- The connected-representative color bound, for both parities and
including the smallest admissible path orders. -/
theorem connected_path_color_bound {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 5 ≤ k)
    (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    Fintype.card C ≤ pathFormula (Fintype.card V) k := by
  by_cases hodd : Odd k
  · exact connected_odd_color_bound c hk hodd hn hfree R hR hconn
  by_cases hk6 : k = 6
  · subst k
    exact connected_path_six_color_bound c hn hfree R hR hconn
  obtain ⟨a, ha⟩ := Nat.not_odd_iff_even.mp hodd
  have hka : k = 2 * (a - 1) + 2 := by omega
  rw [hka] at hn hfree ⊢
  exact connected_even_large_color_bound c (by omega) hn hfree R hR hconn

/-- The sharp color bound for arbitrary complete-graph colorings, with
no connectivity assumption on a representative. -/
theorem path_color_bound {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 5 ≤ k)
    (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) :
    Fintype.card C ≤ pathFormula (Fintype.card V) k :=
  path_color_bound_of_connected hk
    (fun c hn hfree R hR hconn ↦ connected_path_color_bound c hk hn hfree R hR hconn)
    c hn hfree R hR

/-- The full affirmative exact path formula of Erdős Problem 1105. -/
theorem antiRamseyNum_pathGraph {k n : ℕ} (hk : 5 ≤ k) (hn : k ≤ n) :
    antiRamseyNum (pathGraph k) n = pathFormula n k := by
  apply le_antisymm
  · apply antiRamseyNum_le
    intro q c hc hfree
    obtain ⟨R, hR⟩ := exists_fullRepresentative c hc
    have h := path_color_bound c hk (by simpa using hn) hfree R hR
    simpa only [Fintype.card_fin] using h
  · exact path_formula_lower_bound k n hk hn

end Erdos1105

#print axioms Erdos1105.antiRamseyNum_pathGraph
