import ErdosProblems.Erdos1105.PathBoundReduction
import ErdosProblems.Erdos1105.ConnectedOddUpper
import ErdosProblems.Erdos1105.PathConstructions

namespace Erdos1105

open SimpleGraph

/-- The sharp color bound for every odd path, with no connectivity
assumption on any representative. -/
theorem odd_path_color_bound {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) :
    Fintype.card C ≤ pathFormula (Fintype.card V) k :=
  path_color_bound_of_connected hk
    (fun c hn hfree R hR hconn ↦ connected_odd_color_bound c hk hodd hn hfree R hR hconn)
    c hn hfree R hR

/-- The complete affirmative exact path formula for odd `k`. -/
theorem antiRamseyNum_pathGraph_odd {k n : ℕ} (hk : 5 ≤ k) (hodd : Odd k) (hn : k ≤ n) :
    antiRamseyNum (pathGraph k) n = pathFormula n k := by
  apply le_antisymm
  · apply antiRamseyNum_le
    intro q c hc hfree
    obtain ⟨R, hR⟩ := exists_fullRepresentative c hc
    have h := odd_path_color_bound c hk hodd (by simpa using hn) hfree R hR
    simpa only [Fintype.card_fin] using h
  · exact path_formula_lower_bound k n hk hn

end Erdos1105

#print axioms Erdos1105.antiRamseyNum_pathGraph_odd
