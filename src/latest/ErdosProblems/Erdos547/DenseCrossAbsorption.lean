import ErdosProblems.Erdos547.Absorption
import ErdosProblems.Erdos547.BipartiteCore

/-!
# Many cross edges supply an absorbing pair
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

variable {U V : Type*} [Fintype U]

open scoped Classical in
theorem isContained_of_dense_cross_edges (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree)
    (d m : ℕ) (hd : 0 < d) (hm : 20 * d ≤ m) (horder : Fintype.card U = m + 1)
    (A W : Finset V) (hdis : Disjoint A W)
    (hAsize : A.card ≤ m) (hWsize : W.card ≤ m + d)
    (hAdeg : ∀ z ∈ A, m ≤ degreeIn G A z + d)
    (hcross : 20 * (d : ℝ) * m < ∑ a ∈ A, (degreeIn G W a : ℝ)) : T ⊑ G := by
  classical
  have hmpos : 2 ≤ m := by omega
  have hthree : A.card ≤ 3 * (m / 2) := by omega
  obtain ⟨A₀, hA₀A, hA₀size, hweight⟩ := exists_small_large_weight_subset A
    (fun a ↦ (degreeIn G W a : ℝ)) (m / 2) hthree
  have hA₀bound : 2 * A₀.card ≤ m := by omega
  have hbudget : 3 * ((4 * d : ℝ) * (A₀.card + W.card)) ≤ 20 * d * m := by
    have hparts : 2 * ((A₀.card : ℝ) + W.card) ≤ 3 * m + 2 * d := by
      have h₀ : 2 * (A₀.card : ℝ) ≤ m := by exact_mod_cast hA₀bound
      have hW : (W.card : ℝ) ≤ (m : ℝ) + d := by exact_mod_cast hWsize
      linarith
    have hm' : 6 * (d : ℝ) ≤ m := by exact_mod_cast (show 6 * d ≤ m by omega)
    have hmul := mul_le_mul_of_nonneg_left hparts (show (0 : ℝ) ≤ 6 * d by positivity)
    have hslack := mul_le_mul_of_nonneg_left hm' (show (0 : ℝ) ≤ 2 * d by positivity)
    nlinarith only [hmul, hslack]
  have hmass : ((4 * d : ℕ) : ℝ) * (A₀.card + W.card) <
      ∑ a ∈ A₀, (degreeIn G W a : ℝ) := by
    push_cast
    linarith
  obtain ⟨P, hP, Q, hQ, _, hQne, hPQ, hQP⟩ := exists_bipartite_degree_core G A₀ W
    (hdis.mono_left hA₀A) (4 * d) hmass
  apply isContained_of_absorbing_pair T G hT d m hd hm horder A P Q
    (hP.trans hA₀A) (hdis.symm.mono_left hQ) hQne hAsize
  · have hcard := Finset.card_le_card hP
    omega
  · exact hAdeg
  · intro z hz
    exact (hPQ z hz).le
  · intro z hz
    exact (hQP z hz).le

end Erdos547

#print axioms Erdos547.isContained_of_dense_cross_edges
