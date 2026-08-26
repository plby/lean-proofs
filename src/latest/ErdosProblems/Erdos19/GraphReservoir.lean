import ErdosProblems.Erdos19.GraphEdgeSampling
import ErdosProblems.Erdos19.DenseCuts

/-! # A dense graph reservoir with uniform cut expansion

The reservoir is represented by its finite edge set. All degree and cut
conditions refer to that same set, so the existential statement is joint.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_exists_dense_graph_reservoir (k : ℕ) (hk : 0 < k)
    (alpha epsilon : ℝ) (halpha : 0 < alpha) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : _root_.SimpleGraph (Fin n),
      (∀ v, (1 - delta) * n ≤ (G.degree v : ℝ)) →
      ∃ P : Finset (Sym2 (Fin n)), P ⊆ G.edgeFinset ∧
        (∀ v : Fin n, |((G.incidenceFinset v ∩ P).card : ℝ) - (n : ℝ) / k| <
          epsilon * n) ∧
        (∀ A B : Finset (Fin n), Disjoint A B →
          alpha * n ≤ (A.card : ℝ) → alpha * n ≤ (B.card : ℝ) →
          (A.card : ℝ) * B.card / (2 * k) <
            ((G.between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset ∩ P).card) := by
  classical
  let delta := min (epsilon / 4) (alpha / 4)
  let eta := min (epsilon / 4) (alpha ^ 2 / (4 * k))
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨N₀, hN₀⟩ := eventually_exists_graph_edge_sample k hk eta heta
  refine ⟨delta, hdelta, max N₀ 1, ?_⟩
  intro n hn G hdegree
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨P, hP, hdegrees, hcuts⟩ := hN₀ n ((le_max_left _ _).trans hn) G
  refine ⟨P, hP, ?_, ?_⟩
  · intro v
    have hdle : (G.degree v : ℝ) ≤ n := by
      exact_mod_cast (by simpa only [Fintype.card_fin] using (G.degree_lt_card_verts v).le)
    have hdef : (n : ℝ) - G.degree v ≤ delta * n := by linarith [hdegree v]
    have hdist : |(G.degree v : ℝ) / k - (n : ℝ) / k| ≤ delta * n := by
      rw [← sub_div, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdle) hkR.le)]
      calc
        -(((G.degree v : ℝ) - n) / k) = ((n : ℝ) - G.degree v) / k := by ring
        _ ≤ delta * n / k := div_le_div_of_nonneg_right hdef hkR.le
        _ ≤ delta * n := div_le_self (by positivity) hkOne
    have hslack : eta * n + delta * n ≤ epsilon * n := by
      have hη : eta ≤ epsilon / 4 := min_le_left _ _
      have hδ : delta ≤ epsilon / 4 := min_le_left _ _
      have he := mul_le_mul_of_nonneg_right hη hnR.le
      have hd := mul_le_mul_of_nonneg_right hδ hnR.le
      nlinarith only [he, hd, mul_nonneg hepsilon.le hnR.le]
    exact ((abs_sub_le _ ((G.degree v : ℝ) / k) ((n : ℝ) / k)).trans_lt
      (add_lt_add_of_lt_of_le (hdegrees v) hdist)).trans_le hslack
  · intro A B hAB hA hB
    let a : ℝ := A.card
    let b : ℝ := B.card
    let g : ℝ := (G.between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset.card
    let p : ℝ := ((G.between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset ∩ P).card
    have hcut : a * b ≤ g + a * (delta * n) := by
      simpa only [Fintype.card_fin] using cut_card_lower_of_min_degree G A B hAB delta
        (fun v ↦ by simpa only [Fintype.card_fin] using hdegree v)
    have hδ : 4 * delta ≤ alpha := by
      have hd : delta ≤ alpha / 4 := min_le_right _ _
      linarith
    have hδn : 4 * delta * n ≤ b := by
      have hd := mul_le_mul_of_nonneg_right hδ hnR.le
      dsimp only [b]
      nlinarith only [hd, hB]
    have hδa := mul_le_mul_of_nonneg_left hδn (show 0 ≤ a by positivity)
    have hthree : 3 * (a * b) ≤ 4 * g := by
      nlinarith only [hcut, hδa]
    have hη : eta * (4 * k) ≤ alpha ^ 2 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * k)).mp (min_le_right _ _)
    have hηn := mul_le_mul_of_nonneg_right hη (sq_nonneg (n : ℝ))
    have hab : alpha ^ 2 * (n : ℝ) ^ 2 ≤ a * b := by
      have hm := mul_le_mul hA hB (by positivity : 0 ≤ alpha * n)
        (by positivity : (0 : ℝ) ≤ A.card)
      nlinarith only [hm]
    have herror : 4 * k * eta * (n : ℝ) ^ 2 ≤ a * b := by
      nlinarith only [hηn, hab]
    have hsample : g / k < p + eta * (n : ℝ) ^ 2 := by
      have hlow := (abs_lt.mp (hcuts A B)).1
      change -(eta * (n : ℝ) ^ 2) < p - g / k at hlow
      linarith
    have hsample' : g < (p + eta * (n : ℝ) ^ 2) * k := (div_lt_iff₀ hkR).mp hsample
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)).2
    change a * b < p * (2 * k)
    nlinarith only [hthree, herror, hsample']

#print axioms eventually_exists_dense_graph_reservoir

end Erdos19
