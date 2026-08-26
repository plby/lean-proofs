import ErdosProblems.Erdos19.TwoScaleSampling
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Nat.Choose.Bounds

/-! # Sampling graph edges while controlling every cut -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_exists_graph_edge_sample (k : ℕ) (hk : 0 < k)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : _root_.SimpleGraph (Fin n),
      ∃ P : Finset (Sym2 (Fin n)), P ⊆ G.edgeFinset ∧
        (∀ v : Fin n, |((G.incidenceFinset v ∩ P).card : ℝ) - (G.degree v : ℝ) / k| <
          eta * n) ∧
        (∀ A B : Finset (Fin n),
          |(((G.between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset ∩ P).card : ℝ) -
              (G.between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset.card / k| <
            eta * (n : ℝ) ^ 2) := by
  classical
  obtain ⟨N, hN⟩ := eventually_sample_linear_and_quadratic_families k hk eta heta
  refine ⟨N, ?_⟩
  intro n hn G
  let I := Fin n
  let J := Finset (Fin n) × Finset (Fin n)
  let A : I → Finset (Sym2 (Fin n)) := fun v ↦ G.incidenceFinset v
  let B : J → Finset (Sym2 (Fin n)) := fun p ↦
    (G.between (p.1 : Set (Fin n)) (p.2 : Set (Fin n))).edgeFinset
  have hI : Fintype.card I ≤ n := by simp only [I, Fintype.card_fin, le_refl]
  have hJ : Fintype.card J ≤ 4 ^ n := by
    simp only [J, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    rw [← mul_pow]
    norm_num
  have hA : ∀ i, A i ⊆ G.edgeFinset := fun i ↦ G.incidenceFinset_subset i
  have hB : ∀ p, B p ⊆ G.edgeFinset := fun p ↦ edgeFinset_mono between_le
  have hAsize : ∀ i, (A i).card ≤ n := by
    intro i
    dsimp only [A]
    rw [card_incidenceFinset_eq_degree]
    simpa only [Fintype.card_fin] using (G.degree_lt_card_verts i).le
  have hBsize : ∀ p, (B p).card ≤ n ^ 2 := by
    intro p
    exact ((G.between (p.1 : Set (Fin n)) (p.2 : Set (Fin n))).card_edgeFinset_le_card_choose_two).trans
      (by simpa only [Fintype.card_fin] using Nat.choose_le_pow n 2)
  obtain ⟨P, hP, hPA, hPB⟩ := hN n hn (Sym2 (Fin n)) I J hI hJ
    G.edgeFinset A B hA hB hAsize hBsize
  refine ⟨P, hP, ?_, ?_⟩
  · intro v
    simpa only [A, card_incidenceFinset_eq_degree] using hPA v
  · intro S T
    exact hPB (S, T)

#print axioms eventually_exists_graph_edge_sample

end Erdos19
