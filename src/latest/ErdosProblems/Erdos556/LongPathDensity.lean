import ErdosProblems.Erdos556.LongConnections
import ErdosProblems.Erdos556.DeletionEdges
import ErdosProblems.Erdos556.PathBounds
import ErdosProblems.Erdos556.ReservoirAsymptotic

/-!
# Prescribed long paths from density

Delete the reservoir and the two prescribed endpoints, apply the path edge
bound, and reconnect through the reservoir. The final threshold is uniform
over all sufficiently large graphs satisfying the degree and deletion bounds.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_long_prescribed_path_of_density {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L k : ℕ) (R : Finset V)
    (hres : ∀ x y S, S.card ≤ L + 1 → ShortConnection G L x y (R \ S))
    (he : (k + R.card + 2) * Fintype.card V < G.edgeFinset.card)
    (u v : V) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsPath ∧ 2 * k < p.length := by
  classical
  let S := insert u (insert v R)
  let U := (S : Set V)ᶜ
  let H := G.induce U
  have hS : S.card ≤ R.card + 2 := by
    have h1 := card_insert_le u (insert v R)
    have h2 := card_insert_le v R
    dsimp [S]
    omega
  have hdeleted := edge_count_le_induce_compl_add_card_mul G S
  change G.edgeFinset.card ≤ H.edgeFinset.card + S.card * Fintype.card V at hdeleted
  have hmul := Nat.mul_le_mul_right (Fintype.card V) hS
  have hH : k * Fintype.card V < H.edgeFinset.card := by nlinarith
  have hcard := Fintype.card_le_of_injective (fun x : U => x.val) Subtype.val_injective
  have hH' : (2 * k) * Fintype.card U < 2 * H.edgeFinset.card := by
    have hmul' := Nat.mul_le_mul_left k hcard
    nlinarith
  obtain ⟨a, b, p, hp, hlen⟩ := exists_path_of_twice_edges_gt H (2 * k) hH'
  let f : H ↪g G := SimpleGraph.Embedding.induce U
  have hav (x : V) (hx : x ∈ (p.map f.toHom).support) : x ∉ R ∧ x ≠ u ∧ x ≠ v := by
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, hy⟩ := hx
    subst x
    have h := y.property
    change y.val ∉ insert u (insert v R) at h
    simp only [mem_insert, not_or] at h
    exact ⟨h.2.2, h.1, h.2.1⟩
  have hpos : 0 < (p.map f.toHom).length := by
    simpa only [Walk.length_map] using (Nat.lt_of_le_of_lt (Nat.zero_le _) hlen)
  obtain ⟨q, hq, hge, _⟩ := exists_path_with_prescribed_ends_of_reservoir L R hres u v huv
    (p.map f.toHom) (hp.map f.injective) hpos hav
  simp only [Walk.length_map] at hge
  exact ⟨q, hq, hlen.trans_le hge⟩

theorem exists_uniform_long_prescribed_paths (D B : ℕ) (hD : 0 < D) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (b d k : ℕ),
      N₀ ≤ Fintype.card V → ConnectedAfterDeleting G b →
      (∀ w, d + b ≤ G.degree w) → Fintype.card V ≤ D * d → Fintype.card V ≤ B * b →
      (k : ℝ) * Fintype.card V + 2 * q * (Fintype.card V : ℝ) ^ 2 +
        2 * Fintype.card V < (G.edgeFinset.card : ℝ) →
      ∀ u v, u ≠ v → ∃ p : G.Walk u v, p.IsPath ∧ 2 * k < p.length := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_connecting_reservoir D B (3 * D + 1) hD hB q hq0 hq1
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ b d k hN hc hg hd hb he u v huv
  obtain ⟨R, hR, hres⟩ := hN₀ G b d hN hc hg hd hb
  have hmul := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg (Fintype.card V) :
    (0 : ℝ) ≤ Fintype.card V)
  have heR : ((k : ℝ) + R.card + 2) * Fintype.card V < (G.edgeFinset.card : ℝ) := by
    nlinarith
  have heN : (k + R.card + 2) * Fintype.card V < G.edgeFinset.card := by exact_mod_cast heR
  exact exists_long_prescribed_path_of_density G (3 * D) k R hres heN u v huv

#print axioms exists_uniform_long_prescribed_paths

end Erdos556
