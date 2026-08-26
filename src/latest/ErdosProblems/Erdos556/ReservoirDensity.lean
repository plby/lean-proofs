import ErdosProblems.Erdos556.ClosingPaths
import ErdosProblems.Erdos556.DeletionEdges
import ErdosProblems.Erdos556.PathBounds
import ErdosProblems.Erdos556.ParityReservoir

/-!
# Density bounds from parity reservoirs

A path outside the reservoir closes to an odd cycle without losing any of
its length. The Erdős--Gallai path bound controls the remaining edges;
the incidence estimate controls edges lost to the reservoir.
-/

namespace Erdos556

open SimpleGraph

theorem path_length_le_of_parity_reservoir {V : Type*} {G : SimpleGraph V}
    (R : Finset V) (L k : ℕ) (hk : 1 ≤ k)
    (hres : ∀ u v, u ≠ v → ParityConnection G L u v R)
    (hodd : ∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hav : ∀ x ∈ p.support, x ∉ R) :
    p.length ≤ 2 * k := by
  by_contra hlen
  have huv : u ≠ v := by
    intro h
    have hz := ((hp.nil_iff_eq).mpr h).length_eq_zero
    omega
  obtain ⟨c, hc, ho, hge, _⟩ := exists_odd_cycle_of_path_and_parity_connection
    p hp (by omega) L R hav (hres u v huv)
  have hle := hodd u c hc ho
  omega

theorem edge_bound_of_parity_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V) (L k : ℕ) (hk : 1 ≤ k)
    (hres : ∀ u v, u ≠ v → ParityConnection G L u v R)
    (hodd : ∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) :
    G.edgeFinset.card ≤ (k + R.card) * Fintype.card V := by
  classical
  let U := (R : Set V)ᶜ
  let H := G.induce U
  let f : H ↪g G := SimpleGraph.Embedding.induce U
  have hpaths {u v : U} (p : H.Walk u v) (hp : p.IsPath) : p.length ≤ 2 * k := by
    have h := path_length_le_of_parity_reservoir R L k hk hres hodd
      (p.map f.toHom) (hp.map f.injective) (by
        intro x hx
        rw [Walk.support_map, List.mem_map] at hx
        obtain ⟨y, _, hy⟩ := hx
        subst x
        exact y.property)
    simpa only [Walk.length_map] using h
  have hbound := path_edge_bound H (2 * k) hpaths
  have hcard := Fintype.card_le_of_injective (fun x : U => x.val) Subtype.val_injective
  have hretained : H.edgeFinset.card ≤ k * Fintype.card V := by
    have hmul := Nat.mul_le_mul_left k hcard
    nlinarith
  have hdeleted := edge_count_le_induce_compl_add_card_mul G R
  change G.edgeFinset.card ≤ H.edgeFinset.card + R.card * Fintype.card V at hdeleted
  nlinarith

/-- The robustly nonbipartite case of the odd-cycle density estimate.
All graph parameters are quantified after the uniform order threshold. -/
theorem exists_uniform_robust_odd_cycle_density_bound (D B : ℕ) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (b d k : ℕ),
      N₀ ≤ Fintype.card V → ConnectedAfterDeleting G (b + 3 * D + 3) →
      NonbipartiteAfterDeleting G (b + 3 * D + 3) →
      (∀ w, d + (b + 3 * D + 3) ≤ G.degree w) → Fintype.card V ≤ D * d →
      Fintype.card V ≤ B * b → 1 ≤ k →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      (G.edgeFinset.card : ℝ) ≤ (k : ℝ) * Fintype.card V +
        2 * q * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_parity_reservoir D B 0 hB q hq0 hq1
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ b d k hN hc hnb hg hd hb hk ho
  obtain ⟨R, hR, hres⟩ := hN₀ G b d hN hc hnb hg hd hb
  have hres' (u v : V) (huv : u ≠ v) : ParityConnection G (12 * D + 3) u v R := by
    simpa only [Finset.sdiff_empty] using hres u v huv ∅ (by simp)
  have he := edge_bound_of_parity_reservoir G R (12 * D + 3) k hk hres' ho
  have heR : (G.edgeFinset.card : ℝ) ≤ ((k : ℝ) + R.card) * Fintype.card V := by
    exact_mod_cast he
  have hm := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg (Fintype.card V) :
    (0 : ℝ) ≤ Fintype.card V)
  nlinarith

#print axioms edge_bound_of_parity_reservoir
#print axioms exists_uniform_robust_odd_cycle_density_bound

end Erdos556
