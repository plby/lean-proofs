import ErdosProblems.Erdos556.NonbipartiteLinkage
import ErdosProblems.Erdos556.LongPathDensity

/-!
# A bipartite core in a two-connected nonbipartite graph

An inconsistent ear exists unconditionally by finite Menger and the
odd-cycle characterization. A sufficiently long path between its endpoints
inside the bipartite core closes it to a long odd cycle.
-/

namespace Erdos556

open SimpleGraph

theorem long_odd_cycle_of_bipartite_core {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : TwoConnected G) (hnonbip : ¬ G.Colorable 2)
    (S : Set V) (hS : 2 ≤ S.ncard) (colour : (G.induce S).Coloring Bool)
    (k : ℕ) (hk : 1 ≤ k)
    (hlong : ∀ u v : S, u ≠ v → ∃ p : (G.induce S).Walk u v,
      p.IsPath ∧ 2 * k < p.length) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ Odd c.length ∧ 2 * k < c.length := by
  obtain ⟨u, v, huv, q, hq, hwrong, hqS⟩ :=
    exists_inconsistent_ear_of_twoConnected hG hnonbip S hS colour
  obtain ⟨p, hp, hlen⟩ := hlong u v (fun h => huv (congrArg Subtype.val h))
  obtain ⟨c, hc, ho, hge⟩ := odd_cycle_from_inconsistent_ear S colour p hp (by omega)
    q hq hqS hwrong
  exact ⟨u.val, c, hc, ho, hlen.trans_le hge⟩

theorem exists_uniform_bipartite_core_density_bound (D B : ℕ) (hD : 0 < D) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (b d k : ℕ),
      TwoConnected G → ¬ G.Colorable 2 → 2 ≤ S.card →
      N₀ ≤ Fintype.card (S : Set V) → ConnectedAfterDeleting (G.induce (S : Set V)) b →
      (∀ w : (S : Set V), d + b ≤ (G.induce (S : Set V)).degree w) →
      Fintype.card (S : Set V) ≤ D * d → Fintype.card (S : Set V) ≤ B * b → 1 ≤ k →
      (G.induce (S : Set V)).Colorable 2 →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      ((G.induce (S : Set V)).edgeFinset.card : ℝ) ≤
        (k : ℝ) * Fintype.card (S : Set V) + 2 * q * (Fintype.card (S : Set V) : ℝ) ^ 2 +
          2 * Fintype.card (S : Set V) := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_long_prescribed_paths D B hD hB q hq0 hq1
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ S b d k hG hnb hS hN hc hg hd hb hk hcol ho
  by_contra he
  have hdensity := lt_of_not_ge he
  have hlong := hN₀ (G.induce (S : Set V)) b d k hN hc hg hd hb hdensity
  obtain ⟨colour⟩ := hcol
  let col : (G.induce (S : Set V)).Coloring Bool :=
    SimpleGraph.recolorOfEquiv _ finTwoEquiv colour
  have hScard : 2 ≤ (S : Set V).ncard := by simpa only [Set.ncard_coe_finset] using hS
  obtain ⟨w, c, hcyc, hodd, hlen⟩ := long_odd_cycle_of_bipartite_core
    hG hnb (S : Set V) hScard col k hk hlong
  exact (Nat.not_le_of_gt hlen) (ho w c hcyc hodd)

#print axioms exists_uniform_bipartite_core_density_bound

end Erdos556
