import ErdosProblems.Erdos556.HereditaryDensity
import ErdosProblems.Erdos556.DensityParameters

/-!
# Hereditary density for graphs without long odd cycles

For every positive error tolerance there is a uniform order threshold.
In a two-connected nonbipartite graph of order `N ≤ 16 * k` with no odd
cycle longer than `2 * k`, every induced subgraph has at most
`(k + ε * N)` times its order many edges.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_hereditary_density_bound_of_le_one (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ 16 * k → TwoConnected G → ¬ G.Colorable 2 →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      ∀ A : Finset V, ((G.induce (A : Set V)).edgeFinset.card : ℝ) ≤
        ((k : ℝ) + ε * Fintype.card V) * A.card := by
  obtain ⟨B, hB⟩ := exists_nat_gt ((4096 : ℝ) / ε + 128)
  have hdiv0 : (0 : ℝ) ≤ 4096 / ε := by positivity
  have hB128R : (128 : ℝ) ≤ B := by linarith
  have hB128 : 128 ≤ B := by exact_mod_cast hB128R
  have hεB : (4096 : ℝ) ≤ ε * B := by
    have h : (4096 : ℝ) / ε < B := by linarith
    have h' := (div_lt_iff₀ hε).mp h
    nlinarith
  have hBpos : 0 < 2 * B := by omega
  have hqpos : 0 < ε / 16 := by positivity
  have hqle : ε / 16 ≤ 1 := by linarith
  obtain ⟨N₁, hN₁⟩ := exists_hereditary_density_parameter_bound 64 (2 * B)
    (by decide) hBpos (ε / 16) hqpos hqle
  refine ⟨max (195 * B) (64 * (N₁ + 2)), ?_⟩
  intro V _ _ G _ k hN hk hG hnb ho
  let N := Fintype.card V
  have hLarge : 195 * B ≤ N := by dsimp [N]; omega
  have hThreshold : 64 * (N₁ + 2) ≤ N := by dsimp [N]; omega
  have hkpos : 1 ≤ k := by dsimp [N] at hLarge; nlinarith
  obtain ⟨b, d, hDd, hBb, ht, hbudget, hdegree, horder, hmargin⟩ :=
    density_parameters ε hε B N₁ N k hB128 hεB hLarge hThreshold hk
  have hηeq : 2 * (ε / 2) = ε := by ring
  have hqeq : 2 * (ε / 16) = ε / 8 := by ring
  have hquad := hN₁ G b d k ((k : ℝ) + ε * N / 2) (ε / 2) hG hnb hkpos
    (by positivity) (by positivity)
    (by simpa [Nat.add_assoc] using ht)
    (by simpa [Nat.add_assoc, hηeq] using hbudget)
    (by simpa [Nat.add_assoc] using hdegree)
    hDd hBb (by simpa [Nat.add_assoc] using horder)
    (by simpa [Nat.add_assoc, hqeq] using hmargin) ho
  intro A
  have hA := hquad A
  have hcard : (A.card : ℝ) ≤ N := by exact_mod_cast card_le_univ A
  have hsq := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  have hεsq := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ ε / 2)
  change ((G.induce (A : Set V)).edgeFinset.card : ℝ) ≤ ((k : ℝ) + ε * N) * A.card
  nlinarith

theorem exists_hereditary_density_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ 16 * k → TwoConnected G → ¬ G.Colorable 2 →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      ∀ A : Finset V, ((G.induce (A : Set V)).edgeFinset.card : ℝ) ≤
        ((k : ℝ) + ε * Fintype.card V) * A.card := by
  have hδ : 0 < min ε 1 := lt_min hε (by norm_num)
  obtain ⟨N₀, hN₀⟩ := exists_hereditary_density_bound_of_le_one (min ε 1) hδ (min_le_right _ _)
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ k hN hk hG hnb ho A
  apply (hN₀ G k hN hk hG hnb ho A).trans
  gcongr
  exact min_le_left ε 1

#print axioms exists_hereditary_density_bound

end Erdos556
