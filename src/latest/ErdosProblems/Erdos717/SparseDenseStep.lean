/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The high-induced-density alternative in the sparse induction. -/

import ErdosProblems.Erdos717.DegreePruning

open Function Set
open SimpleGraph

namespace Erdos717

noncomputable def sparseIndependentSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) : Finset V :=
  Classical.choose (exists_maximum_independent_subset G (lowDegreeFinset G D))

noncomputable def sparseLowPatternSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D b : ℕ) : Finset V :=
  lowPatternFinset G (lowDegreeFinset G D) (sparseIndependentSet G D) b

noncomputable def sparseCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D b : ℕ) : SimpleGraph V :=
  (G.induce (sparseLowPatternSet G D b : Set V)).spanningCoe

/-- The complete combinatorial sparse step.  All analytic choices (`D`, `b`,
`X0`, `L`, `Q`, `R`, and `s`) are exposed as natural parameters, so this
theorem contains no rounding or real-analysis arguments. -/
theorem sparse_dense_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a D b X0 L Q k : ℕ)
    (hind : G.indepNum ≤ a)
    (ha : 16 * a ≤ Fintype.card V)
    (hdegreeCut : 4 * G.edgeFinset.card ≤ Fintype.card V * (D + 1))
    (hpatternCut : 4 * D * a ≤ (b + 1) * Fintype.card V)
    (hE : 0 < G.edgeFinset.card)
    (hX0 : 20 ≤ X0) (hLX : 5 * L ≤ X0)
    (hEdgeHigh : G.edgeSet.ncard ≤ 1000 * (sparseCore G D b).edgeSet.ncard)
    (hreservoirArithmetic :
      4 * Fintype.card V *
        (Fintype.card V * (X0 * X0) +
          40 * (Fintype.card V * Fintype.card V * L)) ≤
      (sparseCore G D b).edgeSet.ncard ^ 2)
    (hb : 1 ≤ b) (hba : b ≤ a)
    (hQ : a.choose b * Q ≤ X0 / 5)
    (hL : 5 ≤ L) (hk : 2 ≤ k)
    (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    Q < k ∨ L ^ (b - 1) * Q < 38 ^ (b - 1) * k ^ (2 * b - 1) := by
  classical
  let P := lowDegreeFinset G D
  let I := sparseIndependentSet G D
  have hIspec : I ⊆ P ∧ G.IsIndepSet I ∧ IndepBoundOn G P I.card := by
    simpa [I, P, sparseIndependentSet] using
      Classical.choose_spec (exists_maximum_independent_subset G
        (lowDegreeFinset G D))
  have hIP : I ⊆ P := hIspec.1
  have hIind : G.IsIndepSet I := hIspec.2.1
  have hImax : IndepBoundOn G P I.card := hIspec.2.2
  let W := lowPatternFinset G P I b
  have hWP : W ⊆ P := lowPattern_subset G P I b
  have hIW : Disjoint I W := lowPattern_disjoint G P I b
  have hdegreeW : ∀ v ∈ W, (G.neighborFinset v ∩ I).card ≤ b :=
    lowPattern_degree G P I b
  have hIcard : I.card ≤ a := by
    exact (hIind.card_le_indepNum).trans hind
  have hPcard : Fintype.card V / 2 ≤ P.card := by
    exact half_card_le_lowDegreeFinset G D hdegreeCut
  have hXbound := highPattern_card_mul_le G P I D b hIP
    (degree_le_of_mem_lowDegreeFinset G D)
  have hXcard : 4 * (highPatternFinset G P I b).card ≤ Fintype.card V := by
    have hmul : (b + 1) * (4 * (highPatternFinset G P I b).card) ≤
        (b + 1) * Fintype.card V := by
      calc
        (b + 1) * (4 * (highPatternFinset G P I b).card) =
            4 * ((b + 1) * (highPatternFinset G P I b).card) := by ring
        _ ≤ 4 * (D * I.card) := Nat.mul_le_mul_left 4 hXbound
        _ ≤ 4 * D * a := by
          simpa [mul_assoc] using Nat.mul_le_mul_left (4 * D) hIcard
        _ ≤ (b + 1) * Fintype.card V := hpatternCut
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hWcard : Fintype.card V / 8 ≤ W.card := by
    have hpart := low_high_pattern_partition G P I hIP b
    change W.card + (highPatternFinset G P I b).card + I.card = P.card at hpart
    have haCard : 16 * I.card ≤ Fintype.card V :=
      (Nat.mul_le_mul_left 16 hIcard).trans ha
    omega
  let H : SimpleGraph V := sparseCore G D b
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHG : H ≤ G := by
    simpa [H, W, I, P, sparseCore, sparseLowPatternSet] using
      G.spanningCoe_induce_le (W : Set V)
  have hHE : 0 < H.edgeFinset.card := by
    have hEdgeHigh' : G.edgeFinset.card ≤ 1000 * H.edgeFinset.card := by
      rw [Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet,
        Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet]
      simpa [H, W, I, P, sparseCore, sparseLowPatternSet] using hEdgeHigh
    by_contra hzero
    have : H.edgeFinset.card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [this] at hEdgeHigh'
    omega
  have hlarge : 4 * Fintype.card V *
      (Fintype.card V * (X0 * X0) +
        40 * (Fintype.card V * Fintype.card V * L)) ≤
      H.edgeFinset.card * H.edgeFinset.card := by
    rw [Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet]
    simpa [H, W, I, P, sparseCore, sparseLowPatternSet, pow_two] using
      hreservoirArithmetic
  obtain ⟨U₀, hU₀card, hU₀support, hreservoir⟩ :=
    exists_short_path_reservoir_of_edge_square H G hHG X0 L hHE hX0 hLX hlarge
  have hU₀W : U₀ ⊆ W := by
    intro x hx
    have hxH := hU₀support hx
    change x ∈ ((G.induce (W : Set V)).spanningCoe).support at hxH
    rw [SimpleGraph.support_spanningCoe] at hxH
    obtain ⟨y, _hy, hyx⟩ := hxH
    exact hyx ▸ y.property
  have hpatterns : I.card.choose b * Q ≤ U₀.card := by
    calc
      I.card.choose b * Q ≤ a.choose b * Q :=
        Nat.mul_le_mul_right Q (Nat.choose_le_choose b hIcard)
      _ ≤ X0 / 5 := hQ
      _ ≤ U₀.card := hU₀card
  exact patterned_reservoir_order_inequality
    G P I W U₀ X0 L b Q k hIP hWP hIind hImax hIW hdegreeW
    hU₀W hU₀card hreservoir hb
    (by
      have hone : 1 ≤ a.choose b := Nat.one_le_iff_ne_zero.mpr
        (Nat.choose_ne_zero_iff.mpr hba)
      calc
        Q = 1 * Q := by simp
        _ ≤ a.choose b * Q := Nat.mul_le_mul_right Q hone
        _ ≤ X0 / 5 := hQ)
    hpatterns hL hk hnot

end Erdos717
