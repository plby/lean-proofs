import Arxiv.Arxiv2411_18291.EdgeCappedGeneratingData

/-! # Relative loss budgets for generators with an edge cap

An edge cap of order `N*k^2/delta^2` controls both the deleted host edges
and the unsaturated-clique error. This separates the required cap from the
ambient number of vertices.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem face_edge_saturation_budget {k f N v L μ δ cF cE : ℝ}
    (hv : 0 ≤ v) (hμ : 0 ≤ μ) (hcF : 0 < cF) (hcE : 0 < cE)
    (hF : 4 * k * f * N * L ≤ δ ^ 2 * μ * cF)
    (hE : 8 * k ^ 2 * N ≤ δ ^ 2 * cE) :
    k * (f * (N * v) * L / cF + k * (N * v) * (2 * μ) / cE) ≤
      δ ^ 2 * μ * v / 2 := by
  have hFv := mul_le_mul_of_nonneg_right hF hv
  have hEv := mul_le_mul_of_nonneg_right hE (mul_nonneg hμ hv)
  have hf : 4 * k * (f * (N * v) * L / cF) ≤ δ ^ 2 * μ * v := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hcF).mpr
    nlinarith only [hFv]
  have he : 4 * k * (k * (N * v) * (2 * μ) / cE) ≤ δ ^ 2 * μ * v := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hcE).mpr
    nlinarith only [hEv]
  nlinarith only [hf, he]

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem clique_count_upper_of_relative_error (K : Hypergraph V (r + 1))
    (D : Finset (Block V q)) (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K)
    {μ ε : ℝ} (hμ : 0 ≤ μ) (hε : ε ≤ 1)
    (hcount : ∀ e ∈ K, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ)
    (e : Block V (r + 1)) : ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * μ := by
  by_cases heK : e ∈ K
  · have hh := (abs_le.mp (hcount e heK)).2
    have he := mul_le_mul_of_nonneg_right hε hμ
    linarith only [hh, he]
  · have hempty : D.filter (fun Q => e.val ⊆ Q.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      exact heK (hD Q (mem_filter.mp hQ).1 ((mem_cliqueEdges _ _).mpr (mem_filter.mp hQ).2))
    rw [hempty, card_empty, Nat.cast_zero]
    positivity

theorem exists_edge_capped_generating_data_relative (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (faceCap edgeCap : ℕ)
    (hfaceCap : 0 < faceCap) (hedgeCap : 0 < edgeCap) {L μ ε δ : ℝ}
    (hL : 0 ≤ L) (hμ : 0 < μ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ δ / 2)
    (hface : ∀ S : Block V r, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L)
    (hcount : ∀ e ∈ K, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ)
    (hfaceBudget : (4 * q.choose (r + 1) * q.choose r * N : ℝ) * L ≤
      δ ^ 2 * μ * faceCap)
    (hedgeBudget : (8 * (q.choose (r + 1) : ℝ) ^ 2 * N) ≤ δ ^ 2 * edgeCap) :
    ∃ C : ModularGeneratingData K D N,
      (∀ S : Block V r, (C.generators.filter fun Q => S.val ⊆ Q.val).card ≤ faceCap) ∧
      (∀ e : Block V (r + 1),
        (C.generators.filter fun Q => e.val ⊆ Q.val).card ≤ edgeCap) ∧
      C.generators.card ≤ N * K.card ∧
      (q.choose (r + 1) : ℝ) * C.saturated.card ≤ δ ^ 2 * μ * K.card / 2 ∧
      ((K \ C.good).card : ℝ) ≤ δ * K.card ∧
      ∀ e ∈ C.good,
        |(((D \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| < δ * μ := by
  have hτ : 0 < δ * μ / 2 := by positivity
  have hedge : ∀ e : Block V (r + 1),
      ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * μ :=
    clique_count_upper_of_relative_error K D hD hμ.le (by linarith only [hε, hδ1]) hcount
  obtain ⟨C, hF, hE, hsize, hsat, hdel, hgood⟩ :=
    exists_edge_capped_modular_generating_data N hN K D hD faceCap edgeCap
      hfaceCap hedgeCap hL (by positivity : 0 ≤ 2 * μ) hτ hface hedge hcount
  have hbudget : (q.choose (r + 1) : ℝ) * C.saturated.card ≤
      δ ^ 2 * μ * K.card / 2 := by
    have hupper := mul_le_mul_of_nonneg_left hsat (Nat.cast_nonneg (q.choose (r + 1)))
    have hb := face_edge_saturation_budget (v := (K.card : ℝ)) (Nat.cast_nonneg _) hμ.le
      (by exact_mod_cast hfaceCap : (0 : ℝ) < faceCap)
      (by exact_mod_cast hedgeCap : (0 : ℝ) < edgeCap) hfaceBudget hedgeBudget
    exact hupper.trans (by simpa only [Nat.cast_mul] using hb)
  refine ⟨C, hF, hE, hsize, hbudget, ?_, ?_⟩
  · apply hdel.trans
    apply (div_le_iff₀ hτ).mpr
    nlinarith only [hbudget]
  · intro e he
    apply (hgood e he).trans_le
    have hh := mul_le_mul_of_nonneg_right hε hμ.le
    linarith only [hh]

end Arxiv2411_18291
