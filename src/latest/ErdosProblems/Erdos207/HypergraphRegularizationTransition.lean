/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphDegrees
import ErdosProblems.Erdos207.WeightedRegularizationStep

/-! # Degree-gap contraction and the bounded-degree potential for actual hypergraphs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem finiteHypergraphDegree_union_sample
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G H : Finset (Finset V)) (hGH : G ⊆ H) (ω : UniformHyperedge V k → Bool) (v : V) :
    finiteHypergraphDegree (G ∪ sampledFreshUniformHypergraph H ω) v =
      finiteHypergraphDegree G v + sampledFreshUniformDegree H v ω := by
  rw [finiteHypergraphDegree_union G _
    ((sampledFreshUniformHypergraph_disjoint H ω).mono_right hGH).symm]
  simp only [finiteHypergraphDegree, sampledFreshUniformHypergraph_degree]

theorem hypergraph_degree_gap_lt_of_step_good
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G H : Finset (Finset V)) (hGH : G ⊆ H) (a : ℕ)
    (ω : UniformHyperedge V k → Bool)
    (hgood : WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v) a H ω) :
    (finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) : ℝ) < (a : ℝ) / 2 := by
  let G' := G ∪ sampledFreshUniformHypergraph H ω
  obtain ⟨v, _hv, hmax⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty (finiteHypergraphDegree G')
  obtain ⟨u, _hu, hmin⟩ := exists_mem_eq_inf' (s := (univ : Finset V)) univ_nonempty
    (finiteHypergraphDegree G')
  have hpair := hgood.1 v u
  have hv := finiteHypergraphDegree_union_sample G H hGH ω v
  have hu := finiteHypergraphDegree_union_sample G H hGH ω u
  have hpair' : |(finiteHypergraphDegree G' v : ℝ) - finiteHypergraphDegree G' u| < (a : ℝ) / 2 := by
    simpa only [G', hv, hu, Nat.cast_add, NNReal.coe_natCast] using hpair
  change finiteHypergraphMaxDegree G' = finiteHypergraphDegree G' v at hmax
  change finiteHypergraphMinDegree G' = finiteHypergraphDegree G' u at hmin
  rw [← hmax, ← hmin] at hpair'
  have horder := finiteHypergraphMinDegree_le_max G'
  have horderReal : (finiteHypergraphMinDegree G' : ℝ) ≤ finiteHypergraphMaxDegree G' := by
    exact_mod_cast horder
  rw [abs_of_nonneg (sub_nonneg.mpr horderReal), ← Nat.cast_sub horder] at hpair'
  exact hpair'

theorem hypergraph_max_degree_le_of_step_good
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G H : Finset (Finset V)) (hGH : G ⊆ H) (a : ℕ)
    (ω : UniformHyperedge V k → Bool)
    (hgood : WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v) a H ω) :
    finiteHypergraphMaxDegree (G ∪ sampledFreshUniformHypergraph H ω) ≤
      finiteHypergraphMaxDegree G + 4 * a := by
  apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
  intro v
  have hinc : sampledFreshUniformDegree H v ω ≤ 4 * a := by
    exact_mod_cast hgood.2 v
  rw [finiteHypergraphDegree_union_sample G H hGH ω v]
  exact Nat.add_le_add (finiteHypergraphDegree_le_max G v) hinc

theorem hypergraph_regularization_potential_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G H : Finset (Finset V)) (hGH : G ⊆ H)
    (ω : UniformHyperedge V k → Bool)
    (hgood : WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v)
      (finiteHypergraphDegreeGap G) H ω) :
    finiteHypergraphMaxDegree (G ∪ sampledFreshUniformHypergraph H ω) +
      8 * finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) ≤
        finiteHypergraphMaxDegree G + 8 * finiteHypergraphDegreeGap G := by
  have hgap := hypergraph_degree_gap_lt_of_step_good G H hGH (finiteHypergraphDegreeGap G) ω hgood
  have hhalf : 2 * finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) ≤
      finiteHypergraphDegreeGap G := by
    exact_mod_cast (show (2 : ℝ) * finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) ≤
      finiteHypergraphDegreeGap G by linarith)
  have hmax := hypergraph_max_degree_le_of_step_good G H hGH (finiteHypergraphDegreeGap G) ω hgood
  omega

theorem hypergraph_regularization_forbidden_potential_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G H : Finset (Finset V)) (hGH : G ⊆ H)
    (ω : UniformHyperedge V k → Bool)
    (hgood : WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v)
      (finiteHypergraphDegreeGap G) H ω) :
    finiteHypergraphMaxDegree (H ∪ sampledFreshUniformHypergraph H ω) +
      8 * finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) ≤
        finiteHypergraphMaxDegree H + 8 * finiteHypergraphDegreeGap G := by
  have hgap := hypergraph_degree_gap_lt_of_step_good G H hGH (finiteHypergraphDegreeGap G) ω hgood
  have hhalf : 2 * finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) ≤
      finiteHypergraphDegreeGap G := by
    exact_mod_cast (show (2 : ℝ) * finiteHypergraphDegreeGap (G ∪ sampledFreshUniformHypergraph H ω) ≤
      finiteHypergraphDegreeGap G by linarith)
  have hmax : finiteHypergraphMaxDegree (H ∪ sampledFreshUniformHypergraph H ω) ≤
      finiteHypergraphMaxDegree H + 4 * finiteHypergraphDegreeGap G := by
    apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
    intro v
    have hinc : sampledFreshUniformDegree H v ω ≤ 4 * finiteHypergraphDegreeGap G := by
      exact_mod_cast hgood.2 v
    rw [finiteHypergraphDegree_union_sample H H Subset.rfl ω v]
    exact Nat.add_le_add (finiteHypergraphDegree_le_max H v) hinc
  omega

end

end Erdos207
