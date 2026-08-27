/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationKernel

/-! # Uniformly controlled joint inclusion for the actual adaptive regularizer -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def regularizationBaseHazard
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G0 : Finset (Finset V)) (k : ℕ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ k * finiteHypergraphDegreeGap G0 / Nat.choose (Fintype.card V) (k - 1)

def regularizationPointHazard
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G0 : Finset (Finset V)) (k t : ℕ) : ℝ≥0 :=
  regularizationBaseHazard G0 k / (2 : ℝ≥0) ^ t

theorem RegularizationActive.edge_probability_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (hA : RegularizationActive G0 H0 b t S) (hk : 2 ≤ k) (E : UniformHyperedge V k) :
    uniformEdgeProbability (finiteHypergraphRegularizationWeight (regularizationCurrentFamily G0 S)) k E.1 ≤
      regularizationPointHazard G0 k t := by
  have hgap : (finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) : ℝ≥0) ≤
      (finiteHypergraphDegreeGap G0 : ℝ≥0) / (2 : ℝ≥0) ^ t := by
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) t)).mpr
    have hclock : (2 : ℝ≥0) ^ t * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤
        finiteHypergraphDegreeGap G0 := by exact_mod_cast hA.2.2.1
    simpa only [mul_comm] using hclock
  apply (uniformEdgeProbability_le
    (finiteHypergraphRegularizationWeight (regularizationCurrentFamily G0 S))
    (finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) (by omega)
    (by exact_mod_cast Nat.zero_lt_of_lt hA.2.1)
    (fun v ↦ (finiteHypergraphRegularizationWeight_bounds _ v).1)
    (fun v ↦ (finiteHypergraphRegularizationWeight_bounds _ v).2)
    (mem_powersetCard.mp E.2).2).trans
  calc
    _ ≤ ((2 : ℝ≥0) ^ k * ((finiteHypergraphDegreeGap G0 : ℝ≥0) / (2 : ℝ≥0) ^ t)) /
        Nat.choose (Fintype.card V) (k - 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap zero_le) zero_le
    _ = _ := by unfold regularizationPointHazard regularizationBaseHazard; ring

theorem regularizationKernel_joint_new_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (S : HypergraphRegularizationState V k) (U : Finset (UniformHyperedge V k))
    (hdis : Disjoint U S.1) :
    (regularizationKernel G0 H0 hGH hk hsize b t S).probability (fun S' ↦ U ⊆ S'.1) ≤
      setWeight (fun _ ↦ regularizationPointHazard G0 k t) U := by
  classical
  by_cases hA : RegularizationActive G0 H0 b t S
  · rw [regularizationKernel_active G0 H0 hGH hk hsize b t S hA, FiniteLaw.probability_map]
    let P := hypergraphRegularizationParameters (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S)
      (regularizationCurrentFamily_mono_base hGH S) hk (Nat.zero_lt_of_lt hA.2.1) hsize hA.2.2.2
    change P.law.probability _ ≤ _
    calc
      _ ≤ P.law.probability (fun ω ↦ ∀ E ∈ U, ω E = true) := by
        apply P.law.probability_mono
        intro ω hU E hE
        have hmem := regularizationBatchOutcome_added_subset
          (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S) S ω (hU hE)
        rcases mem_union.mp hmem with hold | hnew
        · exact (disjoint_left.mp hdis hE hold).elim
        · exact FiniteLaw.mem_selectedByBits_iff.mp hnew
      _ = ∏ E ∈ U, uniformEdgeProbability
          (finiteHypergraphRegularizationWeight (regularizationCurrentFamily G0 S)) k E.1 := by
        exact FiniteLaw.independentBits_probability_forall_true _ _ U
      _ ≤ _ := prod_le_prod' (fun E _hE ↦ hA.edge_probability_le hk E)
  · rw [regularizationKernel_inactive G0 H0 hGH hk hsize b t S hA, FiniteLaw.probability_pure]
    by_cases hU : U = ∅
    · simp [hU, setWeight]
    · have hnot : ¬ U ⊆ S.1 := by
        intro hsub
        obtain ⟨E, hE⟩ := nonempty_iff_ne_empty.mpr hU
        exact disjoint_left.mp hdis hE (hsub hE)
      rw [if_neg hnot]
      exact zero_le

theorem sum_inv_two_pow_le_two (t : ℕ) :
    ∑ i ∈ range t, ((2 : ℝ≥0) ^ i)⁻¹ ≤ 2 := by
  have heq : (∑ i ∈ range t, ((2 : ℝ≥0) ^ i)⁻¹) + 2 * ((2 : ℝ≥0) ^ t)⁻¹ = 2 := by
    induction t with
    | zero => norm_num
    | succ t ih =>
      have hhalf : (2 : ℝ≥0) * ((2 : ℝ≥0) ^ (t + 1))⁻¹ = ((2 : ℝ≥0) ^ t)⁻¹ := by
        rw [pow_succ, mul_inv_rev]
        field_simp
      rw [sum_range_succ, hhalf]
      calc
        _ = (∑ i ∈ range t, ((2 : ℝ≥0) ^ i)⁻¹) + 2 * ((2 : ℝ≥0) ^ t)⁻¹ := by ring
        _ = 2 := ih
  exact (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ 2 * ((2 : ℝ≥0) ^ t)⁻¹ from zero_le)).trans_eq heq

theorem cumulative_regularizationPointHazard_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G0 : Finset (Finset V)) (k t : ℕ) :
    (∑ i ∈ range t, regularizationPointHazard G0 k i) ≤ 2 * regularizationBaseHazard G0 k := by
  simp only [regularizationPointHazard, div_eq_mul_inv]
  rw [← mul_sum]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (sum_inv_two_pow_le_two t) (show 0 ≤ regularizationBaseHazard G0 k from zero_le)

theorem regularizationEvolve_joint_inclusion
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (U : Finset (UniformHyperedge V k)) :
    (FiniteLaw.evolveKernels (regularizationKernel G0 H0 hGH hk hsize b) t
      (FiniteLaw.pure (regularizationInitialState V k))).probability (fun S ↦ U ⊆ S.1) ≤
      (2 * regularizationBaseHazard G0 k) ^ U.card := by
  have h := evolveKernels_batch_joint_inclusion (regularizationKernel G0 H0 hGH hk hsize b)
    Prod.fst (fun t _ ↦ regularizationPointHazard G0 k t)
    (fun t S U hdis ↦ regularizationKernel_joint_new_le G0 H0 hGH hk hsize b t S U hdis)
    (regularizationInitialState V k) rfl t U
  apply h.trans
  unfold setWeight
  rw [← prod_const]
  exact prod_le_prod' (fun E _hE ↦ cumulative_regularizationPointHazard_le G0 k t)

end

end Erdos207
