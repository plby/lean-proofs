/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInvariant
import ErdosProblems.Erdos207.RegularizationKernelFailure

/-! # The full finite adaptive regularization horizon -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem regularizationEvolve_supported_invariant
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) (b t : ℕ) :
    (FiniteLaw.evolveKernels (regularizationKernel G0 H0 hGH hk hsize b) t
      (FiniteLaw.pure (regularizationInitialState V k))).SupportedOn (RegularizationInvariant G0 H0 b t) := by
  induction t with
  | zero => exact FiniteLaw.supportedOn_pure _ (regularizationInvariant_initial G0 H0 b)
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ]
      exact ih.bind _ (fun S hS ↦ hS.kernel_supported hGH hk hsize hdensity)

theorem RegularizationInvariant.terminal_gap_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b (finiteHypergraphDegreeGap G0) S) (hf : S.2 = false) :
    finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤ b := by
  by_contra hbad
  have hlarge : b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) := lt_of_not_ge hbad
  have hclock := h.clock hf hlarge
  have hpos : 0 < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) := Nat.zero_lt_of_lt hlarge
  have hpowle : 2 ^ finiteHypergraphDegreeGap G0 ≤
      2 ^ finiteHypergraphDegreeGap G0 * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) :=
    Nat.le_mul_of_pos_right _ hpos
  exact (finiteHypergraphDegreeGap G0).lt_two_pow_self.not_ge (hpowle.trans hclock)

theorem RegularizationInvariant.max_degree_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) :
    finiteHypergraphMaxDegree (regularizationCurrentFamily G0 S) ≤ 9 * finiteHypergraphMaxDegree G0 := by
  have hgap : finiteHypergraphDegreeGap G0 ≤ finiteHypergraphMaxDegree G0 := Nat.sub_le _ _
  have := h.graph_potential
  omega

def regularizationProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V) (b : ℕ) :
    FiniteLaw (HypergraphRegularizationState V k) :=
  FiniteLaw.evolveKernels (regularizationKernel G0 H0 hGH hk hsize b) (finiteHypergraphDegreeGap G0)
    (FiniteLaw.pure (regularizationInitialState V k))

theorem regularizationProcessLaw_avoids_and_bounded
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) (b : ℕ) :
    (regularizationProcessLaw G0 H0 hGH hk hsize b).SupportedOn (fun S ↦
      Disjoint (regularizationAcceptedEdges S) H0 ∧
      (∀ E ∈ regularizationAcceptedEdges S, E.card = k) ∧
      finiteHypergraphMaxDegree (regularizationCurrentFamily G0 S) ≤ 9 * finiteHypergraphMaxDegree G0) := by
  intro S hS
  have hInv := regularizationEvolve_supported_invariant G0 H0 hGH hk hsize hdensity b
    (finiteHypergraphDegreeGap G0) S hS
  exact ⟨hInv.avoid, regularizationAcceptedEdges_uniform S, hInv.max_degree_le⟩

theorem regularizationProcessLaw_gap_failure
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) (b : ℕ) :
    ((regularizationProcessLaw G0 H0 hGH hk hsize b).probability
      (fun S ↦ b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) : ℝ) ≤
      finiteHypergraphDegreeGap G0 * (2 * Fintype.card V * Real.exp (-(b : ℝ) / 8192)) := by
  let L := regularizationProcessLaw G0 H0 hGH hk hsize b
  have hmono : L.probability (fun S ↦ b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) ≤
      L.probability (fun S ↦ S.2 = true) := by
    apply L.probability_mono_of_supported
      (regularizationEvolve_supported_invariant G0 H0 hGH hk hsize hdensity b (finiteHypergraphDegreeGap G0))
    intro S hInv hbad
    by_contra hf
    have hfalse : S.2 = false := by cases h : S.2 <;> simp_all
    exact (not_lt_of_ge (hInv.terminal_gap_le hfalse)) hbad
  have hmonoReal : (L.probability (fun S ↦ b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) : ℝ) ≤
      (L.probability (fun S ↦ S.2 = true) : ℝ) := by exact_mod_cast hmono
  exact hmonoReal.trans (regularizationEvolve_failure_le G0 H0 hGH hk hsize b (finiteHypergraphDegreeGap G0))

end

end Erdos207
