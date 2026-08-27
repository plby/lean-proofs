/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualLocalDegreeControl
import ErdosProblems.Erdos207.FiniteMomentPolynomialBudget

/-! # Local regularization inputs with polynomial, rather than geometric, prior errors -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceLocalPolynomialTailCoefficient (j' s : ℕ) (C B : ℝ≥0) : ℝ≥0 :=
  (2 * C) ^ (s * (3 * j')) *
    ((boundedIntersectionMomentCoefficient (3 * j') s : ℝ≥0) ^ s +
      B * ((2 ^ j' * 2 ^ (3 * j') : ℕ) : ℝ≥0) ^ s)

theorem sourceLocalDegreeTailBudget_polynomial_prior
    (ell j j' R s c L t N n : ℕ) (p C b y K B : ℝ≥0)
    (ht : 1 ≤ t) (hN : N ≤ t ^ R) (hs : 3 * R + c ≤ s)
    (hL : 3 * R + R * (3 * j') * s + c ≤ L)
    (hK : (t : ℝ≥0) * (sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
      (n : ℝ≥0) ^ (j - 3)) ≤ K) (hK1 : 1 ≤ K) (hb : b ≤ B / (t : ℝ≥0) ^ L) :
    sourceLocalDegreeTailBudget ell j j' s N n p C b y K ≤
      sourceLocalPolynomialTailCoefficient j' s C B / (t : ℝ≥0) ^ c := by
  let A := (2 * C) ^ (s * (3 * j'))
  let M : ℝ≥0 := boundedIntersectionMomentCoefficient (3 * j') s
  let Q : ℝ≥0 := (2 ^ j' * 2 ^ (3 * j') : ℕ)
  let count : ℝ≥0 := (2 ^ j' * (N + 1) ^ (3 * j') : ℕ)
  let kappa := sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
    (n : ℝ≥0) ^ (j - 3)
  have hcard : (Fintype.card (Fin (N ^ 3)) : ℝ≥0) ≤ 1 * (t : ℝ≥0) ^ (3 * R) := by
    have hn : N ^ 3 ≤ t ^ (3 * R) := by
      simpa only [← pow_mul, Nat.mul_comm R 3] using Nat.pow_le_pow_left hN 3
    simpa only [Fintype.card_fin, one_mul] using (show ((N ^ 3 : ℕ) : ℝ≥0) ≤
      (t : ℝ≥0) ^ (3 * R) by exact_mod_cast hn)
  have hcount : count ≤ Q * (t : ℝ≥0) ^ (R * (3 * j')) := by
    dsimp only [count, Q]
    exact_mod_cast sourceNibbleWitnessBound_le_power N t R j' ht hN
  have herror : A * b ≤ A * B / (t : ℝ≥0) ^ L := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb (show 0 ≤ A from zero_le)
  have h := finiteMoment_polynomial_prior_error_budget (I := Fin (N ^ 3))
    (fun _ ↦ 3 * j') (fun _ ↦ kappa) (fun _ ↦ count) (fun _ ↦ K)
    s (3 * R) c (R * (3 * j')) L t A (A * b) 1 M Q B
    (by exact_mod_cast ht) hs hL hcard (fun _ ↦ hK) (fun _ ↦ hK1)
    (fun _ ↦ le_rfl) (fun _ ↦ hcount) herror
  simpa only [sourceLocalDegreeTailBudget, sourceLocalPolynomialTailCoefficient, sourceMomentTailExpression,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, one_mul,
    A, M, Q, count, kappa] using h

theorem sourceLocalDegreeCanonicalTail_polynomial_prior
    (ell j j' R s c L t N n : ℕ) (p C b y B : ℝ≥0)
    (ht : 1 ≤ t) (hN : N ≤ t ^ R) (hs : 3 * R + c ≤ s)
    (hL : 3 * R + R * (3 * j') * s + c ≤ L)
    (hy : 1 ≤ y) (hdensity : 1 ≤ p ^ 3 * n) (hb : b ≤ B / (t : ℝ≥0) ^ L) :
    sourceLocalDegreeTailBudget ell j j' s N n p C b y
      (sourceLocalDegreeCutoff ell j j' t n p y) ≤
        sourceLocalPolynomialTailCoefficient j' s C B / (t : ℝ≥0) ^ c :=
  sourceLocalDegreeTailBudget_polynomial_prior ell j j' R s c L t N n p C b y _ B
    ht hN hs hL le_rfl (sourceLocalDegreeCutoff_one_le ell j j' t n p y ht hy hdensity) hb

theorem sourceResidualGraph_local_degree_polynomial_control
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j q : ℕ}
    (L₀ : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later available : Ω → TripleSystemOn V) (F : ℕ → ForbiddenFamilyOn V)
    (R s c L t : ℕ) (p C b B : ℝ≥0) (y z : ℕ → ℝ≥0)
    (ht : 1 ≤ t) (hN : Fintype.card V ≤ t ^ R) (hs : 3 * R + c ≤ s)
    (hL : 3 * R + R * (3 * q) * s + c ≤ L)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hj : 4 ≤ j)
    (hy : ∀ j' ∈ Icc j q, 1 ≤ y j') (hdensity : 1 ≤ p ^ 3 * (W.prefix k).terminalSize)
    (hb : b ≤ B / (t : ℝ≥0) ^ L) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hstrong : IsResidualGraphStronglyWellDistributed L₀ W k G initial later p C b)
    (hF : ∀ j' ∈ Icc 4 q, SourceVortexWellSpread (W.prefix k) j' (F j') (y j') (z j'))
    (hz : ∀ j' ∈ Icc j q, z j' ≤ y j' * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L₀.SupportedOn (fun ω ↦
      (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω ∪ later ω)).edgeSet))) :
    L₀.probability (fun ω ↦
      ((t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient k.val j' 2 * y j') *
        (p ^ 3) ^ (j - 3) * ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3) <
      (finiteHypergraphMaxDegree (localForbiddenConfigurations ((Icc 4 q).biUnion F)
        (available ω) (initial ω ∪ later ω) j) : ℝ≥0)) ≤
      (∑ j' ∈ Icc j q, sourceLocalPolynomialTailCoefficient j' s C B) / (t : ℝ≥0) ^ c := by
  let K := fun j' ↦ sourceLocalDegreeCutoff k.val j j' t (W.prefix k).terminalSize p (y j')
  have hK : ∀ j' ∈ Icc j q, 0 < K j' := fun j' hj' ↦ zero_lt_one.trans_le
    (sourceLocalDegreeCutoff_one_le k.val j j' t (W.prefix k).terminalSize p (y j') ht (hy j' hj') hdensity)
  have hprob := sourceResidualGraph_all_local_forbidden_maximum_tail (s := s) L₀ W k G initial later
    available F p C b y z K hp hC hK hnonempty hj hstrong hF hz hgeometry
  have hbudget : (∑ j' ∈ Icc j q, sourceLocalDegreeTailBudget k.val j j' s (Fintype.card V)
      (W.prefix k).terminalSize p C b (y j') (K j')) ≤
      (∑ j' ∈ Icc j q, sourceLocalPolynomialTailCoefficient j' s C B) / (t : ℝ≥0) ^ c := by
    simp only [div_eq_mul_inv, sum_mul]
    apply sum_le_sum
    intro j' hj'
    have hle : 3 * R + R * (3 * j') * s + c ≤ L := by
      apply le_trans _ hL
      have hjq := (mem_Icc.mp hj').2
      gcongr
    exact sourceLocalDegreeCanonicalTail_polynomial_prior k.val j j' R s c L t (Fintype.card V)
      (W.prefix k).terminalSize p C b (y j') B ht hN hs hle (hy j' hj') hdensity hb
  have hsum := sourceLocalDegreeCutoff_sum k.val j q t (W.prefix k).terminalSize p y
  change (∑ j' ∈ Icc j q, K j') = _ at hsum
  rw [hsum] at hprob
  exact hprob.trans hbudget

end

end Erdos207
