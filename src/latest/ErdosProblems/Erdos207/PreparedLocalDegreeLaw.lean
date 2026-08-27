/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualLocalPolynomialBudget
import ErdosProblems.Erdos207.ResidualSupportedSubtype
import ErdosProblems.Erdos207.LocalForbiddenAuxiliary

/-! # Simultaneous actual auxiliary-degree inputs with the corrected reserve law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceAuxiliaryDegreeGood
    {Omega V : Type*} [DecidableEq V] [Fintype V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (q t : ℕ)
    (F : ℕ → ForbiddenFamilyOn V) (available old : Omega → TripleSystemOn V)
    (p : ℝ≥0) (y : ℕ → ℝ≥0) (omega : Omega) : Prop :=
  ∀ j ∈ Icc 4 q,
    (finiteHypergraphMaxDegree (finiteHypergraphOnSubset (available omega)
      (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) j)) : ℝ≥0) ≤
      ((t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient k.val j' 2 * y j') *
        (p ^ 3) ^ (j - 3) * ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3)

def sourceAllAuxiliaryDegreeFailure (q s t decay : ℕ) (C B : ℝ≥0) : ℝ≥0 :=
  (∑ j ∈ Icc 4 q, ∑ j' ∈ Icc j q, sourceLocalPolynomialTailCoefficient j' s C B) / (t : ℝ≥0) ^ decay

theorem IsResidualGraphStronglyWellDistributed.all_auxiliary_degree_failure_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V} {p C beta : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C beta)
    (q R s decay errorExponent t : ℕ) (priorCoefficient : ℝ≥0)
    (available : Omega → TripleSystemOn V) (F : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0)
    (ht : 1 ≤ t) (hN : Fintype.card V ≤ t ^ R) (hs : 3 * R + decay ≤ s)
    (hL : 3 * R + R * (3 * q) * s + decay ≤ errorExponent)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hy : ∀ j ∈ Icc 4 q, 1 ≤ y j)
    (hdensity : 1 ≤ p ^ 3 * (W.prefix k).terminalSize)
    (hbeta : beta ≤ priorCoefficient / (t : ℝ≥0) ^ errorExponent)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hF : ∀ j ∈ Icc 4 q, SourceVortexWellSpread (W.prefix k) j (F j) (y j) (z j))
    (hz : ∀ j ∈ Icc 4 q, ∀ j' ∈ Icc j q,
      z j' ≤ y j' * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L.SupportedOn (fun omega ↦
      (∀ U ∈ available omega, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available omega, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial omega ∪ later omega)).edgeSet))) :
    L.probability (fun omega ↦ ¬ sourceAuxiliaryDegreeGood W k q t F available
      (fun omega ↦ initial omega ∪ later omega) p y omega) ≤
        sourceAllAuxiliaryDegreeFailure q s t decay C priorCoefficient := by
  have hsingle : ∀ j ∈ Icc 4 q, L.probability (fun omega ↦
      ((t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient k.val j' 2 * y j') *
        (p ^ 3) ^ (j - 3) * ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3) <
      (finiteHypergraphMaxDegree (localForbiddenConfigurations ((Icc 4 q).biUnion F)
        (available omega) (initial omega ∪ later omega) j) : ℝ≥0)) ≤
      (∑ j' ∈ Icc j q, sourceLocalPolynomialTailCoefficient j' s C priorCoefficient) /
        (t : ℝ≥0) ^ decay := by
    intro j hj
    exact sourceResidualGraph_local_degree_polynomial_control L W k G initial later available F
      R s decay errorExponent t p C beta priorCoefficient y z ht hN hs hL hp hC (mem_Icc.mp hj).1
      (fun j' hj' ↦ hy j' (mem_Icc.mpr ⟨(mem_Icc.mp hj).1.trans (mem_Icc.mp hj').1, (mem_Icc.mp hj').2⟩))
      hdensity hbeta hnonempty hstrong hF (hz j hj) hgeometry
  simp only [sourceAuxiliaryDegreeGood, localForbiddenAuxiliary_maxDegree, not_forall, not_le, exists_prop] at *
  have hprob := L.probability_exists_le (Icc 4 q) (fun j omega ↦
    ((t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient k.val j' 2 * y j') *
      (p ^ 3) ^ (j - 3) * ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3) <
      (finiteHypergraphMaxDegree (localForbiddenConfigurations ((Icc 4 q).biUnion F)
        (available omega) (initial omega ∪ later omega) j) : ℝ≥0))
  have hsum := sum_le_sum (fun j hj ↦ hsingle j hj)
  simpa only [sourceAllAuxiliaryDegreeFailure, div_eq_mul_inv, sum_mul] using hprob.trans hsum

theorem IsResidualReserveStronglyWellDistributed.condition_auxiliary_degree_inputs
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V} {reserve : Omega → Finset (Sym2 V)} {p r C beta : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C beta)
    (q t : ℕ) (available : Omega → TripleSystemOn V) (F : ℕ → ForbiddenFamilyOn V) (y : ℕ → ℝ≥0)
    (error : ℝ≥0) (herror : error < 1)
    (hfailure : L.probability (fun omega ↦ ¬ sourceAuxiliaryDegreeGood W k q t F available
      (fun omega ↦ initial omega ∪ later omega) p y omega) ≤ error) :
    let Good := sourceAuxiliaryDegreeGood W k q t F available (fun omega ↦ initial omega ∪ later omega) p y
    ∃ hpos : 0 < L.probability Good,
      1 - error ≤ L.probability Good ∧
      IsResidualReserveStronglyWellDistributed (L.conditionSubtype Good hpos) W k G
        (fun x ↦ initial x.val) (fun x ↦ later x.val) (fun x ↦ reserve x.val)
        p r (C / (1 - error)) beta := by
  dsimp only
  let Good := sourceAuxiliaryDegreeGood W k q t F available (fun omega ↦ initial omega ∪ later omega) p y
  have hlower : 1 - error ≤ L.probability Good := by
    rw [L.probability_not Good] at hfailure
    exact tsub_le_iff_tsub_le.mp hfailure
  have hden : 0 < 1 - error := tsub_pos_iff_lt.mpr herror
  have hpos : 0 < L.probability Good := hden.trans_le hlower
  exact ⟨hpos, hlower, (hstrong.conditionSubtype Good hpos).mono
    (div_le_div_of_nonneg_left zero_le hden hlower) le_rfl⟩

end

end Erdos207
