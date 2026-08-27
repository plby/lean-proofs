/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGraphLocalMaximumTail
import ErdosProblems.Erdos207.LocalForbiddenUnion
import ErdosProblems.Erdos207.FiniteUnionMaximumTail

/-! # All original configuration orders in the actual local-degree tail -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceLocalDegreeTailBudget (ell j j' s N n : ℕ) (p C b y K : ℝ≥0) : ℝ≥0 :=
  let kappa := sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
    (n : ℝ≥0) ^ (j - 3)
  (N : ℝ≥0) ^ 3 *
    ((2 * C) ^ (s * (3 * j')) *
      (((boundedIntersectionMomentCoefficient (3 * j') s : ℝ≥0) * kappa) / K) ^ s +
    ((2 * C) ^ (s * (3 * j')) * b) *
      (((2 ^ j' * (N + 1) ^ (3 * j') : ℕ) : ℝ≥0) / K) ^ s)

theorem sourceGraph_all_local_forbidden_maximum_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j q s : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later available : Ω → TripleSystemOn V) (F : ℕ → ForbiddenFamilyOn V)
    (p C b : ℝ≥0) (y z K : ℕ → ℝ≥0) (hp : p ≤ 1) (hC : 1 ≤ C)
    (hK : ∀ j' ∈ Icc j q, 0 < K j')
    (hnonempty : ∀ i, (W.U i).Nonempty) (hj : 4 ≤ j)
    (hstrong : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (hF : ∀ j' ∈ Icc 4 q, SourceVortexWellSpread (W.prefix k) j' (F j') (y j') (z j'))
    (hz : ∀ j' ∈ Icc j q, z j' ≤ y j' * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L.SupportedOn (fun ω ↦
      (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω)).edgeSet))) :
    L.probability (fun ω ↦ (∑ j' ∈ Icc j q, K j') <
      (finiteHypergraphMaxDegree (localForbiddenConfigurations ((Icc 4 q).biUnion F)
        (available ω) (initial ω ∪ later ω) j) : ℝ≥0)) ≤
      ∑ j' ∈ Icc j q, sourceLocalDegreeTailBudget k.val j j' s (Fintype.card V)
        (W.prefix k).terminalSize p C b (y j') (K j') := by
  classical
  have hrepr (ω : Ω) := localForbiddenConfigurations_order_union F (available ω)
    (initial ω ∪ later ω) j q hj (fun j' hj' E hE ↦ (hF j' hj').uniform E hE |>.1)
  simp_rw [hrepr]
  apply finiteHypergraphMaxDegree_biUnion_probability_le L (Icc j q)
    (fun j' ω ↦ localForbiddenConfigurations (F j') (available ω) (initial ω ∪ later ω) j) K
  intro j' hj'
  have hj'4q : j' ∈ Icc 4 q := mem_Icc.mpr
    ⟨hj.trans (mem_Icc.mp hj').1, (mem_Icc.mp hj').2⟩
  exact sourceGraph_local_forbidden_maximum_tail (s := s) L W k G initial later available
    (F j') p C b (y j') (z j') (K j') hp hC (hK j' hj') hnonempty hj
    (mem_Icc.mp hj').1 hstrong (hF j' hj'4q) (hz j' hj') hgeometry

end

end Erdos207
