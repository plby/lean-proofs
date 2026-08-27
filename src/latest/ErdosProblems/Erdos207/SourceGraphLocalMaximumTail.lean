/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGraphLocalDegreeTail
import ErdosProblems.Erdos207.FiniteHypergraphMaximumTail

/-! # Simultaneous local forbidden-degree control for the actual master law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceGraph_local_forbidden_maximum_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j j' s : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later available : Ω → TripleSystemOn V) (F : ForbiddenFamilyOn V)
    (p C b y z K : ℝ≥0) (hp : p ≤ 1) (hC : 1 ≤ C) (hK : 0 < K)
    (hnonempty : ∀ i, (W.U i).Nonempty) (hj : 4 ≤ j) (hjj : j ≤ j')
    (hstrong : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (hF : SourceVortexWellSpread (W.prefix k) j' F y z)
    (hz : z ≤ y * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L.SupportedOn (fun ω ↦
      (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω)).edgeSet))) :
    let kappa := sourceNibbleMomentCoefficient k.val j' 2 * y * p ^ (3 * (j - 3)) *
      ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3)
    L.probability (fun ω ↦ K ≤
      (finiteHypergraphMaxDegree (localForbiddenConfigurations F (available ω) (initial ω ∪ later ω) j) : ℝ≥0)) ≤
      (Fintype.card V : ℝ≥0) ^ 3 *
        ((2 * C) ^ (s * (3 * j')) *
          (((boundedIntersectionMomentCoefficient (3 * j') s : ℝ≥0) * kappa) / K) ^ s +
        ((2 * C) ^ (s * (3 * j')) * b) *
          (((2 ^ j' * (Fintype.card V + 1) ^ (3 * j') : ℕ) : ℝ≥0) / K) ^ s) := by
  classical
  dsimp only
  let kappa := sourceNibbleMomentCoefficient k.val j' 2 * y * p ^ (3 * (j - 3)) *
    ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3)
  let epsilon := (2 * C) ^ (s * (3 * j')) *
      (((boundedIntersectionMomentCoefficient (3 * j') s : ℝ≥0) * kappa) / K) ^ s +
    ((2 * C) ^ (s * (3 * j')) * b) *
      (((2 ^ j' * (Fintype.card V + 1) ^ (3 * j') : ℕ) : ℝ≥0) / K) ^ s
  have hmax := finiteHypergraphMaxDegree_probability_le L
    (fun ω ↦ localForbiddenConfigurations F (available ω) (initial ω ∪ later ω) j) K epsilon hK
    (fun T ↦ sourceGraph_local_forbidden_degree_tail (s := s) L W k G initial later available F
      p C b y z K hp hC hK hnonempty hj hjj hstrong hF hz hgeometry T)
  apply hmax.trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  have htri : Fintype.card (TripleOn V) ≤ Fintype.card V ^ 3 := by
    rw [show Fintype.card (TripleOn V) = Nat.choose (Fintype.card V) 3 from Fintype.card_finset_len 3]
    exact Nat.choose_le_pow _ _
  exact_mod_cast htri

end

end Erdos207
