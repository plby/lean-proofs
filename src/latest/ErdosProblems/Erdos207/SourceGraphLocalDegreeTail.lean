/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalForbiddenDegreeDomination
import ErdosProblems.Erdos207.SourceNibbleMaximumWeight
import ErdosProblems.Erdos207.AdditiveConfigurationMoment

/-! # The actual local forbidden-degree tail under a graph-restricted law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceGraph_local_forbidden_degree_tail
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
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω)).edgeSet)))
    (T : TripleOn V) :
    let kappa := sourceNibbleMomentCoefficient k.val j' 2 * y * p ^ (3 * (j - 3)) *
      ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3)
    L.probability (fun ω ↦ K ≤
      (finiteHypergraphDegree (localForbiddenConfigurations F (available ω) (initial ω ∪ later ω) j) T : ℝ≥0)) ≤
      (2 * C) ^ (s * (3 * j')) *
        (((boundedIntersectionMomentCoefficient (3 * j') s : ℝ≥0) * kappa) / K) ^ s +
      ((2 * C) ^ (s * (3 * j')) * b) *
        (((2 ^ j' * (Fintype.card V + 1) ^ (3 * j') : ℕ) : ℝ≥0) / K) ^ s := by
  classical
  dsimp only
  let codes := sourceNibbleCodes (W.prefix k) F T j j'
  let coords := fun x : codes ↦ sourceNibbleCoordinates T x.1
  let R := sourceGraphMixedSelected G initial later
  let X := fun ω ↦ (finiteHypergraphDegree
    (localForbiddenConfigurations F (available ω) (initial ω ∪ later ω) j) T : ℝ≥0)
  let kappa := sourceNibbleMomentCoefficient k.val j' 2 * y * p ^ (3 * (j - 3)) *
    ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3)
  have hdom : L.SupportedOn (fun ω ↦ X ω ≤ selectedCount coords (R ω)) := by
    intro ω hω
    have hg := hgeometry ω hω
    exact localForbidden_degree_le_selectedCount (W.prefix k) F G (available ω) (initial ω) (later ω)
      (fun E hE ↦ (hF.uniform E hE).1) hj hjj hg.1 hg.2 T
  have hcard : ∀ x : codes, (coords x).card ≤ 3 * j' := fun x ↦
    sourceNibbleCoordinates_card_le (fun E hE ↦ (hF.uniform E hE).1)
      (fun E hE ↦ (hF.uniform E hE).2) hj hjj x.2
  have hkappa : HasExtensionBound coords (sourceNibbleMixedWeight (W.prefix k) 2 p) kappa :=
    hF.nibble_mixed_hasExtensionBound T j hj hjj 2 p (by norm_num) hp hz
  have htail := dominatedConfigurationTailBound_additive L coords R X
    (sourceNibbleMixedWeight (W.prefix k) 2 p)
    ((2 * C) ^ (s * (3 * j'))) ((2 * C) ^ (s * (3 * j')) * b) kappa K
    hdom hcard hkappa hK
    (fun A hA ↦ hstrong.mixed_bounded_joint_inclusion hp hC hnonempty (s * (3 * j')) A hA)
  apply htail.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  have hcount := card_sourceNibbleCodes_le_polynomial (W.prefix k) F T j j'
    (fun E hE ↦ (hF.uniform E hE).1)
  dsimp [codes]
  rw [Fintype.card_coe]
  exact_mod_cast hcount

end

end Erdos207
