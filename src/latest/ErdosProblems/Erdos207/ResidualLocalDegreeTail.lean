/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphMixedLaw
import ErdosProblems.Erdos207.SourceGraphAllLocalDegrees

/-! # Local-degree tails with edges residual after the full selected family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceResidualGraph_local_forbidden_degree_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j j' s : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later available : Ω → TripleSystemOn V) (F : ForbiddenFamilyOn V)
    (p C b y z K : ℝ≥0) (hp : p ≤ 1) (hC : 1 ≤ C) (hK : 0 < K)
    (hnonempty : ∀ i, (W.U i).Nonempty) (hj : 4 ≤ j) (hjj : j ≤ j')
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hF : SourceVortexWellSpread (W.prefix k) j' F y z)
    (hz : z ≤ y * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L.SupportedOn (fun ω ↦
      (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω ∪ later ω)).edgeSet)))
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
  let R := residualGraphMixedSelected G initial later
  let X := fun ω ↦ (finiteHypergraphDegree
    (localForbiddenConfigurations F (available ω) (initial ω ∪ later ω) j) T : ℝ≥0)
  let kappa := sourceNibbleMomentCoefficient k.val j' 2 * y * p ^ (3 * (j - 3)) *
    ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3)
  have hdom : L.SupportedOn (fun ω ↦ X ω ≤ selectedCount coords (R ω)) := by
    intro ω hω
    have hg := hgeometry ω hω
    simpa only [X, coords, R, union_empty, sourceGraphMixedSelected, residualGraphMixedSelected] using
      localForbidden_degree_le_selectedCount (W.prefix k) F G (available ω) (initial ω ∪ later ω) ∅
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


theorem sourceResidualGraph_local_forbidden_maximum_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j j' s : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later available : Ω → TripleSystemOn V) (F : ForbiddenFamilyOn V)
    (p C b y z K : ℝ≥0) (hp : p ≤ 1) (hC : 1 ≤ C) (hK : 0 < K)
    (hnonempty : ∀ i, (W.U i).Nonempty) (hj : 4 ≤ j) (hjj : j ≤ j')
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hF : SourceVortexWellSpread (W.prefix k) j' F y z)
    (hz : z ≤ y * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L.SupportedOn (fun ω ↦
      (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω ∪ later ω)).edgeSet))) :
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
    (fun T ↦ sourceResidualGraph_local_forbidden_degree_tail (s := s) L W k G initial later available F
      p C b y z K hp hC hK hnonempty hj hjj hstrong hF hz hgeometry T)
  apply hmax.trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  have htri : Fintype.card (TripleOn V) ≤ Fintype.card V ^ 3 := by
    rw [show Fintype.card (TripleOn V) = Nat.choose (Fintype.card V) 3 from Fintype.card_finset_len 3]
    exact Nat.choose_le_pow _ _
  exact_mod_cast htri


theorem sourceResidualGraph_all_local_forbidden_maximum_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j q s : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later available : Ω → TripleSystemOn V) (F : ℕ → ForbiddenFamilyOn V)
    (p C b : ℝ≥0) (y z K : ℕ → ℝ≥0) (hp : p ≤ 1) (hC : 1 ≤ C)
    (hK : ∀ j' ∈ Icc j q, 0 < K j')
    (hnonempty : ∀ i, (W.U i).Nonempty) (hj : 4 ≤ j)
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hF : ∀ j' ∈ Icc 4 q, SourceVortexWellSpread (W.prefix k) j' (F j') (y j') (z j'))
    (hz : ∀ j' ∈ Icc j q, z j' ≤ y j' * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize)
    (hgeometry : L.SupportedOn (fun ω ↦
      (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
      (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω ∪ later ω)).edgeSet))) :
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
  exact sourceResidualGraph_local_forbidden_maximum_tail (s := s) L W k G initial later available
    (F j') p C b (y j') (z j') (K j') hp hC (hK j' hj') hnonempty hj
    (mem_Icc.mp hj').1 hstrong (hF j' hj'4q) (hz j' hj') hgeometry


end

end Erdos207
