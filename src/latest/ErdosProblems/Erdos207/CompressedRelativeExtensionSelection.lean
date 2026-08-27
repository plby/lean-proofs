/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterLawCompression
import ErdosProblems.Erdos207.StrongRelativeExtension
import ErdosProblems.Erdos207.DependentSigmaExtension

/-!
# Selecting a pointwise-good master state with relative extension bounds

The compressed law is used once more before the last cover-down stage.  A
union bound selects a positive-mass state which is simultaneously pointwise
good and has the required extension estimate after deleting its old packing.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsCompressedMasterLaw.exists_supported_pointwise_relativeExtensionBound
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {ell : ℕ} {law : FiniteLaw (MasterStateOn V)}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V} {p eta xi C b : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (hC : 1 ≤ C) (d : ℕ)
    (configurations : I → TripleSystemOn V)
    (hcard : ∀ a, (configurations a).card ≤ d)
    (hb : ∀ S : TripleSystemOn V, S.card ≤ d →
      b ≤ setWeight (masterUnionTriangleWeight W k p) S)
    (sigma : TripleOn V → ℝ≥0) (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound configurations
      (fun T ↦ masterUnionTriangleWeight W k p T + sigma T) kappa)
    (hkappaOut : 0 < kappaOut)
    (hsmall : xi + (configurationRoots configurations).card *
      (((2 * (2 * C) ^ d) * kappa) / kappaOut) < 1) :
    ∃ state : MasterStateOn V,
      0 < law.mass state ∧
      IsMasterStagePointwiseGood W k F state.graph state.available
        state.initial state.later p eta xi h ∧
      HasExtensionBound
        (fun a ↦ configurations a \ (state.initial ∪ state.later))
        sigma kappaOut := by
  let PointGood : MasterStateOn V → Prop := fun state ↦
    IsMasterStagePointwiseGood W k F state.graph state.available
      state.initial state.later p eta xi h
  let RelativeGood : MasterStateOn V → Prop := fun state ↦
    HasExtensionBound
      (fun a ↦ configurations a \ (state.initial ∪ state.later))
      sigma kappaOut
  have hpointBad : law.probability (fun state ↦ ¬ PointGood state) ≤ xi := by
    rw [law.probability_not PointGood]
    exact tsub_le_iff_tsub_le.mp hmaster.1.2.2
  have hjoint : ∀ S : TripleSystemOn V, S.card ≤ d →
      law.probability
          (fun state ↦ S ⊆ state.initial ∪ state.later) ≤
        (2 * (2 * C) ^ d) *
          setWeight (masterUnionTriangleWeight W k p) S := by
    intro S hSd
    exact hmaster.1.2.1.probability_subset_union_le_product
      hC S hSd (hb S hSd)
  have hrelativeBad : law.probability (fun state ↦ ¬ RelativeGood state) ≤
      (configurationRoots configurations).card *
        (((2 * (2 * C) ^ d) * kappa) / kappaOut) := by
    simpa only [RelativeGood] using
      law.probability_not_relativeExtensionBound_le_of_joint
        (fun state ↦ state.initial ∪ state.later)
        configurations (masterUnionTriangleWeight W k p) sigma
        (2 * (2 * C) ^ d) d hcard hjoint kappa kappaOut hkappa hkappaOut
  let Good : MasterStateOn V → Prop := fun state ↦
    PointGood state ∧ RelativeGood state
  have hbad : law.probability (fun state ↦ ¬ Good state) < 1 := by
    calc
      law.probability (fun state ↦ ¬ Good state) =
          law.probability (fun state ↦
            ¬ PointGood state ∨ ¬ RelativeGood state) := by
        congr 1
        funext state
        simp only [Good, not_and_or]
      _ ≤ law.probability (fun state ↦ ¬ PointGood state) +
          law.probability (fun state ↦ ¬ RelativeGood state) :=
        law.probability_or_le _ _
      _ ≤ xi + (configurationRoots configurations).card *
          (((2 * (2 * C) ^ d) * kappa) / kappaOut) :=
        add_le_add hpointBad hrelativeBad
      _ < 1 := hsmall
  have hgoodPos : 0 < law.probability Good := by
    calc
      0 < 1 - law.probability (fun state ↦ ¬ Good state) :=
        tsub_pos_iff_lt.mpr hbad
      _ = law.probability (fun state ↦ ¬¬ Good state) :=
        (law.probability_not (fun state ↦ ¬ Good state)).symm
      _ = law.probability Good := by
        congr 1
        funext state
        simp
  obtain ⟨state, hmass, hgood⟩ := law.exists_supported_of_probability_pos hgoodPos
  exact ⟨state, hmass, hgood⟩

/-- After the last genuinely random master transition, a positive-mass
pointwise-good state may be frozen.  The resulting one-point law retains all
deterministic compressed-master invariants.  We deliberately use additive
error one: this is the coarse endpoint needed by the terminal cover-down, and
it makes strong well-distributedness automatic for the deterministic law. -/
theorem IsCompressedMasterLaw.pure_of_supported_pointwise
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw (MasterStateOn V)}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V} {p eta xi C b : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (state : MasterStateOn V) (hmass : 0 < law.mass state)
    (hpoint : IsMasterStagePointwiseGood W k F state.graph state.available
      state.initial state.later p eta xi h) :
    IsCompressedMasterLaw (FiniteLaw.pure state) W k F Gzero ambient
      p eta xi 1 1 h := by
  classical
  have hstrong : IsStronglyWellDistributed (FiniteLaw.pure state) W k
      MasterStateOn.initial MasterStateOn.later p 1 1 := by
    intro Ifix Dfix Efix _hdisjoint
    calc
      (FiniteLaw.pure state).probability
          (StrongDistributionEvent MasterStateOn.initial
            MasterStateOn.later Ifix Dfix Efix) ≤ 1 :=
        (FiniteLaw.pure state).probability_le_one _
      _ ≤ 1 ^ (Ifix.card + Dfix.card + Efix.card) *
          (p ^ Efix.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p Dfix + 1) := by simp
  have hgood : IsMasterIterationGood (FiniteLaw.pure state) W k F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi 1 1 h := by
    refine ⟨FiniteLaw.supportedOn_pure _ (hmaster.1.1 state hmass),
      hstrong, ?_⟩
    rw [FiniteLaw.probability_pure]
    simp only [hpoint, if_pos]
    exact tsub_le_self
  exact ⟨hgood,
    FiniteLaw.supportedOn_pure _ (hmaster.2.1 state hmass),
    FiniteLaw.supportedOn_pure _ (hmaster.2.2.1 state hmass),
    FiniteLaw.supportedOn_pure _ (hmaster.2.2.2.1 state hmass),
    FiniteLaw.supportedOn_pure _ (hmaster.2.2.2.2.1 state hmass),
    FiniteLaw.supportedOn_pure _ (hmaster.2.2.2.2.2 state hmass)⟩

end

end Erdos207
