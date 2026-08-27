/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalComposition
import ErdosProblems.Erdos207.StrongRootedThreatProbability
import ErdosProblems.Erdos207.CoverDownProbability

/-!
# Extracting a successful raw internal outcome

The updated strong law makes failure of the terminal rooted cap have
probability strictly below one.  A positive-mass rooted-good outcome lies in
the joint support; there the retrospective certificate rules out failure and
proves coverage of every residual scheduled edge.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsStronglyWellDistributed.exists_successful_rawResidualInternal_outcome
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {W : Vortex V ell} {level : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ}
    {initial later : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (i : Fin ell)
    (hstrong : IsStronglyWellDistributed
      (law.jointBind (rawResidualInternalKernel W i F G A P0 bits D)) W level
      (jointInitial initial)
      (jointLater later (rawResidualInternalAdded P0)) p C b)
    (Good : Omega → Prop)
    (hsupport :
      (law.jointBind
        (rawResidualInternalKernel W i F G A P0 bits D)).SupportedOn
          (fun z ↦ Good z.1 ∧
            RawResidualInternalOutcomeGood W i F G A P0 bits D R
              z.1 z.2))
    (hP0 : ∀ omega, Good omega →
      initial omega ∪ later omega = P0 omega)
    (hC : 1 ≤ C) {q s : ℕ}
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      b ≤ setWeight (masterUnionTriangleWeight W level p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W level p) kappa)
    (htail : strongRootedTail V C kappa R q s < 1) :
    ∃ z : Omega × InternalEdgeGreedyStateOn V,
      0 < ((law.jointBind
        (rawResidualInternalKernel W i F G A P0 bits D)).mass z) ∧
      Good z.1 ∧
      RawResidualInternalOutcomeGood W i F G A P0 bits D R z.1 z.2 ∧
      RootedActiveCapsGood F z.2.chosen R ∧
      z.2.failed = false ∧
      ∀ e ∈ preliminaryResidualInternalEdges
          (G z.1) (W.U i.succ) (P0 z.1),
        (coveredGraph z.2.chosen).Adj e.out.1 e.out.2 := by
  let K := rawResidualInternalKernel W i F G A P0 bits D
  let J := law.jointBind K
  let Accumulated : Omega × InternalEdgeGreedyStateOn V →
      TripleSystemOn V := fun z ↦
    jointInitial initial z ∪
      jointLater later (rawResidualInternalAdded P0) z
  have hbad : J.probability (fun z ↦
      ¬ RootedActiveCapsGood F (Accumulated z) R) ≤
      strongRootedTail V C kappa R q s := by
    simpa only [J, K, Accumulated] using
      hstrong.probability_not_rootedActiveCapsGood_le F R hC hFcard hb
        kappa hkappa
  have hbadlt : J.probability (fun z ↦
      ¬ RootedActiveCapsGood F (Accumulated z) R) < 1 :=
    hbad.trans_lt htail
  have hrootPos : 0 < J.probability (fun z ↦
      RootedActiveCapsGood F (Accumulated z) R) := by
    calc
      0 < 1 - J.probability (fun z ↦
          ¬ RootedActiveCapsGood F (Accumulated z) R) :=
        tsub_pos_iff_lt.mpr hbadlt
      _ = J.probability (fun z ↦
          ¬¬ RootedActiveCapsGood F (Accumulated z) R) :=
        (J.probability_not (fun z ↦
          ¬ RootedActiveCapsGood F (Accumulated z) R)).symm
      _ = J.probability (fun z ↦
          RootedActiveCapsGood F (Accumulated z) R) := by
        congr 1
        funext z
        simp
  obtain ⟨z, hrootAccumulated, hmass⟩ :=
    J.exists_of_probability_pos_with_mass hrootPos
  have hsupp := hsupport z (by simpa only [J, K] using hmass)
  have hsubset : P0 z.1 ⊆ z.2.chosen := hsupp.2.1.1.initial_subset
  have haccumulated : Accumulated z = z.2.chosen := by
    dsimp only [Accumulated, jointInitial, jointLater,
      rawResidualInternalAdded]
    rw [← union_assoc, hP0 z.1 hsupp.1]
    exact union_sdiff_of_subset hsubset
  have hroot : RootedActiveCapsGood F z.2.chosen R := by
    simpa only [haccumulated] using hrootAccumulated
  have hsuccess := hsupp.2.2.2.2.2 hroot
  refine ⟨z, by simpa only [J, K] using hmass, hsupp.1, hsupp.2,
    hroot, hsuccess.1, hsuccess.2⟩

end

end Erdos207
