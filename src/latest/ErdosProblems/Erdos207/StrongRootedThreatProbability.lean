/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributedUnion
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Rooted-active tails from strong well-distributedness

The union joint-inclusion estimate supplied by strong distribution is the
probabilistic input to the rooted configuration moment lemma.  This file
packages that substitution and the union bound over all ordered pairs.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Explicit union-bound tail supplied by a strong-distribution law. -/
def strongRootedTail (V : Type*) [Fintype V] [DecidableEq V]
    (C kappa : NNReal) (r q s : Nat) : NNReal :=
  (Fintype.card (DistinctPair V) : NNReal) *
    (((2 * (2 * C) ^ (s * (q - 1))) *
        (((2 : NNReal) ^ (s * (q - 1)) * kappa) ^ s)) /
      (r + 1 : NNReal) ^ s)

/-- Density-sensitive first-moment union-bound tail.  In contrast with
`strongRootedTail`, its combinatorial input is only the empty-root extension
weight. -/
def strongRootedFirstTail (V : Type*) [Fintype V] [DecidableEq V]
    (C kappa : ℝ≥0) (r q : ℕ) : ℝ≥0 :=
  (Fintype.card (DistinctPair V) : ℝ≥0) *
    (((2 * (2 * C) ^ (q - 1)) * kappa) / (r + 1 : ℝ≥0))

theorem IsStronglyWellDistributed.probability_not_rootedActiveCapsGood_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)}
    {initial later : Omega -> TripleSystemOn V}
    {p C b : NNReal}
    (hstrong : IsStronglyWellDistributed L W stage initial later p C b)
    (F : ForbiddenFamilyOn V) (r : Nat) {q s : Nat}
    (hC : 1 <= C)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) ->
      b <= setWeight (masterUnionTriangleWeight W stage p) T)
    (kappa : NNReal)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 =>
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W stage p) kappa) :
    L.probability (fun omega =>
      ¬ RootedActiveCapsGood F (initial omega ∪ later omega) r) <=
      strongRootedTail V C kappa r q s := by
  unfold strongRootedTail
  apply probability_not_rootedActiveCapsGood_le_of_moment L
    (fun omega => initial omega ∪ later omega) F
    (masterUnionTriangleWeight W stage p)
    (2 * (2 * C) ^ (s * (q - 1))) kappa r hFcard hkappa
  intro T hTcard
  exact hstrong.probability_subset_union_le_product hC T hTcard
    (hb T hTcard)

/-- Strong-distribution specialization of the empty-root first-moment
rooted-threat tail. -/
theorem IsStronglyWellDistributed.probability_not_rootedActiveCapsGood_le_firstMoment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hstrong : IsStronglyWellDistributed L W stage initial later p C b)
    (F : ForbiddenFamilyOn V) (r : ℕ) {q : ℕ}
    (hC : 1 ≤ C)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      b ≤ setWeight (masterUnionTriangleWeight W stage p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W stage p) (∅ : TripleSystemOn V) ≤
          kappa) :
    L.probability (fun omega ↦
      ¬ RootedActiveCapsGood F (initial omega ∪ later omega) r) ≤
      strongRootedFirstTail V C kappa r q := by
  unfold strongRootedFirstTail
  apply probability_not_rootedActiveCapsGood_le_of_firstMoment L
    (fun omega ↦ initial omega ∪ later omega) F
    (masterUnionTriangleWeight W stage p)
    (2 * (2 * C) ^ (q - 1)) kappa r hFcard hkappa
  intro T hTcard
  exact hstrong.probability_subset_union_le_product hC T hTcard
    (hb T hTcard)

end

end Erdos207
