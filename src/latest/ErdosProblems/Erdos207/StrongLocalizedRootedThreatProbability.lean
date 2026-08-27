/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributedUnion
import ErdosProblems.Erdos207.LocalizedRootedThreatExtraction

/-!
# Localized rooted-active tails from strong well-distributedness

The strong joint-inclusion estimate applies verbatim to the witness family
whose missing third vertex is restricted to a fixed finite set `U`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Explicit union-bound tail for rooted threats whose missing third vertex
is required to lie in `U`. -/
def strongLocalizedRootedTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (C kappa : NNReal) (r q s : Nat) : NNReal :=
  (Fintype.card (DistinctPair V) : NNReal) *
    (((2 * (2 * C) ^ (s * (q - 1))) *
        (((2 : NNReal) ^ (s * (q - 1)) * kappa) ^ s)) /
      (r + 1 : NNReal) ^ s)

/-- First-moment localized rooted tail.  Unlike
`strongLocalizedRootedTail`, this needs no extension estimates above
nonempty planted roots. -/
def strongLocalizedRootedFirstTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (C kappa : ℝ≥0) (r q : ℕ) : ℝ≥0 :=
  (Fintype.card (DistinctPair V) : ℝ≥0) *
    (((2 * (2 * C) ^ (q - 1)) * kappa) / (r + 1 : ℝ≥0))

theorem IsStronglyWellDistributed.probability_not_rootedActiveCapsGoodIn_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)}
    {initial later : Omega -> TripleSystemOn V}
    {p C b : NNReal}
    (hstrong : IsStronglyWellDistributed L W stage initial later p C b)
    (F : ForbiddenFamilyOn V) (U : Finset V) (r : Nat) {q s : Nat}
    (hC : 1 <= C)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) ->
      b ≤ setWeight (masterUnionTriangleWeight W stage p) T)
    (kappa : NNReal)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2 U =>
          localizedRootedThreatRemainder z)
        (masterUnionTriangleWeight W stage p) kappa) :
    L.probability (fun omega =>
      ¬ RootedActiveCapsGoodIn F (initial omega ∪ later omega) U r) <=
      strongLocalizedRootedTail V C kappa r q s := by
  unfold strongLocalizedRootedTail
  apply probability_not_rootedActiveCapsGoodIn_le_of_moment L
    (fun omega => initial omega ∪ later omega) F U
    (masterUnionTriangleWeight W stage p)
    (2 * (2 * C) ^ (s * (q - 1))) kappa r hFcard hkappa
  intro T hTcard
  exact hstrong.probability_subset_union_le_product hC T hTcard
    (hb T hTcard)

/-- Strong-distribution specialization of the localized empty-root first
moment. -/
theorem IsStronglyWellDistributed.probability_not_rootedActiveCapsGoodIn_le_firstMoment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hstrong : IsStronglyWellDistributed L W stage initial later p C b)
    (F : ForbiddenFamilyOn V) (U : Finset V) (r : ℕ) {q : ℕ}
    (hC : 1 ≤ C)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      b ≤ setWeight (masterUnionTriangleWeight W stage p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2 U ↦
          localizedRootedThreatRemainder z)
        (masterUnionTriangleWeight W stage p)
        (∅ : TripleSystemOn V) ≤ kappa) :
    L.probability (fun omega ↦
      ¬ RootedActiveCapsGoodIn F (initial omega ∪ later omega) U r) ≤
      strongLocalizedRootedFirstTail V C kappa r q := by
  unfold strongLocalizedRootedFirstTail
  apply probability_not_rootedActiveCapsGoodIn_le_of_firstMoment L
    (fun omega ↦ initial omega ∪ later omega) F U
    (masterUnionTriangleWeight W stage p)
    (2 * (2 * C) ^ (q - 1)) kappa r hFcard hkappa
  intro T hTcard
  exact hstrong.probability_subset_union_le_product hC T hTcard
    (hb T hTcard)

end

end Erdos207
