/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphMixedLaw
import ErdosProblems.Erdos207.StrongRootedThreatProbability
import ErdosProblems.Erdos207.StrongLocalizedRootedThreatProbability

/-! # Retrospective rooted threats need only the selected part of the corrected law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.probability_subset_union_le_product
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    {d : ℕ} (hC : 1 ≤ C) (T : TripleSystemOn V) (hcard : T.card ≤ d)
    (hb : b ≤ setWeight (masterUnionTriangleWeight W k p) T) :
    L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
      (2 * (2 * C) ^ d) * setWeight (masterUnionTriangleWeight W k p) T := by
  let w := setWeight (masterUnionTriangleWeight W k p) T
  have hbase : L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
      C ^ T.card * (w + 2 ^ T.card * b) := by
    simpa using h.probability_union_and_edges_le T ∅ (empty_subset _)
  have htwo : (1 : ℝ≥0) ≤ 2 ^ T.card := one_le_pow₀ (by norm_num)
  have hw : w + 2 ^ T.card * b ≤ 2 * (2 ^ T.card * w) := by
    calc
      _ ≤ 2 ^ T.card * w + 2 ^ T.card * w :=
        add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo (show 0 ≤ w from zero_le))
          (mul_le_mul_of_nonneg_left hb zero_le)
      _ = _ := by ring
  calc
    _ ≤ C ^ T.card * (w + 2 ^ T.card * b) := hbase
    _ ≤ C ^ T.card * (2 * (2 ^ T.card * w)) := mul_le_mul_of_nonneg_left hw zero_le
    _ = (2 * (2 * C) ^ T.card) * w := by rw [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply mul_le_mul_of_nonneg_left _ zero_le
      exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by norm_num) hC) hcard

theorem IsResidualGraphStronglyWellDistributed.probability_not_rootedActiveCapsGood_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega -> TripleSystemOn V}
    {p C b : NNReal}
    (hstrong : IsResidualGraphStronglyWellDistributed L W stage G initial later p C b)
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
theorem IsResidualGraphStronglyWellDistributed.probability_not_rootedActiveCapsGood_le_firstMoment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W stage G initial later p C b)
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

theorem IsResidualGraphStronglyWellDistributed.probability_not_rootedActiveCapsGoodIn_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega -> TripleSystemOn V}
    {p C b : NNReal}
    (hstrong : IsResidualGraphStronglyWellDistributed L W stage G initial later p C b)
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
theorem IsResidualGraphStronglyWellDistributed.probability_not_rootedActiveCapsGoodIn_le_firstMoment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {stage : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W stage G initial later p C b)
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
