/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawSampledLinkJointLaw

/-! # A source-correct finite certificate for the geometric part of link sampling -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure RawLinkMatchingGeometry
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (F : ForbiddenFamilyOn V) (A I D : TripleSystemOn V)
    (sigma : ℝ≥0) (Delta collisionCap forbiddenCap degree overlap s t N c : ℕ) : Prop where
  center_eq : ∀ o, (K o).center = center o
  outside : ∀ o, center o ∉ U
  left_inner : ∀ o, (K o).left ⊆ U
  right_inner : ∀ o, (K o).right ⊆ U
  packing : IsPackingOn (I ∪ D)
  avoids : AvoidsForbidden (I ∪ D) F
  pair_safe : ∀ o a b, linkAvailableRelation (K o) A a b →
    TriangleAvoidsGraph (coveredGraph (I ∪ D)) (simultaneousLinkPairTriple K ⟨o,(a,b)⟩)
  deletion_cap : collisionCap+forbiddenCap ≤ Delta
  balanced : ∀ o, (K o).left.card = (K o).right.card
  side_size : ∀ o, (K o).left.card ≤ N ∧ (K o).right.card ≤ N
  degree_left : ∀ o (a : ↥(K o).left), (univ.filter (linkAvailableRelation (K o) A a)).card ≤ degree
  degree_right : ∀ o (b : ↥(K o).right), (univ.filter (fun a ↦ linkAvailableRelation (K o) A a b)).card ≤ degree
  overlap_bound : ∀ x : SimultaneousLinkPair O V K,
    (otherLinkCoordinates K (fun o ↦ linkAvailableRelation (K o) A) x).card ≤ overlap
  moment_size : 2*s ≤ collisionCap+1
  hall_candidates : ∀ o (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right),
    c*orientedSmallHallSize h ≤ (orientedSmallHallCandidates (linkAvailableRelation (K o) A) h).card
  hall_budget : (Delta+t : ℝ≥0) ≤ sigma*c/2
  hall_small : 2*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤ 1/2

def rawLinkGeometricFailure (centers N degree overlap collisionCap s t : ℕ) (sigma : ℝ≥0) : ℝ≥0 :=
  8*(centers : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t+
    2*(centers : ℝ≥0)*N*(2*(degree : ℝ≥0)*overlap*sigma^2/(collisionCap+1))^s

theorem RawLinkMatchingGeometry.exists_joint_law
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    {F : ForbiddenFamilyOn V} {A I D : TripleSystemOn V}
    {sigma : ℝ≥0} {Delta collisionCap forbiddenCap degree overlap s t N c : ℕ}
    (hg : RawLinkMatchingGeometry U center K F A I D sigma Delta collisionCap forbiddenCap degree overlap s t N c)
    (hsigma : sigma ≤ 1) :
    ∃ law : FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      law.SupportedOn (IsSampledLinkJointOutcome F A (I ∪ D) K) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun result ↦ Q ⊆ result.1) ≤ sigma^Q.card) ∧
      law.probability (fun result ↦ ¬ ∀ o, CoversBipartiteLink (K o) result.2) ≤
        rawLinkGeometricFailure (Fintype.card O) N degree overlap collisionCap s t sigma+
          law.probability (fun result ↦ ¬ IsSampledLinkForbiddenGood K F I D result.1 forbiddenCap) := by
  obtain ⟨law, hstruct, hpoint, hfail⟩ := exists_rawSampledLinkJointLaw_geometric U center K
    hg.center_eq hg.outside hg.left_inner hg.right_inner F A I D
    (fun o ↦ linkAvailableRelation (K o) A) Delta collisionCap forbiddenCap degree overlap s t N (fun _ ↦ c)
    sigma hsigma hg.packing hg.avoids (fun _ _ _ h ↦ h) hg.pair_safe hg.deletion_cap hg.balanced
    hg.side_size hg.degree_left hg.degree_right hg.overlap_bound hg.moment_size hg.hall_candidates
    (fun _ ↦ hg.hall_budget) hg.hall_small
  refine ⟨law, hstruct, hpoint, hfail.trans ?_⟩
  simp only [rawLinkGeometricFailure]
  refine add_le_add (add_le_add le_rfl ?_) le_rfl
  calc
    _ ≤ ∑ _o : O, (2*(N : ℝ≥0))*(2*(degree : ℝ≥0)*overlap*sigma^2/(collisionCap+1))^s := by
      apply sum_le_sum
      intro o _
      apply mul_le_mul_of_nonneg_right _ zero_le
      have hleft : ((K o).left.card : ℝ≥0) ≤ N := by exact_mod_cast (hg.side_size o).1
      have hright : ((K o).right.card : ℝ≥0) ≤ N := by exact_mod_cast (hg.side_size o).2
      simpa only [two_mul] using add_le_add hleft hright
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

end

end Erdos207
