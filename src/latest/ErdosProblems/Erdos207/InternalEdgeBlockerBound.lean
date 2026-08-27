/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeCoverStage
import ErdosProblems.Erdos207.ForbiddenCompletionCount
import ErdosProblems.Erdos207.RelativeGreedyObstruction

/-!
# Numerical obstruction bounds for the internal-edge stage

The KSSS random-greedy argument separates the triangles lost at a step into
two classes: triangles meeting an already covered pair, and triangles which
complete a forbidden configuration.  This file packages the corresponding
deterministic estimates in precisely the form consumed by the internal-edge
cover theorem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- If the two endpoint degrees are at most `d`, there are at most `R`
active forbidden configurations rooted at the current pair, and forbidden
configurations have at most `k` triangles, then the total number of blocked
third vertices is at most `2 * d + R * k`. -/
theorem card_blockedThirdVertices_le_two_mul_add_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A Q : TripleSystemOn V}
    {u v : V} (huv : (leaveGraph Q).Adj u v)
    {d R k a : ℕ}
    (hdu : (coveredGraph Q).degree u ≤ d)
    (hdv : (coveredGraph Q).degree v ≤ d)
    (hroot :
      (rootedActiveForbiddenConfigurations F Q u v).card ≤ R)
    (hfamily : ∀ S ∈ F, S.card ≤ k)
    (hscalar : 2 * d + R * k ≤ a) :
    (edgeBlockedThirdVertices A Q huv.ne ∪
      forbiddenBlockedThirdVertices F A Q huv.ne).card ≤ a := by
  have hedge := card_edgeBlockedThirdVertices_le_degree_add
    (A := A) (P := Q) huv
  have hforbidden :=
    card_forbiddenBlockedThirdVertices_le_mul_rooted_active
      (F := F) (A := A) (P := Q) huv.ne hfamily
  have hforbiddenR :
      (forbiddenBlockedThirdVertices F A Q huv.ne).card ≤ R * k :=
    hforbidden.trans (Nat.mul_le_mul_right k hroot)
  have hunion := card_blocked_union_le_add
    (F := F) (A := A) (P := Q) huv.ne
  omega

/-- Relative version used in the master iteration: candidates already avoid
the initial packing, so only stars of triangles inserted in the current
stage contribute to the pair-conflict loss. -/
theorem card_blockedThirdVertices_le_four_mul_add_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P₀ Q : TripleSystemOn V}
    (hQ : IsPackingOn Q)
    (hinitial : ∀ T ∈ A,
      TriangleAvoidsGraph (coveredGraph P₀) T)
    {u v : V} (huv : (leaveGraph Q).Adj u v)
    {d R k a : ℕ}
    (hdu : (triplesThrough (Q \ P₀) u).card ≤ d)
    (hdv : (triplesThrough (Q \ P₀) v).card ≤ d)
    (hroot :
      (rootedActiveForbiddenConfigurations F Q u v).card ≤ R)
    (hfamily : ∀ S ∈ F, S.card ≤ k)
    (hscalar : 4 * d + R * k ≤ a) :
    (edgeBlockedThirdVertices A Q huv.ne ∪
      forbiddenBlockedThirdVertices F A Q huv.ne).card ≤ a := by
  have hedge := card_edgeBlockedThirdVertices_le_two_mul_new_star_add
    hQ hinitial huv
  have hforbidden :=
    card_forbiddenBlockedThirdVertices_le_mul_rooted_active
      (F := F) (A := A) (P := Q) huv.ne hfamily
  have hforbiddenR :
      (forbiddenBlockedThirdVertices F A Q huv.ne).card ≤ R * k :=
    hforbidden.trans (Nat.mul_le_mul_right k hroot)
  have hunion := card_blocked_union_le_add
    (F := F) (A := A) (P := Q) huv.ne
  omega

/-- The internal-edge cover stage with the obstruction hypothesis expressed
as the KSSS degree and rooted-active-configuration estimates. -/
theorem IsIterationTypical.exists_internalOuterEdge_greedy_cover_of_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P₀ : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking₀ : IsPackingOn P₀) (havoid₀ : AvoidsForbidden P₀ F)
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a d R k : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : (a : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ k)
    (hscalar : 2 * d + R * k ≤ a)
    (hdegree : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P₀ Q →
      Q ⊆ P₀ ∪ A →
      e ∈ internalOuterEdges G (W.U i.succ) →
      (coveredGraph Q).degree e.out.1 ≤ d ∧
        (coveredGraph Q).degree e.out.2 ≤ d)
    (hroot : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P₀ Q →
      Q ⊆ P₀ ∪ A →
      (Q \ P₀).card ≤ (internalOuterEdges G (W.U i.succ)).card →
      e ∈ internalOuterEdges G (W.U i.succ) →
      (rootedActiveForbiddenConfigurations F Q e.out.1 e.out.2).card ≤ R) :
    ∃ ω : Sym2 V → Bool, ∃ Q : TripleSystemOn V,
      GreedyReachable F P₀ Q ∧ Q ⊆ P₀ ∪ A ∧
      ∀ e ∈ internalOuterEdges G (W.U i.succ),
        (coveredGraph Q).Adj e.out.1 e.out.2 := by
  apply htyp.exists_internalOuterEdge_greedy_cover htri i hstage hGsupp
    hpacking₀ havoid₀ hh r hr m a hm ha hsmall
  intro Q e hreach hsub hcard he hleave
  obtain ⟨hdu, hdv⟩ := hdegree Q e hreach hsub he
  exact card_blockedThirdVertices_le_two_mul_add_mul hleave hdu hdv
    (hroot Q e hreach hsub hcard he) hfamily hscalar

/-- Stage-level form using only stars of triangles inserted after `P₀`.
This is the deterministic interface matching the edge-intersection estimate
in KSSS Section 10.2.4. -/
theorem IsIterationTypical.exists_internalOuterEdge_greedy_cover_of_relative_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P₀ : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking₀ : IsPackingOn P₀) (havoid₀ : AvoidsForbidden P₀ F)
    (hinitial : ∀ T ∈ A,
      TriangleAvoidsGraph (coveredGraph P₀) T)
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a d R k : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : (a : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ k)
    (hscalar : 4 * d + R * k ≤ a)
    (hnewStar : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P₀ Q →
      Q ⊆ P₀ ∪ A →
      e ∈ internalOuterEdges G (W.U i.succ) →
      (triplesThrough (Q \ P₀) e.out.1).card ≤ d ∧
        (triplesThrough (Q \ P₀) e.out.2).card ≤ d)
    (hroot : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P₀ Q →
      Q ⊆ P₀ ∪ A →
      (Q \ P₀).card ≤ (internalOuterEdges G (W.U i.succ)).card →
      e ∈ internalOuterEdges G (W.U i.succ) →
      (rootedActiveForbiddenConfigurations F Q e.out.1 e.out.2).card ≤ R) :
    ∃ ω : Sym2 V → Bool, ∃ Q : TripleSystemOn V,
      GreedyReachable F P₀ Q ∧ Q ⊆ P₀ ∪ A ∧
      ∀ e ∈ internalOuterEdges G (W.U i.succ),
        (coveredGraph Q).Adj e.out.1 e.out.2 := by
  apply htyp.exists_internalOuterEdge_greedy_cover htri i hstage hGsupp
    hpacking₀ havoid₀ hh r hr m a hm ha hsmall
  intro Q e hreach hsub hcard he hleave
  obtain ⟨hdu, hdv⟩ := hnewStar Q e hreach hsub he
  exact card_blockedThirdVertices_le_four_mul_add_mul
    (hreach.isPacking hpacking₀) hinitial hleave hdu hdv
      (hroot Q e hreach hsub hcard he) hfamily hscalar

end

end Erdos207
