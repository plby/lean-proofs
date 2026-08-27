/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeBlockerBound
import ErdosProblems.Erdos207.InternalEdgeStarBound

/-!
# Internal-edge cover from residual degree and rooted-threat bounds

This is the deterministic/reserve-probability endpoint of KSSS Sections
10.2.1, 10.2.3, and 10.2.4.  Residual graph degree controls pair collisions;
the rooted-active count controls forbidden completions; and reserve
concentration supplies strictly more candidate third vertices than the sum
of those two losses.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.exists_internalOuterEdge_greedy_cover_of_degree_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P₀ : TripleSystemOn V}
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
    (hdegree : ∀ v : V, G.degree v ≤ d)
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
  apply htyp.exists_internalOuterEdge_greedy_cover_of_relative_bounds
    htri i hstage hGsupp hpacking₀ havoid₀ hinitial hh r hr
      m a d R k hm ha hsmall hfamily hscalar
  · intro Q e hreach hsub he
    exact internalOuterEdge_new_endpoint_stars_le htri
      (hreach.isPacking hpacking₀) hsub hdegree e he
  · exact hroot

end

end Erdos207
