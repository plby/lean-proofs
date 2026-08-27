/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeDegreeCover
import ErdosProblems.Erdos207.RootedThreatTransport

/-!
# Transporting rooted threats through the internal-edge stage

An active rooted configuration after a greedy prefix was either already
active initially, or has a witness whose selected remainder uses a triangle
inserted during this stage.  The prefix-size invariant from the internal
edge-list induction makes the latter contribution explicit.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Deterministic rooted-threat transport with an explicit new-triangle
budget. -/
theorem card_rootedActive_le_of_initial_and_new_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P₀ Q : TripleSystemOn V}
    {u v : V} {k K R₀ t R : ℕ}
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (husing : ∀ T : TripleOn V,
      (rootedThreatWitnessesUsing F u v T).card ≤ K)
    (hP₀Q : P₀ ⊆ Q)
    (hroot₀ :
      (rootedActiveForbiddenConfigurations F P₀ u v).card ≤ R₀)
    (hnew : (Q \ P₀).card ≤ t)
    (hscalar : R₀ * k + t * K ≤ R) :
    (rootedActiveForbiddenConfigurations F Q u v).card ≤ R := by
  have htransport :=
    card_rootedActiveForbiddenConfigurations_le_of_enlargement
      k K hfamily husing hP₀Q
  have hfirst :
      (rootedActiveForbiddenConfigurations F P₀ u v).card * k ≤
        R₀ * k := Nat.mul_le_mul_right k hroot₀
  have hsecond : (Q \ P₀).card * K ≤ t * K :=
    Nat.mul_le_mul_right K hnew
  exact htransport.trans ((Nat.add_le_add hfirst hsecond).trans hscalar)

/-- Internal-edge coverage from a residual degree bound, initial rooted
counts, and a uniform number of rooted witnesses using one new triangle. -/
theorem IsIterationTypical.exists_internalOuterEdge_greedy_cover_of_initial_rooted
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
    (m a d R₀ R k K : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : (a : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ k)
    (hblockScalar : 4 * d + R * k ≤ a)
    (hdegree : ∀ v : V, G.degree v ≤ d)
    (hroot₀ : ∀ e ∈ internalOuterEdges G (W.U i.succ),
      (rootedActiveForbiddenConfigurations
        F P₀ e.out.1 e.out.2).card ≤ R₀)
    (husing : ∀ e ∈ internalOuterEdges G (W.U i.succ),
      ∀ T : TripleOn V,
        (rootedThreatWitnessesUsing F e.out.1 e.out.2 T).card ≤ K)
    (htransportScalar :
      R₀ * k + (internalOuterEdges G (W.U i.succ)).card * K ≤ R) :
    ∃ ω : Sym2 V → Bool, ∃ Q : TripleSystemOn V,
      GreedyReachable F P₀ Q ∧ Q ⊆ P₀ ∪ A ∧
      ∀ e ∈ internalOuterEdges G (W.U i.succ),
        (coveredGraph Q).Adj e.out.1 e.out.2 := by
  apply htyp.exists_internalOuterEdge_greedy_cover_of_degree_rooted
    htri i hstage hGsupp hpacking₀ havoid₀ hinitial hh r hr
      m a d R k hm ha hsmall hfamily hblockScalar hdegree
  intro Q e hreach _hsub hnew he
  exact card_rootedActive_le_of_initial_and_new_budget hfamily
    (husing e he) hreach.initial_subset (hroot₀ e he) hnew
      htransportScalar

end

end Erdos207
