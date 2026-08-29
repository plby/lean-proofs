/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IntermediateRelationLimit

/-!
# Strong rays at intermediate relation limits

This file discharges the only infinitary boundary left open by
`IntermediateRelationLimit`.  If a ray in the eventual full-edge relation
had only finitely many strong imaginary edges, discard that finite prefix.
At any stage containing the first remaining edge, the whole weak tail cannot
already lie in one stage blueprint.  At the first absent edge, (9.32) forces
the boundary vertex onto a completed real path to `B`.  Bi-uniqueness makes
the limit ray follow that path to `B`.  Its next edge is then either an
original edge leaving the target, contrary to normalization, or an imaginary
edge leaving the target.  In the latter case the edge is automatically
strong: a degeneracy witness would again be an original path leaving the
target.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- In a normalized web an imaginary edge with distinct endpoints and tail
in the target is strong. -/
theorem isStrongImaginaryEdge_of_tail_mem_target
    (hGamma : Gamma.IsNormalized) {u w : V} (hu : u ∈ Gamma.target)
    (huw : u ≠ w) (h : IsImaginaryEdge Gamma Y kappa u w) :
    IsStrongImaginaryEdge Gamma Y kappa u w := by
  rcases h with ⟨K, hK, hcard⟩
  refine ⟨K, ⟨hK, ?_⟩, hcard⟩
  intro Q hQK hdegenerate
  rcases hdegenerate with ⟨p, hpstart, hpfinish, _hpcontains⟩
  have hQinitial : Q.initial = u := (hK.1 Q hQK).2.1
  have hpTarget : p.start ∈ Gamma.target := by
    simpa only [hpstart, hQinitial] using hu
  have hstartFinish : p.start = p.finish :=
    hGamma.eq_finish_of_mem_walk p.walk p.start_mem_support hpTarget
  apply huw
  calc
    u = Q.initial := hQinitial.symm
    _ = p.start := hpstart.symm
    _ = p.finish := hstartFinish
    _ = w := hpfinish

namespace RealExtensionChain

variable {T Z persistent B : Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- The order-theoretic condition which lets a countable configuration in a
limit relation be captured at one stage.  This is source-faithful under edge
subdivision: it makes no assertion about predecessors of old vertices. -/
def CountablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop :=
  ∀ f : ℕ → I, ∃ j : I, ∀ n, f n ≤ j

/-- Under countable boundedness, every reverse ray in the eventual full-edge
relation would already occur in one stage blueprint. -/
theorem eventualEdgeLimit_not_containsReverseDirectedRay_of_countablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.CountablyBounded) :
    ¬ Alternating.ContainsReverseDirectedRay C.eventualEdgeLimit := by
  rintro ⟨r, hr⟩
  let stageAt : ℕ → I := fun n ↦
    Classical.choose ((WarpLimits.mem_setLiminf _ _).1 (hr n))
  have hstageAt (n : ℕ) : ∀ j, stageAt n ≤ j →
      (r.vertex (n + 1), r.vertex n) ∈ (C.stage j).edgeSet :=
    Classical.choose_spec ((WarpLimits.mem_setLiminf _ _).1 (hr n))
  obtain ⟨j, hj⟩ := H stageAt
  exact blueprint_edgeSet_not_containsReverseDirectedRay (C.stage j)
    ⟨r, fun n ↦ hstageAt n j (hj n)⟩

/-- The same localization excludes a reverse ray in the monotone union of
real edges, without any predecessor-preservation hypothesis. -/
theorem realEdgeLimit_not_containsReverseDirectedRay_of_countablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.CountablyBounded) :
    ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit := by
  rintro ⟨r, hr⟩
  let stageAt : ℕ → I := fun n ↦
    Classical.choose (Set.mem_iUnion.1 (hr n))
  have hstageAt (n : ℕ) :
      (r.vertex (n + 1), r.vertex n) ∈
        (C.stage (stageAt n)).realPart.edges :=
    Classical.choose_spec (Set.mem_iUnion.1 (hr n))
  obtain ⟨j, hj⟩ := H stageAt
  exact blueprint_edgeSet_not_containsReverseDirectedRay (C.stage j)
    ⟨r, fun n ↦ (C.stage_edges_mono (hj n) (hstageAt n)).1⟩

/-- Countable boundedness also supplies the honest core for the final
all-real relation limit.  No predecessor-preservation hypothesis is used. -/
def relationLimitCore_of_countablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.CountablyBounded) : C.RelationLimitCore where
  no_directed_cycle := C.realEdgeLimit_not_containsDirectedCycle
  no_reverse_ray :=
    C.realEdgeLimit_not_containsReverseDirectedRay_of_countablyBounded H

private theorem finite_Iio_nat (k : ℕ) : (Set.Iio k : Set ℕ).Finite := by
  induction k with
  | zero => simp
  | succ k ih =>
      have heq : (Set.Iio (k + 1) : Set ℕ) =
          insert k (Set.Iio k) := by
        ext n
        simp only [Set.mem_Iio, Set.mem_insert_iff]
        omega
      rw [heq]
      exact ih.insert k

/-- A ray all of whose edges lie in a single blueprint has infinitely many
strong edges.  The ray may begin in the middle of the blueprint member, so
the proof identifies it with a suffix of that member. -/
theorem ray_strong_of_edgeSet_subset_stage
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) (i : I)
    (r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa))
    (hr : r.edgeSet ⊆ (C.stage i).edgeSet) :
    (strongEdgeIndices r).Infinite := by
  have hfirst : (r 0, r 1) ∈ (C.stage i).edgeSet :=
    hr ⟨0, by simp⟩
  simp only [edgeSet, Set.mem_iUnion] at hfirst
  obtain ⟨p, hpstage, hpfirst⟩ := hfirst
  have hpedge : ∀ n : ℕ, (r n, r (n + 1)) ∈ p.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hpfirst
    | succ n ih =>
        have hn := hr ⟨n + 1, rfl⟩
        simp only [edgeSet, Set.mem_iUnion] at hn
        obtain ⟨q, hqstage, hqn⟩ := hn
        have hrp : r (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod ih).2
        have hrq : r (n + 1) ∈ q.support :=
          (q.edgeSet_subset_support_prod hqn).1
        have hqp : q = p :=
          Alternating.DWeb.IsWarp.eq_of_mem_support
            (C.stage i).isWarp hqstage hpstage hrq hrp
        exact hqp ▸ hqn
  rcases p with p | s
  · have hall : ∀ n : ℕ, r n ∈ p.support := by
      intro n
      cases n with
      | zero => exact (p.edgeSet_subset_support_prod (hpedge 0)).1
      | succ n => exact (p.edgeSet_subset_support_prod (hpedge n)).2
    exact False.elim <| p.support_finite.not_infinite
      (Set.infinite_of_injective_forall_mem r.injective hall)
  · have hsstrong : (strongEdgeIndices s).Infinite :=
      (C.isBlueprint i).infinitely_many_strong s hpstage
    have hr0s : r 0 ∈ s.support :=
      (s.edgeSet_subset_support_prod (hpedge 0)).1
    obtain ⟨k, hk⟩ := hr0s
    have hrs : ∀ n : ℕ, r n = s (k + n) := by
      intro n
      induction n with
      | zero => simpa using hk.symm
      | succ n ih =>
          have hredge : (r n, r (n + 1)) ∈ s.edgeSet := hpedge n
          obtain ⟨m, hm⟩ := hredge
          have hmfirst : s m = s (k + n) := by
            exact (congrArg Prod.fst hm).symm.trans ih
          have hmindex : m = k + n := s.injective hmfirst
          have hmsecond := congrArg Prod.snd hm
          simpa [hmindex, Nat.add_assoc] using hmsecond
    have htailStrong : {n | k + n ∈ strongEdgeIndices s}.Infinite := by
      by_contra hfinite
      have hprefix : strongEdgeIndices s ⊆
          Set.Iio k ∪ (fun n ↦ k + n) ''
            {n | k + n ∈ strongEdgeIndices s} := by
        intro n hn
        by_cases hnk : n < k
        · exact Or.inl hnk
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnk)
          exact Or.inr ⟨m, hn, rfl⟩
      have hIio : (Set.Iio k : Set ℕ).Finite := finite_Iio_nat k
      exact hsstrong <| (hIio.union
        ((Set.not_infinite.mp hfinite).image (fun n ↦ k + n))).subset hprefix
    apply htailStrong.mono
    intro n hn
    change IsStrongImaginaryEdge Gamma Y kappa (r n) (r (n + 1))
    simpa [strongEdgeIndices, hrs, Nat.add_assoc] using hn

/-- Under countable boundedness, every ray in the eventual full relation is
already a ray of one stage and hence has infinitely many strong edges. -/
theorem eventualEdgeLimit_every_ray_strong_of_countablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.CountablyBounded) :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.eventualEdgeLimit →
        (strongEdgeIndices r).Infinite := by
  intro r hr
  let stageAt : ℕ → I := fun n ↦
    Classical.choose ((WarpLimits.mem_setLiminf _ _).1
      (hr ⟨n, rfl⟩))
  have hstageAt (n : ℕ) : ∀ j, stageAt n ≤ j →
      (r n, r (n + 1)) ∈ (C.stage j).edgeSet :=
    Classical.choose_spec ((WarpLimits.mem_setLiminf _ _).1
      (hr ⟨n, rfl⟩))
  obtain ⟨j, hj⟩ := H stageAt
  apply C.ray_strong_of_edgeSet_subset_stage j r
  rintro e ⟨n, rfl⟩
  exact hstageAt n j (hj n)

/-- A finite real path already present at one stage must follow any ray of
the eventual full relation from a common starting vertex. -/
theorem walk_finish_eq_eventual_ray
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    {a b : V} (p : DirectedPath.Walk Gamma.graph a b) (j : I)
    (r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa))
    (hr : r.edgeSet ⊆ C.eventualEdgeLimit) (n : ℕ)
    (hstart : a = r n)
    (hp : p.edgeSet ⊆ (C.stage j).realPart.edges) :
    b = r (n + p.length) := by
  induction p generalizing n with
  | nil => simpa using hstart
  | @cons a c b hac q ih =>
      have hacj : (a, c) ∈ (C.stage j).realPart.edges := by
        apply hp
        simp
      have hrn : (r n, r (n + 1)) ∈ C.eventualEdgeLimit :=
        hr ⟨n, rfl⟩
      obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hrn
      obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
      have hack : (a, c) ∈ (C.stage k).edgeSet :=
        (C.stage_edges_mono hjk hacj).1
      have hrnk : (r n, r (n + 1)) ∈ (C.stage k).edgeSet :=
        hi k hik
      have hc : c = r (n + 1) := by
        apply Alternating.IsWarp.familyEdges_rightUnique
          (C.stage k).isWarp hack
        rw [hstart]
        exact hrnk
      have hq : q.edgeSet ⊆ (C.stage j).realPart.edges := by
        intro e he
        apply hp
        exact Set.mem_union_right _ he
      have hfinish := ih (n + 1) hc hq
      simpa only [DirectedPath.Walk.length, Nat.add_assoc,
        Nat.add_comm 1 q.length, Nat.add_left_comm] using hfinish

/-- The strong-ray boundary in Assertion 9.33 is automatic for a normalized
web when the real-completion target lies in the web target. -/
theorem eventualRelationLimit_every_ray_strong
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target) :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.eventualEdgeLimit →
        (strongEdgeIndices r).Infinite := by
  classical
  intro r hr
  by_contra hrfinite
  have hrfinite' : (strongEdgeIndices r).Finite :=
    Set.not_infinite.mp hrfinite
  obtain ⟨N, hN⟩ := hrfinite'.exists_le
  let s := r.tail (N + 1)
  have hsEventual : s.edgeSet ⊆ C.eventualEdgeLimit := by
    rintro e ⟨n, rfl⟩
    apply hr
    refine ⟨N + 1 + n, ?_⟩
    simp only [s, DirectedPath.Ray.tail_apply]
    congr 2 <;> omega
  have hsWeak (n : ℕ) :
      ¬IsStrongImaginaryEdge Gamma Y kappa (s n) (s (n + 1)) := by
    intro hn
    have hn' : N + 1 + n ∈ strongEdgeIndices r := by
      change IsStrongImaginaryEdge Gamma Y kappa
        (r (N + 1 + n)) (r (N + 1 + n + 1))
      simpa only [s, DirectedPath.Ray.tail_apply, Nat.add_assoc] using hn
    have := hN (N + 1 + n) hn'
    omega
  have hs0 : (s 0, s 1) ∈ C.eventualEdgeLimit :=
    hsEventual ⟨0, by simp⟩
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hs0
  have hnotAll : ¬s.edgeSet ⊆ (C.stage i).edgeSet := by
    intro hall
    have hinfinite := C.ray_strong_of_edgeSet_subset_stage i s hall
    apply hinfinite.not_finite
    apply (Set.finite_empty : (∅ : Set ℕ).Finite).subset
    intro n hn
    exact False.elim (hsWeak n hn)
  have hmissing : ∃ n : ℕ,
      (s n, s (n + 1)) ∉ (C.stage i).edgeSet := by
    obtain ⟨e, heRay, heStage⟩ := Set.not_subset.mp hnotAll
    obtain ⟨n, rfl⟩ := heRay
    exact ⟨n, heStage⟩
  let m := Nat.find hmissing
  have hmMissing : (s m, s (m + 1)) ∉ (C.stage i).edgeSet :=
    by simpa only [m] using Nat.find_spec hmissing
  have hsmStage : s m ∈ (C.stage i).vertexSet := by
    dsimp only [m]
    cases hfind : Nat.find hmissing with
    | zero =>
        have hm := Nat.find_spec hmissing
        rw [hfind] at hm
        exact False.elim <| hm (by simpa using hi i le_rfl)
    | succ n =>
        have hnlt : n < Nat.find hmissing := by omega
        have hprevNotMissing :=
          Nat.find_min hmissing hnlt
        have hprev : (s n, s (n + 1)) ∈ (C.stage i).edgeSet :=
          Classical.byContradiction hprevNotMissing
        have hsSucc : s (n + 1) ∈ (C.stage i).vertexSet :=
          (Alternating.familyEdges_subset_vertexSet_prod
            (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hprev).2
        simpa only [hfind] using hsSucc
  have hmEventual : (s m, s (m + 1)) ∈ C.eventualEdgeLimit :=
    hsEventual ⟨m, rfl⟩
  obtain ⟨i', hi'⟩ := (WarpLimits.mem_setLiminf _ _).1 hmEventual
  obtain ⟨j, hij, hi'j⟩ := exists_ge_ge i i'
  have hmj : (s m, s (m + 1)) ∈ (C.stage j).edgeSet :=
    hi' j hi'j
  have hcompleted : s m ∈ (C.stage j).completedRealVertices B := by
    rcases (C.realExtends hij).2 hsmStage with hcommon | hdone
    · rcases hcommon with hterm | hedge
      · exact False.elim <|
          (mem_familyGraph_terminals_of_mem_terminalSet hterm.1).2
            ⟨s (m + 1), hmj⟩
      · rcases hedge with ⟨z, hmzi, hmzj⟩
        have hz : z = s (m + 1) :=
          Alternating.IsWarp.familyEdges_rightUnique
            (C.stage j).isWarp hmzj hmj
        exact False.elim (hmMissing (hz ▸ hmzi))
    · exact hdone
  rcases hcompleted with ⟨p, hpB, _hpvertices, hpEdges, hmp⟩
  let q := p.suffixFrom (s m) hmp
  have hqStart : q.start = s m :=
    p.suffixFrom_start (s m) hmp
  have hqEdges : q.edgeSet ⊆ (C.stage j).realPart.edges :=
    (p.suffixFrom_edgeSet_subset (s m) hmp).trans hpEdges
  have hqFinish : q.finish = s (m + q.walk.length) :=
    C.walk_finish_eq_eventual_ray q.walk j s hsEventual m hqStart hqEdges
  have hpFinish : p.finish = s (m + q.walk.length) := by
    rw [← hqFinish]
    exact (p.suffixFrom_finish (s m) hmp).symm
  let ell := m + q.walk.length
  have hsTarget : s ell ∈ Gamma.target := by
    rw [← hpFinish]
    exact hB hpB
  have hsAdj : (imaginaryGraph Gamma Y kappa).Adj
      (s ell) (s (ell + 1)) :=
    C.eventualEdgeLimit_in_graph
      (hsEventual ⟨ell, rfl⟩)
  rcases hsAdj with hsOriginal | hsImaginary
  · exact (hGamma hsOriginal).2 hsTarget
  · apply hsWeak ell
    apply isStrongImaginaryEdge_of_tail_mem_target hGamma hsTarget
    · intro heq
      have := s.injective heq
      omega
    · exact hsImaginary

/-- The same normalized-target argument discharges the ray boundary of the
final all-real relation limit.  This is a direct consequence of the fact
that every real edge in the monotone union belongs to the eventual full-edge
relation. -/
theorem realEdgeLimit_every_ray_strong
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target) :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.realEdgeLimit →
        (strongEdgeIndices r).Infinite := by
  intro r hr
  exact C.eventualRelationLimit_every_ray_strong hGamma hB r
    (hr.trans C.realEdgeLimit_subset_eventualEdgeLimit)

/-- In a normalized web the complete proper-limit boundary has no residual
ray premise: only the carrier cardinality remains to be supplied. -/
def eventualRelationLimitBoundary_of_normalized
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target)
    (hcard : #C.realVertexLimit ≤ kappa) :
    C.EventualRelationLimitBoundary where
  card_vertices := hcard
  every_relation_ray_strong :=
    C.eventualRelationLimit_every_ray_strong hGamma hB

/-- The index-cardinality form used by a transfinite scheduler. -/
def eventualRelationLimitBoundary_of_normalized_index
    {J : Type u} [LinearOrder J] [Nonempty J]
    (C : RealExtensionChain J Gamma Y kappa T Z persistent B)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target)
    (hkappa : aleph0 ≤ kappa) (hindex : #J ≤ kappa) :
    C.EventualRelationLimitBoundary :=
  C.eventualRelationLimitBoundary_of_normalized hGamma hB
    (C.mk_realVertexLimit_le hkappa hindex)

/-- Assertion 9.33 at a proper limit, with the strong-ray condition derived
from normalization and the completion-target boundary. -/
theorem stableLimitConclusion_eventualRelationLimit_of_normalized
    {J : Type u} [LinearOrder J] [Nonempty J]
    (C : RealExtensionChain J Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (hYwarp : Gamma.IsWarp Y)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (hkappa : aleph0 ≤ kappa) (hindex : #J ≤ kappa) :
    StableLimitConclusion C.stage (C.eventualRelationLimit H)
      T Z persistent B :=
  C.stableLimitConclusion_eventualRelationLimit H hYwarp hterminalB
    hstableB
    (C.eventualRelationLimitBoundary_of_normalized_index
      hGamma hBtarget hkappa hindex)

end RealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
