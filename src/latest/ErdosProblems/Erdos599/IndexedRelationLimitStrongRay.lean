/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedRelationLimit

/-!
# Strong rays in moving-slice limits

The first-missing-edge argument depends only on real extension, the strong
ray property at each stage, and the normalized completion target. No equality
of slice indices or closure sets is used. This extracts that argument for the
actual indexed relation chain.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedRealExtensionChain

universe u v

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {B : Set V}

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
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges) (i : I)
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
      hstrong i s hpstage
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

/-- A finite real path already present at one stage must follow any ray of
the eventual full relation from a common starting vertex. -/
theorem walk_finish_eq_eventual_ray
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
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
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges)
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
    have hinfinite := C.ray_strong_of_edgeSet_subset_stage hstrong i s hall
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
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target) :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.realEdgeLimit →
        (strongEdgeIndices r).Infinite := by
  intro r hr
  exact C.eventualRelationLimit_every_ray_strong hstrong hGamma hB r
    (hr.trans C.realEdgeLimit_subset_eventualEdgeLimit)


#print axioms eventualRelationLimit_every_ray_strong
#print axioms realEdgeLimit_every_ray_strong

end IndexedRealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599

