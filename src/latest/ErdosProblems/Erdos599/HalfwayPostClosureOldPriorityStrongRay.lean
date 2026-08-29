/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureMarkedStrongRay
import ErdosProblems.Erdos599.HalfwayPostClosurePrefixedAttachment

/-!
# Strong rays after the prefixed old-priority attachment

The prefix seed is the disjoint union of the old blueprint and finite
reference prefixes.  Hence a ray in the seed lies wholly in the old
blueprint: it cannot cross between the two disjoint carriers, and the finite
prefix warp contains no ray.

For the subsequent old-priority attachment, once a ray uses a fresh edge it
can never return to the seed.  Indeed the head of every fresh edge lies
outside the seed carrier.  The resulting fresh tail is contained in the
actual post-closure relation, where the marked-edge theorem supplies
infinitely many strong edges.  This keeps switching safety as an explicit
hypothesis and does not manufacture any contact-classification data.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

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

/-- A ray whose entire edge set lies in one blueprint has infinitely many
strong edges.  The ray may start in the middle of a blueprint ray. -/
theorem strongEdgeIndices_infinite_of_edgeSet_subset
    (W : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hstrong : W.InfinitelyManyStrongEdges)
    (r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hr : r.edgeSet ⊆ W.edgeSet) :
    (strongEdgeIndices r).Infinite := by
  have hfirst : (r 0, r 1) ∈ W.edgeSet := hr ⟨0, by simp⟩
  simp only [edgeSet, Set.mem_iUnion] at hfirst
  obtain ⟨p, hpW, hpfirst⟩ := hfirst
  have hpedge : ∀ n : ℕ, (r n, r (n + 1)) ∈ p.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hpfirst
    | succ n ih =>
        have hn := hr ⟨n + 1, rfl⟩
        simp only [edgeSet, Set.mem_iUnion] at hn
        obtain ⟨q, hqW, hqn⟩ := hn
        have hrp : r (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod ih).2
        have hrq : r (n + 1) ∈ q.support :=
          (q.edgeSet_subset_support_prod hqn).1
        have hqp : q = p :=
          _root_.Erdos599.Alternating.DWeb.IsWarp.eq_of_mem_support
            W.isWarp hqW hpW hrq hrp
        exact hqp ▸ hqn
  rcases p with p | s
  · have hall : ∀ n : ℕ, r n ∈ p.support := by
      intro n
      cases n with
      | zero => exact (p.edgeSet_subset_support_prod (hpedge 0)).1
      | succ n => exact (p.edgeSet_subset_support_prod (hpedge n)).2
    exact False.elim <| p.support_finite.not_infinite
      (Set.infinite_of_injective_forall_mem r.injective hall)
  · have hsstrong : (strongEdgeIndices s).Infinite := hstrong s hpW
    have hr0s : r 0 ∈ s.support :=
      (s.edgeSet_subset_support_prod (hpedge 0)).1
    obtain ⟨m, hm⟩ := hr0s
    have hrs : ∀ n : ℕ, r n = s (m + n) := by
      intro n
      induction n with
      | zero => simpa using hm.symm
      | succ n ih =>
          have hredge : (r n, r (n + 1)) ∈ s.edgeSet := hpedge n
          obtain ⟨j, hj⟩ := hredge
          have hjfirst : s j = s (m + n) := by
            exact (congrArg Prod.fst hj).symm.trans ih
          have hjindex : j = m + n := s.injective hjfirst
          have hjsecond := congrArg Prod.snd hj
          simpa [hjindex, Nat.add_assoc] using hjsecond
    have htailStrong : {n | m + n ∈ strongEdgeIndices s}.Infinite := by
      by_contra hfinite
      have hprefix : strongEdgeIndices s ⊆
          Set.Iio m ∪ (fun n ↦ m + n) ''
            {n | m + n ∈ strongEdgeIndices s} := by
        intro n hn
        by_cases hnm : n < m
        · exact Or.inl hnm
        · obtain ⟨j, rfl⟩ :=
            Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnm)
          exact Or.inr ⟨j, hn, rfl⟩
      have hIio : (Set.Iio m : Set ℕ).Finite := finite_Iio_nat m
      exact hsstrong <| (hIio.union
        ((Set.not_infinite.mp hfinite).image (fun n ↦ m + n))).subset hprefix
    apply htailStrong.mono
    intro n hn
    change IsStrongImaginaryEdge Gamma C.ladder.limitWarp kappa
      (r n) (r (n + 1))
    simpa [strongEdgeIndices, hrs, Nat.add_assoc] using hn

/-- Infinitely many strong edges on a tail give infinitely many strong edges
on the original ray. -/
theorem strongEdgeIndices_infinite_of_tail
    (r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa)) (m : ℕ)
    (h : (strongEdgeIndices (r.tail m)).Infinite) :
    (strongEdgeIndices r).Infinite := by
  have himage : ((fun n : ℕ ↦ m + n) ''
      strongEdgeIndices (r.tail m)).Infinite :=
    h.image (by
      intro a _ b _ hab
      exact Nat.add_left_cancel hab)
  apply himage.mono
  rintro n ⟨j, hj, rfl⟩
  change IsStrongImaginaryEdge Gamma C.ladder.limitWarp kappa
    (r (m + j)) (r (m + j + 1))
  simpa [strongEdgeIndices, Ray.tail_apply, Nat.add_assoc] using hj

namespace referencePrefixSeed

variable {current : LinkageBlueprint Gamma C.ladder.limitWarp kappa}
variable {X : Set V}

/-- A ray in the literal old-plus-prefix seed lies in the old blueprint.
The alternative would be a ray in the finite-character prefix warp. -/
theorem strongEdgeIndices_infinite_of_subset_seed
    (hstrong : current.InfinitelyManyStrongEdges)
    (r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hr : r.edgeSet ⊆ referencePrefixSeedEdges current X) :
    (strongEdgeIndices r).Infinite := by
  have hfirst : (r 0, r 1) ∈ referencePrefixSeedEdges current X :=
    hr ⟨0, rfl⟩
  rcases hfirst with hold | hpref
  · have hall : r.edgeSet ⊆ current.edgeSet := by
      rintro e ⟨n, rfl⟩
      induction n with
      | zero => simpa using hold
      | succ n ih =>
          have hn := hr ⟨n + 1, rfl⟩
          rcases hn with hn | hn
          · exact hn
          · have hcurrentVertex : r (n + 1) ∈ current.vertexSet := by
              change (r n, r (n + 1)) ∈ familyEdges
                (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
                current.paths at ih
              exact (familyEdges_subset_vertexSet_prod
                (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
                current.paths ih).2
            have hprefixVertex : r (n + 1) ∈
                Gamma.vertexSet (activatedReferencePrefixes C current X) :=
              (familyEdges_subset_vertexSet_prod
                (activatedReferencePrefixes C current X) hn).1
            exact False.elim <| Set.disjoint_left.1 vertexSets_disjoint
              hcurrentVertex hprefixVertex
    exact strongEdgeIndices_infinite_of_edgeSet_subset current hstrong r hall
  · have hall : r.edgeSet ⊆
        familyEdges (activatedReferencePrefixes C current X) := by
      rintro e ⟨n, rfl⟩
      induction n with
      | zero => simpa using hpref
      | succ n ih =>
          have hn := hr ⟨n + 1, rfl⟩
          rcases hn with hn | hn
          · have hprefixVertex : r (n + 1) ∈
                Gamma.vertexSet (activatedReferencePrefixes C current X) :=
              (familyEdges_subset_vertexSet_prod
                (activatedReferencePrefixes C current X) ih).2
            have hcurrentVertex : r (n + 1) ∈ current.vertexSet := by
              change (r (n + 1), r (n + 1 + 1)) ∈ familyEdges
                (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
                current.paths at hn
              exact (familyEdges_subset_vertexSet_prod
                (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
                current.paths hn).1
            exact False.elim <| Set.disjoint_left.1 vertexSets_disjoint
              hcurrentVertex hprefixVertex
          · exact hn
    exact False.elim <|
      (_root_.Erdos599.Alternating.familyEdges_not_containsDirectedRay
        activatedReferencePrefixes.isWarp
        activatedReferencePrefixes.finiteCharacter)
        ⟨⟨r, r.injective⟩, by
          rintro e ⟨n, rfl⟩
          exact hall ⟨n, rfl⟩⟩

/-- The exact reference-prefix seed blueprint inherits the old blueprint's
strong-ray condition. -/
theorem blueprint_infinitelyManyStrong
    {A : LinkageBlueprint Gamma C.ladder.limitWarp kappa}
    (hstrong : current.InfinitelyManyStrongEdges)
    (hAE : A.edgeSet = referencePrefixSeedEdges current X) :
    A.InfinitelyManyStrongEdges := by
  intro r hrA
  apply strongEdgeIndices_infinite_of_subset_seed hstrong r
  rw [← hAE]
  intro e he
  simp only [edgeSet, Set.mem_iUnion]
  exact ⟨(.inr r : Path _), hrA, he⟩

end referencePrefixSeed

namespace PostClosureMacroCompressorAssignment

/-- A ray in the old-priority relation either stays in the seed forever or,
after its first chosen fresh edge, has a fresh-only tail. -/
theorem oldPriorityAttachedEdges_strongEdgeIndices_infinite
    (M : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hroof : current.vertexSet ⊆ Gamma.roof C.newSlice)
    (hstrong : current.InfinitelyManyStrongEdges)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof
        C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
        kappa)
    (hswitch : ∀ e
      (he : e ∈ (M.toPostClosureCompressorAssignment
        |>.actualPostClosureShortcutEdges)),
      IsSwitchingSafe C.ladder.limitWarp
        (M.toPostClosureCompressorAssignment
          |>.actualShortcutIntervalWitness he).path)
    (r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hr : r.edgeSet ⊆ M.oldPriorityAttachedEdges current) :
    (strongEdgeIndices r).Infinite := by
  by_cases hold : ∀ n : ℕ, (r n, r (n + 1)) ∈ current.edgeSet
  · apply strongEdgeIndices_infinite_of_edgeSet_subset current hstrong r
    rintro e ⟨n, rfl⟩
    exact hold n
  · push Not at hold
    obtain ⟨m, hm⟩ := hold
    have hmfresh : (r m, r (m + 1)) ∈ M.oldPriorityFreshEdges current := by
      rcases hr ⟨m, rfl⟩ with hmold | hmfresh
      · exact (hm hmold).elim
      · exact hmfresh
    have htailFresh : ∀ n : ℕ,
        (r.tail m n, r.tail m (n + 1)) ∈
          M.oldPriorityFreshEdges current := by
      intro n
      induction n with
      | zero => simpa [Ray.tail_apply] using hmfresh
      | succ n ih =>
          have hn0 := hr ⟨m + (n + 1), rfl⟩
          have hn : (r.tail m (n + 1), r.tail m (n + 1 + 1)) ∈
              M.oldPriorityAttachedEdges current := by
            simpa [Ray.tail_apply, Nat.add_assoc] using hn0
          rcases hn with hn | hn
          · have hseedVertex : r.tail m (n + 1) ∈ current.vertexSet := by
              change (r.tail m (n + 1), r.tail m (n + 1 + 1)) ∈
                familyEdges
                  (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
                  current.paths at hn
              exact (familyEdges_subset_vertexSet_prod
                (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
                current.paths hn).1
            exact False.elim <|
              M.oldPriorityFreshEdge_head_not_mem_of_vertices_roofed
                current hroof ih hseedVertex
          · simpa [Ray.tail_apply, Nat.add_assoc] using hn
    have hclosed : (r.tail m).edgeSet ⊆
        (M.toPostClosureCompressorAssignment
          |>.actualPostClosureClosedEdges) := by
      rintro e ⟨n, rfl⟩
      exact M.oldPriorityFreshEdges_subset_closedEdges current (htailFresh n)
    apply strongEdgeIndices_infinite_of_tail r m
    exact M.toPostClosureCompressorAssignment
      |>.actualClosedEdges_strongEdgeIndices_infinite
        hfiltered hswitch (r.tail m) hclosed

/-- The actual root-reachable old-priority output inherits the strong-ray
condition from the prefixed seed and the marked fresh relation. -/
theorem rootReachableOldPriority_infinitelyManyStrong
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof
        C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
        kappa)
    (hswitch : ∀ e
      (he : e ∈ (M.toPostClosureCompressorAssignment
        |>.actualPostClosureShortcutEdges)),
      IsSwitchingSafe C.ladder.limitWarp
        (M.toPostClosureCompressorAssignment
          |>.actualShortcutIntervalWitness he).path) :
    U.InfinitelyManyStrongEdges := by
  have hAroof : A.vertexSet ⊆ Gamma.roof C.newSlice :=
    referencePrefixSeed.blueprint_vertices_roofed hcurrent hAV
  have hAstrong : A.InfinitelyManyStrongEdges :=
    referencePrefixSeed.blueprint_infinitelyManyStrong
      hcurrent.infinitely_many_strong hAE
  intro r hrU
  apply M.oldPriorityAttachedEdges_strongEdgeIndices_infinite
    A hAroof hAstrong hfiltered hswitch r
  have hrUEdge : r.edgeSet ⊆ U.edgeSet := by
    intro e he
    simp only [edgeSet, Set.mem_iUnion]
    exact ⟨(.inr r : Path _), hrU, he⟩
  rw [hUE] at hrUEdge
  exact hrUEdge.trans
    (RootReachableRelation.edges_subset
      (M.oldPriorityAttachedEdges A) A.initialSet)

#print axioms rootReachableOldPriority_infinitelyManyStrong

end PostClosureMacroCompressorAssignment
end Erdos599.Blueprint.LinkageBlueprint
