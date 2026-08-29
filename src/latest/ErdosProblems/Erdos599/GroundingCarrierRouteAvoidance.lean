/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentSplice
import ErdosProblems.Erdos599.JoinedFamilyOwnerThinning

/-!
# First-hit avoidance of disjoint countable carriers with routes to the cut

Each carrier avoids the join, is countable, and supplies internal finite
routes to the popular cut. Stationary first-hit owner thinning and actual
pairwise-disjoint splicing contradict the failure of strong popularity.
No fragment or parent-grounding predicate occurs in this generic lemma.
-/

noncomputable section

namespace Erdos599.Popular

open Cardinal Order Set DirectedPath Stationary

universe u v

/-- A joined fan cannot stationarily meet disjoint countable off-join
carriers which supply internal paths to a non-strongly-popular cut. -/
theorem initialIndices_nonstationary_of_carrier_routes
    {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa) (S : PopularSeparator U)
    {D : Set V} (F : JoinedFamily Gamma D) {X : Type v}
    (Z : X → Set V) (hcount : ∀ i, (Z i).Countable)
    (hoff : ∀ i, Disjoint (Z i) D)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    (hroute : ∀ i x, x ∈ Z i → ∃ q : FinitePath Gamma.graph,
      q.start = x ∧ q.finish ∈ S.cut ∧ q.support ⊆ Z i) :
    ¬ IsStationaryBelow kappa
      (initialIndicesOf U
        (PopularSwitching.restrictPaths F {p | p.walk.Meets (⋃ i, Z i)}).paths
        (PopularSwitching.restrictPaths F
          {p | p.walk.Meets (⋃ i, Z i)}).starts_in_source) := by
  classical
  let H := ⋃ i, Z i
  let F' := PopularSwitching.restrictPaths F {p | p.walk.Meets H}
  let A := initialIndicesOf U F'.paths F'.starts_in_source
  intro hstationary
  change IsStationaryBelow kappa A at hstationary
  have hdata (a : A) : ∃ p, ∃ hp : p ∈ F'.paths,
      U.f ⟨p.start, F'.starts_in_source hp⟩ = a.1 := a.2
  choose p hp hindex using hdata
  let pre (a : A) := (p a).firstHit H (hp a).2
  have howner (a : A) : ∃ i, (pre a).finish ∈ Z i :=
    Set.mem_iUnion.mp ((p a).firstHit_finish_mem H (hp a).2)
  choose owner hfinish using howner
  obtain ⟨a₀, ha₀⟩ := hstationary.nonempty
  let totalOwner (a : Below kappa) : X :=
    if ha : a ∈ A then owner ⟨a, ha⟩ else owner ⟨a₀, ha₀⟩
  have htotal (a : A) : totalOwner a.1 = owner a := by
    simp only [totalOwner, dif_pos a.2]
  obtain ⟨B, hBA, hBstationary, hownerInj⟩ :=
    exists_stationary_owner_transversal U F' hstationary totalOwner Z
      hcount hoff (by
        intro a ha
        let j : A := ⟨a, ha⟩
        refine ⟨p j, hp j, hindex j, (pre j).finish, ?_, ?_⟩
        · rw [htotal j]
          exact hfinish j
        · exact (p j).firstHit_support_subset H (hp j).2
            (pre j).finish_mem_support)
  let inc : B → A := fun b ↦ ⟨b.1, hBA b.2⟩
  have hownerNe {j k : B} (hjk : j ≠ k) : owner (inc j) ≠ owner (inc k) := by
    intro heq
    apply hjk
    apply Subtype.ext
    apply hownerInj j.2 k.2
    exact (htotal (inc j)).trans (heq.trans (htotal (inc k)).symm)
  have hpathNe {j k : B} (hjk : j ≠ k) : p (inc j) ≠ p (inc k) := by
    intro heq
    apply hjk
    apply Subtype.ext
    have hs :
        (⟨(p (inc j)).start, F'.starts_in_source (hp (inc j))⟩ : Gamma.source) =
          ⟨(p (inc k)).start, F'.starts_in_source (hp (inc k))⟩ :=
      Subtype.ext (congrArg FinitePath.start heq)
    exact (hindex (inc j)).symm.trans ((congrArg U.f hs).trans (hindex (inc k)))
  have hHD : Disjoint H D := by
    apply Set.disjoint_left.2
    intro x hxH hxD
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxH
    exact Set.disjoint_left.1 (hoff i) hxi hxD
  have hpreDisjoint {j k : B} (hjk : j ≠ k) :
      Disjoint (pre (inc j)).support (pre (inc k)).support := by
    apply Set.disjoint_left.2
    intro x hxj hxk
    have hxD := F.joined (hp (inc j)).1 (hp (inc k)).1 (hpathNe hjk)
      ⟨(p (inc j)).firstHit_support_subset H (hp (inc j)).2 hxj,
        (p (inc k)).firstHit_support_subset H (hp (inc k)).2 hxk⟩
    exact Set.disjoint_left.1
      (PopularSwitching.firstHit_support_disjoint_join F hHD
        (hp (inc j)).1 (hp (inc j)).2) hxj hxD
  have hpreZDisjoint {j k : B} (hjk : j ≠ k) :
      Disjoint (pre (inc j)).support (Z (owner (inc k))) := by
    apply Set.disjoint_left.2
    intro x hxj hxk
    have hxH : x ∈ H := Set.mem_iUnion.2 ⟨owner (inc k), hxk⟩
    have heq : x = (pre (inc j)).finish := Set.mem_singleton_iff.mp
      (GroundingFragmentSplice.firstHit_inter_subset_finish
        (p (inc j)) H (hp (inc j)).2 ⟨hxj, hxH⟩)
    exact Set.disjoint_left.1 (hdisjoint (hownerNe hjk))
      (heq ▸ hfinish (inc j)) hxk
  choose tail htailStart htailCut htailSupport using
    fun j : B ↦ hroute (owner (inc j)) (pre (inc j)).finish (hfinish (inc j))
  have hinter (j : B) : (pre (inc j)).support ∩ (tail j).support ⊆
      {(pre (inc j)).finish} := by
    intro x hx
    exact GroundingFragmentSplice.firstHit_inter_subset_finish
      (p (inc j)) H (hp (inc j)).2
      ⟨hx.1, Set.mem_iUnion.2 ⟨owner (inc j), htailSupport j hx.2⟩⟩
  let q (j : B) := (pre (inc j)).appendFinite (tail j) (htailStart j) (hinter j)
  have hqStart (j : B) : (q j).start = (p (inc j)).start :=
    FinitePath.appendFinite_start _ _ _ _
  have hqCut (j : B) : (q j).finish ∈ S.cut := by
    change ((pre (inc j)).appendFinite (tail j) (htailStart j) (hinter j)).finish ∈ S.cut
    rw [FinitePath.appendFinite_finish]
    exact htailCut j
  have hqSupport (j : B) : (q j).support ⊆
      (pre (inc j)).support ∪ Z (owner (inc j)) := by
    rw [show (q j).support = (pre (inc j)).support ∪ (tail j).support from
      FinitePath.support_appendFinite_eq_union _ _ _ _]
    exact Set.union_subset_union_right _ (htailSupport j)
  have hqDisjoint {j k : B} (hjk : j ≠ k) : Disjoint (q j).support (q k).support := by
    apply Set.disjoint_left.2
    intro x hxj hxk
    rcases hqSupport j hxj with hxj | hxj
    · rcases hqSupport k hxk with hxk | hxk
      · exact Set.disjoint_left.1 (hpreDisjoint hjk) hxj hxk
      · exact Set.disjoint_left.1 (hpreZDisjoint hjk) hxj hxk
    · rcases hqSupport k hxk with hxk | hxk
      · exact Set.disjoint_left.1 (hpreZDisjoint (Ne.symm hjk)) hxk hxj
      · exact Set.disjoint_left.1 (hdisjoint (hownerNe hjk)) hxj hxk
  let W : XSWarp Gamma S.cut := {
    paths := Set.range q
    disjoint := by
      rintro s ⟨j, rfl⟩ t ⟨k, rfl⟩ hne
      exact hqDisjoint (fun h ↦ hne (congrArg q h))
    starts_in_source := by
      rintro s ⟨j, rfl⟩
      rw [hqStart]
      exact F'.starts_in_source (hp (inc j))
    ends_in_target := by
      rintro s ⟨j, rfl⟩
      exact hqCut j }
  apply S.not_strongly_popular
  refine ⟨W, hBstationary.mono ?_⟩
  intro a ha
  let j : B := ⟨a, ha⟩
  have hqW : q j ∈ W.paths := ⟨j, rfl⟩
  refine ⟨q j, hqW, ?_⟩
  have hs : (⟨(q j).start, W.starts_in_source hqW⟩ : Gamma.source) =
      ⟨(p (inc j)).start, F'.starts_in_source (hp (inc j))⟩ :=
    Subtype.ext (hqStart j)
  exact (congrArg U.f hs).trans (hindex (inc j))

#print axioms initialIndices_nonstationary_of_carrier_routes

end Erdos599.Popular
