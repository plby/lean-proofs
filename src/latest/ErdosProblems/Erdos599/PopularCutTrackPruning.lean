/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.JoinedFamilyOwnerThinning
import ErdosProblems.Erdos599.PopularLayers

/-!
# First-contact transfer from countable tracks to a cut

Disjoint countable tracks avoid the cut and lead internally to distinct
cut endpoints. A normalized singleton fan cannot hit their union at a
stationary set of initial indices when the cut is not strongly popular.
The construction preserves each selected original source: it keeps the
prefix to the first track contact and appends a tail inside that track.
-/

noncomputable section

namespace Erdos599.Popular

open Set Cardinal DirectedPath Stationary

universe u v

variable {V : Type u} {J : Type v} {Gamma : DWeb V} {kappa : Cardinal.{u}}

structure CutTrackFamily (Gamma : DWeb V) (C : Set V) (J : Type v) where
  carrier : J → Set V
  countable : ∀ j, (carrier j).Countable
  disjoint : Pairwise (fun i j ↦ Disjoint (carrier i) (carrier j))
  avoids_cut : ∀ j, Disjoint (carrier j) C
  endpoint : J → V
  endpoint_mem : ∀ j, endpoint j ∈ C
  endpoint_injective : Function.Injective endpoint
  continuation : ∀ j x, x ∈ carrier j →
    ∃ p : FinitePath Gamma.graph, p.start = x ∧ p.finish = endpoint j ∧
      p.support ⊆ carrier j ∪ {endpoint j}

namespace CutTrackFamily

variable {C : Set V} (T : CutTrackFamily Gamma C J)

def tracks : Set V := ⋃ j, T.carrier j

def enlarged (j : J) : Set V := T.carrier j ∪ {T.endpoint j}

theorem tracks_disjoint_cut : Disjoint T.tracks C := by
  apply Set.disjoint_left.mpr
  rintro x hx hxC
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
  exact Set.disjoint_left.mp (T.avoids_cut j) hxj hxC

theorem enlarged_disjoint : Pairwise (fun i j ↦ Disjoint (T.enlarged i) (T.enlarged j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x (hxi | rfl) (hxj | hxe)
  · exact Set.disjoint_left.mp (T.disjoint hij) hxi hxj
  · exact Set.disjoint_left.mp (T.avoids_cut i) hxi (hxe ▸ T.endpoint_mem j)
  · exact Set.disjoint_left.mp (T.avoids_cut j) hxj (T.endpoint_mem i)
  · exact hij (T.endpoint_injective hxe)

private theorem append_continuation (q : FinitePath Gamma.graph) (j : J)
    (hq : q.finish ∈ T.carrier j) :
    ∃ p : FinitePath Gamma.graph, p.start = q.start ∧ p.finish = T.endpoint j ∧
      p.support ⊆ q.support ∪ T.enlarged j := by
  obtain ⟨r, hrStart, hrEnd, hrSupport⟩ := T.continuation j q.finish hq
  let rw : Walk Gamma.graph q.finish r.finish :=
    RelationalRoof.castStart Gamma.graph.Adj hrStart r.walk
  let w := q.walk.append rw
  obtain ⟨s, hs⟩ := RelationalRoof.exists_pathTo_support_subset (R := Gamma.graph.Adj) w
  refine ⟨⟨q.start, r.finish, s.1, s.2⟩, rfl, hrEnd, ?_⟩
  intro z hz
  have hzw := hs hz
  simp only [w, Walk.support_append, List.mem_append] at hzw
  rcases hzw with hzq | hzr
  · exact Or.inl hzq
  · apply Or.inr
    apply hrSupport
    change z ∈ r.walk.support
    have hzrw := List.mem_of_mem_tail hzr
    simpa only [rw, RelationalRoof.support_castStart] using hzrw

/-- A stationary set of first contacts can be thinned to distinct tracks,
then extended to a disjoint source--cut warp with stationary initial image. -/
theorem contact_indices_not_stationary (U : KappaIndexed Gamma kappa)
    {s : V} (hs : s ∈ C) (F : JoinedFamily Gamma {s})
    (hF : ∀ {p}, p ∈ F.paths → p.support ∩ C ⊆ {s})
    (hC : ¬ IsStronglyPopular U C) :
    ¬ IsStationaryBelow kappa
      (initialIndicesOf U (PopularSwitching.restrictPaths F
        {p | p.walk.Meets T.tracks}).paths
        (PopularSwitching.restrictPaths F {p | p.walk.Meets T.tracks}).starts_in_source) := by
  classical
  let H := PopularSwitching.restrictPaths F {p | p.walk.Meets T.tracks}
  let A := initialIndicesOf U H.paths H.starts_in_source
  intro hA
  change IsStationaryBelow kappa A at hA
  have hchoose (a : A) : ∃ (p : FinitePath Gamma.graph) (hp : p ∈ H.paths),
      U.f ⟨p.start, H.starts_in_source hp⟩ = a.1 := a.2
  choose path hpath hindex using hchoose
  let front (a : A) := (path a).firstHit T.tracks (hpath a).2
  have hcontact (a : A) : (front a).finish ∈ T.tracks :=
    (path a).firstHit_finish_mem T.tracks (hpath a).2
  let owner (a : A) : J := Classical.choose (Set.mem_iUnion.mp (hcontact a))
  have howner (a : A) : (front a).finish ∈ T.carrier (owner a) :=
    Classical.choose_spec (Set.mem_iUnion.mp (hcontact a))
  have hprefSupport (a : A) : (front a).support ⊆ (path a).support :=
    (path a).firstHit_support_subset T.tracks (hpath a).2
  have hprefCut (a : A) : Disjoint (front a).support C := by
    apply Set.disjoint_left.mpr
    intro x hx hxC
    have hxs : x = s := hF (hpath a).1 ⟨hprefSupport a hx, hxC⟩
    have hfinish : (path a).finish = s := F.ends_in_join (hpath a).1
    have hnot : (path a).finish ∉ T.tracks := by
      rw [hfinish]
      exact fun ht ↦ Set.disjoint_left.mp T.tracks_disjoint_cut ht hs
    exact firstHit_not_mem_of_finish_not_mem (path a) T.tracks (hpath a).2 hnot
      ((hxs.trans hfinish.symm) ▸ hx)
  have hprefTracks (a : A) : (front a).support ∩ T.tracks ⊆ {(front a).finish} := by
    intro x hx
    by_contra hne
    have hxdrop : x ∈ (front a).walk.support.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hx.1
      simpa only [Walk.getLast_support, Set.mem_singleton_iff] using hne
    exact (path a).firstHit_no_mem_before T.tracks (hpath a).2 hxdrop hx.2
  obtain ⟨a0, ha0⟩ := hA.nonempty
  let totalOwner (a : Below kappa) : J :=
    if ha : a ∈ A then owner ⟨a, ha⟩ else owner ⟨a0, ha0⟩
  have htotal (a : A) : totalOwner a.1 = owner a := by
    simp only [totalOwner, dif_pos a.2]
  obtain ⟨B, hBA, hB, hBinj⟩ := exists_stationary_owner_transversal U H hA
    totalOwner T.carrier T.countable
    (fun j ↦ Set.disjoint_left.mpr (fun _ hx hxs ↦
      Set.disjoint_left.mp (T.avoids_cut j) hx (hxs ▸ hs))) (by
      intro a ha
      let b : A := ⟨a, ha⟩
      refine ⟨path b, hpath b, hindex b, (front b).finish, ?_, ?_⟩
      · rw [htotal b]
        exact howner b
      · exact hprefSupport b (front b).finish_mem_support)
  let old (b : B) : A := ⟨b.1, hBA b.2⟩
  have hOwners {a b : B} (hab : a ≠ b) : owner (old a) ≠ owner (old b) := by
    intro h
    have htotalEq : totalOwner a.1 = totalOwner b.1 :=
      (htotal (old a)).trans (h.trans (htotal (old b)).symm)
    exact hab (Subtype.ext (hBinj a.2 b.2 htotalEq))
  have hPrefixes {a b : B} (hab : a ≠ b) :
      Disjoint (front (old a)).support (front (old b)).support := by
    have hpne : path (old a) ≠ path (old b) := by
      intro hpEq
      have hsrc : (⟨(path (old a)).start, H.starts_in_source (hpath (old a))⟩ : Gamma.source) =
          ⟨(path (old b)).start, H.starts_in_source (hpath (old b))⟩ :=
        Subtype.ext (congrArg FinitePath.start hpEq)
      exact hab (Subtype.ext ((hindex (old a)).symm.trans
        ((congrArg U.f hsrc).trans (hindex (old b)))))
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hxs : x = s := F.joined (hpath (old a)).1 (hpath (old b)).1 hpne
      ⟨hprefSupport (old a) hxa, hprefSupport (old b) hxb⟩
    exact Set.disjoint_left.mp (hprefCut (old a)) hxa (hxs ▸ hs)
  have hPrefixTail {a b : B} (hab : a ≠ b) :
      Disjoint (front (old a)).support (T.enlarged (owner (old b))) := by
    apply Set.disjoint_left.mpr
    rintro x hxa (hxb | hxb)
    · have hxTracks : x ∈ T.tracks := Set.mem_iUnion.mpr ⟨owner (old b), hxb⟩
      have hxFirst : x = (front (old a)).finish := hprefTracks (old a) ⟨hxa, hxTracks⟩
      exact Set.disjoint_left.mp (T.disjoint (hOwners hab)) (hxFirst ▸ howner (old a)) hxb
    · exact Set.disjoint_left.mp (hprefCut (old a)) hxa (hxb ▸ T.endpoint_mem (owner (old b)))
  have hQ (b : B) : ∃ q : FinitePath Gamma.graph,
      q.start = (front (old b)).start ∧ q.finish = T.endpoint (owner (old b)) ∧
        q.support ⊆ (front (old b)).support ∪ T.enlarged (owner (old b)) :=
    T.append_continuation (front (old b)) (owner (old b)) (howner (old b))
  choose Q hQStart hQEnd hQSupport using hQ
  let W : XSWarp Gamma C := {
    paths := Set.range Q
    disjoint := by
      rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hpq
      have hab : a ≠ b := fun h ↦ hpq (congrArg Q h)
      apply Set.disjoint_left.mpr
      intro x hxa hxb
      rcases hQSupport a hxa with hxa | hxa
      · rcases hQSupport b hxb with hxb | hxb
        · exact Set.disjoint_left.mp (hPrefixes hab) hxa hxb
        · exact Set.disjoint_left.mp (hPrefixTail hab) hxa hxb
      · rcases hQSupport b hxb with hxb | hxb
        · exact Set.disjoint_left.mp (hPrefixTail hab.symm) hxb hxa
        · exact Set.disjoint_left.mp (T.enlarged_disjoint (hOwners hab)) hxa hxb
    starts_in_source := by
      rintro p ⟨b, rfl⟩
      rw [hQStart b]
      change (path (old b)).start ∈ Gamma.source
      exact H.starts_in_source (hpath (old b))
    ends_in_target := by
      rintro p ⟨b, rfl⟩
      rw [hQEnd b]
      exact T.endpoint_mem (owner (old b)) }
  apply hC
  refine ⟨W, hB.mono ?_⟩
  intro a ha
  let b : B := ⟨a, ha⟩
  have hmem : Q b ∈ W.paths := ⟨b, rfl⟩
  refine ⟨Q b, hmem, ?_⟩
  have hsrc : (⟨(Q b).start, W.starts_in_source hmem⟩ : Gamma.source) =
      ⟨(path (old b)).start, H.starts_in_source (hpath (old b))⟩ :=
    Subtype.ext (hQStart b)
  exact (congrArg U.f hsrc).trans (hindex (old b))

/-- The actual pruned family, not merely a bound on its discarded paths. -/
def avoidingFan {s : V} (F : JoinedFamily Gamma {s}) : JoinedFamily Gamma {s} :=
  PopularSwitching.restrictPaths F {p | ¬ p.walk.Meets T.tracks}

theorem avoidingFan_stationary (U : KappaIndexed Gamma kappa)
    {s : V} (hs : s ∈ C) (F : JoinedFamily Gamma {s})
    (hF : ∀ {p}, p ∈ F.paths → p.support ∩ C ⊆ {s})
    (hC : ¬ IsStronglyPopular U C)
    (hstat : IsStationaryBelow kappa (initialIndicesOf U F.paths F.starts_in_source)) :
    IsStationaryBelow kappa
      (initialIndicesOf U (T.avoidingFan F).paths (T.avoidingFan F).starts_in_source) := by
  have hbad := T.contact_indices_not_stationary U hs F hF hC
  have hremain := PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable hstat hbad
  apply hremain.mono
  rintro a ⟨⟨p, hp, hpa⟩, hnot⟩
  have havoid : ¬ p.walk.Meets T.tracks := by
    intro hmeet
    exact hnot ⟨p, ⟨hp, hmeet⟩, hpa⟩
  exact ⟨p, ⟨hp, havoid⟩, hpa⟩

theorem avoidingFan_disjoint_tracks {s : V} (F : JoinedFamily Gamma {s})
    {p : FinitePath Gamma.graph} (hp : p ∈ (T.avoidingFan F).paths) :
    Disjoint p.support T.tracks :=
  Set.disjoint_left.mpr (fun x hxp hxt ↦ hp.2 ⟨x, hxp, hxt⟩)

theorem avoidingFan_cut_normalized {s : V} (F : JoinedFamily Gamma {s})
    (hF : ∀ {p}, p ∈ F.paths → p.support ∩ C ⊆ {s})
    {p : FinitePath Gamma.graph} (hp : p ∈ (T.avoidingFan F).paths) :
    p.support ∩ C ⊆ {s} := hF hp.1

#print axioms contact_indices_not_stationary
#print axioms avoidingFan_stationary

end CutTrackFamily
end Erdos599.Popular
