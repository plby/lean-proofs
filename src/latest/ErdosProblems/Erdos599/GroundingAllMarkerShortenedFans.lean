/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerRayShortening

/-!
# Stationary request fans with normalized ray origins

Pointwise shortening preserves both endpoints and decreases support.
Taking its image therefore preserves joinedness and the exact initial
index set. Every ray-origin path now avoids its own carrier except at
its source proxy, while all cut and hanging-fragment avoidance survives.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}

theorem exists_shortened_pruned_path {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.prunedRecordFan S r).paths) :
    ∃ q : FinitePath L.web.graph, q.start = p.start ∧ q.finish = p.finish ∧
      q.support ⊆ p.support ∧
      ∀ (i : I) (ray : Ray G.graph), p.start = .source i → L.record i = .inr ray →
        q.support ∩ L.recordCarrier i ⊆ {Vertex.source i} := by
  obtain ⟨i, hpi, hiGood⟩ := L.prunedRecordFan_start_good_record S r hp
  cases hrecord : L.record i with
  | inl f =>
      refine ⟨p, rfl, rfl, Set.Subset.rfl, ?_⟩
      intro j ray hpj hj
      have hji : j = i := Vertex.source.inj (hpj.symm.trans hpi)
      subst j
      rw [hrecord] at hj
      cases hj
  | inr ray =>
      have hfinish : p.finish ∉ L.recordCarrier i := by
        rw [L.goodRecordFan_finish S r (L.prunedRecordFan_subset_good S r hp)]
        exact L.goodRecordFan_request_not_in_origin_carrier S r hiGood
      obtain ⟨q, hqs, hqt, hqSub, hqOwn⟩ :=
        L.exists_ray_record_shortening i ray hrecord (hInitial i) p hpi hfinish
      refine ⟨q, hqs, hqt, hqSub, ?_⟩
      intro j _ hpj _
      have hji : j = i := Vertex.source.inj (hpj.symm.trans hpi)
      subst j
      exact hqOwn

def shortenedPrunedPath {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    (p : (L.prunedRecordFan S r).paths) : FinitePath L.web.graph :=
  Classical.choose (L.exists_shortened_pruned_path S r hInitial p.2)

theorem shortenedPrunedPath_spec {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    (p : (L.prunedRecordFan S r).paths) :
    (L.shortenedPrunedPath S r hInitial p).start = p.1.start ∧
      (L.shortenedPrunedPath S r hInitial p).finish = p.1.finish ∧
      (L.shortenedPrunedPath S r hInitial p).support ⊆ p.1.support ∧
      ∀ (i : I) (ray : Ray G.graph), p.1.start = .source i → L.record i = .inr ray →
        (L.shortenedPrunedPath S r hInitial p).support ∩ L.recordCarrier i ⊆ {Vertex.source i} :=
  Classical.choose_spec (L.exists_shortened_pruned_path S r hInitial p.2)

def shortenedRecordFan {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers) :
    Popular.JoinedFamily L.web {r.1} where
  paths := Set.range (L.shortenedPrunedPath S r hInitial)
  starts_in_source := by
    rintro q ⟨p, rfl⟩
    rw [(L.shortenedPrunedPath_spec S r hInitial p).1]
    exact (L.prunedRecordFan S r).starts_in_source p.2
  ends_in_join := by
    rintro q ⟨p, rfl⟩
    rw [(L.shortenedPrunedPath_spec S r hInitial p).2.1]
    exact (L.prunedRecordFan S r).ends_in_join p.2
  join_only_at_end := by
    rintro q ⟨p, rfl⟩ z hz
    have hspec := L.shortenedPrunedPath_spec S r hInitial p
    have hzEnd := (L.prunedRecordFan S r).join_only_at_end p.2 ⟨hspec.2.2.1 hz.1, hz.2⟩
    exact hzEnd.trans hspec.2.1.symm
  joined := by
    rintro q ⟨p, rfl⟩ q' ⟨p', rfl⟩ hqq z hz
    have hpp : p.1 ≠ p'.1 := by
      intro h
      exact hqq (congrArg (L.shortenedPrunedPath S r hInitial) (Subtype.ext h))
    exact (L.prunedRecordFan S r).joined p.2 p'.2 hpp
      ⟨(L.shortenedPrunedPath_spec S r hInitial p).2.2.1 hz.1,
        (L.shortenedPrunedPath_spec S r hInitial p').2.2.1 hz.2⟩

/-- The image construction loses no initial indices and introduces none. -/
theorem shortenedRecordFan_indices {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers) :
    Popular.initialIndicesOf U (L.shortenedRecordFan S r hInitial).paths
        (L.shortenedRecordFan S r hInitial).starts_in_source =
      Popular.initialIndicesOf U (L.prunedRecordFan S r).paths
        (L.prunedRecordFan S r).starts_in_source := by
  ext a
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqa⟩
    refine ⟨p.1, p.2, ?_⟩
    have hsource :
        (⟨(L.shortenedPrunedPath S r hInitial p).start,
          (L.shortenedRecordFan S r hInitial).starts_in_source ⟨p, rfl⟩⟩ : L.web.source) =
        ⟨p.1.start, (L.prunedRecordFan S r).starts_in_source p.2⟩ :=
      Subtype.ext (L.shortenedPrunedPath_spec S r hInitial p).1
    exact (congrArg U.f hsource).symm.trans hqa
  · rintro ⟨p, hp, hpa⟩
    let t : (L.prunedRecordFan S r).paths := ⟨p, hp⟩
    refine ⟨L.shortenedPrunedPath S r hInitial t, ⟨t, rfl⟩, ?_⟩
    have hsource :
        (⟨(L.shortenedPrunedPath S r hInitial t).start,
          (L.shortenedRecordFan S r hInitial).starts_in_source ⟨t, rfl⟩⟩ : L.web.source) =
        ⟨p.start, (L.prunedRecordFan S r).starts_in_source hp⟩ :=
      Subtype.ext (L.shortenedPrunedPath_spec S r hInitial t).1
    exact (congrArg U.f hsource).trans hpa

theorem shortenedRecordFan_stationary {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U (L.shortenedRecordFan S r hInitial).paths
        (L.shortenedRecordFan S r hInitial).starts_in_source) := by
  rw [L.shortenedRecordFan_indices S r hInitial]
  exact L.prunedRecordFan_stationary S r

theorem shortenedRecordFan_cut_normalized {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) :
    q.support ∩ S.cut ⊆ {r.1} := by
  obtain ⟨p, rfl⟩ := hq
  intro z hz
  exact L.prunedRecordFan_cut_normalized S r p.2
    ⟨(L.shortenedPrunedPath_spec S r hInitial p).2.2.1 hz.1, hz.2⟩

theorem shortenedRecordFan_start_good_record {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) :
    ∃ i : I, q.start = Vertex.source i ∧ i ∉ L.badRecords S.cut := by
  obtain ⟨p, rfl⟩ := hq
  obtain ⟨i, hpi, hi⟩ := L.prunedRecordFan_start_good_record S r p.2
  exact ⟨i, (L.shortenedPrunedPath_spec S r hInitial p).1.trans hpi, hi⟩

theorem shortenedRecordFan_avoids_hanging_fragment
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments S.cut) (hHang : ¬ L.CutFragmentGrounded P) :
    Disjoint q.support (L.fragmentEdgeVertices P) := by
  obtain ⟨p, rfl⟩ := hq
  exact (L.prunedRecordFan_avoids_hanging_fragment S r hInitials p.2 hP hHang).mono_left
    (L.shortenedPrunedPath_spec S r hInitial p).2.2.1

theorem shortenedRecordFan_own_ray_carrier {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    (i : I) (ray : Ray G.graph) (hqi : q.start = .source i) (hi : L.record i = .inr ray) :
    q.support ∩ L.recordCarrier i ⊆ {Vertex.source i} := by
  obtain ⟨p, rfl⟩ := hq
  have hspec := L.shortenedPrunedPath_spec S r hInitial p
  exact hspec.2.2.2 i ray (hspec.1.symm.trans hqi) hi

/-- No represented receiving or sending coordinate of the shortened path
lies on its origin ray. Its only physical ray contact is the original
departure encoded by the source proxy's first arc. -/
theorem shortenedRecordFan_own_ray_ports {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    (i : I) (ray : Ray G.graph) (hqi : q.start = .source i) (hi : L.record i = .inr ray)
    {a : L.Vertex} (ha : a ∈ q.support) {x : V} (hx : x ∈ ray.support) :
    L.sending a ≠ some x ∧ L.receiving a ≠ some x := by
  have hxRecord : x ∈ (L.record i).support := by simpa only [hi, Path.support] using hx
  have hOwn := L.shortenedRecordFan_own_ray_carrier S r hInitial hq i ray hqi hi
  constructor
  · intro hsend
    obtain ⟨b, hb, hbsend⟩ := L.exists_recordCarrier_sending i hxRecord
    have hab : a = b := L.sending_unique hsend hbsend
    have haOwn : a ∈ L.recordCarrier i := hab.symm ▸ hb
    have hai : a = .source i := hOwn ⟨ha, haOwn⟩
    simp [hai, sending, hi] at hsend
  · intro hreceive
    have haOwn := L.receiving_mem_recordCarrier i (hInitial i) hreceive hxRecord
    have hai : a = .source i := hOwn ⟨ha, haOwn⟩
    simp [hai, receiving] at hreceive

#print axioms shortenedRecordFan
#print axioms shortenedRecordFan_indices
#print axioms shortenedRecordFan_stationary
#print axioms shortenedRecordFan_own_ray_carrier
#print axioms shortenedRecordFan_own_ray_ports

end Erdos599.GroundingAllMarkerAuxiliary.Input
