/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerRequestFans

/-!
# Restricting normalized request fans to surviving record owners

The initial indices removed from a normalized request fan form a subset of
the already-proved nonstationary bad-record set. The remaining initial
indices are exactly the original fan indices minus that set. The resulting
stationary family has genuine good record sources and retains cut avoidance
and strict-roof localization. No stationarity assertion is added as a new
input beyond the popular separator.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}

def goodRecordFan {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Popular.JoinedFamily L.web {r.1} where
  paths := {p | ∃ hp : p ∈ (L.normalizedRequestFan S r).paths,
    U.f ⟨p.start, (L.normalizedRequestFan S r).starts_in_source hp⟩ ∉
      L.badRecordIndices U S.cut}
  starts_in_source := by
    rintro p ⟨hp, _⟩
    exact (L.normalizedRequestFan S r).starts_in_source hp
  ends_in_join := by
    rintro p ⟨hp, _⟩
    exact (L.normalizedRequestFan S r).ends_in_join hp
  join_only_at_end := by
    rintro p ⟨hp, _⟩
    exact (L.normalizedRequestFan S r).join_only_at_end hp
  joined := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact (L.normalizedRequestFan S r).joined hp hq hpq

theorem goodRecordFan_subset_normalized {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    (L.goodRecordFan S r).paths ⊆ (L.normalizedRequestFan S r).paths := by
  rintro p ⟨hp, _⟩
  exact hp

theorem goodRecordFan_indices {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Popular.initialIndicesOf U (L.goodRecordFan S r).paths
        (L.goodRecordFan S r).starts_in_source =
      Popular.initialIndicesOf U (L.normalizedRequestFan S r).paths
        (L.normalizedRequestFan S r).starts_in_source \ L.badRecordIndices U S.cut := by
  ext a
  constructor
  · rintro ⟨p, hp, hpa⟩
    obtain ⟨hpF, hgood⟩ := hp
    refine ⟨⟨p, hpF, hpa⟩, ?_⟩
    intro ha
    apply hgood
    rwa [hpa]
  · rintro ⟨⟨p, hp, hpa⟩, hgood⟩
    have hpGood : p ∈ (L.goodRecordFan S r).paths :=
      ⟨hp, by simpa only [hpa] using hgood⟩
    exact ⟨p, hpGood, hpa⟩

theorem goodRecordFan_stationary {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U (L.goodRecordFan S r).paths
        (L.goodRecordFan S r).starts_in_source) := by
  rw [L.goodRecordFan_indices S r]
  exact PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable (L.normalizedRequestFan_stationary S r)
    (L.badRecordIndices_nonstationary U S)

theorem goodRecordFan_cut_normalized {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.goodRecordFan S r).paths) :
    p.support ∩ S.cut ⊆ {r.1} :=
  L.normalizedRequestFan_cut_normalized S r (L.goodRecordFan_subset_normalized S r hp)

theorem goodRecordFan_support_subset {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.goodRecordFan S r).paths) :
    p.support ⊆ L.web.strictRoof S.cut ∪ {r.1} :=
  L.normalizedRequestFan_support_subset S r (L.goodRecordFan_subset_normalized S r hp)

theorem goodRecordFan_finish {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.goodRecordFan S r).paths) :
    p.finish = r.1 := (L.goodRecordFan S r).ends_in_join hp

theorem goodRecordFan_start_index_good {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.goodRecordFan S r).paths) :
    U.f ⟨p.start, (L.goodRecordFan S r).starts_in_source hp⟩ ∈
      L.goodRecordIndices U S.cut := by
  obtain ⟨hpF, hgood⟩ := hp
  exact ⟨⟨⟨p.start, (L.normalizedRequestFan S r).starts_in_source hpF⟩, rfl⟩, hgood⟩

/-- The surviving initial really is a good record source, with equality
of vertices, not merely equality of their potentially noninjective indices. -/
theorem goodRecordFan_start_good_record {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.goodRecordFan S r).paths) :
    ∃ i : I, p.start = Vertex.source i ∧ i ∉ L.badRecords S.cut := by
  obtain ⟨hpF, hgood⟩ := hp
  let x : L.web.source := ⟨p.start, (L.normalizedRequestFan S r).starts_in_source hpF⟩
  let i := L.sourceEquiv.symm x
  refine ⟨i, (L.sourceEquiv_symm_val x).symm, ?_⟩
  intro hi
  apply hgood
  refine ⟨i, ?_, hi⟩
  exact congrArg U.f (L.sourceEquiv.apply_symm_apply x)

/-- The request lies outside the complete carrier of its good origin
record. In particular the final cut edge cannot belong to that record. -/
theorem goodRecordFan_request_not_in_origin_carrier
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut) {i : I} (hi : i ∉ L.badRecords S.cut) :
    r.1 ∉ L.recordCarrier i := by
  intro hr
  exact Set.disjoint_left.mp (L.recordCarrier_disjoint_cut_of_not_bad S.cut hi) hr r.2.1

#print axioms goodRecordFan_indices
#print axioms goodRecordFan_stationary
#print axioms goodRecordFan_start_good_record
#print axioms goodRecordFan_request_not_in_origin_carrier

end Erdos599.GroundingAllMarkerAuxiliary.Input
