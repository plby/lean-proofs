/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeBatchCounterexample

/-!
# The crossing obstruction has an unhindered old quotient

This file strengthens `SingularSafeBatchCounterexample`: the displayed
minimal separating boundary is also a genuine half-way stop-over.  Its old
quotient is unhindered, although deleting the completed carrier before
quotienting destroys the pending request.  Thus the obstruction is not an
artifact of omitting the quotient-unhindered field.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeBatchCounterexample

open DirectedPath SingularExtension SingularSafeBatch
  SingularFutureSafeBatch
open Vertex

/-- The surviving `w`--target suffix. -/
def wt2 : FinitePath web.graph where
  start := w
  finish := t2
  walk := Walk.cons (u := w) (v := t2) (w := t2) (by simp [web, graph]) Walk.nil
  isPath := by
    change [w, t2].Nodup
    simp

/-- The surviving `x`--target suffix. -/
def xr : FinitePath web.graph where
  start := x
  finish := r
  walk := Walk.cons (u := x) (v := r) (w := r) (by simp [web, graph]) Walk.nil
  isPath := by
    change [x, r].Nodup
    simp

@[simp] theorem support_wt2 : wt2.support = ({w, t2} : Set Vertex) := by
  ext v
  change v ∈ [w, t2] ↔ _
  simp

@[simp] theorem support_xr : xr.support = ({x, r} : Set Vertex) := by
  ext v
  change v ∈ [x, r] ↔ _
  simp

/-- The old `d-w-t2` path, with its graph definitionally exposed as the
web graph. -/
def webDwt2 : FinitePath web.graph where
  start := d
  finish := t2
  walk := Walk.cons (u := d) (v := w) (w := t2) (by simp [web, graph])
    (Walk.cons (u := w) (v := t2) (w := t2) (by simp [web, graph]) Walk.nil)
  isPath := by
    change [d, w, t2].Nodup
    simp

/-- The old `y-x-r` path, with its graph definitionally exposed as the web
graph. -/
def webYxr : FinitePath web.graph where
  start := y
  finish := r
  walk := Walk.cons (u := y) (v := x) (w := r) (by simp [web, graph])
    (Walk.cons (u := x) (v := r) (w := r) (by simp [web, graph]) Walk.nil)
  isPath := by
    change [y, x, r].Nodup
    simp

@[simp] theorem support_webDwt2 :
    webDwt2.support = ({d, w, t2} : Set Vertex) := by
  ext v
  change v ∈ [d, w, t2] ↔ _
  simp [or_assoc]

@[simp] theorem support_webYxr :
    webYxr.support = ({y, x, r} : Set Vertex) := by
  ext v
  change v ∈ [y, x, r] ↔ _
  simp [or_assoc]

private theorem not_mem_roof_boundary_w : w ∉ web.roof boundary := by
  rw [web.not_mem_roof_iff]
  refine ⟨wt2, ⟨rfl, by simp [web, wt2]⟩, ?_⟩
  change Disjoint wt2.support boundary
  rw [support_wt2]
  exact Set.disjoint_left.2 (by
    intro v hv hC
    cases v <;> simp [boundary] at hv hC)

private theorem not_mem_roof_boundary_x : x ∉ web.roof boundary := by
  rw [web.not_mem_roof_iff]
  refine ⟨xr, ⟨rfl, by simp [web, xr]⟩, ?_⟩
  change Disjoint xr.support boundary
  rw [support_xr]
  exact Set.disjoint_left.2 (by
    intro v hv hC
    cases v <;> simp [boundary] at hv hC)

private theorem not_mem_roof_boundary_t2 : t2 ∉ web.roof boundary := by
  rw [web.not_mem_roof_iff]
  let p := FinitePath.trivial web.graph t2
  refine ⟨p, ⟨rfl, by simp [web, p]⟩, ?_⟩
  change Disjoint p.support boundary
  simp [p, boundary]

private theorem not_mem_roof_boundary_r : r ∉ web.roof boundary := by
  rw [web.not_mem_roof_iff]
  let p := FinitePath.trivial web.graph r
  refine ⟨p, ⟨rfl, by simp [web, p]⟩, ?_⟩
  change Disjoint p.support boundary
  simp [p, boundary]

private theorem d_not_mem_strictRoof : d ∉ web.strictRoof boundary := by
  intro hd
  exact Set.disjoint_left.1 (web.disjoint_strictRoof_essential boundary)
    hd (boundary_trimmed.symm ▸ (show d ∈ boundary by simp [boundary]))

private theorem y_not_mem_strictRoof : y ∉ web.strictRoof boundary := by
  intro hy
  exact Set.disjoint_left.1 (web.disjoint_strictRoof_essential boundary)
    hy (boundary_trimmed.symm ▸ (show y ∈ boundary by simp [boundary]))

private theorem dwt2_quotientAdmissible :
    web.QuotientAdmissible boundary (.inl webDwt2) := by
  constructor
  · change Disjoint webDwt2.support (web.strictRoof boundary)
    rw [support_webDwt2]
    apply Set.disjoint_left.2
    intro v hv hvStrict
    rcases hv with rfl | hv
    · exact d_not_mem_strictRoof hvStrict
    · rcases hv with rfl | hv
      · exact not_mem_roof_boundary_w hvStrict.1
      · have h : v = t2 := by simpa using hv
        subst v
        exact not_mem_roof_boundary_t2 hvStrict.1
  · intro u v huv hu hv
    change v ∈ webDwt2.support at hv
    rw [support_webDwt2] at hv
    rcases hv with rfl | hv
    · simpa [web, graph] using huv
    · rcases hv with rfl | hv
      · simp [boundary]
      · have h : v = t2 := by simpa using hv
        subst v
        simp [boundary]

private theorem yxr_quotientAdmissible :
    web.QuotientAdmissible boundary (.inl webYxr) := by
  constructor
  · change Disjoint webYxr.support (web.strictRoof boundary)
    rw [support_webYxr]
    apply Set.disjoint_left.2
    intro v hv hvStrict
    rcases hv with rfl | hv
    · exact y_not_mem_strictRoof hvStrict
    · rcases hv with rfl | hv
      · exact not_mem_roof_boundary_x hvStrict.1
      · have h : v = r := by simpa using hv
        subst v
        exact not_mem_roof_boundary_r hvStrict.1
  · intro u v huv hu hv
    change v ∈ webYxr.support at hv
    rw [support_webYxr] at hv
    rcases hv with rfl | hv
    · have hub : u = b := by simpa [web, graph] using huv
      subst u
      change b ∈ webYxr.support at hu
      rw [support_webYxr] at hu
      simp at hu
    · rcases hv with rfl | hv
      · simp [boundary]
      · have h : v = r := by simpa using hv
        subst v
        simp [boundary]

private theorem webDwt2_quotientEdge {u v : Vertex}
    (e : web.graph.Adj u v) (hu : u ∈ webDwt2.support)
    (hv : v ∈ webDwt2.support) :
    (web.quotient boundary).graph.Adj u v := by
  refine ⟨e, ?_, ?_, ?_⟩
  · have h := dwt2_quotientAdmissible.1
    change Disjoint webDwt2.support (web.strictRoof boundary) at h
    exact Set.disjoint_left.1 h hu
  · have h := dwt2_quotientAdmissible.1
    change Disjoint webDwt2.support (web.strictRoof boundary) at h
    exact Set.disjoint_left.1 h hv
  · exact dwt2_quotientAdmissible.2 (u := _) (v := _) e hu hv

def quotientDFinite : FinitePath (web.quotient boundary).graph :=
  webDwt2.restrictGraphOnSupport webDwt2_quotientEdge

private theorem webYxr_quotientEdge {u v : Vertex}
    (e : web.graph.Adj u v) (hu : u ∈ webYxr.support)
    (hv : v ∈ webYxr.support) :
    (web.quotient boundary).graph.Adj u v := by
  refine ⟨e, ?_, ?_, ?_⟩
  · have h := yxr_quotientAdmissible.1
    change Disjoint webYxr.support (web.strictRoof boundary) at h
    exact Set.disjoint_left.1 h hu
  · have h := yxr_quotientAdmissible.1
    change Disjoint webYxr.support (web.strictRoof boundary) at h
    exact Set.disjoint_left.1 h hv
  · exact yxr_quotientAdmissible.2 (u := _) (v := _) e hu hv

def quotientYFinite : FinitePath (web.quotient boundary).graph :=
  webYxr.restrictGraphOnSupport webYxr_quotientEdge

def quotientDPath : (web.quotient boundary).DPath := .inl quotientDFinite

def quotientYPath : (web.quotient boundary).DPath := .inl quotientYFinite

@[simp] theorem quotientDPath_support :
    quotientDPath.support = ({d, w, t2} : Set Vertex) := by
  change quotientDFinite.support = ({d, w, t2} : Set Vertex)
  unfold quotientDFinite
  exact (FinitePath.support_restrictGraphOnSupport webDwt2 webDwt2_quotientEdge).trans
    support_webDwt2

@[simp] theorem quotientYPath_support :
    quotientYPath.support = ({y, x, r} : Set Vertex) := by
  change quotientYFinite.support = ({y, x, r} : Set Vertex)
  unfold quotientYFinite
  exact (FinitePath.support_restrictGraphOnSupport webYxr webYxr_quotientEdge).trans
    support_webYxr

@[simp] theorem quotientDFinite_start : quotientDFinite.start = d := rfl
@[simp] theorem quotientDFinite_finish : quotientDFinite.finish = t2 := rfl
@[simp] theorem quotientYFinite_start : quotientYFinite.start = y := rfl
@[simp] theorem quotientYFinite_finish : quotientYFinite.finish = r := rfl

/-- Only the five displayed edges survive in the old quotient. -/
theorem quotient_adj_cases {u v : Vertex}
    (huv : (web.quotient boundary).graph.Adj u v) :
    (u = d ∧ v = x) ∨ (u = d ∧ v = w) ∨
      (u = w ∧ v = t2) ∨ (u = y ∧ v = x) ∨
        (u = x ∧ v = r) := by
  have hold : web.graph.Adj u v := web.quotient_adj_imp huv
  change graph.Adj u v at hold
  rcases hold with hold | hold | hold | hold | hold | hold | hold | hold | hold
  · exact Or.inl hold
  · exact (huv.2.2.2 (hold.2.symm ▸ (show t1 ∈ boundary by simp [boundary]))).elim
  · exact Or.inr (Or.inl hold)
  · exact Or.inr (Or.inr (Or.inl hold))
  · exact (huv.2.2.2 (hold.2.symm ▸ (show y ∈ boundary by simp [boundary]))).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl hold)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hold)))
  · rcases hold with ⟨rfl, rfl⟩
    have hbRoof : b ∈ web.roof boundary :=
      boundary_separator (by simp [web])
    have hbNotEssential : b ∉ web.essential boundary := by
      rw [boundary_trimmed]
      simp [boundary]
    exact (huv.2.1 ⟨hbRoof, hbNotEssential⟩).elim
  · rcases hold with ⟨rfl, rfl⟩
    exact (huv.2.2.2 (by simp [boundary])).elim

private def dReach : Set Vertex := {d, x, w, t2, r}
private def yReach : Set Vertex := {y, x, r}

private theorem dReach_step {u v : Vertex}
    (hu : u ∈ dReach) (huv : (web.quotient boundary).graph.Adj u v) :
    v ∈ dReach := by
  rcases quotient_adj_cases huv with h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩ <;> simp [dReach] at hu ⊢

private theorem yReach_step {u v : Vertex}
    (hu : u ∈ yReach) (huv : (web.quotient boundary).graph.Adj u v) :
    v ∈ yReach := by
  rcases quotient_adj_cases huv with h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩ <;> simp [yReach] at hu ⊢

private theorem t1_no_step {v : Vertex} :
    ¬ (web.quotient boundary).graph.Adj t1 v := by
  intro h
  rcases quotient_adj_cases h with h | h | h | h | h
  all_goals rcases h with ⟨h, -⟩ <;> cases h

private theorem walk_preserves_dReach {u v : Vertex}
    (p : Walk (web.quotient boundary).graph u v) (hu : u ∈ dReach) :
    v ∈ dReach := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (dReach_step hu hab)

private theorem walk_preserves_yReach {u v : Vertex}
    (p : Walk (web.quotient boundary).graph u v) (hu : u ∈ yReach) :
    v ∈ yReach := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (yReach_step hu hab)

private theorem walk_from_t1_finish {v : Vertex}
    (p : Walk (web.quotient boundary).graph t1 v) : v = t1 := by
  cases p with
  | nil => rfl
  | cons h _ => exact (t1_no_step h).elim

private theorem finite_start_eq_d_of_finish_mem_dBranch
    (p : FinitePath (web.quotient boundary).graph)
    (hstart : p.start ∈ boundary)
    (hfinish : p.finish ∈ ({d, w, t2} : Set Vertex)) :
    p.start = d := by
  rcases hstart with h | h | h
  · exact h
  · have pWalk : Walk (web.quotient boundary).graph t1 p.finish := h ▸ p.walk
    have hfinish' : p.finish = t1 := walk_from_t1_finish pWalk
    rw [hfinish'] at hfinish
    simp at hfinish
  · have hs : p.start = y := by simpa using h
    have hreach : p.finish ∈ yReach :=
      walk_preserves_yReach p.walk (by simp [hs, yReach])
    have hdisj : Disjoint yReach ({d, w, t2} : Set Vertex) := by
      exact Set.disjoint_left.2 (by intro v hv₁ hv₂; cases v <;> simp [yReach] at hv₁ hv₂)
    exact (Set.disjoint_left.1 hdisj hreach hfinish).elim

private theorem finite_start_eq_t1_of_finish_eq_t1
    (p : FinitePath (web.quotient boundary).graph)
    (hstart : p.start ∈ boundary) (hfinish : p.finish = t1) :
    p.start = t1 := by
  rcases hstart with h | h | h
  · have hreach : p.finish ∈ dReach :=
      walk_preserves_dReach p.walk (by simp [h, dReach])
    rw [hfinish] at hreach
    simp [dReach] at hreach
  · exact h
  · have hs : p.start = y := by simpa using h
    have hreach : p.finish ∈ yReach :=
      walk_preserves_yReach p.walk (by simp [hs, yReach])
    rw [hfinish] at hreach
    simp [yReach] at hreach

private theorem finite_start_eq_d_or_y_of_finish_mem_yBranch
    (p : FinitePath (web.quotient boundary).graph)
    (hstart : p.start ∈ boundary)
    (hfinish : p.finish ∈ ({y, x, r} : Set Vertex)) :
    p.start = d ∨ p.start = y := by
  rcases hstart with h | h | h
  · exact Or.inl h
  · have pWalk : Walk (web.quotient boundary).graph t1 p.finish := h ▸ p.walk
    have hfinish' : p.finish = t1 := walk_from_t1_finish pWalk
    rw [hfinish'] at hfinish
    simp at hfinish
  · exact Or.inr (by simpa using h)

@[simp] theorem quotient_source_eq_boundary :
    (web.quotient boundary).source = boundary :=
  SingularContinuation.quotient_source_eq_stopover web boundary_separator
    boundary_trimmed

private theorem exists_wave_member_starting_d
    (W : Set (web.quotient boundary).DPath)
    (hW : (web.quotient boundary).IsWave W) :
    ∃ f : FinitePath (web.quotient boundary).graph,
      (.inl f : (web.quotient boundary).DPath) ∈ W ∧
        f.start = d ∧ f.finish ∈ ({d, w, t2} : Set Vertex) := by
  have hdSource : d ∈ (web.quotient boundary).source := by
    rw [quotient_source_eq_boundary]
    simp [boundary]
  obtain ⟨z, hzD, hzW⟩ := hW.2.2 hdSource quotientDFinite (by
    constructor
    · rfl
    · simp [web])
  obtain ⟨p, hpW, hpz⟩ := hzW
  rcases p with f | ray
  · have hfinish : f.finish = z := Option.some.inj hpz
    have hzBranch : z ∈ ({d, w, t2} : Set Vertex) := by
      have hs := quotientDPath_support
      change quotientDFinite.support = ({d, w, t2} : Set Vertex) at hs
      simpa only [hs] using hzD
    have hstartSource : f.start ∈ (web.quotient boundary).source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    have hstartBoundary : f.start ∈ boundary := by
      simpa only [quotient_source_eq_boundary] using hstartSource
    refine ⟨f, hpW, finite_start_eq_d_of_finish_mem_dBranch f hstartBoundary ?_, ?_⟩
    · simpa only [hfinish] using hzBranch
    · simpa only [hfinish] using hzBranch
  · simp at hpz

private theorem exists_wave_member_starting_t1
    (W : Set (web.quotient boundary).DPath)
    (hW : (web.quotient boundary).IsWave W) :
    ∃ f : FinitePath (web.quotient boundary).graph,
      (.inl f : (web.quotient boundary).DPath) ∈ W ∧ f.start = t1 := by
  have htSource : t1 ∈ (web.quotient boundary).source := by
    rw [quotient_source_eq_boundary]
    simp [boundary]
  let qt := FinitePath.trivial (web.quotient boundary).graph t1
  obtain ⟨z, hzT, hzW⟩ := hW.2.2 htSource qt (by
    constructor
    · rfl
    · simp [web, qt])
  have hz : z = t1 := by
    simpa [qt] using hzT
  obtain ⟨p, hpW, hpz⟩ := hzW
  rcases p with f | ray
  · have hfinish : f.finish = t1 := (Option.some.inj hpz).trans hz
    have hstartSource : f.start ∈ (web.quotient boundary).source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    have hstartBoundary : f.start ∈ boundary := by
      simpa only [quotient_source_eq_boundary] using hstartSource
    exact ⟨f, hpW,
      finite_start_eq_t1_of_finish_eq_t1 f hstartBoundary hfinish⟩
  · simp at hpz

private theorem exists_wave_member_starting_y
    (W : Set (web.quotient boundary).DPath)
    (hW : (web.quotient boundary).IsWave W) :
    ∃ f : FinitePath (web.quotient boundary).graph,
      (.inl f : (web.quotient boundary).DPath) ∈ W ∧ f.start = y := by
  have hySource : y ∈ (web.quotient boundary).source := by
    rw [quotient_source_eq_boundary]
    simp [boundary]
  obtain ⟨z, hzY, hzW⟩ := hW.2.2 hySource quotientYFinite (by
    constructor
    · rfl
    · simp [web])
  obtain ⟨p, hpW, hpz⟩ := hzW
  rcases p with f | ray
  · have hfinish : f.finish = z := Option.some.inj hpz
    have hzBranch : z ∈ ({y, x, r} : Set Vertex) := by
      have hs := quotientYPath_support
      change quotientYFinite.support = ({y, x, r} : Set Vertex) at hs
      simpa only [hs] using hzY
    have hfinishBranch : f.finish ∈ ({y, x, r} : Set Vertex) := by
      simpa only [hfinish] using hzBranch
    have hstartSource : f.start ∈ (web.quotient boundary).source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    have hstartBoundary : f.start ∈ boundary := by
      simpa only [quotient_source_eq_boundary] using hstartSource
    rcases finite_start_eq_d_or_y_of_finish_mem_yBranch f hstartBoundary
        hfinishBranch with hfd | hfy
    · obtain ⟨g, hgW, hgd, hgfinish⟩ := exists_wave_member_starting_d W hW
      by_cases hfg : (.inl f : (web.quotient boundary).DPath) = .inl g
      · have hfg' : f = g := Sum.inl.inj hfg
        subst g
        have hdisj : Disjoint ({y, x, r} : Set Vertex)
            ({d, w, t2} : Set Vertex) := by
          exact Set.disjoint_left.2 (by
            intro v hv₁ hv₂
            cases v <;> simp at hv₁ hv₂)
        exact (Set.disjoint_left.1 hdisj hfinishBranch hgfinish).elim
      · have hdisj := hW.1 hpW hgW hfg
        have hfsupport : d ∈ f.support := hfd ▸ f.start_mem_support
        have hgsupport : d ∈ g.support := hgd ▸ g.start_mem_support
        exact (Set.disjoint_left.1 hdisj hfsupport hgsupport).elim
    · exact ⟨f, hpW, hfy⟩
  · simp at hpz

/-- The old quotient by the exact minimal boundary is unhindered.  This is
the field missing from the purely geometric crossing obstruction. -/
theorem quotient_unhindered :
    (web.quotient boundary).IsUnhindered := by
  rw [(web.quotient boundary).isUnhindered_iff]
  intro W hW
  apply Set.Subset.antisymm hW.2.1
  rw [quotient_source_eq_boundary]
  intro v hv
  rcases hv with h | h | h
  · obtain ⟨f, hfW, hfd, -⟩ := exists_wave_member_starting_d W hW
    exact ⟨.inl f, hfW, hfd.trans h.symm⟩
  · obtain ⟨f, hfW, hft⟩ := exists_wave_member_starting_t1 W hW
    exact ⟨.inl f, hfW, hft.trans h.symm⟩
  · have hvy : v = y := by simpa using h
    obtain ⟨f, hfW, hfy⟩ := exists_wave_member_starting_y W hW
    exact ⟨.inl f, hfW, hfy.trans hvy.symm⟩

/-- The obstruction row satisfies even the stronger, globally minimal
half-way-stopover interface. -/
theorem exactHalfwayStopover :
    IsExactHalfwayStopover web paths boundary where
  linkage := paths_linkage
  minimal := boundary_minimal
  quotient_unhindered := quotient_unhindered

/-- The same row in the separating wrapper used by singular continuation. -/
theorem separatingHalfwayStopover :
    IsSeparatingHalfwayStopover web paths boundary where
  stopover := exactHalfwayStopover.toHalfwayStopover
  separator := boundary_minimal.separator

/-- The completed `d-x-t1` component supplies the designated target link. -/
theorem paths_linksToTarget_d : LinksToTarget web paths {d} := by
  intro a ha
  have had : a = d := Set.mem_singleton_iff.mp ha
  subst a
  refine ⟨.inl dxt1, by simp [paths], dxt1, rfl, ?_, ?_⟩
  · have h : dxt1.support ∩ ({d} : Set Vertex) = {d} := by
      rw [support_dxt1]
      simp
    simpa only [web] using h
  · exact ⟨[], [x, t1], rfl, t1, by simp [web], by simp⟩

/-- The concrete exact stopover as the batch interface consumed by the
singular successor code. -/
def obstructedFullSourceSafeBatch : FullSourceSafeBatch web {d} where
  paths := paths
  boundary := boundary
  separating := separatingHalfwayStopover
  links := paths_linksToTarget_d

theorem obstructedFullSourceSafeBatch_no_forward_links_b :
    ¬ ∃ T : Set web.DPath,
      web.IsWarp T ∧
        web.ForwardExtension obstructedFullSourceSafeBatch.paths T ∧
          LinksToTarget web T {b} :=
  no_forward_warp_links_b

/-- A sharp operational obstruction: all exact half-way hypotheses hold,
but no forward warp can link the newly exposed source `b` to the target. -/
theorem exactHalfway_no_forward_links_b :
    IsExactHalfwayStopover web paths boundary ∧
      ¬ ∃ T : Set web.DPath,
        web.IsWarp T ∧ web.ForwardExtension paths T ∧
          LinksToTarget web T {b} :=
  ⟨exactHalfwayStopover, no_forward_warp_links_b⟩

#print axioms exactHalfway_no_forward_links_b

/-- Even the complete old frame data—normalization, a full linkage to a
separating trimmed boundary, and an unhindered boundary quotient—does not
produce a successor row completing a pending source by forward extension.
This is the precise obstruction to rebuilding a protected restoration frame
from `ProtectedBatch.quotient_unhindered` alone. -/
theorem unhindered_stopover_no_forward_completion :
    web.IsNormalized ∧
      IsLinkageBetween web web.source boundary paths ∧
      IsSeparatorFrom web web.source boundary ∧
      IsTrimmedSeparator web boundary ∧
      (web.quotient boundary).IsUnhindered ∧
      ¬ ∃ T : Set web.DPath,
        web.IsWarp T ∧ web.ForwardExtension paths T ∧
          LinksToTarget web T {b} :=
  ⟨web_normalized, paths_linkage, boundary_separator, boundary_trimmed,
    quotient_unhindered, no_forward_warp_links_b⟩

end SingularSafeBatchCounterexample
end CardinalInduction
end Erdos599
