/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossRouting
import ErdosProblems.Erdos916.ThreeTerminalPath

/-!
# Disjoint attachment paths in Voss's lasso argument

The finite two-path theorem is reused from `Erdos916.ThreeTerminalPath`.
The remaining operations trim the paths and reroute one along the lasso stem,
as on page 271 of Voss's paper.
-/

open SimpleGraph

namespace Erdos1091.Voss

/-- A path between two vertex sets which meets either set only at its
corresponding endpoint.  A trivial connector at an intersection is allowed. -/
structure Connector {V : Type*} (G : SimpleGraph V) (A B : Set V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  start_mem : start ∈ A
  finish_mem : finish ∈ B
  only_start : ∀ v ∈ walk.support, v ∈ A → v = start
  only_finish : ∀ v ∈ walk.support, v ∈ B → v = finish

namespace Connector

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- Shorten a path between two sets until no interior vertex lies in either set. -/
theorem exists_in_path {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (ha : a ∈ A) (hb : b ∈ B) :
    ∃ Q : Connector G A B, ∀ v ∈ Q.walk.support, v ∈ p.support := by
  classical
  let P : ℕ → Prop := fun n => ∃ a ∈ A, ∃ b ∈ B, ∃ q : G.Walk a b,
    q.IsPath ∧ (∀ v ∈ q.support, v ∈ p.support) ∧ q.length = n
  have hex : ∃ n, P n := ⟨p.length, a, ha, b, hb, p, hp, fun _ hv => hv, rfl⟩
  obtain ⟨x, hx, y, hy, q, hq, hsub, hlen⟩ := Nat.find_spec hex
  have hmin {c d : V} (r : G.Walk c d) (hc : c ∈ A) (hd : d ∈ B)
      (hr : r.IsPath) (hsubr : ∀ v ∈ r.support, v ∈ p.support) : q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨c, hc, d, hd, r, hr, hsubr, rfl⟩
  refine ⟨⟨x, y, q, hq, hx, hy, ?_, ?_⟩, hsub⟩
  · intro v hv hvA
    by_contra hvx
    have hm := hmin (q.dropUntil v hv) hvA hy (hq.dropUntil hv)
      (fun w hw => hsub w (q.support_dropUntil_subset_support hv hw))
    exact (Nat.not_lt_of_ge hm) (Walk.length_dropUntil_lt_length hv hvx)
  · intro v hv hvB
    by_contra hvy
    have hm := hmin (q.takeUntil v hv) hx hvB (hq.takeUntil hv)
      (fun w hw => hsub w (q.support_takeUntil_subset_support hv hw))
    exact (Nat.not_lt_of_ge hm) (q.length_takeUntil_lt_length hv hvy)

theorem start_ne_of_disjoint (P Q : Connector G A B)
    (hd : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support}) :
    P.start ≠ Q.start := by
  intro he
  exact Set.disjoint_left.mp hd P.walk.start_mem_support
    (by rw [he]; exact Q.walk.start_mem_support)

theorem finish_ne_of_disjoint (P Q : Connector G A B)
    (hd : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support}) :
    P.finish ≠ Q.finish := by
  intro he
  exact Set.disjoint_left.mp hd P.walk.end_mem_support (by rw [he]; exact Q.walk.end_mem_support)

/-- The two pieces of a simple path meet only at the cutting vertex. -/
theorem eq_cut_of_mem_both [DecidableEq V] {a b s v : V}
    (p : G.Walk a b) (hp : p.IsPath) (hs : s ∈ p.support)
    (hv₁ : v ∈ (p.takeUntil s hs).support) (hv₂ : v ∈ (p.dropUntil s hs).support) :
    v = s := by
  have hsplit : ((p.takeUntil s hs).append (p.dropUntil s hs)).IsPath := by
    rw [p.take_spec hs]
    exact hp
  by_contra hne
  exact hsplit.ne_of_mem_support_of_append hne hv₁ hv₂ rfl

/-- Replace the initial part of one connector by a prefix of another,
provided that prefix first meets the old connector at its final vertex. -/
def splice [DecidableEq V] (R P : Connector G A B) {s : V}
    (hsR : s ∈ R.walk.support) (hsP : s ∈ P.walk.support)
    (hfirst : ∀ v ∈ (R.walk.takeUntil s hsR).support, v ∈ P.walk.support → v = s) :
    Connector G A B where
  start := R.start
  finish := P.finish
  walk := (R.walk.takeUntil s hsR).append (P.walk.dropUntil s hsP)
  isPath := Erdos1105.isPath_append_of_inter_eq_end
    (R.isPath.takeUntil hsR) (P.isPath.dropUntil hsP)
    (fun v hvR hvP => hfirst v hvR (P.walk.support_dropUntil_subset_support hsP hvP))
  start_mem := R.start_mem
  finish_mem := P.finish_mem
  only_start := by
    intro v hv hvA
    rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · exact R.only_start v (R.walk.support_takeUntil_subset_support hsR hv) hvA
    · have hvP : v = P.start := P.only_start v
        (P.walk.support_dropUntil_subset_support hsP hv) hvA
      have hvs : v = s := eq_cut_of_mem_both P.walk P.isPath hsP
        (by rw [hvP]; exact (P.walk.takeUntil s hsP).start_mem_support) hv
      exact hvs.trans (R.only_start s hsR (hvs ▸ hvA))
  only_finish := by
    intro v hv hvB
    rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · have hvR : v = R.finish := R.only_finish v
        (R.walk.support_takeUntil_subset_support hsR hv) hvB
      have hvs : v = s := eq_cut_of_mem_both R.walk R.isPath hsR hv
        (by rw [hvR]; exact (R.walk.dropUntil s hsR).end_mem_support)
      exact hvs.trans (P.only_finish s hsP (hvs ▸ hvB))
    · exact P.only_finish v (P.walk.support_dropUntil_subset_support hsP hv) hvB

theorem splice_disjoint [DecidableEq V] (R P Q : Connector G A B) {s : V}
    (hsR : s ∈ R.walk.support) (hsP : s ∈ P.walk.support)
    (hfirst : ∀ v ∈ (R.walk.takeUntil s hsR).support, v ∈ P.walk.support → v = s)
    (hpre : ∀ v ∈ (R.walk.takeUntil s hsR).support, v ∉ Q.walk.support)
    (hPQ : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support}) :
    Disjoint {v | v ∈ (R.splice P hsR hsP hfirst).walk.support} {v | v ∈ Q.walk.support} := by
  apply Set.disjoint_left.mpr
  intro v hv hvQ
  change v ∈ ((R.walk.takeUntil s hsR).append (P.walk.dropUntil s hsP)).support at hv
  rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
  · exact hpre v hv hvQ
  · exact Set.disjoint_left.mp hPQ (P.walk.support_dropUntil_subset_support hsP hv) hvQ

/-- The prefix up to the first hit of a set meets that set only at its end. -/
theorem exists_first_hit [DecidableEq V] {a b : V} (p : G.Walk a b) (T : Set V)
    (hex : ∃ s ∈ p.support, s ∈ T) :
    ∃ s, ∃ hs : s ∈ p.support, s ∈ T ∧
      ∀ v ∈ (p.takeUntil s hs).support, v ∈ T → v = s := by
  classical
  let F : ℕ → Prop := fun n => ∃ s, ∃ hs : s ∈ p.support,
    s ∈ T ∧ (p.takeUntil s hs).length = n
  have hF : ∃ n, F n := by
    obtain ⟨s, hs, hsT⟩ := hex
    exact ⟨_, s, hs, hsT, rfl⟩
  obtain ⟨s, hs, hsT, hlen⟩ := Nat.find_spec hF
  refine ⟨s, hs, hsT, ?_⟩
  intro v hv hvT
  by_contra hvs
  have hvp := p.support_takeUntil_subset_support hs hv
  have hmin : Nat.find hF ≤ (p.takeUntil v hvp).length :=
    Nat.find_min' hF ⟨v, hvp, hvT, rfl⟩
  have hlt := (p.takeUntil s hs).length_takeUntil_lt_length hv hvs
  rw [p.takeUntil_takeUntil hs hv, hlen] at hlt
  omega

/-- Given two disjoint connectors, another connector's starting vertex can
be prescribed for one of them by rerouting at its first intersection. -/
theorem exists_disjoint_with_start (R P Q : Connector G A B)
    (hPQ : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support}) :
    ∃ P' Q' : Connector G A B, P'.start = R.start ∧
      Disjoint {v | v ∈ P'.walk.support} {v | v ∈ Q'.walk.support} := by
  classical
  by_cases hex : ∃ s ∈ R.walk.support, s ∈ P.walk.support ∨ s ∈ Q.walk.support
  · obtain ⟨s, hsR, hsPQ, hfirst⟩ := exists_first_hit R.walk
      {v | v ∈ P.walk.support ∨ v ∈ Q.walk.support} hex
    rcases hsPQ with hsP | hsQ
    · have hfirstP : ∀ v ∈ (R.walk.takeUntil s hsR).support,
          v ∈ P.walk.support → v = s := fun v hv hvP => hfirst v hv (Or.inl hvP)
      have hpreQ : ∀ v ∈ (R.walk.takeUntil s hsR).support, v ∉ Q.walk.support := by
        intro v hv hvQ
        have hvs := hfirst v hv (Or.inr hvQ)
        exact Set.disjoint_left.mp hPQ hsP (hvs ▸ hvQ)
      exact ⟨R.splice P hsR hsP hfirstP, Q, rfl,
        splice_disjoint R P Q hsR hsP hfirstP hpreQ hPQ⟩
    · have hfirstQ : ∀ v ∈ (R.walk.takeUntil s hsR).support,
          v ∈ Q.walk.support → v = s := fun v hv hvQ => hfirst v hv (Or.inr hvQ)
      have hpreP : ∀ v ∈ (R.walk.takeUntil s hsR).support, v ∉ P.walk.support := by
        intro v hv hvP
        have hvs := hfirst v hv (Or.inl hvP)
        exact Set.disjoint_left.mp hPQ (hvs ▸ hvP) hsQ
      exact ⟨R.splice Q hsR hsQ hfirstQ, P, rfl,
        splice_disjoint R Q P hsR hsQ hfirstQ hpreP hPQ.symm⟩
  · refine ⟨R, P, rfl, Set.disjoint_left.mpr ?_⟩
    intro v hvR hvP
    exact hex ⟨v, hvR, Or.inl hvP⟩

/-- Join two disjoint attachment arms through a path in the source set. -/
def joinEar (P Q : Connector G A B) (r : G.Walk Q.start P.start) (hr : r.IsPath)
    (hrA : ∀ v ∈ r.support, v ∈ A)
    (hPQ : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support})
    (hAB : ∀ v ∈ A, v ∈ B → v = P.start) : Ear G B where
  start := Q.finish
  finish := P.finish
  walk := Q.walk.reverse.append (r.append P.walk)
  isPath := by
    have hrP : (r.append P.walk).IsPath :=
      Erdos1105.isPath_append_of_inter_eq_end hr P.isPath
        (fun v hvr hvP => P.only_start v hvP (hrA v hvr))
    apply Erdos1105.isPath_append_of_inter_eq_end Q.isPath.reverse hrP
    intro v hvQ hvRP
    have hvQ' : v ∈ Q.walk.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hvQ
    rcases (Walk.mem_support_append_iff _ _).mp hvRP with hvr | hvP
    · exact Q.only_start v hvQ' (hrA v hvr)
    · exact (Set.disjoint_left.mp hPQ hvP hvQ').elim
  start_mem := Q.finish_mem
  finish_mem := P.finish_mem
  endpoints_ne := (P.finish_ne_of_disjoint Q hPQ).symm
  only_ends := by
    intro v hv hvB
    rcases (Walk.mem_support_append_iff _ _).mp hv with hvQ | hvRP
    · left
      exact Q.only_finish v (by simpa only [Walk.support_reverse, List.mem_reverse] using hvQ) hvB
    · right
      rcases (Walk.mem_support_append_iff _ _).mp hvRP with hvr | hvP
      · have hv : v = P.start := hAB v (hrA v hvr) hvB
        exact P.only_finish v (by rw [hv]; exact P.walk.start_mem_support) hvB
      · exact P.only_finish v hvP hvB

/-- Source-set chords cannot become traversed edges of the external arms. -/
theorem isChord_joinEar (P Q : Connector G A B) (r : G.Walk Q.start P.start)
    (hr : r.IsPath) (hrA : ∀ v ∈ r.support, v ∈ A)
    (hPQ : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support})
    (hAB : ∀ v ∈ A, v ∈ B → v = P.start) {e : Sym2 V} (he : r.IsChord e) :
    (P.joinEar Q r hr hrA hPQ hAB).walk.IsChord e := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hxy, hnot, hx, hy⟩ := Walk.isChord_sym2Mk.mp he
    refine ⟨hxy, ?_, ?_, ?_⟩
    · intro he
      change s(x, y) ∈ (Q.walk.reverse.append (r.append P.walk)).edges at he
      simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at he
      rcases he with heQ | her | heP
      · have hxQ := Q.only_start x (Q.walk.fst_mem_support_of_mem_edges heQ) (hrA x hx)
        have hyQ := Q.only_start y (Q.walk.snd_mem_support_of_mem_edges heQ) (hrA y hy)
        exact hxy.ne (hxQ.trans hyQ.symm)
      · exact hnot her
      · have hxP := P.only_start x (P.walk.fst_mem_support_of_mem_edges heP) (hrA x hx)
        have hyP := P.only_start y (P.walk.snd_mem_support_of_mem_edges heP) (hrA y hy)
        exact hxy.ne (hxP.trans hyP.symm)
    · exact (Walk.mem_support_append_iff _ _).mpr
        (Or.inr ((Walk.mem_support_append_iff _ _).mpr (Or.inl hx)))
    · exact (Walk.mem_support_append_iff _ _).mpr
        (Or.inr ((Walk.mem_support_append_iff _ _).mpr (Or.inl hy)))

theorem chord_ne_joinEar_endpoints (P Q : Connector G A B) (r : G.Walk Q.start P.start)
    (hrA : ∀ v ∈ r.support, v ∈ A)
    (hPQ : Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support})
    (hAB : ∀ v ∈ A, v ∈ B → v = P.start) {e : Sym2 V} (he : r.IsChord e) :
    e ≠ s(Q.finish, P.finish) := by
  intro heq
  have he' : r.IsChord s(Q.finish, P.finish) := heq ▸ he
  have hQ := hAB Q.finish (hrA Q.finish he'.2.2.1) Q.finish_mem
  have hP := hAB P.finish (hrA P.finish he'.2.2.2) P.finish_mem
  exact (P.finish_ne_of_disjoint Q hPQ) (hP.trans hQ.symm)

end Connector

/-- A walk with a chord has at least two edges. -/
theorem two_le_length_of_isChord {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {e : Sym2 V} (he : p.IsChord e) : 2 ≤ p.length := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hxy, hnot, hx, hy⟩ := Walk.isChord_sym2Mk.mp he
    cases p with
    | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hx hy
      exact (hxy.ne (hx.trans hy.symm)).elim
    | @cons a c b hac q =>
      cases q with
      | nil =>
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy.ne rfl).elim
        · exact (hnot (by simp)).elim
        · exact (hnot (by simp [Sym2.eq_swap])).elim
        · exact (hxy.ne rfl).elim
      | cons h q => simp only [Walk.length_cons]; omega

/-- Two-connectivity supplies disjoint connectors between any two sets
having two distinct vertices each. -/
theorem exists_two_disjoint_connectors {V : Type} [Finite V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce {v | v ≠ d}).Connected)
    {A B : Set V} {a₀ a₁ b₀ b₁ : V}
    (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (ha : a₀ ≠ a₁)
    (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B) (hb : b₀ ≠ b₁) :
    ∃ P Q : Connector G A B,
      Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support} := by
  classical
  obtain ⟨L⟩ := Erdos916.exists_twoABLinkage_of_separator_two_le G A B (by
    intro S hS
    by_contra hcard
    have hle : S.ncard ≤ 1 := by omega
    rcases (Set.ncard_le_one_iff_eq (Set.toFinite S)).mp hle with rfl | ⟨d, rfl⟩
    · obtain ⟨p, hp⟩ := (hconn a₀ b₀).exists_isPath
      obtain ⟨v, _, hv⟩ := hS a₀ ha₀ b₀ hb₀ p hp
      exact hv
    · let a := if a₀ = d then a₁ else a₀
      let b := if b₀ = d then b₁ else b₀
      have haA : a ∈ A := by
        by_cases h : a₀ = d <;> simp [a, h, ha₀, ha₁]
      have hbB : b ∈ B := by
        by_cases h : b₀ = d <;> simp [b, h, hb₀, hb₁]
      have had : a ≠ d := by
        by_cases h : a₀ = d
        · simpa [a, h] using fun h₁ : a₁ = d => ha (h.trans h₁.symm)
        · simp [a, h]
      have hbd : b ≠ d := by
        by_cases h : b₀ = d
        · simpa [b, h] using fun h₁ : b₁ = d => hb (h.trans h₁.symm)
        · simp [b, h]
      obtain ⟨q, hq⟩ := (hdelete d (⟨a, had⟩ : {v : V // v ≠ d}) ⟨b, hbd⟩).exists_isPath
      let inc := SimpleGraph.Embedding.induce (G := G) (s := {v : V | v ≠ d})
      obtain ⟨v, hvq, hv⟩ := hS a haA b hbB (q.map inc.toHom) (hq.map inc.injective)
      have hvd : v = d := by simpa using hv
      subst v
      have hsupp := Walk.support_map inc.toHom q
      have hvq' : d ∈ q.support.map inc.toHom := hsupp ▸ hvq
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hvq'
      exact w.2 (by simpa [inc] using hw))
  obtain ⟨P, hP⟩ := Connector.exists_in_path (L.path 0) (L.isPath 0) (L.left_mem 0) (L.right_mem 0)
  obtain ⟨Q, hQ⟩ := Connector.exists_in_path (L.path 1) (L.isPath 1) (L.left_mem 1) (L.right_mem 1)
  refine ⟨P, Q, Set.disjoint_left.mpr ?_⟩
  intro v hvP hvQ
  exact Set.disjoint_left.mp (L.disjoint (by decide : (0 : Fin 2) ≠ 1)) (hP v hvP) (hQ v hvQ)

namespace AttachmentLasso

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- The reversed stem is a clean connector from the cycle to the attachment set. -/
def stemConnector (L : AttachmentLasso G S) :
    Connector G {v | v ∈ L.cycle.support} S where
  start := L.stem.finish
  finish := L.stem.start
  walk := L.stem.walk.reverse
  isPath := L.stem.isPath.reverse
  start_mem := L.cycle.start_mem_support
  finish_mem := L.stem.start_mem
  only_start := by
    intro v hv hvC
    exact L.intersection v (by simpa only [Walk.support_reverse, List.mem_reverse] using hv) hvC
  only_finish := by
    intro v hv hvS
    exact L.stem.only_start v
      (by simpa only [Walk.support_reverse, List.mem_reverse] using hv) hvS

/-- The two attachment arms in Voss's Figure 6, with one end fixed at the branch. -/
theorem exists_branch_connectors {V : Type} [Finite V] {G : SimpleGraph V} {S : Set V}
    (L : AttachmentLasso G S) (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce {v | v ≠ d}).Connected)
    {s t : V} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t) :
    ∃ P Q : Connector G {v | v ∈ L.cycle.support} S,
      P.start = L.stem.finish ∧
      Disjoint {v | v ∈ P.walk.support} {v | v ∈ Q.walk.support} := by
  obtain ⟨P, Q, hPQ⟩ := exists_two_disjoint_connectors G hconn hdelete
    (A := {v | v ∈ L.cycle.support}) L.cycle.start_mem_support
    (L.cycle.getVert_mem_support 1) (L.cycle.adj_snd L.isCycle.not_nil).ne hs ht hst
  exact L.stemConnector.exists_disjoint_with_start P Q hPQ

/-- A maximal lasso without a long ear would yield an ear with two chords
other than the edge joining its attachment endpoints. -/
theorem exists_ear_two_chords {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Set V}
    (L : AttachmentLasso G S) (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce {v | v ≠ d}).Connected)
    {s t : V} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hdegree : ∀ v, v ∉ S → 3 ≤ G.degree v)
    (hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length + 1 ≤ L.length)
    (hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length)
    (hmaxCycle : ∀ K : AttachmentLasso G S, K.length = L.length →
      K.cycle.length ≤ L.cycle.length) :
    ∃ E : Ear G S, 2 ≤ E.walk.length ∧ ∃ e f : Sym2 V,
      e ≠ f ∧ E.walk.IsChord e ∧ E.walk.IsChord f ∧
      e ≠ s(E.start, E.finish) ∧ f ≠ s(E.start, E.finish) := by
  obtain ⟨P, Q, hPstart, hPQ⟩ := L.exists_branch_connectors hconn hdelete hs ht hst
  have hQne : Q.start ≠ L.stem.finish := by
    intro he
    exact (P.start_ne_of_disjoint Q hPQ) (hPstart.trans he.symm)
  obtain ⟨r₀, hr₀, hr₀C, e, f, hef, he, hf⟩ :=
    L.exists_path_two_chords_to_branch hdegree hmaxPath hnoEar hmaxCycle Q.start_mem hQne
  let r := r₀.copy rfl hPstart.symm
  have hrsup : r.support = r₀.support := Walk.support_copy _ _ _
  have hredge : r.edges = r₀.edges := Walk.edges_copy _ _ _
  have hr : r.IsPath := (Walk.isPath_copy _ _ _).mpr hr₀
  have hrA : ∀ v ∈ r.support, v ∈ L.cycle.support := by
    intro v hv
    exact hr₀C v (hrsup ▸ hv)
  have hAB : ∀ v ∈ L.cycle.support, v ∈ S → v = P.start := by
    intro v hvC hvS
    have hvx := L.cycle_only_start v hvC hvS
    have hvStem : v ∈ L.stem.walk.support := by rw [hvx]; exact L.stem.walk.start_mem_support
    exact (L.intersection v hvStem hvC).trans hPstart.symm
  have he' : r.IsChord e := by simpa only [Walk.IsChord, hrsup, hredge] using he
  have hf' : r.IsChord f := by simpa only [Walk.IsChord, hrsup, hredge] using hf
  let E := P.joinEar Q r hr hrA hPQ hAB
  have heE : E.walk.IsChord e := P.isChord_joinEar Q r hr hrA hPQ hAB he'
  have hfE : E.walk.IsChord f := P.isChord_joinEar Q r hr hrA hPQ hAB hf'
  exact ⟨E, two_le_length_of_isChord E.walk heE, e, f, hef, heE, hfE,
    P.chord_ne_joinEar_endpoints Q r hrA hPQ hAB he',
    P.chord_ne_joinEar_endpoints Q r hrA hPQ hAB hf'⟩

end AttachmentLasso

namespace AttachmentPath

/-- Voss's long-ear lemma.  In a two-connected graph of minimum degree
three outside the attachment set, the absence of two internal ear chords
forces an ear one edge longer than a longest attachment path. -/
theorem exists_long_ear {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Set V}
    (P : AttachmentPath G S)
    (hmax : ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length)
    (hconn : G.Connected) (hdelete : ∀ d : V, (G.induce {v | v ≠ d}).Connected)
    {s t : V} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hdegree : ∀ v, v ∉ S → 3 ≤ G.degree v)
    (hone : ∀ E : Ear G S, 2 ≤ E.walk.length → ∀ e f : Sym2 V,
      E.walk.IsChord e → E.walk.IsChord f →
      e ≠ s(E.start, E.finish) → f ≠ s(E.start, E.finish) → e = f) :
    ∃ E : Ear G S, E.walk.length = P.walk.length + 1 := by
  classical
  by_contra hnone
  have hno : ∀ E : Ear G S, E.walk.length ≠ P.walk.length + 1 := by
    intro E hE
    exact hnone ⟨E, hE⟩
  obtain ⟨L₀, hL₀⟩ := P.exists_lasso_of_no_long_ear hmax hno (hdegree P.finish P.finish_notMem)
  obtain ⟨L, hL, hmaxCycle⟩ := L₀.exists_maximum_cycle
  have hlength : L.length = P.walk.length + 1 := hL.trans hL₀
  have hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length + 1 ≤ L.length := by
    intro Q
    rw [hlength]
    exact Nat.add_le_add_right (hmax Q) 1
  have hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length := by
    intro E
    rw [hlength]
    exact hno E
  obtain ⟨E, hElen, e, f, hef, he, hf, heEnds, hfEnds⟩ :=
    L.exists_ear_two_chords hconn hdelete hs ht hst hdegree hmaxPath hnoEar
      (fun K hK => hmaxCycle K (hK.trans hL))
  exact hef (hone E hElen e f he hf heEnds hfEnds)

/-- Applied to an odd cycle, the long-ear lemma needs only the exclusion
of an odd cycle with two chords. -/
theorem exists_long_ear_of_odd_cycle {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {z : V} (C : G.Walk z z) (hC : C.IsCycle)
    (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (P : AttachmentPath G {v | v ∈ C.support})
    (hmax : ∀ Q : AttachmentPath G {v | v ∈ C.support}, Q.walk.length ≤ P.walk.length)
    (hconn : G.Connected) (hdelete : ∀ d : V, (G.induce {v | v ≠ d}).Connected)
    (hdegree : ∀ v, v ∉ C.support → 3 ≤ G.degree v) :
    ∃ E : Ear G {v | v ∈ C.support}, E.walk.length = P.walk.length + 1 := by
  apply P.exists_long_ear hmax hconn hdelete C.start_mem_support
    (C.getVert_mem_support 1) (C.adj_snd hC.not_nil).ne hdegree
  intro E hElen e f he hf heEnds hfEnds
  exact Ear.chords_eq_of_no_odd_two_chords C hC hodd hno E hElen he hf heEnds hfEnds

end AttachmentPath

#print axioms Erdos916.exists_twoABLinkage_of_separator_two_le
#print axioms AttachmentPath.exists_long_ear_of_odd_cycle

end Erdos1091.Voss
