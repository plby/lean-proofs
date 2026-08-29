/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.FamilyTools
import ErdosProblems.Erdos599.InfiniteKonig
import ErdosProblems.Erdos599.Stationary

/-!
# Popular separators in unbalanced webs

This file formalizes the popularity argument in Section 8 of
Aharoni--Berger.  It uses the canonical concrete paths of `Core.lean`.
In particular it contains Definition 8.2, the definitions of popular and
strongly popular sets, Lemma 8.3, and the layer separator used in Theorem
8.4.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u

variable {V : Type u}

/-! ## Indexed and unbalanced webs -/

/-- The ordinal index data used by popularity.  Strict source--target
descent is intentionally not part of this structure: the layer argument
needs only these five fields. -/
structure KappaIndexed (Γ : DWeb V) (κ : Cardinal.{u}) where
  regular : κ.IsRegular
  uncountable : ℵ₀ < κ
  f : Γ.source → Below κ
  g : Γ.target ↪ Below κ
  f_range_stationary : IsStationaryBelow κ (Set.range f)

/-- Data witnessing that a concrete web is strictly `κ`-unbalanced
(Aharoni--Berger, Definition 8.2).  The base index data is separated so the
successor-new grounding branch can use the true weak chronology. -/
structure KappaUnbalanced (Γ : DWeb V) (κ : Cardinal.{u})
    extends KappaIndexed Γ κ where
  descends : ∀ (p : FinitePath Γ.graph)
    (hstart : p.start ∈ Γ.source) (hfinish : p.finish ∈ Γ.target),
    g ⟨p.finish, hfinish⟩ < f ⟨p.start, hstart⟩

instance {Gamma : DWeb V} {kappa : Cardinal.{u}} :
    Coe (KappaUnbalanced Gamma kappa) (KappaIndexed Gamma kappa) :=
  ⟨KappaUnbalanced.toKappaIndexed⟩

/-- The extra source-size hypothesis used at the actual Section 8
application.  It is not part of the printed Definition 8.2, but it is needed
by Lemma 8.6: Aharoni's Lemma 2.5 assumes that the destination side of the
reversed web has cardinality at most `κ`. -/
def KappaIndexed.SourceBounded {Γ : DWeb V} {κ : Cardinal.{u}}
    (_U : KappaIndexed Γ κ) : Prop :=
  Cardinal.lift.{u + 1, u} #Γ.source ≤
    Cardinal.lift.{u + 1, u} κ

/-- In the auxiliary web used to prove Theorem 7.30, source vertices are
literally indexed by ordinals below `κ`; this is the convenient stronger
form of `SourceBounded`. -/
def KappaIndexed.SourceIndexed {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : Prop :=
  Function.Injective U.f

theorem KappaIndexed.sourceBounded_of_sourceIndexed
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hU : U.SourceIndexed) : U.SourceBounded := by
  rw [KappaIndexed.SourceBounded, ← mk_below κ]
  simpa using Cardinal.lift_mk_le_lift_mk_of_injective hU

theorem KappaIndexed.source_card_le
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hU : U.SourceBounded) : #Γ.source ≤ κ := by
  exact Cardinal.lift_le.1 hU

/-- The target side of a `κ`-unbalanced web has cardinality at most `κ`.
The lifts only reconcile the universe of `Below κ` with the vertex
universe. -/
theorem target_card_le {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) :
    Cardinal.lift.{u + 1, u} #Γ.target ≤
      Cardinal.lift.{u + 1, u} κ := by
  rw [← mk_below κ]
  simpa using Cardinal.lift_mk_le_lift_mk_of_injective U.g.injective

/-- Countable completeness in the positive form used to split a stationary
path family according to the first layer containing its terminal. -/
theorem exists_stationary_of_subset_iUnion {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    {S : Set (Below κ)} {F : ℕ → Set (Below κ)}
    (hS : IsStationaryBelow κ S) (hcover : S ⊆ ⋃ n, F n) :
    ∃ n, IsStationaryBelow κ (F n) := by
  by_contra h
  push Not at h
  exact (not_isStationaryBelow_iUnion_of_countable hκ hκu h)
    (hS.mono hcover)

/-! ## Warps, joined families, and popularity -/

/-- A pairwise vertex-disjoint family of concrete finite paths. -/
structure FiniteWarp (Γ : DWeb V) where
  paths : Set (FinitePath Γ.graph)
  disjoint : paths.PairwiseDisjoint FinitePath.support

/-- A finite warp from the source of `Γ` to a set `S`. -/
structure XSWarp (Γ : DWeb V) (S : Set V) extends FiniteWarp Γ where
  starts_in_source : ∀ {p}, p ∈ paths → p.start ∈ Γ.source
  ends_in_target : ∀ {p}, p ∈ paths → p.finish ∈ S

namespace XSWarp

/-- Retarget a warp along an inclusion of terminal sets. -/
def mono {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S) (hST : S ⊆ T) :
    XSWarp Γ T where
  paths := P.paths
  disjoint := P.disjoint
  starts_in_source := P.starts_in_source
  ends_in_target hp := hST (P.ends_in_target hp)

/-- Paths in a warp sharing their terminal vertex coincide. -/
theorem eq_of_finish_eq {Γ : DWeb V} {S : Set V} (P : XSWarp Γ S)
    {p q : FinitePath Γ.graph} (hp : p ∈ P.paths) (hq : q ∈ P.paths)
    (hfinish : p.finish = q.finish) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (P.disjoint hp hq hpq)
    p.finish_mem_support (hfinish ▸ q.finish_mem_support)

/-- Paths in a warp sharing their initial vertex coincide. -/
theorem eq_of_start_eq {Γ : DWeb V} {S : Set V} (P : XSWarp Γ S)
    {p q : FinitePath Γ.graph} (hp : p ∈ P.paths) (hq : q ∈ P.paths)
    (hstart : p.start = q.start) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (P.disjoint hp hq hpq)
    p.start_mem_support (hstart ▸ q.start_mem_support)

/-- Push a warp path forward to its first vertex in `T`, using one
prescribed outgoing edge from its terminal if the path does not already
meet `T`. -/
noncomputable def pushPath {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (p : FinitePath Γ.graph) (hp : p ∈ P.paths) : FinitePath Γ.graph := by
  let w : V := Classical.choose (hstep (P.ends_in_target hp))
  have hwT : w ∈ T := (Classical.choose_spec
    (hstep (P.ends_in_target hp))).1
  have hpw : Γ.graph.Adj p.finish w := (Classical.choose_spec
    (hstep (P.ends_in_target hp))).2
  by_cases hm : p.walk.Meets T
  · exact p.firstHit T hm
  · have hne : p.finish ≠ w := by
      intro h
      exact hm ⟨p.finish, p.finish_mem_support, h ▸ hwT⟩
    let q : Walk Γ.graph p.finish w := .cons hpw .nil
    have hq : q.IsPath := by simp [q, Walk.IsPath, hne]
    have hd : p.walk.support.Disjoint q.support.tail := by
      rw [List.disjoint_left]
      intro x hxp hxq
      have hxw : x = w := by simpa [q] using hxq
      subst x
      exact hm ⟨w, hxp, hwT⟩
    exact p.appendWalkOfDisjoint q hq hd

@[simp]
theorem pushPath_start {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (p : FinitePath Γ.graph) (hp : p ∈ P.paths) :
    (P.pushPath hstep p hp).start = p.start := by
  classical
  simp only [pushPath]
  split <;> rfl

/-- The pushed path ends in `T`. -/
theorem pushPath_finish_mem {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (p : FinitePath Γ.graph) (hp : p ∈ P.paths) :
    (P.pushPath hstep p hp).finish ∈ T := by
  classical
  simp only [pushPath]
  split
  · exact FinitePath.firstHit_finish_mem _ _ _
  · exact (Classical.choose_spec (hstep (P.ends_in_target hp))).1

/-- Apart from its new terminal in `T`, pushing introduces no vertices. -/
theorem pushPath_support_subset {Γ : DWeb V} {S T : Set V}
    (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (p : FinitePath Γ.graph) (hp : p ∈ P.paths) :
    (P.pushPath hstep p hp).support ⊆ p.support ∪ T := by
  classical
  simp only [pushPath]
  split
  · intro x hx
    exact Or.inl (FinitePath.firstHit_support_subset _ _ _ hx)
  · intro x hx
    have hxsupp : x ∈ p.walk.support ++
        [Classical.choose (hstep (P.ends_in_target hp))] := by
      simpa [FinitePath.support, FinitePath.appendWalkOfDisjoint,
        FinitePath.appendWalk] using hx
    simp only [List.mem_append, List.mem_singleton] at hxsupp
    exact hxsupp.elim Or.inl fun hxw ↦
      Or.inr (hxw ▸ (Classical.choose_spec
        (hstep (P.ends_in_target hp))).1)

/-- A pushed path first enters `T` at its terminal. -/
theorem pushPath_join_only_at_end {Γ : DWeb V} {S T : Set V}
    (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (p : FinitePath Γ.graph) (hp : p ∈ P.paths) :
    (P.pushPath hstep p hp).support ∩ T ⊆
      {(P.pushPath hstep p hp).finish} := by
  classical
  intro x hx
  apply Set.mem_singleton_iff.2
  by_contra hne
  by_cases hm : p.walk.Meets T
  · simp only [pushPath, dif_pos hm] at hx hne ⊢
    have hlast :
        (p.firstHit T hm).walk.support.getLast
          (p.firstHit T hm).walk.support_ne_nil = (p.firstHit T hm).finish :=
        (p.firstHit T hm).walk.getLast_support
    have hxlast : x ≠ (p.firstHit T hm).walk.support.getLast
        (p.firstHit T hm).walk.support_ne_nil := by
      intro heq
      exact hne (heq.trans hlast)
    exact FinitePath.firstHit_no_mem_before p T hm
      (List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast) hx.2
  · simp only [pushPath, dif_neg hm] at hx hne ⊢
    have hxsupp : x ∈ p.walk.support ++
        [Classical.choose (hstep (P.ends_in_target hp))] := by
      simpa [FinitePath.support, FinitePath.appendWalkOfDisjoint,
        FinitePath.appendWalk] using hx.1
    simp only [List.mem_append, List.mem_singleton] at hxsupp
    rcases hxsupp with hxp | hxw
    · exact hm ⟨x, hxp, hx.2⟩
    · exact hne hxw

end XSWarp

/-- An `S`-joined family of normalized source--`S` paths.  Distinct paths
may meet only in `S`; normalization says that each path first enters `S`
at its terminal vertex. -/
structure JoinedFamily (Γ : DWeb V) (S : Set V) where
  paths : Set (FinitePath Γ.graph)
  starts_in_source : ∀ {p}, p ∈ paths → p.start ∈ Γ.source
  ends_in_join : ∀ {p}, p ∈ paths → p.finish ∈ S
  join_only_at_end : ∀ {p}, p ∈ paths → p.support ∩ S ⊆ {p.finish}
  joined : ∀ {p}, p ∈ paths → ∀ {q}, q ∈ paths → p ≠ q →
    p.support ∩ q.support ⊆ S

namespace JoinedFamily

/-- When the join set is disjoint from the web source, distinct paths of a
joined family have distinct initial vertices. -/
def startEmbedding {Γ : DWeb V} {S : Set V} (F : JoinedFamily Γ S)
    (hdisjoint : Disjoint Γ.source S) : F.paths ↪ Γ.source where
  toFun p := ⟨p.1.start, F.starts_in_source p.2⟩
  inj' := by
    intro p q hstart
    apply Subtype.ext
    by_contra hpq
    have hstartEq : p.1.start = q.1.start :=
      congrArg Subtype.val hstart
    have hstartS : p.1.start ∈ S :=
      F.joined p.2 q.2 hpq
        ⟨p.1.start_mem_support,
          hstartEq ▸ q.1.start_mem_support⟩
    exact Set.disjoint_left.1 hdisjoint
      (F.starts_in_source p.2) hstartS

/-- Cardinal bound on a joined family whose join set misses the source. -/
theorem paths_card_le_source {Γ : DWeb V} {S : Set V}
    (F : JoinedFamily Γ S) (hdisjoint : Disjoint Γ.source S) :
    #F.paths ≤ #Γ.source :=
  Cardinal.mk_le_of_injective (F.startEmbedding hdisjoint).injective

/-- The source bound used in Lemma 8.6 also bounds every joined family
whose join set is disjoint from the source. -/
theorem paths_card_le_kappa {Γ : DWeb V} {S : Set V}
    {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hU : U.SourceBounded) (F : JoinedFamily Γ S)
    (hdisjoint : Disjoint Γ.source S) :
    Cardinal.lift.{u + 1, u} #F.paths ≤
      Cardinal.lift.{u + 1, u} κ :=
  (Cardinal.lift_le.2 (F.paths_card_le_source hdisjoint)).trans hU

/-- If a forbidden vertex set is smaller than a joined family, one member
meets it only inside the permitted join set.  This is the selection step in
the transfinite splice of Aharoni's Lemma 2.5: outside the join set the path
supports are pairwise disjoint, so distinct bad paths require distinct
forbidden witnesses. -/
theorem exists_member_inter_subset_join_of_card_lt
    {Γ : DWeb V} {S Z : Set V} (F : JoinedFamily Γ S)
    (hcard : #Z < #F.paths) :
    ∃ p ∈ F.paths, p.support ∩ Z ⊆ S := by
  classical
  by_contra hex
  have hfail : ∀ p, p ∈ F.paths → ¬ p.support ∩ Z ⊆ S := by
    intro p hp hsub
    exact hex ⟨p, hp, hsub⟩
  have hdisjoint : F.paths.PairwiseDisjoint
      (fun p : FinitePath Γ.graph ↦ p.support \ S) := by
    intro p hp q hq hpq
    change Disjoint (p.support \ S) (q.support \ S)
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact hxp.2 (F.joined hp hq hpq ⟨hxp.1, hxq.1⟩)
  have hmeet : ∀ p ∈ F.paths,
      ∃ x ∈ Z, x ∈ p.support \ S := by
    intro p hp
    obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp (hfail p hp)
    exact ⟨x, hx.2, hx.1, hxnot⟩
  have hle : #F.paths ≤ #Z :=
    FamilyTools.mk_le_of_pairwiseDisjoint_of_meets hdisjoint hmeet
  exact (not_le_of_gt hcard) hle

/-- The paths of a joined family ending at one prescribed vertex form an
in-fan.  The normalization field is what turns intersection in the old
join set into intersection only at the common terminal. -/
def finishFiber {Γ : DWeb V} {S : Set V} (F : JoinedFamily Γ S) (y : V) :
    JoinedFamily Γ {y} where
  paths := {p | p ∈ F.paths ∧ p.finish = y}
  starts_in_source hp := F.starts_in_source hp.1
  ends_in_join hp := Set.mem_singleton_iff.2 hp.2
  join_only_at_end := by
    intro p hp x hx
    exact Set.mem_singleton_iff.2
      ((Set.mem_singleton_iff.1 hx.2).trans hp.2.symm)
  joined := by
    intro p hp q hq hpq x hx
    have hxS : x ∈ S := F.joined hp.1 hq.1 hpq hx
    have hxpS : x ∈ p.support ∩ S := ⟨hx.1, hxS⟩
    have hxp : x = p.finish :=
      Set.mem_singleton_iff.1 (F.join_only_at_end hp.1 hxpS)
    exact Set.mem_singleton_iff.2 (hxp.trans hp.2)

@[simp]
theorem mem_finishFiber {Γ : DWeb V} {S : Set V}
    (F : JoinedFamily Γ S) (y : V) (p : FinitePath Γ.graph) :
    p ∈ (F.finishFiber y).paths ↔ p ∈ F.paths ∧ p.finish = y :=
  Iff.rfl

/-- Selecting one path for each of a family of distinct terminal vertices
turns a joined family into a genuine warp. -/
def selectedTerminalWarp {Γ : DWeb V} {S : Set V} (F : JoinedFamily Γ S)
    {ι : Type*} (select : ι → FinitePath Γ.graph)
    (hmem : ∀ i, select i ∈ F.paths)
    (hfinish : Function.Injective fun i ↦ (select i).finish) :
    XSWarp Γ S where
  paths := Set.range select
  disjoint := by
    rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ hpq
    change Disjoint (select i).support (select j).support
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hijPath : select i ≠ select j := hpq
    have hxS : x ∈ S := F.joined (hmem i) (hmem j) hijPath ⟨hxi, hxj⟩
    have hxi' : x = (select i).finish :=
      Set.mem_singleton_iff.1
        (F.join_only_at_end (hmem i) ⟨hxi, hxS⟩)
    have hxj' : x = (select j).finish :=
      Set.mem_singleton_iff.1
        (F.join_only_at_end (hmem j) ⟨hxj, hxS⟩)
    have hij : i = j := hfinish (hxi'.symm.trans hxj')
    exact hpq (congrArg select hij)
  starts_in_source := by
    rintro p ⟨i, rfl⟩
    exact F.starts_in_source (hmem i)
  ends_in_target := by
    rintro p ⟨i, rfl⟩
    exact F.ends_in_join (hmem i)

end JoinedFamily

/-! ## Reversal to Aharoni's cardinally imbalanced out-fans -/

namespace JoinedFamily

/-- Avoiding all other vertices of an ambient set is exactly the
normalization condition needed for a path starting or ending at `c`. -/
theorem support_inter_subset_singleton_of_not_meets_sdiff
    {G : Digraph V} (p : FinitePath G) {C : Set V} {c : V}
    (havoid : ¬ p.walk.Meets (C \ {c})) :
    p.support ∩ C ⊆ {c} := by
  intro x hx
  by_cases hxc : x = c
  · exact Set.mem_singleton_iff.2 hxc
  · exact False.elim <| havoid ⟨x, hx.1, hx.2,
      fun hxs ↦ hxc (Set.mem_singleton_iff.1 hxs)⟩

/-- Reverse a finite path in the transposed graph back into the original
graph.  The `simpa` only transports the path along `transpose_transpose`. -/
def unreverse {G : Digraph V} (q : FinitePath (transpose G)) :
    FinitePath G :=
  cast (congrArg FinitePath (transpose_transpose G)) q.reverse

private theorem finitePath_start_cast {G H : Digraph V} (h : G = H)
    (p : FinitePath G) :
    (cast (congrArg FinitePath h) p).start = p.start := by
  subst h
  rfl

private theorem finitePath_finish_cast {G H : Digraph V} (h : G = H)
    (p : FinitePath G) :
    (cast (congrArg FinitePath h) p).finish = p.finish := by
  subst h
  rfl

private theorem finitePath_support_cast {G H : Digraph V} (h : G = H)
    (p : FinitePath G) :
    (cast (congrArg FinitePath h) p).support = p.support := by
  subst h
  rfl

@[simp]
theorem unreverse_start {G : Digraph V}
    (q : FinitePath (transpose G)) : (unreverse q).start = q.finish := by
  exact finitePath_start_cast (transpose_transpose G) q.reverse

@[simp]
theorem unreverse_finish {G : Digraph V}
    (q : FinitePath (transpose G)) : (unreverse q).finish = q.start := by
  exact finitePath_finish_cast (transpose_transpose G) q.reverse

@[simp]
theorem unreverse_support {G : Digraph V}
    (q : FinitePath (transpose G)) : (unreverse q).support = q.support := by
  exact (finitePath_support_cast (transpose_transpose G) q.reverse).trans
    (FinitePath.support_reverse q)

/-- A singleton joined in-family, reversed into the out-fan convention of
Aharoni's Lemma 2.5. -/
def reverseOutFan {Γ : DWeb V} {c : V} (F : JoinedFamily Γ {c}) :
    InfiniteKonig.OutFan (transpose Γ.graph) c Γ.source where
  paths := FinitePath.reverse '' F.paths
  starts_at := by
    rintro q ⟨p, hp, rfl⟩
    exact Set.mem_singleton_iff.1 (F.ends_in_join hp)
  finishes_in := by
    rintro q ⟨p, hp, rfl⟩
    exact F.starts_in_source hp
  joined := by
    rintro q ⟨p, hp, rfl⟩ r ⟨s, hs, rfl⟩ hne
    simpa only [FinitePath.support_reverse] using
      F.joined hp hs (fun hps ↦ hne (congrArg FinitePath.reverse hps))

/-- Reversal preserves the extra ambient-candidate normalization required
when Aharoni's Lemma 2.5 is applied to a family of `C`--source paths. -/
theorem reverseOutFan_normalized {Γ : DWeb V} {c : V}
    (F : JoinedFamily Γ {c}) {C : Set V}
    (hnorm : ∀ {p}, p ∈ F.paths → p.support ∩ C ⊆ {c}) :
    ∀ {q}, q ∈ F.reverseOutFan.paths → q.support ∩ C ⊆ {c} := by
  rintro q ⟨p, hp, rfl⟩
  simpa only [FinitePath.support_reverse] using hnorm hp

/-- Reverse a normalized singleton joined family into the precise in-fan
interface of Aharoni's Lemma 2.5.  The ambient set `C` is deliberately
larger than the singleton join set: its normalization is the extra
hypothesis needed by the transfinite splicing argument. -/
def reverseInFan {Γ : DWeb V} {C : Set V} (c : C)
    (F : JoinedFamily Γ {c.1})
    (hnorm : ∀ {p}, p ∈ F.paths → p.support ∩ C ⊆ {c.1}) :
    Aharoni25.InFan (transpose Γ.graph) C Γ.source c.1 where
  paths := FinitePath.reverse '' F.paths
  start_eq := by
    rintro q ⟨p, hp, rfl⟩
    exact Set.mem_singleton_iff.1 (F.ends_in_join hp)
  join_mem := c.2
  finish_mem := by
    rintro q ⟨p, hp, rfl⟩
    exact F.starts_in_source hp
  normalized := by
    rintro q ⟨p, hp, rfl⟩
    simpa only [FinitePath.support_reverse] using hnorm hp
  joined := by
    rintro q ⟨p, hp, rfl⟩ r ⟨s, hs, rfl⟩ hne
    simpa only [FinitePath.support_reverse] using
      F.joined hp hs (fun hps ↦ hne (congrArg FinitePath.reverse hps))

/-- Reverse a disjoint out-warp in the transposed graph back to a genuine
source--`C` warp in the original web. -/
def unreverseWarp {Γ : DWeb V} {C : Set V}
    (Q : Set (FinitePath (transpose Γ.graph)))
    (hdisjoint : Q.PairwiseDisjoint FinitePath.support)
    (hstarts : ∀ {q}, q ∈ Q → q.start ∈ C)
    (hfinishes : ∀ {q}, q ∈ Q → q.finish ∈ Γ.source) :
    XSWarp Γ C where
  paths := unreverse '' Q
  disjoint := by
    rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ hne
    change Disjoint (unreverse q).support (unreverse s).support
    rw [unreverse_support, unreverse_support]
    exact hdisjoint hq hs (fun hqs ↦ hne (congrArg unreverse hqs))
  starts_in_source := by
    rintro p ⟨q, hq, rfl⟩
    simpa only [unreverse_start] using hfinishes hq
  ends_in_target := by
    rintro p ⟨q, hq, rfl⟩
    simpa only [unreverse_finish] using hstarts hq

@[simp]
theorem mem_unreverseWarp {Γ : DWeb V} {C : Set V}
    (Q : Set (FinitePath (transpose Γ.graph)))
    (hdisjoint : Q.PairwiseDisjoint FinitePath.support)
    (hstarts : ∀ {q}, q ∈ Q → q.start ∈ C)
    (hfinishes : ∀ {q}, q ∈ Q → q.finish ∈ Γ.source)
    (p : FinitePath Γ.graph) :
    p ∈ (unreverseWarp Q hdisjoint hstarts hfinishes).paths ↔
      ∃ q ∈ Q, p = unreverse q := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩

end JoinedFamily

namespace XSWarp

/-- Push every member of a warp to its first vertex in `T`.  The resulting
family need not be disjoint at `T`, but it is `T`-joined. -/
noncomputable def pushFamily {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w) :
    JoinedFamily Γ T where
  paths := {q | ∃ (p : FinitePath Γ.graph) (hp : p ∈ P.paths),
    q = P.pushPath hstep p hp}
  starts_in_source := by
    rintro q ⟨p, hp, rfl⟩
    simpa using P.starts_in_source hp
  ends_in_join := by
    rintro q ⟨p, hp, rfl⟩
    exact P.pushPath_finish_mem hstep p hp
  join_only_at_end := by
    rintro q ⟨p, hp, rfl⟩
    exact P.pushPath_join_only_at_end hstep p hp
  joined := by
    rintro q ⟨p, hp, rfl⟩ r ⟨p', hp', rfl⟩ hne x hx
    by_cases hxT : x ∈ T
    · exact hxT
    · exfalso
      have hxp : x ∈ p.support := by
        rcases P.pushPath_support_subset hstep p hp hx.1 with hxp | hxT'
        · exact hxp
        · exact (hxT hxT').elim
      have hxp' : x ∈ p'.support := by
        rcases P.pushPath_support_subset hstep p' hp' hx.2 with hxp' | hxT'
        · exact hxp'
        · exact (hxT hxT').elim
      have hpp' : p ≠ p' := by
        intro h
        subst p'
        exact hne rfl
      exact Set.disjoint_left.1 (P.disjoint hp hp' hpp') hxp hxp'

@[simp]
theorem mem_pushFamily {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (q : FinitePath Γ.graph) :
    q ∈ (P.pushFamily hstep).paths ↔
      ∃ (p : FinitePath Γ.graph) (hp : p ∈ P.paths),
        q = P.pushPath hstep p hp :=
  Iff.rfl

end XSWarp

/-- The `f`-indices of the initial vertices used by a source-certified
finite path family. -/
def initialIndicesOf {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (P : Set (FinitePath Γ.graph))
    (hP : ∀ {p}, p ∈ P → p.start ∈ Γ.source) : Set (Below κ) :=
  {a | ∃ (p : FinitePath Γ.graph) (hp : p ∈ P), U.f ⟨p.start, hP hp⟩ = a}

@[simp]
theorem mem_initialIndicesOf_iff {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (P : Set (FinitePath Γ.graph))
    (hP : ∀ {p}, p ∈ P → p.start ∈ Γ.source) (a : Below κ) :
    a ∈ initialIndicesOf U P hP ↔
      ∃ (p : FinitePath Γ.graph) (hp : p ∈ P), U.f ⟨p.start, hP hp⟩ = a :=
  Iff.rfl

namespace JoinedFamily

/-- Terminals actually used by a joined family.  Restricting to these
vertices makes every terminal fiber nonempty, as required by Lemma 8.5. -/
def UsedTerminal {Γ : DWeb V} {S : Set V} (F : JoinedFamily Γ S) :=
  {v : V // ∃ p ∈ F.paths, p.finish = v}

theorem usedTerminal_mem_join {Γ : DWeb V} {S : Set V}
    (F : JoinedFamily Γ S) (v : F.UsedTerminal) : v.1 ∈ S := by
  obtain ⟨p, hp, hpv⟩ := v.2
  exact hpv ▸ F.ends_in_join hp

/-- Initial indices in the fan ending at one used terminal. -/
def fiberIndices {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (v : F.UsedTerminal) : Set (Below κ) :=
  initialIndicesOf U (F.finishFiber v.1).paths
    (F.finishFiber v.1).starts_in_source

theorem fiberIndices_nonempty {Γ : DWeb V} {S : Set V}
    {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (F : JoinedFamily Γ S) (v : F.UsedTerminal) :
    (F.fiberIndices U v).Nonempty := by
  obtain ⟨p, hp, hpv⟩ := v.2
  exact ⟨U.f ⟨p.start, F.starts_in_source hp⟩,
    p, ⟨hp, hpv⟩, rfl⟩

/-- The terminal fibers cover all initial indices of the family. -/
theorem initialIndices_subset_iUnion_fiberIndices
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S) :
    initialIndicesOf U F.paths F.starts_in_source ⊆
      ⋃ v : F.UsedTerminal, F.fiberIndices U v := by
  intro a ha
  obtain ⟨p, hp, hpa⟩ := ha
  let v : F.UsedTerminal := ⟨p.finish, p, hp, rfl⟩
  exact Set.mem_iUnion.2 ⟨v, p, ⟨hp, rfl⟩, hpa⟩

end JoinedFamily

/-- A set is popular if it contains a source vertex or supports an
`S`-joined family with stationary initial-index set. -/
def IsPopular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (S : Set V) : Prop :=
  (S ∩ Γ.source).Nonempty ∨
    ∃ F : JoinedFamily Γ S,
      IsStationaryBelow κ (initialIndicesOf U F.paths F.starts_in_source)

/-- Strong popularity requires a genuine disjoint source--`S` warp. -/
def IsStronglyPopular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (S : Set V) : Prop :=
  ∃ P : XSWarp Γ S,
    IsStationaryBelow κ (initialIndicesOf U P.paths P.starts_in_source)

/-- Strong popularity is monotone in the terminal set. -/
theorem IsStronglyPopular.mono {Γ : DWeb V} {κ : Cardinal.{u}}
    {U : KappaIndexed Γ κ} {S T : Set V}
    (hS : IsStronglyPopular U S) (hST : S ⊆ T) :
    IsStronglyPopular U T := by
  obtain ⟨P, hP⟩ := hS
  exact ⟨P.mono hST, hP⟩

/-- Covering the initial vertices of a joined family by a genuine warp
preserves all of that family's ordinal indices. -/
theorem initialIndices_subset_of_covers_joinedFamily
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {C : Set V} (P : XSWarp Γ C) {c : V} (F : JoinedFamily Γ {c})
    (hcover : ∀ {p}, p ∈ F.paths →
      ∃ q ∈ P.paths, q.start = p.start) :
    initialIndicesOf U F.paths F.starts_in_source ⊆
      initialIndicesOf U P.paths P.starts_in_source := by
  rintro a ⟨p, hp, hpa⟩
  obtain ⟨q, hq, hstart⟩ := hcover hp
  refine ⟨q, hq, ?_⟩
  have hsource :
      (⟨q.start, P.starts_in_source hq⟩ : Γ.source) =
        ⟨p.start, F.starts_in_source hp⟩ := by
    apply Subtype.ext
    exact hstart
  exact (congrArg U.f hsource).trans hpa

/-- Covering the initial vertices of one stationary joined family by a
genuine warp makes the warp's terminal set strongly popular. -/
theorem stronglyPopular_of_covers_joinedFamily
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {C : Set V} (P : XSWarp Γ C) {c : V} (F : JoinedFamily Γ {c})
    (hF : IsStationaryBelow κ
      (initialIndicesOf U F.paths F.starts_in_source))
    (hcover : ∀ {p}, p ∈ F.paths →
      ∃ q ∈ P.paths, q.start = p.start) :
    IsStronglyPopular U C :=
  ⟨P, hF.mono (initialIndices_subset_of_covers_joinedFamily U P F hcover)⟩

/-- Aharoni's Lemma 2.5 in the orientation used in Section 8.  More than
`κ` ambient candidate vertices carry normalized singleton joined families;
after reversing the web, Lemma 2.5 produces a disjoint warp covering all
initial vertices of one family.  The explicit source-cardinality bound is
the hypothesis suppressed in the informal statement of Lemma 8.6. -/
theorem exists_warp_covering_one_joinedFamily_of_source_card_le
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hsource : #Γ.source ≤ κ) {C : Set V}
    (hCX : Disjoint C Γ.source) (hlarge : κ < #C)
    (F : (c : C) → JoinedFamily Γ {c.1})
    (hnorm : ∀ c {p}, p ∈ (F c).paths → p.support ∩ C ⊆ {c.1}) :
    ∃ (P : XSWarp Γ C) (c : C),
      initialIndicesOf U (F c).paths (F c).starts_in_source ⊆
        initialIndicesOf U P.paths P.starts_in_source := by
  let Fs : (c : C) →
      Aharoni25.InFan (transpose Γ.graph) C Γ.source c.1 :=
    fun c ↦ (F c).reverseInFan c (hnorm c)
  obtain ⟨c, W, hW⟩ :=
    Aharoni25.exists_warp_covering_one_fan
      (G := transpose Γ.graph) U.uncountable.le hCX hsource hlarge Fs
  let P : XSWarp Γ C :=
    JoinedFamily.unreverseWarp W.paths W.disjoint W.start_mem W.finish_mem
  refine ⟨P, c, initialIndices_subset_of_covers_joinedFamily U P (F c) ?_⟩
  intro p hp
  obtain ⟨q, hq, hfinish⟩ := hW p.reverse ⟨p, hp, rfl⟩
  refine ⟨JoinedFamily.unreverse q, ⟨q, hq, rfl⟩, ?_⟩
  change q.finish = p.start at hfinish
  simpa only [JoinedFamily.unreverse_start] using hfinish

/-- Source-bounded form of the Section 8 consequence of Aharoni's
Lemma 2.5. -/
theorem exists_warp_covering_one_joinedFamily
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hU : U.SourceBounded) {C : Set V}
    (hCX : Disjoint C Γ.source) (hlarge : κ < #C)
    (F : (c : C) → JoinedFamily Γ {c.1})
    (hnorm : ∀ c {p}, p ∈ (F c).paths → p.support ∩ C ⊆ {c.1}) :
    ∃ (P : XSWarp Γ C) (c : C),
      initialIndicesOf U (F c).paths (F c).starts_in_source ⊆
        initialIndicesOf U P.paths P.starts_in_source :=
  exists_warp_covering_one_joinedFamily_of_source_card_le U
    (U.source_card_le hU) hCX hlarge F hnorm

/-- If every member of a set larger than `κ` carries a stationary,
ambient-normalized fan, Aharoni's Lemma 2.5 makes the set strongly popular.
This is the contradiction form used to bound each popular layer. -/
theorem stronglyPopular_of_large_normalized_fans_of_source_card_le
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hsource : #Γ.source ≤ κ) {C : Set V}
    (hCX : Disjoint C Γ.source) (hlarge : κ < #C)
    (F : (c : C) → JoinedFamily Γ {c.1})
    (hnorm : ∀ c {p}, p ∈ (F c).paths → p.support ∩ C ⊆ {c.1})
    (hstationary : ∀ c, IsStationaryBelow κ
      (initialIndicesOf U (F c).paths (F c).starts_in_source)) :
    IsStronglyPopular U C := by
  obtain ⟨P, c, hindices⟩ :=
    exists_warp_covering_one_joinedFamily_of_source_card_le U hsource
      hCX hlarge F hnorm
  exact ⟨P, (hstationary c).mono hindices⟩

/-- Source-bounded convenience form of the large-normalized-fans
criterion. -/
theorem stronglyPopular_of_large_normalized_fans
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hU : U.SourceBounded) {C : Set V}
    (hCX : Disjoint C Γ.source) (hlarge : κ < #C)
    (F : (c : C) → JoinedFamily Γ {c.1})
    (hnorm : ∀ c {p}, p ∈ (F c).paths → p.support ∩ C ⊆ {c.1})
    (hstationary : ∀ c, IsStationaryBelow κ
      (initialIndicesOf U (F c).paths (F c).starts_in_source)) :
    IsStronglyPopular U C :=
  stronglyPopular_of_large_normalized_fans_of_source_card_le U
    (U.source_card_le hU) hCX hlarge F hnorm hstationary

def IsPopularVertex {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (v : V) : Prop :=
  IsPopular U {v}

namespace JoinedFamily

/-- A terminal fiber is nonstationary whenever its terminal vertex is
unpopular. -/
theorem fiberIndices_not_stationary_of_not_popular
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (v : F.UsedTerminal) (hv : ¬ IsPopularVertex U v.1) :
    ¬ IsStationaryBelow κ (F.fiberIndices U v) := by
  intro hstat
  apply hv
  exact Or.inr ⟨F.finishFiber v.1, hstat⟩

/-- Select the path in a terminal fiber carrying a prescribed initial
index. -/
noncomputable def pathAtFiberIndex
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (index : F.UsedTerminal → Below κ)
    (hindex : ∀ v, index v ∈ F.fiberIndices U v)
    (v : F.UsedTerminal) : FinitePath Γ.graph :=
  Classical.choose (hindex v)

theorem pathAtFiberIndex_mem
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (index : F.UsedTerminal → Below κ)
    (hindex : ∀ v, index v ∈ F.fiberIndices U v)
    (v : F.UsedTerminal) :
    F.pathAtFiberIndex U index hindex v ∈ F.paths :=
  (Classical.choose (Classical.choose_spec (hindex v))).1

theorem pathAtFiberIndex_finish
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (index : F.UsedTerminal → Below κ)
    (hindex : ∀ v, index v ∈ F.fiberIndices U v)
    (v : F.UsedTerminal) :
    (F.pathAtFiberIndex U index hindex v).finish = v.1 :=
  (Classical.choose (Classical.choose_spec (hindex v))).2

theorem pathAtFiberIndex_index
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (index : F.UsedTerminal → Below κ)
    (hindex : ∀ v, index v ∈ F.fiberIndices U v)
    (v : F.UsedTerminal) :
    U.f ⟨(F.pathAtFiberIndex U index hindex v).start,
      F.starts_in_source (F.pathAtFiberIndex_mem U index hindex v)⟩ =
        index v :=
  Classical.choose_spec (Classical.choose_spec (hindex v))

/-- The paths selected from distinct terminal fibers form a warp. -/
noncomputable def fiberSelectionWarp
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (index : F.UsedTerminal → Below κ)
    (hindex : ∀ v, index v ∈ F.fiberIndices U v) : XSWarp Γ S :=
  F.selectedTerminalWarp (F.pathAtFiberIndex U index hindex)
    (F.pathAtFiberIndex_mem U index hindex) <| by
      intro v w hfinish
      apply Subtype.ext
      exact (F.pathAtFiberIndex_finish U index hindex v).symm.trans
        (hfinish.trans (F.pathAtFiberIndex_finish U index hindex w))

/-- The selected warp retains every index in the range of the selector. -/
theorem range_subset_initialIndices_fiberSelectionWarp
    {Γ : DWeb V} {S : Set V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (F : JoinedFamily Γ S)
    (index : F.UsedTerminal → Below κ)
    (hindex : ∀ v, index v ∈ F.fiberIndices U v) :
    Set.range index ⊆ initialIndicesOf U
      (F.fiberSelectionWarp U index hindex).paths
      (F.fiberSelectionWarp U index hindex).starts_in_source := by
  rintro a ⟨v, rfl⟩
  let p := F.pathAtFiberIndex U index hindex v
  have hp : p ∈ (F.fiberSelectionWarp U index hindex).paths := ⟨v, rfl⟩
  refine ⟨p, hp, ?_⟩
  simpa [p] using F.pathAtFiberIndex_index U index hindex v

end JoinedFamily

/-- Lemma 8.5 turns a stationary joined family whose used terminals are all
unpopular into a strongly popular warp.  Each terminal fibre is nonempty and
nonstationary; the stationary-range selector chooses one initial index in
every fibre, and paths realizing those choices are disjoint because distinct
terminal fibres of a joined family can meet only at the join set. -/
theorem stronglyPopular_of_joined_of_unpopular_terminals
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S : Set V} (F : JoinedFamily Γ S)
    (hstat : IsStationaryBelow κ
      (initialIndicesOf U F.paths F.starts_in_source))
    (hunpopular : ∀ v ∈ S, ¬ IsPopularVertex U v) :
    IsStronglyPopular U S := by
  let Ξ : F.UsedTerminal → Set (Below κ) := F.fiberIndices U
  have hΞnonempty : ∀ v, (Ξ v).Nonempty := fun v ↦
    F.fiberIndices_nonempty U v
  have hΞnonstationary : ∀ v, ¬ IsStationaryBelow κ (Ξ v) := fun v ↦
    F.fiberIndices_not_stationary_of_not_popular U v
      (hunpopular v.1 (F.usedTerminal_mem_join v))
  have hΞunion : IsStationaryBelow κ (⋃ v, Ξ v) :=
    hstat.mono (F.initialIndices_subset_iUnion_fiberIndices U)
  obtain ⟨g, hg, hgstat⟩ :=
    InfiniteKonig.stationary_range_choice U.uncountable U.regular Ξ
      hΞnonempty hΞnonstationary hΞunion
  let P : XSWarp Γ S := F.fiberSelectionWarp U g hg
  exact ⟨P, hgstat.mono
    (F.range_subset_initialIndices_fiberSelectionWarp U g hg)⟩

/-- One-step propagation used in Assertions 8.8 and 8.9: a stationary
warp to `S`, together with an outgoing edge from every member of `S` into
`T`, produces a stationary `T`-joined family. -/
theorem popular_of_stronglyPopular_of_step
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S T : Set V}
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (hS : IsStronglyPopular U S) : IsPopular U T := by
  classical
  rcases hS with ⟨P, hstat⟩
  let F : JoinedFamily Γ T := P.pushFamily hstep
  apply Or.inr
  refine ⟨F, hstat.mono ?_⟩
  intro a ha
  obtain ⟨p, hp, hpa⟩ := ha
  let q : FinitePath Γ.graph := P.pushPath hstep p hp
  have hq : q ∈ F.paths := ⟨p, hp, rfl⟩
  refine ⟨q, hq, ?_⟩
  have hstart : q.start = p.start := P.pushPath_start hstep p hp
  subst q
  simpa only [XSWarp.pushFamily, XSWarp.pushPath_start] using hpa

/-- Every source vertex is popular. -/
theorem popularVertex_of_mem_source {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {v : V} (hv : v ∈ Γ.source) :
    IsPopularVertex U v := by
  exact Or.inl ⟨v, Set.mem_singleton v, hv⟩

/-- On a set consisting entirely of unpopular vertices, popularity already
implies strong popularity.  The source-vertex alternative is impossible,
and Lemma 8.5 converts the remaining stationary joined family into a warp. -/
theorem stronglyPopular_of_popular_of_all_vertices_unpopular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S : Set V} (hpopular : IsPopular U S)
    (hunpopular : ∀ v ∈ S, ¬ IsPopularVertex U v) :
    IsStronglyPopular U S := by
  rcases hpopular with hsource | ⟨F, hstat⟩
  · obtain ⟨v, hvS, hvsource⟩ := hsource
    exact (hunpopular v hvS (popularVertex_of_mem_source U hvsource)).elim
  · exact stronglyPopular_of_joined_of_unpopular_terminals
      U F hstat hunpopular

/-- Generic successor step of Assertion 8.8.  If every vertex of `S` is
unpopular, every vertex of `S` has an edge into `T`, and `T` is not popular,
then `S` is not popular. -/
theorem not_popular_of_all_vertices_unpopular_of_step
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S T : Set V}
    (hunpopular : ∀ v ∈ S, ¬ IsPopularVertex U v)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (hT : ¬ IsPopular U T) :
    ¬ IsPopular U S := by
  intro hS
  exact hT (popular_of_stronglyPopular_of_step U hstep
    (stronglyPopular_of_popular_of_all_vertices_unpopular
      U hS hunpopular))

/-- Generic successor step of Assertion 8.9. -/
theorem not_stronglyPopular_of_step_of_not_popular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S T : Set V}
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w)
    (hT : ¬ IsPopular U T) :
    ¬ IsStronglyPopular U S := by
  intro hS
  exact hT (popular_of_stronglyPopular_of_step U hstep hS)

/-! ## Lemma 8.3 -/

/-- Aharoni--Berger Lemma 8.3: the initial indices of every source--target
warp in a `κ`-unbalanced web are nonstationary. -/
theorem warp_initialIndices_nonstationary {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ) (P : XSWarp Γ Γ.target) :
    ¬ IsStationaryBelow κ
      (initialIndicesOf U P.paths P.starts_in_source) := by
  classical
  let I : Set (Below κ) := initialIndicesOf U P.paths P.starts_in_source
  let chosen : (a : Below κ) → a ∈ I → FinitePath Γ.graph := fun a ha ↦
    Classical.choose ha
  have chosen_mem (a : Below κ) (ha : a ∈ I) : chosen a ha ∈ P.paths :=
    Classical.choose (Classical.choose_spec ha)
  have chosen_index (a : Below κ) (ha : a ∈ I) :
      U.f ⟨(chosen a ha).start, P.starts_in_source (chosen_mem a ha)⟩ = a :=
    Classical.choose_spec (Classical.choose_spec ha)
  let r : Below κ → Below κ := fun a ↦
    if ha : a ∈ I then
      U.g ⟨(chosen a ha).finish, P.ends_in_target (chosen_mem a ha)⟩
    else a
  have hreg : IsRegressiveOn I r := by
    intro a ha
    have hdesc := U.descends (chosen a ha)
      (P.starts_in_source (chosen_mem a ha))
      (P.ends_in_target (chosen_mem a ha))
    have hr : r a = U.g ⟨(chosen a ha).finish,
        P.ends_in_target (chosen_mem a ha)⟩ := by simp [r, ha]
    rw [hr]
    exact lt_of_lt_of_eq hdesc (chosen_index a ha)
  have hinj : Set.InjOn r I := by
    intro a ha b hb hrab
    have hra : r a = U.g ⟨(chosen a ha).finish,
        P.ends_in_target (chosen_mem a ha)⟩ := by simp [r, ha]
    have hrb : r b = U.g ⟨(chosen b hb).finish,
        P.ends_in_target (chosen_mem b hb)⟩ := by simp [r, hb]
    have hterminal :
        (⟨(chosen a ha).finish,
          P.ends_in_target (chosen_mem a ha)⟩ : Γ.target) =
        ⟨(chosen b hb).finish,
          P.ends_in_target (chosen_mem b hb)⟩ := by
      apply U.g.injective
      exact hra.symm.trans (hrab.trans hrb)
    have hfinish : (chosen a ha).finish = (chosen b hb).finish :=
      congrArg Subtype.val hterminal
    have hpath : chosen a ha = chosen b hb :=
      P.eq_of_finish_eq (chosen_mem a ha) (chosen_mem b hb) hfinish
    have hsource :
        (⟨(chosen a ha).start,
          P.starts_in_source (chosen_mem a ha)⟩ : Γ.source) =
        ⟨(chosen b hb).start,
          P.starts_in_source (chosen_mem b hb)⟩ := by
      apply Subtype.ext
      exact congrArg FinitePath.start hpath
    exact (chosen_index a ha).symm.trans
      ((congrArg U.f hsource).trans (chosen_index b hb))
  exact not_isStationaryBelow_of_injOn_regressive
    U.uncountable U.regular hreg hinj

/-- Consequently a subset of the target is not strongly popular. -/
theorem not_stronglyPopular_of_subset_target {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ) {S : Set V} (hS : S ⊆ Γ.target) :
    ¬ IsStronglyPopular U.toKappaIndexed S := by
  rintro ⟨P, hstat⟩
  let Q : XSWarp Γ Γ.target :=
    { P with ends_in_target := fun hp ↦ hS (P.ends_in_target hp) }
  exact warp_initialIndices_nonstationary U Q hstat

/-- The base case of Assertion 8.8.  A set of unpopular target vertices is
not popular.  Pressing down makes the terminal of a stationary joined
family constant, contradicting the unpopularity of that terminal. -/
theorem not_popular_of_subset_target_unpopular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ)
    {S : Set V}
    (hS : S ⊆ Γ.target ∩ {v | ¬ IsPopularVertex U.toKappaIndexed v}) :
    ¬ IsPopular U.toKappaIndexed S := by
  classical
  rintro (hsource | ⟨F, hstat⟩)
  · obtain ⟨x, hxS, hxX⟩ := hsource
    exact (hS hxS).2 (popularVertex_of_mem_source U.toKappaIndexed hxX)
  · let I : Set (Below κ) :=
      initialIndicesOf U.toKappaIndexed F.paths F.starts_in_source
    let chosen : (a : Below κ) → a ∈ I → FinitePath Γ.graph := fun a ha ↦
      Classical.choose ha
    have chosen_mem (a : Below κ) (ha : a ∈ I) : chosen a ha ∈ F.paths :=
      Classical.choose (Classical.choose_spec ha)
    have chosen_index (a : Below κ) (ha : a ∈ I) :
        U.f ⟨(chosen a ha).start, F.starts_in_source (chosen_mem a ha)⟩ = a :=
      Classical.choose_spec (Classical.choose_spec ha)
    have chosen_finish_target (a : Below κ) (ha : a ∈ I) :
        (chosen a ha).finish ∈ Γ.target :=
      (hS (F.ends_in_join (chosen_mem a ha))).1
    let r : Below κ → Below κ := fun a ↦
      if ha : a ∈ I then
        U.g ⟨(chosen a ha).finish, chosen_finish_target a ha⟩
      else a
    have hreg : IsRegressiveOn I r := by
      intro a ha
      have hdesc := U.descends (chosen a ha)
        (F.starts_in_source (chosen_mem a ha))
        (chosen_finish_target a ha)
      have hr : r a = U.g ⟨(chosen a ha).finish,
          chosen_finish_target a ha⟩ := by simp [r, ha]
      rw [hr]
      exact lt_of_lt_of_eq hdesc (chosen_index a ha)
    obtain ⟨i, hi⟩ := pressingDown U.uncountable U.regular hstat hreg
    obtain ⟨a₀, ha₀I, ha₀r⟩ := hi.nonempty
    let y : V := (chosen a₀ ha₀I).finish
    have hyS : y ∈ S := F.ends_in_join (chosen_mem a₀ ha₀I)
    let Fy : JoinedFamily Γ {y} := F.finishFiber y
    have hJsub : I ∩ {a | r a = i} ⊆
        initialIndicesOf U.toKappaIndexed Fy.paths Fy.starts_in_source := by
      intro a ha
      have hram : r a = U.g ⟨(chosen a ha.1).finish,
          chosen_finish_target a ha.1⟩ := by
        dsimp only [r]
        rw [dif_pos ha.1]
      have hra₀ : r a₀ = U.g ⟨(chosen a₀ ha₀I).finish,
          chosen_finish_target a₀ ha₀I⟩ := by
        dsimp only [r]
        rw [dif_pos ha₀I]
      have hfinish : (chosen a ha.1).finish = y := by
        have hsub :
            (⟨(chosen a ha.1).finish,
              chosen_finish_target a ha.1⟩ : Γ.target) =
            ⟨(chosen a₀ ha₀I).finish,
              chosen_finish_target a₀ ha₀I⟩ := by
          apply U.g.injective
          exact hram.symm.trans (ha.2.trans (ha₀r.symm.trans hra₀))
        simpa [y] using congrArg Subtype.val hsub
      exact ⟨chosen a ha.1, ⟨chosen_mem a ha.1, hfinish⟩,
        chosen_index a ha.1⟩
    have hFy : IsStationaryBelow κ
        (initialIndicesOf U.toKappaIndexed Fy.paths Fy.starts_in_source) :=
      hi.mono hJsub
    have hypop : IsPopularVertex U.toKappaIndexed y := Or.inr ⟨Fy, hFy⟩
    exact (hS hyS).2 hypop

/-! ## The layer separator from Theorem 8.4 -/

/-- In-neighbours of a vertex set. -/
def inNeighbors (Γ : DWeb V) (S : Set V) : Set V :=
  {v | ∃ w ∈ S, Γ.graph.Adj v w}

/-- Popular and unpopular vertices. -/
def popularVertices {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : Set V :=
  {v | IsPopularVertex U v}

def unpopularVertices {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : Set V :=
  (popularVertices U)ᶜ

/-- The unpopular layers `U_i` of Theorem 8.4. -/
def unpopularLayer {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : ℕ → Set V
  | 0 => Γ.target ∩ unpopularVertices U
  | n + 1 => inNeighbors Γ (unpopularLayer U n) ∩ unpopularVertices U

/-- Every unpopular layer consists of unpopular vertices. -/
theorem unpopularLayer_subset_unpopular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (n : ℕ) :
    unpopularLayer U n ⊆ unpopularVertices U := by
  cases n <;> exact Set.inter_subset_right

/-- The popular layers `P_i` of Theorem 8.4. -/
def popularLayer {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : ℕ → Set V
  | 0 => Γ.target ∩ popularVertices U
  | n + 1 => inNeighbors Γ (unpopularLayer U n) ∩ popularVertices U

/-- Every popular layer consists of popular vertices. -/
theorem popularLayer_subset_popular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (n : ℕ) :
    popularLayer U n ⊆ popularVertices U := by
  cases n <;> exact Set.inter_subset_right

/-- Assertion 8.8 at layer zero. -/
theorem unpopularLayer_zero_not_popular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ) :
    ¬ IsPopular U.toKappaIndexed (unpopularLayer U.toKappaIndexed 0) := by
  apply not_popular_of_subset_target_unpopular U
  intro x hx
  exact ⟨hx.1, hx.2⟩

/-- Assertion 8.9 at layer zero. -/
theorem popularLayer_zero_not_stronglyPopular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ) :
    ¬ IsStronglyPopular U.toKappaIndexed
      (popularLayer U.toKappaIndexed 0) := by
  apply not_stronglyPopular_of_subset_target U
  exact Set.inter_subset_left

/-- The inductive implication in Assertion 8.9.  If the preceding
unpopular layer is not popular, then the next popular layer cannot be
strongly popular. -/
theorem popularLayer_succ_not_stronglyPopular_of_not_popular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ) (n : ℕ)
    (hUn : ¬ IsPopular U (unpopularLayer U n)) :
    ¬ IsStronglyPopular U (popularLayer U (n + 1)) := by
  intro hPn
  apply hUn
  apply popular_of_stronglyPopular_of_step U (hS := hPn)
  intro v hv
  exact hv.1

/-- The canonical layer separator `S = ⋃ i<ω P_i`. -/
def layerSeparator {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : Set V :=
  ⋃ n : ℕ, popularLayer U n

/-- Every member of the canonical separator is a popular vertex. -/
theorem layerSeparator_subset_popular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) :
    layerSeparator U ⊆ popularVertices U := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact popularLayer_subset_popular U n hxn

/-- A set separates the source from the target when every finite
source--target path meets it. -/
def IsSeparator (Γ : DWeb V) (S : Set V) : Prop :=
  ∀ p : FinitePath Γ.graph, p.start ∈ Γ.source → p.finish ∈ Γ.target →
    (p.support ∩ S).Nonempty

/-- The localized popularity conclusion in Theorem 8.4: the in-fan lies
inside the strict roof of the separator, apart from its common terminal. -/
def IsLocallyPopularAt {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (C : Set V) (c : V) : Prop :=
  c ∈ Γ.source ∨
    ∃ F : JoinedFamily Γ {c},
      IsStationaryBelow κ (initialIndicesOf U F.paths F.starts_in_source) ∧
      ∀ p ∈ F.paths, p.support ⊆ Γ.strictRoof C ∪ {c}

/-- The exact three conclusions of source Theorem 8.4, bundled with the
separator it constructs. -/
structure PopularSeparator {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) where
  cut : Set V
  separates : IsSeparator Γ cut
  locally_popular : ∀ c ∈ cut, IsLocallyPopularAt U cut c
  card_diff_source : Cardinal.lift.{u + 1, u} #{x // x ∈ cut \ Γ.source} ≤
    Cardinal.lift.{u + 1, u} κ
  not_strongly_popular : ¬ IsStronglyPopular U cut

private theorem walk_start_mem_unpopularLayer_of_avoids
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {a b : V} (w : Walk Γ.graph a b) (hb : b ∈ Γ.target)
    (hav : ∀ x ∈ w.support, x ∉ layerSeparator U) :
    ∃ n : ℕ, a ∈ unpopularLayer U n := by
  match w with
  | .nil =>
      by_cases hpop : a ∈ popularVertices U
      · exact False.elim <| hav a (by simp)
          (Set.mem_iUnion.2 ⟨0, ⟨hb, hpop⟩⟩)
      · exact ⟨0, hb, hpop⟩
  | .cons e w =>
      have havTail : ∀ x ∈ w.support, x ∉ layerSeparator U := by
        intro x hx
        exact hav x (by simp [hx])
      obtain ⟨n, hcn⟩ :=
        walk_start_mem_unpopularLayer_of_avoids U w hb havTail
      have hain : a ∈ inNeighbors Γ (unpopularLayer U n) := ⟨_, hcn, e⟩
      by_cases hpop : a ∈ popularVertices U
      · exact False.elim <| hav a (by simp)
          (Set.mem_iUnion.2 ⟨n + 1, ⟨hain, hpop⟩⟩)
      · exact ⟨n + 1, hain, hpop⟩

/-- The layer construction always gives a source--target separator. -/
theorem layerSeparator_isSeparator {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) : IsSeparator Γ (layerSeparator U) := by
  intro p hpX hpY
  by_contra hmeet
  have hav : ∀ x ∈ p.walk.support, x ∉ layerSeparator U := by
    intro x hxp hxS
    exact hmeet ⟨x, hxp, hxS⟩
  obtain ⟨n, hUn⟩ :=
    walk_start_mem_unpopularLayer_of_avoids U p.walk hpY hav
  exact (unpopularLayer_subset_unpopular U n hUn)
    (popularVertex_of_mem_source U hpX)

end Popular
end Erdos599
