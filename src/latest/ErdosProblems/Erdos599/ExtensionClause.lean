/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.SingularCardinal

/-!
# Erdős Problem 599: the extension clause

This file records the correctly quantified form of the extension clause in
Aharoni--Berger, Theorem 9.2.  The predicate
`CardinalInduction.ExtensionClauseAt Γ κ` deliberately describes only the
conclusion at `κ`; the theorem which establishes it has the indispensable
additional hypothesis that `Γ` is unhindered.

The elementary facts below are useful independently of the three cardinal
cases.  In particular, the zero-cardinal case follows directly from the
given linkage on the complementary source set.  The equivalence at the end
also makes precise that proving the extension clause at every cardinal of a
fixed unhindered web is exactly as strong as proving that the web is
linkable: specialize to the cardinality of the entire source.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-! ## The exhaustive cardinal split used by the extension step -/

/-- The source proof has a zero case, a positive countable case, and the
regular/singular alternatives above `aleph_0`.  Keeping `aleph_0` in the
countable branch is important: the generic regular/singular trichotomy
classifies it as regular. -/
inductive ExtensionCardinalCase (κ : Cardinal.{u}) : Prop
  | zero (hκ : κ = 0)
  | countable (hκpos : 0 < κ) (hκc : κ ≤ ℵ₀)
  | uncountableRegular (hκu : ℵ₀ < κ) (hκr : κ.IsRegular)
  | uncountableSingular (hκu : ℵ₀ < κ) (hκs : κ.IsSingular)

theorem extensionCardinalCase (κ : Cardinal.{u}) :
    ExtensionCardinalCase κ := by
  rcases eq_zero_or_pos κ with hκ | hκpos
  · exact .zero hκ
  rcases le_or_gt κ ℵ₀ with hκc | hκu
  · exact .countable hκpos hκc
  rcases Cardinal.isRegular_or_isSingular hκu.le with hκr | hκs
  · exact .uncountableRegular hκu hκr
  · exact .uncountableSingular hκu hκs

/-- The source-faithful formulation of the extension clause theorem.

The `IsUnhindered` assumption belongs outside `ExtensionClauseAt`, because
the latter is the conclusion labelled `(clubsuit)` in Theorem 9.2. -/
def UnhinderedExtensionClauseAt (Γ : DWeb V) (κ : Cardinal.{u}) : Prop :=
  Γ.IsUnhindered → ExtensionClauseAt Γ κ

/-- A linkable web satisfies the extension clause at every cardinal. -/
theorem extensionClauseAt_of_linkable (Γ : DWeb V) (κ : Cardinal.{u})
    (hΓ : IsLinkable Γ) : ExtensionClauseAt Γ κ := by
  intro A₀ hA₀ hcard hcomplement
  exact hΓ

/-- A linkable web satisfies the correctly quantified extension theorem. -/
theorem unhinderedExtensionClauseAt_of_linkable (Γ : DWeb V)
    (κ : Cardinal.{u}) (hΓ : IsLinkable Γ) :
    UnhinderedExtensionClauseAt Γ κ := by
  intro _
  exact extensionClauseAt_of_linkable Γ κ hΓ

/-- Cardinal zero is the genuine base case of `(clubsuit)`: the designated
source set is empty, so the supplied complementary linkage already links all
sources.  No unhinderedness assumption is needed in this degenerate case. -/
theorem extensionClauseAt_zero (Γ : DWeb V) :
    ExtensionClauseAt Γ 0 := by
  intro A₀ hA₀ hcard hcomplement
  have hA₀empty : A₀ = ∅ := by
    exact Cardinal.mk_set_eq_zero_iff.mp hcard
  obtain ⟨F, hF⟩ := hcomplement
  refine ⟨F, ?_⟩
  simpa [hA₀empty] using hF

/-- The zero-cardinal instance in the source-faithful formulation. -/
theorem unhinderedExtensionClauseAt_zero (Γ : DWeb V) :
    UnhinderedExtensionClauseAt Γ 0 := by
  intro _
  exact extensionClauseAt_zero Γ

/-! ## Closed-set assembly

The last step in both uncountable cases is the same.  A new linkage is
built wholly inside a closed vertex set `Z`; it is then united with exactly
the paths of the old complementary linkage whose initial vertices lie
outside `Z`.  Competitor closure ensures that those old paths avoid `Z`, so
the union is still a warp. -/

theorem linkage_union_outside
    (Γ : DWeb V) (A₀ Z : Set V) (P F : Set Γ.DPath)
    (hA₀ : A₀ ⊆ Z)
    (hP : IsLinkageBetween Γ (Γ.source ∩ Z) Γ.target P)
    (hPZ : Γ.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F)
    (hclosed : ∀ p ∈ F, (p.support ∩ Z).Nonempty → p.initial ∈ Z) :
    IsLinkageBetween Γ Γ.source Γ.target
      (P ∪ {p | p ∈ F ∧ p.initial ∉ Z}) := by
  let Fout : Set Γ.DPath := {p | p ∈ F ∧ p.initial ∉ Z}
  have hFout_support (p : Γ.DPath) (hp : p ∈ Fout) :
      Disjoint p.support Z := by
    rw [Set.disjoint_left]
    intro x hxp hxZ
    exact hp.2 (hclosed p hp.1 ⟨x, hxp, hxZ⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpP | hpO
    · rcases hq with hqP | hqO
      · exact hP.isWarp hpP hqP hpq
      · change Disjoint p.support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        have hxZ : x ∈ Z := hPZ ⟨p, hpP, hxp⟩
        exact Set.disjoint_left.1 (hFout_support q hqO) hxq hxZ
    · rcases hq with hqP | hqO
      · change Disjoint p.support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        have hxZ : x ∈ Z := hPZ ⟨q, hqP, hxq⟩
        exact Set.disjoint_left.1 (hFout_support p hpO) hxp hxZ
      · exact hF.isWarp hpO.1 hqO.1 hpq
  · intro p hp
    rcases hp with hpP | hpO
    · exact hP.finiteCharacter hpP
    · exact hF.finiteCharacter hpO.1
  · ext x
    constructor
    · rintro ⟨p, hpP | hpO, rfl⟩
      · have hx := show p.initial ∈ Γ.initialSet P from ⟨p, hpP, rfl⟩
        rw [hP.initialSet_eq] at hx
        exact hx.1
      · have hx := show p.initial ∈ Γ.initialSet F from ⟨p, hpO.1, rfl⟩
        rw [hF.initialSet_eq] at hx
        exact hx.1
    · intro hx
      by_cases hxZ : x ∈ Z
      · have hxP : x ∈ Γ.initialSet P := by
          rw [hP.initialSet_eq]
          exact ⟨hx, hxZ⟩
        rcases hxP with ⟨p, hpP, hpinit⟩
        exact ⟨p, Or.inl hpP, hpinit⟩
      · have hxA₀ : x ∉ A₀ := fun hxA₀ ↦ hxZ (hA₀ hxA₀)
        have hxF : x ∈ Γ.initialSet F := by
          rw [hF.initialSet_eq]
          exact ⟨hx, hxA₀⟩
        rcases hxF with ⟨p, hpF, hpinit⟩
        refine ⟨p, Or.inr ⟨hpF, ?_⟩, hpinit⟩
        simpa [hpinit] using hxZ
  · intro x hx
    rcases hx with ⟨p, hpP | hpO, hpterm⟩
    · exact hP.terminalFrontier_subset ⟨p, hpP, hpterm⟩
    · exact hF.terminalFrontier_subset ⟨p, hpO.1, hpterm⟩
  · intro p hp
    rcases hp with hpP | hpO
    · rcases hP.endpointPure p hpP with ⟨q, rfl, hends, hsource⟩
      have hsZ : q.support ⊆ Z := by
        intro x hx
        exact hPZ ⟨Sum.inl q, hpP, hx⟩
      refine ⟨q, rfl, ?_, ?_⟩
      · rw [← hends]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hxs, hxsour | hxtarget⟩
          · exact ⟨hxs, Or.inl ⟨hxsour, hsZ hxs⟩⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
        · rintro ⟨hxs, ⟨hxsour, -⟩ | hxtarget⟩
          · exact ⟨hxs, Or.inl hxsour⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
      · rw [← hsource]
        ext x
        simp only [Set.mem_inter_iff]
        constructor
        · rintro ⟨hxs, hxsour⟩
          exact ⟨hxs, hxsour, hsZ hxs⟩
        · rintro ⟨hxs, hxsour, -⟩
          exact ⟨hxs, hxsour⟩
    · rcases hF.endpointPure p hpO.1 with ⟨q, hpq, hends, hsource⟩
      have hpDisjoint : Disjoint p.support Z := hFout_support p hpO
      subst p
      have hsA₀ : Disjoint q.support A₀ := hpDisjoint.mono_right hA₀
      refine ⟨q, rfl, ?_, ?_⟩
      · rw [← hends]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
        constructor
        · rintro ⟨hxs, hxsour | hxtarget⟩
          · exact ⟨hxs, Or.inl ⟨hxsour,
              fun hxA₀ ↦ Set.disjoint_left.1 hsA₀ hxs hxA₀⟩⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
        · rintro ⟨hxs, ⟨hxsour, -⟩ | hxtarget⟩
          · exact ⟨hxs, Or.inl hxsour⟩
          · exact ⟨hxs, Or.inr hxtarget⟩
      · rw [← hsource]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_diff]
        constructor
        · rintro ⟨hxs, hxsour⟩
          exact ⟨hxs, hxsour,
            fun hxA₀ ↦ Set.disjoint_left.1 hsA₀ hxs hxA₀⟩
        · rintro ⟨hxs, hxsour, -⟩
          exact ⟨hxs, hxsour⟩

/-! ## From suffix certificates to matrix target segments -/

/-- The list-based suffix certificate in `LinksToTarget` gives an actual
finite suffix beginning at the designated vertex and meeting the target.
The proof uses simplicity of the carrier path to identify its canonical
last-hit suffix with the displayed list suffix. -/
theorem suffixFrom_meets_of_finitePathSuffixMeets
    {D : Digraph V} (q : DirectedPath.FinitePath D) (a : V) (B : Set V)
    (h : FinitePathSuffixMeets q a B) :
    ∃ ha : a ∈ q.support, (q.suffixFrom a ha).walk.Meets B := by
  obtain ⟨before, after, hsupport, b, hbB, hb⟩ := h
  have ha : a ∈ q.support := by
    change a ∈ q.walk.support
    rw [hsupport]
    simp
  refine ⟨ha, ?_⟩
  let s := q.suffixFrom a ha
  have hscons : s.walk.support = a :: s.walk.support.tail := by
    have h := (List.cons_head_tail s.walk.support_ne_nil).symm
    simpa only [s, DirectedPath.FinitePath.suffixFrom_start,
      DirectedPath.Walk.head_support] using h
  have hsuffix : s.walk.support <:+ q.walk.support := by
    exact (q.walk.lastHit {a} ⟨a, ha, Set.mem_singleton a⟩).support_suffix
  obtain ⟨pre, hpre⟩ := hsuffix
  have heq : pre ++ a :: s.walk.support.tail = before ++ a :: after := by
    calc
      pre ++ a :: s.walk.support.tail = pre ++ s.walk.support :=
        congrArg (fun l ↦ pre ++ l) hscons.symm
      _ = q.walk.support := hpre
      _ = before ++ a :: after := hsupport
  have hnd : (pre ++ a :: s.walk.support.tail).Nodup := by
    rw [heq, ← hsupport]
    exact q.isPath
  have hnotpre : a ∉ pre := by
    have hparts := List.nodup_append.1 hnd
    intro hapre
    exact hparts.2.2 a hapre a (by simp) rfl
  have hnottail : a ∉ s.walk.support.tail := by
    exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have htail : s.walk.support.tail = after :=
    (List.append_cons_inj_of_notMem hnotpre hnottail).1 heq |>.2.2
  refine ⟨b, ?_, hbB⟩
  rw [hscons, htail]
  exact hb

/-- A strengthened half-way target certificate supplies exactly the finite
target segment required in every cell of the singular competitor matrix. -/
theorem targetSegment_of_linksToTarget
    {Gamma : DWeb V} {W : Set Gamma.DPath} {A : Set V}
    (hlinks : LinksToTarget Gamma W A) {a : V} (ha : a ∈ A) :
    Nonempty (Gamma.TargetSegment W A a) := by
  obtain ⟨p, hpW, q, rfl, hpure, hsuffix⟩ := hlinks a ha
  obtain ⟨haq, hmeet⟩ :=
    suffixFrom_meets_of_finitePathSuffixMeets q a Gamma.target hsuffix
  exact ⟨{
    source_mem := ha
    carrier := .inl q
    carrier_mem := hpW
    carrier_pure := hpure
    path := q.suffixFrom a haq
    path_start := q.suffixFrom_start a haq
    path_meets_target := hmeet
    path_support_subset := q.suffixFrom_support_subset a haq }⟩

/-! ## The singular-column linkage adapter

Assertion 9.18 constructs its paths in `SingularCardinal`, below the import
of the canonical linkage predicate in this file's dependency graph.  The
following theorem is the non-circular adapter: the first-target prefixes in
one completed matrix column satisfy all five clauses of
`IsLinkageBetween`, including the source's endpoint-purity requirement. -/

theorem linkageBetween_limitSources_of_competitorMatrix
    {I : Type u} [Preorder I]
    {κs : I → Cardinal.{u}} {A₀ : Set V}
    {Qualified : Set V → Cardinal.{u} → Set (Γ.DPath) → Prop}
    (M : SingularCardinal.CompetitorMatrix (I := I) Γ κs A₀ Qualified)
    (i : I) :
    IsLinkageBetween Γ
      (SingularCardinal.CompetitorMatrix.limitSources Γ M i) Γ.target
      (SingularCardinal.CompetitorMatrix.targetPaths Γ M i) := by
  refine ⟨SingularCardinal.CompetitorMatrix.targetPaths_isWarp Γ M i,
    SingularCardinal.CompetitorMatrix.targetPaths_finiteCharacter Γ M i,
    SingularCardinal.CompetitorMatrix.initialSet_targetPaths Γ M i,
    SingularCardinal.CompetitorMatrix.terminalFrontier_targetPaths_subset
      Γ M i, ?_⟩
  rintro p ⟨a, rfl⟩
  refine ⟨SingularCardinal.CompetitorMatrix.targetPath Γ M i a, rfl,
    SingularCardinal.CompetitorMatrix.targetPath_endpoint_pure Γ M i a,
    ?_⟩
  simpa only [SingularCardinal.CompetitorMatrix.targetPath_start] using
    SingularCardinal.CompetitorMatrix.targetPath_source_pure Γ M i a

/-- In a warp which covers every source, a source vertex on a member is
necessarily that member's initial vertex. -/
theorem source_mem_support_eq_initial_of_full_warp
    (Γ : DWeb V) {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hinit : Γ.initialSet W = Γ.source) {p : Γ.DPath} (hp : p ∈ W)
    {x : V} (hxp : x ∈ p.support) (hxsource : x ∈ Γ.source) :
    x = p.initial := by
  have hxinit : x ∈ Γ.initialSet W := hinit.symm ▸ hxsource
  obtain ⟨q, hq, hqx⟩ := hxinit
  by_cases hpq : p = q
  · subst q
    exact hqx.symm
  · exact False.elim <| Set.disjoint_left.1 (hW hp hq hpq) hxp
      (hqx ▸ q.initial_mem_support)

/-- The direct-limit carrier selected for a matrix source really starts at
that source.  The suffix witness itself need not state this; it follows from
the fact that every finite row is a warp covering the full source. -/
theorem competitorMatrix_limitAmbient_initial
    {I : Type u} [Preorder I]
    {κs : I → Cardinal.{u}} {A₀ : Set V}
    {Qualified : Set V → Cardinal.{u} → Set (Γ.DPath) → Prop}
    (M : SingularCardinal.CompetitorMatrix (I := I) Γ κs A₀ Qualified)
    (i : I)
    (a : SingularCardinal.CompetitorMatrix.limitSources Γ M i) :
    (SingularCardinal.CompetitorMatrix.limitAmbient Γ M i a).initial = a.1 := by
  let n := SingularCardinal.CompetitorMatrix.sourceStage Γ M i a
  let T := SingularCardinal.CompetitorMatrix.stageTargetSegment Γ M i a
  have haCarrier : a.1 ∈ T.carrier.support :=
    T.path_support_subset (by simpa only [T.path_start] using
      T.path.start_mem_support)
  have hcarrierInitial : T.carrier.initial = a.1 :=
    (source_mem_support_eq_initial_of_full_warp Γ
      (M.paths_isWarp i n) (M.paths_initial i n) T.carrier_mem haCarrier
      (M.sources_subset_source i n T.source_mem)).symm
  exact (Γ.extends_initial
    (SingularCardinal.CompetitorMatrix.stageCarrier_extends_limitAmbient
      Γ M i a)).symm.trans hcarrierInitial

/-- Although a matrix row records purity only against its designated
subset, its being a full-source warp upgrades every extracted target prefix
to purity against the entire source of the web. -/
theorem competitorMatrix_targetPath_source_pure_full
    {I : Type u} [Preorder I]
    {κs : I → Cardinal.{u}} {A₀ : Set V}
    {Qualified : Set V → Cardinal.{u} → Set (Γ.DPath) → Prop}
    (M : SingularCardinal.CompetitorMatrix (I := I) Γ κs A₀ Qualified)
    (i : I)
    (a : SingularCardinal.CompetitorMatrix.limitSources Γ M i) :
    (SingularCardinal.CompetitorMatrix.targetPath Γ M i a).support ∩
        Γ.source =
      {(SingularCardinal.CompetitorMatrix.targetPath Γ M i a).start} := by
  let n := SingularCardinal.CompetitorMatrix.sourceStage Γ M i a
  let T := SingularCardinal.CompetitorMatrix.stageTargetSegment Γ M i a
  let q := SingularCardinal.CompetitorMatrix.targetPath Γ M i a
  have hqsub : q.support ⊆ T.carrier.support :=
    DWeb.TargetSegment.firstTarget_support_subset_carrier Γ T
  have hcarrierInit : T.carrier.initial = a.1 := by
    have haCarrier : a.1 ∈ T.carrier.support := hqsub (by
      simpa only [q, SingularCardinal.CompetitorMatrix.targetPath_start] using
        q.start_mem_support)
    exact (source_mem_support_eq_initial_of_full_warp Γ
      (M.paths_isWarp i n) (M.paths_initial i n) T.carrier_mem haCarrier
      (M.sources_subset_source i n T.source_mem)).symm
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxsource⟩
    have hxinit : x = T.carrier.initial :=
      source_mem_support_eq_initial_of_full_warp Γ
        (M.paths_isWarp i n) (M.paths_initial i n) T.carrier_mem
        (hqsub hxq) hxsource
    exact Set.mem_singleton_iff.2 <|
      hxinit.trans (hcarrierInit.trans (by
        simpa only [q,
          SingularCardinal.CompetitorMatrix.targetPath_start]))
  · rintro x hx
    have hxq : x = q.start := Set.mem_singleton_iff.1 hx
    subst x
    refine ⟨q.start_mem_support, ?_⟩
    simpa only [q,
      SingularCardinal.CompetitorMatrix.targetPath_start] using
      M.sources_subset_source i n T.source_mem

/-- The target prefix in any completed matrix column is an exact
`source`--`target` path, not merely a path pure against the current column's
source set. -/
theorem competitorMatrix_targetPath_isPathBetween_full
    {I : Type u} [Preorder I]
    {κs : I → Cardinal.{u}} {A₀ : Set V}
    {Qualified : Set V → Cardinal.{u} → Set (Γ.DPath) → Prop}
    (M : SingularCardinal.CompetitorMatrix (I := I) Γ κs A₀ Qualified)
    (i : I)
    (a : SingularCardinal.CompetitorMatrix.limitSources Γ M i) :
    IsPathBetween Γ Γ.source Γ.target
      (Sum.inl (SingularCardinal.CompetitorMatrix.targetPath Γ M i a)) := by
  let q := SingularCardinal.CompetitorMatrix.targetPath Γ M i a
  refine ⟨q, rfl, ?_, competitorMatrix_targetPath_source_pure_full M i a⟩
  rw [Set.inter_union_distrib_left,
    competitorMatrix_targetPath_source_pure_full M i a,
    SingularCardinal.CompetitorMatrix.targetPath_target_pure Γ M i a]
  change ({q.start} ∪ {q.finish} : Set V) = {q.start, q.finish}
  simp only [Set.singleton_union]

/-! ## Least-column assembly in the singular case -/

namespace SingularLeast

open SingularCardinal
open SingularCardinal.CompetitorMatrix

variable {Γ : DWeb V}
variable {I : Type u} [LinearOrder I] [WellFoundedLT I]
variable {κs : I → Cardinal.{u}} {A₀ : Set V}
variable {Qualified : Set V → Cardinal.{u} → Set Γ.DPath → Prop}

abbrev Matrix (Γ : DWeb V) (κs : I → Cardinal.{u}) (A₀ : Set V)
    (Qualified : Set V → Cardinal.{u} → Set Γ.DPath → Prop) :=
  CompetitorMatrix (I := I) Γ κs A₀ Qualified

/-- The sources occurring in at least one completed matrix column. -/
def globalSources (M : Matrix Γ κs A₀ Qualified) : Set V :=
  ⋃ i, limitSources Γ M i

/-- The nonempty set of columns containing a global source. -/
def sourceColumns (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) : Set I :=
  {i | a.1 ∈ limitSources Γ M i}

theorem sourceColumns_nonempty (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) :
    (sourceColumns M a).Nonempty := by
  obtain ⟨i, hai⟩ := Set.mem_iUnion.1 a.2
  exact ⟨i, hai⟩

/-- The least matrix column containing a given global source. -/
def leastColumn (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) : I :=
  wellFounded_lt.min (sourceColumns M a) (sourceColumns_nonempty M a)

theorem leastColumn_mem (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) :
    a.1 ∈ limitSources Γ M (leastColumn M a) :=
  wellFounded_lt.min_mem (sourceColumns M a) (sourceColumns_nonempty M a)

theorem leastColumn_le (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) {i : I}
    (hai : a.1 ∈ limitSources Γ M i) : leastColumn M a ≤ i := by
  exact le_of_not_gt (wellFounded_lt.not_lt_min (sourceColumns M a) hai)

/-- The target prefix selected in the least column containing `a`. -/
def selectedTargetPath (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) : Γ.DPath :=
  .inl (targetPath Γ M (leastColumn M a) ⟨a.1, leastColumn_mem M a⟩)

/-- One selected target prefix for every source occurring in the matrix. -/
def selectedTargetPaths (M : Matrix Γ κs A₀ Qualified) : Set Γ.DPath :=
  Set.range (selectedTargetPath M)

@[simp]
theorem selectedTargetPath_initial (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) :
    (selectedTargetPath M a).initial = a.1 := by
  change (targetPath Γ M (leastColumn M a)
    ⟨a.1, leastColumn_mem M a⟩).start = a.1
  exact targetPath_start Γ M (leastColumn M a)
    ⟨a.1, leastColumn_mem M a⟩

theorem selectedTargetPath_support_subset_ambient
    (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) :
    (selectedTargetPath M a).support ⊆
      (limitAmbient Γ M (leastColumn M a)
        ⟨a.1, leastColumn_mem M a⟩).support := by
  change (targetPath Γ M (leastColumn M a)
    ⟨a.1, leastColumn_mem M a⟩).support ⊆ _
  exact targetPath_support_subset_limitAmbient Γ M (leastColumn M a)
    ⟨a.1, leastColumn_mem M a⟩

theorem selectedTargetPath_mem_limitFamily
    (M : Matrix Γ κs A₀ Qualified)
    (a : globalSources M) :
    limitAmbient Γ M (leastColumn M a)
      ⟨a.1, leastColumn_mem M a⟩ ∈ limitFamily Γ M := by
  exact Or.inr (Set.mem_iUnion.2 ⟨leastColumn M a,
    limitAmbient_mem Γ M (leastColumn M a)
      ⟨a.1, leastColumn_mem M a⟩⟩)

/-- If two selected paths meet, their least columns coincide. -/
theorem leastColumn_eq_of_not_disjoint
    (M : Matrix Γ κs A₀ Qualified)
    (a b : globalSources M)
    (hab : ¬ Disjoint (selectedTargetPath M a).support
      (selectedTargetPath M b).support) :
    leastColumn M a = leastColumn M b := by
  let ia := leastColumn M a
  let ib := leastColumn M b
  let pa := limitAmbient Γ M ia ⟨a.1, leastColumn_mem M a⟩
  let pb := limitAmbient Γ M ib ⟨b.1, leastColumn_mem M b⟩
  have hpmeet : ¬ Disjoint pa.support pb.support := by
    intro hd
    exact hab (hd.mono (selectedTargetPath_support_subset_ambient M a)
      (selectedTargetPath_support_subset_ambient M b))
  have hcompAB : Γ.Competitors (limitFamily Γ M) a.1 b.1 := by
    exact ⟨pa, selectedTargetPath_mem_limitFamily M a,
      competitorMatrix_limitAmbient_initial M ia ⟨a.1, leastColumn_mem M a⟩,
      pb, selectedTargetPath_mem_limitFamily M b,
      competitorMatrix_limitAmbient_initial M ib ⟨b.1, leastColumn_mem M b⟩,
      hpmeet⟩
  have hbIa : b.1 ∈ limitSources Γ M ia :=
    limitSources_closed Γ M ia ⟨a.1, leastColumn_mem M a, hcompAB⟩
  have hib_le : ib ≤ ia := leastColumn_le M b hbIa
  have hcompBA := hcompAB.symm
  have haIb : a.1 ∈ limitSources Γ M ib :=
    limitSources_closed Γ M ib ⟨b.1, leastColumn_mem M b, hcompBA⟩
  have hia_le : ia ≤ ib := leastColumn_le M a haIb
  exact le_antisymm hia_le hib_le

/-- Target prefixes belonging to equal (possibly dependently presented)
columns are disjoint when their initial vertices differ. -/
theorem targetPath_disjoint_of_index_eq (M : Matrix Γ κs A₀ Qualified)
    {i j : I} (hij : i = j)
    (a : limitSources Γ M i) (b : limitSources Γ M j)
    (hab : a.1 ≠ b.1) :
    Disjoint
      (DirectedPath.Path.support
        (Sum.inl (targetPath Γ M i a) : Γ.DPath))
      (DirectedPath.Path.support
        (Sum.inl (targetPath Γ M j b) : Γ.DPath)) := by
  subst j
  apply targetPaths_isWarp Γ M i
    (show (Sum.inl (targetPath Γ M i a) : Γ.DPath) ∈
      targetPaths Γ M i from ⟨a, rfl⟩)
    (show (Sum.inl (targetPath Γ M i b) : Γ.DPath) ∈
      targetPaths Γ M i from ⟨b, rfl⟩)
  intro hpq
  apply hab
  have hinit := congrArg DirectedPath.Path.initial hpq
  change (targetPath Γ M i a).start =
    (targetPath Γ M i b).start at hinit
  simpa only [targetPath_start] using hinit

/-- Least-column target prefixes from all columns form one warp. -/
theorem selectedTargetPaths_isWarp (M : Matrix Γ κs A₀ Qualified) :
    Γ.IsWarp (selectedTargetPaths M) := by
  rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hpq
  by_contra hab
  have hij := leastColumn_eq_of_not_disjoint M a b hab
  have habval : a.1 ≠ b.1 := by
    intro heq
    apply hpq
    have habsub : a = b := Subtype.ext heq
    subst b
    rfl
  exact hab (targetPath_disjoint_of_index_eq M hij
    ⟨a.1, leastColumn_mem M a⟩ ⟨b.1, leastColumn_mem M b⟩ habval)

theorem initialSet_selectedTargetPaths (M : Matrix Γ κs A₀ Qualified) :
    Γ.initialSet (selectedTargetPaths M) = globalSources M := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, ⟨a, rfl⟩, hpx⟩
    rw [selectedTargetPath_initial] at hpx
    exact hpx ▸ a.2
  · intro x hx
    let a : globalSources M := ⟨x, hx⟩
    exact ⟨selectedTargetPath M a, ⟨a, rfl⟩,
      selectedTargetPath_initial M a⟩

theorem selectedTargetPaths_finiteCharacter
    (M : Matrix Γ κs A₀ Qualified) :
    Γ.HasFiniteCharacter (selectedTargetPaths M) := by
  rintro p ⟨a, rfl⟩
  exact ⟨targetPath Γ M (leastColumn M a) ⟨a.1, leastColumn_mem M a⟩, rfl⟩

theorem terminalFrontier_selectedTargetPaths
    (M : Matrix Γ κs A₀ Qualified) :
    Γ.terminalFrontier (selectedTargetPaths M) ⊆ Γ.target := by
  rintro x ⟨p, ⟨a, rfl⟩, hterm⟩
  have hfinish :
      (targetPath Γ M (leastColumn M a)
        ⟨a.1, leastColumn_mem M a⟩).finish = x :=
    Option.some.inj hterm
  exact hfinish ▸ targetPath_finish_mem Γ M (leastColumn M a)
    ⟨a.1, leastColumn_mem M a⟩

theorem selectedTargetPath_source_pure
    (M : Matrix Γ κs A₀ Qualified) (a : globalSources M) :
    (selectedTargetPath M a).support ∩ Γ.source = {a.1} := by
  change (targetPath Γ M (leastColumn M a)
    ⟨a.1, leastColumn_mem M a⟩).support ∩ Γ.source = {a.1}
  simpa only [targetPath_start] using
    competitorMatrix_targetPath_source_pure_full M (leastColumn M a)
      ⟨a.1, leastColumn_mem M a⟩

theorem selectedTargetPath_endpoint_pure
    (M : Matrix Γ κs A₀ Qualified) (a : globalSources M) :
    (selectedTargetPath M a).support ∩ (Γ.source ∪ Γ.target) =
      {(selectedTargetPath M a).initial,
        (targetPath Γ M (leastColumn M a)
          ⟨a.1, leastColumn_mem M a⟩).finish} := by
  rw [Set.inter_union_distrib_left,
    selectedTargetPath_source_pure M a]
  change {a.1} ∪
      (targetPath Γ M (leastColumn M a)
        ⟨a.1, leastColumn_mem M a⟩).support ∩ Γ.target = _
  rw [targetPath_target_pure]
  simp only [selectedTargetPath_initial]
  exact Set.singleton_union

/-- A fixed path meeting the global source union must itself start in that
union, by column closure and full-source coverage of the direct limit. -/
theorem fixed_initial_mem_globalSources_of_meets
    (M : Matrix Γ κs A₀ Qualified)
    {p : Γ.DPath} (hp : p ∈ M.fixed)
    (hmeet : (p.support ∩ globalSources M).Nonempty) :
    p.initial ∈ globalSources M := by
  obtain ⟨x, hxp, hxZ⟩ := hmeet
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxZ
  have hxinit : x ∈ Γ.initialSet (limitPaths Γ M i) := by
    rw [limitPaths_initialSet Γ M i]
    exact limitSources_subset_source Γ M i hxi
  obtain ⟨q, hq, hqx⟩ := hxinit
  have hqmem : q ∈ limitFamily Γ M :=
    Or.inr (Set.mem_iUnion.2 ⟨i, hq⟩)
  have hpmem : p ∈ limitFamily Γ M := Or.inl hp
  have hcomp : Γ.Competitors (limitFamily Γ M) x p.initial := by
    refine ⟨q, hqmem, hqx, p, hpmem, rfl, ?_⟩
    exact Set.not_disjoint_iff.2 ⟨x, hqx ▸ q.initial_mem_support, hxp⟩
  exact Set.mem_iUnion.2 ⟨i,
    limitSources_closed Γ M i ⟨x, hxi, hcomp⟩⟩

/-- The final singular assembly: a complementary linkage carried by the
matrix's fixed family plus least-column target prefixes links every source. -/
theorem isLinkable_of_competitorMatrix
    (M : Matrix Γ κs A₀ Qualified)
    (hfixed : IsLinkageBetween Γ (Γ.source \ A₀) Γ.target M.fixed) :
    IsLinkable Γ := by
  let Z := globalSources M
  let P := selectedTargetPaths M
  let Fout : Set Γ.DPath := {p | p ∈ M.fixed ∧ p.initial ∉ Z}
  have hA₀Z : A₀ ⊆ Z := cover_limitSources Γ M
  have hFout_support (p : Γ.DPath) (hp : p ∈ Fout) :
      Disjoint p.support Z := by
    rw [Set.disjoint_left]
    intro x hxp hxZ
    exact hp.2 (fixed_initial_mem_globalSources_of_meets M hp.1 ⟨x, hxp, hxZ⟩)
  refine ⟨P ∪ Fout, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpP | hpF
    · rcases hq with hqP | hqF
      · exact selectedTargetPaths_isWarp M hpP hqP hpq
      · obtain ⟨a, rfl⟩ := hpP
        change Disjoint (selectedTargetPath M a).support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        let i := leastColumn M a
        let r := limitAmbient Γ M i ⟨a.1, leastColumn_mem M a⟩
        have hcomp : Γ.Competitors (limitFamily Γ M) a.1 q.initial := by
          refine ⟨r, selectedTargetPath_mem_limitFamily M a,
            competitorMatrix_limitAmbient_initial M i
              ⟨a.1, leastColumn_mem M a⟩,
            q, Or.inl hqF.1, rfl, ?_⟩
          exact Set.not_disjoint_iff.2 ⟨x,
            selectedTargetPath_support_subset_ambient M a hxp, hxq⟩
        have hqZi : q.initial ∈ limitSources Γ M i :=
          limitSources_closed Γ M i ⟨a.1, leastColumn_mem M a, hcomp⟩
        exact hqF.2 (Set.mem_iUnion.2 ⟨i, hqZi⟩)
    · rcases hq with hqP | hqF
      · exact (show Disjoint q.support p.support by
          obtain ⟨a, rfl⟩ := hqP
          rw [Set.disjoint_left]
          intro x hxq hxp
          let i := leastColumn M a
          let r := limitAmbient Γ M i ⟨a.1, leastColumn_mem M a⟩
          have hcomp : Γ.Competitors (limitFamily Γ M) a.1 p.initial := by
            refine ⟨r, selectedTargetPath_mem_limitFamily M a,
              competitorMatrix_limitAmbient_initial M i
                ⟨a.1, leastColumn_mem M a⟩,
              p, Or.inl hpF.1, rfl, ?_⟩
            exact Set.not_disjoint_iff.2 ⟨x,
              selectedTargetPath_support_subset_ambient M a hxq, hxp⟩
          have hpZi : p.initial ∈ limitSources Γ M i :=
            limitSources_closed Γ M i ⟨a.1, leastColumn_mem M a, hcomp⟩
          exact hpF.2 (Set.mem_iUnion.2 ⟨i, hpZi⟩)).symm
      · exact hfixed.isWarp hpF.1 hqF.1 hpq
  · intro p hp
    rcases hp with hpP | hpF
    · exact selectedTargetPaths_finiteCharacter M hpP
    · exact hfixed.finiteCharacter hpF.1
  · ext x
    constructor
    · rintro ⟨p, hpP | hpF, rfl⟩
      · have hx : p.initial ∈ Z := by
          change p.initial ∈ globalSources M
          rw [← initialSet_selectedTargetPaths M]
          exact ⟨p, hpP, rfl⟩
        exact limitSources_subset_source Γ M _
          (Set.mem_iUnion.1 hx).choose_spec
      · have hx : p.initial ∈ Γ.source \ A₀ := by
          rw [← hfixed.initialSet_eq]
          exact ⟨p, hpF.1, rfl⟩
        exact hx.1
    · intro hx
      by_cases hxZ : x ∈ Z
      · change x ∈ globalSources M at hxZ
        rw [← initialSet_selectedTargetPaths M] at hxZ
        obtain ⟨p, hp, hpx⟩ := hxZ
        exact ⟨p, Or.inl hp, hpx⟩
      · have hxA₀ : x ∉ A₀ := fun h ↦ hxZ (hA₀Z h)
        have hxF : x ∈ Γ.initialSet M.fixed := by
          rw [hfixed.initialSet_eq]
          exact ⟨hx, hxA₀⟩
        obtain ⟨p, hp, hpx⟩ := hxF
        exact ⟨p, Or.inr ⟨hp, hpx ▸ hxZ⟩, hpx⟩
  · rintro x ⟨p, hpP | hpF, hterm⟩
    · exact terminalFrontier_selectedTargetPaths M ⟨p, hpP, hterm⟩
    · exact hfixed.terminalFrontier_subset ⟨p, hpF.1, hterm⟩
  · intro p hp
    rcases hp with hpP | hpF
    · obtain ⟨a, rfl⟩ := hpP
      exact competitorMatrix_targetPath_isPathBetween_full M
        (leastColumn M a) ⟨a.1, leastColumn_mem M a⟩
    · rcases hfixed.endpointPure p hpF.1 with ⟨q, hpq, hends, hsour⟩
      subst p
      have hdisA₀ : Disjoint q.support A₀ :=
        (hFout_support (Sum.inl q) hpF).mono_right hA₀Z
      refine ⟨q, rfl, ?_, ?_⟩
      · rw [← hends]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
        constructor
        · rintro ⟨hxs, hxsour | hxt⟩
          · exact ⟨hxs, Or.inl ⟨hxsour,
              fun hxA₀ ↦ Set.disjoint_left.1 hdisA₀ hxs hxA₀⟩⟩
          · exact ⟨hxs, Or.inr hxt⟩
        · rintro ⟨hxs, ⟨hxsour, -⟩ | hxt⟩
          · exact ⟨hxs, Or.inl hxsour⟩
          · exact ⟨hxs, Or.inr hxt⟩
      · rw [← hsour]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_diff]
        constructor
        · rintro ⟨hxs, hxsour⟩
          exact ⟨hxs, hxsour,
            fun hxA₀ ↦ Set.disjoint_left.1 hdisA₀ hxs hxA₀⟩
        · rintro ⟨hxs, hxsour, -⟩
          exact ⟨hxs, hxsour⟩

end SingularLeast

/-- At the cardinality of the entire source, the extension clause implies
linkability by taking the designated set to be the entire source. -/
theorem linkable_of_unhinderedExtensionClauseAt_source (Γ : DWeb V)
    (h : UnhinderedExtensionClauseAt Γ #Γ.source)
    (hunhindered : Γ.IsUnhindered) : IsLinkable Γ :=
  linkable_of_extension_at_source_card Γ (h hunhindered)

/-- For a fixed unhindered web, having the extension clause at every
cardinal is equivalent to linkability.  This is a useful completeness check
on any proposed finite/regular/singular assembly of Theorem 9.2. -/
theorem all_extensionClauses_iff_linkable (Γ : DWeb V)
    (_hunhindered : Γ.IsUnhindered) :
    (∀ κ : Cardinal.{u}, ExtensionClauseAt Γ κ) ↔ IsLinkable Γ := by
  constructor
  · intro h
    exact linkable_of_extension_at_source_card Γ (h #Γ.source)
  · intro h κ
    exact extensionClauseAt_of_linkable Γ κ h

/-- Equivalent formulation using the corrected theorem predicate. -/
theorem all_unhinderedExtensionClauses_iff
    (Γ : DWeb V) :
    (∀ κ : Cardinal.{u}, UnhinderedExtensionClauseAt Γ κ) ↔
      (Γ.IsUnhindered → IsLinkable Γ) := by
  constructor
  · intro h hunhindered
    exact linkable_of_unhinderedExtensionClauseAt_source Γ
      (h #Γ.source) hunhindered
  · intro h κ hunhindered
    exact extensionClauseAt_of_linkable Γ κ (h hunhindered)

end CardinalInduction
end Erdos599
