/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularClosedTargetRows
import ErdosProblems.Erdos599.SingularJointFullRow

/-!
# Historical competitor closure for singular target rows

Closing the `i`-th source set at stage `n + 1` under every row chosen
through stage `n` is enough to make the omega union of the source sets
closed under *all* historically chosen rows.  The proof uses only the
finite character of a competition: its source witness and its two paths
occur at finitely many stages, hence all occur in one later finite history.

This removes the apparent "+1" defect in the source-set bookkeeping.  It
does not remove the genuinely geometric defect.  Least-column assembly
needs paths selected in one column to form a warp.  Rows independently
chosen at different historical stages in the same column need not be
mutually disjoint.  Accordingly, `HistoricalRows.toClosedRows` has the
precise remaining premise that the historical union in each column is a
warp.  No forward extension or adjacent-stage coherence is assumed.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularHistoricalClosure

open SingularExtension SingularMatrix SingularClosedTargetRows
  SingularJointFullRow

universe u

variable {V : Type u}

/-- All simultaneous rows selected at stages at most `n`. -/
def historyThrough {G : DWeb V} {I : Type u}
    (paths : I → ℕ → Set G.DPath) (n : ℕ) : Set G.DPath :=
  ⋃ m : ℕ, ⋃ (_ : m ≤ n), ⋃ i, paths i m

/-- Every path selected at any stage. -/
def allPaths {G : DWeb V} {I : Type u}
    (paths : I → ℕ → Set G.DPath) : Set G.DPath :=
  ⋃ i, ⋃ n, paths i n

/-- All paths ever selected in one column. -/
def columnPaths {G : DWeb V} {I : Type u}
    (paths : I → ℕ → Set G.DPath) (i : I) : Set G.DPath :=
  ⋃ n, paths i n

/-- The omega union of one column's increasing auxiliary source sets. -/
def limitSources {I : Type u}
    (sources : I → ℕ → Set V) (i : I) : Set V :=
  ⋃ n, sources i n

/-- The simultaneous union represented by a finite list of rows. -/
def listFamily {G : DWeb V} {I : Type u}
    (rows : List (I → Set G.DPath)) : Set G.DPath :=
  ⋃ k : Fin rows.length, ⋃ i, (rows.get k) i

theorem row_subset_listFamily_cons
    {G : DWeb V} {I : Type u}
    (row : I → Set G.DPath) (rows : List (I → Set G.DPath))
    (i : I) : row i ⊆ listFamily (row :: rows) := by
  intro p hp
  exact Set.mem_iUnion.2 ⟨⟨0, by simp⟩,
    Set.mem_iUnion.2 ⟨i, by simpa⟩⟩

theorem listFamily_subset_cons
    {G : DWeb V} {I : Type u}
    (row : I → Set G.DPath) (rows : List (I → Set G.DPath)) :
    listFamily rows ⊆ listFamily (row :: rows) := by
  intro p hp
  obtain ⟨k, hp⟩ := Set.mem_iUnion.1 hp
  obtain ⟨i, hp⟩ := Set.mem_iUnion.1 hp
  exact Set.mem_iUnion.2 ⟨k.succ, Set.mem_iUnion.2 ⟨i, by simpa⟩⟩

/-- Reindex a finite list of simultaneous rows by the product of its list
position and its column. -/
def indexedListFamily {G : DWeb V} {I : Type u}
    (rows : List (I → Set G.DPath)) :
    Fin rows.length × I → Set G.DPath :=
  fun z ↦ (rows.get z.1) z.2

theorem iUnion_indexedListFamily
    {G : DWeb V} {I : Type u}
    (rows : List (I → Set G.DPath)) :
    (⋃ z, indexedListFamily rows z) = listFamily rows := by
  ext p
  constructor
  · intro hp
    obtain ⟨z, hp⟩ := Set.mem_iUnion.1 hp
    exact Set.mem_iUnion.2 ⟨z.1, Set.mem_iUnion.2 ⟨z.2, hp⟩⟩
  · intro hp
    obtain ⟨k, hp⟩ := Set.mem_iUnion.1 hp
    obtain ⟨i, hp⟩ := Set.mem_iUnion.1 hp
    exact Set.mem_iUnion.2 ⟨(k, i), hp⟩

theorem paths_subset_historyThrough_of_le
    {G : DWeb V} {I : Type u}
    {paths : I → ℕ → Set G.DPath} {i : I} {m n : ℕ}
    (hmn : m ≤ n) :
    paths i m ⊆ historyThrough paths n := by
  intro p hp
  exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2
    ⟨hmn, Set.mem_iUnion.2 ⟨i, hp⟩⟩⟩

theorem historyThrough_mono
    {G : DWeb V} {I : Type u}
    {paths : I → ℕ → Set G.DPath} {m n : ℕ}
    (hmn : m ≤ n) :
    historyThrough paths m ⊆ historyThrough paths n := by
  intro p hp
  obtain ⟨r, hp⟩ := Set.mem_iUnion.1 hp
  obtain ⟨hrm, hp⟩ := Set.mem_iUnion.1 hp
  obtain ⟨i, hp⟩ := Set.mem_iUnion.1 hp
  exact paths_subset_historyThrough_of_le (hrm.trans hmn) hp

theorem mem_fixed_union_allPaths_exists_history
    {G : DWeb V} {I : Type u}
    (fixed : Set G.DPath) (paths : I → ℕ → Set G.DPath)
    {p : G.DPath} (hp : p ∈ fixed ∪ allPaths paths) :
    ∃ n, p ∈ fixed ∪ historyThrough paths n := by
  rcases hp with hp | hp
  · exact ⟨0, Or.inl hp⟩
  · obtain ⟨i, hp⟩ := Set.mem_iUnion.1 hp
    obtain ⟨n, hp⟩ := Set.mem_iUnion.1 hp
    exact ⟨n, Or.inr (paths_subset_historyThrough_of_le le_rfl hp)⟩

/-- Successive source sets absorb competitors from the complete finite row
history available at that stage.  The rows themselves may be selected from
scratch; no adjacent forward-extension relation is imposed. -/
structure HistoricalRows
    (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) where
  sources : Index kappa → ℕ → Set V
  paths : Index kappa → ℕ → Set G.DPath
  seed : ∀ i,
    sourceLayer A₀ kappa hcard huncountable hsingular i ⊆ sources i 0
  sources_subset : ∀ i n, sources i n ⊆ G.source
  sources_mono : ∀ i, Monotone (sources i)
  isWarp : ∀ i n, G.IsWarp (paths i n)
  finiteCharacter : ∀ i n, G.HasFiniteCharacter (paths i n)
  initialSet : ∀ i n, G.initialSet (paths i n) = G.source
  links : ∀ i n, LinksToTarget G (paths i n) (sources i n)
  close : ∀ i n,
    G.competitorClosure (fixed ∪ historyThrough paths n) (sources i n) ⊆
      sources i (n + 1)

namespace HistoricalRows

variable {G : DWeb V} {fixed : Set G.DPath}
variable {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- Finite-history closure becomes closure under the entire omega history
after taking the union of the increasing source sets. -/
theorem limitSources_closed
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) (i : Index kappa) :
    G.competitorClosure (fixed ∪ allPaths R.paths)
        (limitSources R.sources i) ⊆
      limitSources R.sources i := by
  rintro b ⟨a, ha, p, hp, hpa, q, hq, hqb, hpq⟩
  obtain ⟨na, ha⟩ := Set.mem_iUnion.1 ha
  obtain ⟨np, hp⟩ :=
    mem_fixed_union_allPaths_exists_history fixed R.paths hp
  obtain ⟨nq, hq⟩ :=
    mem_fixed_union_allPaths_exists_history fixed R.paths hq
  let N : ℕ := max na (max np nq)
  have hna : na ≤ N := Nat.le_max_left _ _
  have hnp : np ≤ N :=
    (Nat.le_max_left np nq).trans (Nat.le_max_right na (max np nq))
  have hnq : nq ≤ N :=
    (Nat.le_max_right np nq).trans (Nat.le_max_right na (max np nq))
  have hpN : p ∈ fixed ∪ historyThrough R.paths N := by
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (historyThrough_mono hnp hp)
  have hqN : q ∈ fixed ∪ historyThrough R.paths N := by
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (historyThrough_mono hnq hq)
  have haN : a ∈ R.sources i N := R.sources_mono i hna ha
  have hb : b ∈ R.sources i (N + 1) :=
    R.close i N ⟨a, haN, p, hpN, hpa, q, hqN, hqb, hpq⟩
  exact Set.mem_iUnion.2 ⟨N + 1, hb⟩

/-- The union of all column histories is exactly `allPaths`. -/
theorem iUnion_columnPaths
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) :
    (⋃ i, columnPaths R.paths i) = allPaths R.paths := by
  rfl

/-- Each historical source union contains its canonical singular layer. -/
theorem seed_limitSources
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) (i : Index kappa) :
    sourceLayer A₀ kappa hcard huncountable hsingular i ⊆
      limitSources R.sources i := by
  exact (R.seed i).trans fun _ hx ↦ Set.mem_iUnion.2 ⟨0, hx⟩

/-- Finite character is preserved by an arbitrary union of finite-character
families, since it is a pointwise property of paths. -/
theorem columnPaths_finiteCharacter
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) (i : Index kappa) :
    G.HasFiniteCharacter (columnPaths R.paths i) := by
  intro p hp
  obtain ⟨n, hp⟩ := Set.mem_iUnion.1 hp
  exact R.finiteCharacter i n hp

/-- Every historical row has the full ambient source as initial set, hence
so does its union. -/
theorem initialSet_columnPaths
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) (i : Index kappa) :
    G.initialSet (columnPaths R.paths i) = G.source := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    obtain ⟨n, hp⟩ := Set.mem_iUnion.1 hp
    rw [← R.initialSet i n]
    exact ⟨p, hp, rfl⟩
  · intro x hx
    rw [← R.initialSet i 0] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, Set.mem_iUnion.2 ⟨0, hp⟩, hpx⟩

/-- A source which appears at a finite stage keeps its target segment in
the union of all rows. -/
theorem columnPaths_links
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) (hNorm : G.IsNormalized)
    (i : Index kappa) :
    LinksToTarget G (columnPaths R.paths i)
      (limitSources R.sources i) := by
  intro a ha
  obtain ⟨n, ha⟩ := Set.mem_iUnion.1 ha
  obtain ⟨p, hp, q, hq, hpure, hsuffix⟩ := R.links i n a ha
  have haSupport : a ∈ q.support := by
    have : a ∈ q.support ∩ R.sources i n := hpure.symm ▸ Set.mem_singleton a
    exact this.1
  have haStart : a = q.start :=
    hNorm.eq_start_of_mem_walk q.walk haSupport (R.sources_subset i n ha)
  refine ⟨p, Set.mem_iUnion.2 ⟨n, hp⟩, q, hq, ?_, hsuffix⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxLimit⟩
    obtain ⟨m, hxm⟩ := Set.mem_iUnion.1 hxLimit
    have hxStart : x = q.start :=
      hNorm.eq_start_of_mem_walk q.walk hxq (R.sources_subset i m hxm)
    exact Set.mem_singleton_iff.2 (hxStart.trans haStart.symm)
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨haSupport, Set.mem_iUnion.2 ⟨n, ha⟩⟩

/-- Since every historical row starts at the full ambient source, requiring
their union to be a warp forces all rows in that column to be literally
equal.  Thus the remaining `columnUnion_isWarp` field is stronger than mere
pairwise compatibility: it is a constant-column/master-row condition. -/
theorem paths_eq_of_columnUnion_isWarp
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (columnUnion_isWarp : ∀ i, G.IsWarp (columnPaths R.paths i))
    (i : Index kappa) (m n : ℕ) :
    R.paths i m = R.paths i n := by
  have hunion : G.IsWarp (R.paths i m ∪ R.paths i n) := by
    intro p hp q hq hpq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact columnUnion_isWarp i
        (Set.mem_iUnion.2 ⟨m, hp⟩) (Set.mem_iUnion.2 ⟨m, hq⟩) hpq
    · exact columnUnion_isWarp i
        (Set.mem_iUnion.2 ⟨m, hp⟩) (Set.mem_iUnion.2 ⟨n, hq⟩) hpq
    · exact columnUnion_isWarp i
        (Set.mem_iUnion.2 ⟨n, hp⟩) (Set.mem_iUnion.2 ⟨m, hq⟩) hpq
    · exact columnUnion_isWarp i
        (Set.mem_iUnion.2 ⟨n, hp⟩) (Set.mem_iUnion.2 ⟨n, hq⟩) hpq
  apply eq_of_union_isWarp_of_initialSet_eq_source G
    (R.initialSet i m) (R.initialSet i n)
  exact hunion

/-- Historical source closure is enough for the constant-row singular
construction exactly when the paths accumulated in each column form a
warp.  This is the precise same-column/different-stage coherence boundary
left by shifted least-column ownership. -/
noncomputable def toClosedRows
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hNorm : G.IsNormalized)
    (columnUnion_isWarp : ∀ i, G.IsWarp (columnPaths R.paths i)) :
    ClosedRows G fixed A₀ kappa huncountable hsingular hcard where
  sources i := limitSources R.sources i
  paths i := columnPaths R.paths i
  seed := R.seed_limitSources
  isWarp := columnUnion_isWarp
  finiteCharacter := R.columnPaths_finiteCharacter
  initialSet := R.initialSet_columnPaths
  links := R.columnPaths_links hNorm
  closed i := by
    rw [R.iUnion_columnPaths]
    exact R.limitSources_closed i

/-- The exact target-row matrix follows from historical closure plus the
single missing same-column union-warp condition. -/
noncomputable def toTargetRows
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hNorm : G.IsNormalized)
    (columnUnion_isWarp : ∀ i, G.IsWarp (columnPaths R.paths i)) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard :=
  (R.toClosedRows hNorm columnUnion_isWarp).toTargetRows

end HistoricalRows

/-! ## Unconditional finite-history construction

The lower induction hypothesis constructs every individual bounded row.
The following state machine accumulates all earlier rows in a finite list
and closes the next source set under that entire list.  Thus the
`HistoricalRows` bookkeeping itself is available unconditionally.  The
machine deliberately does not assert that the union of the successive
rows in one column is a warp. -/

/-- One bounded simultaneous row together with the finite list of all
strictly earlier simultaneous rows. -/
structure FiniteHistoryState
    (G : DWeb V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) where
  sources : Index kappa → Set V
  sources_subset : ∀ i, sources i ⊆ G.source
  sources_card : ∀ i,
    #(sources i) = scale kappa huncountable hsingular i
  current : Index kappa → Set G.DPath
  current_isWarp : ∀ i, G.IsWarp (current i)
  current_finiteCharacter : ∀ i, G.HasFiniteCharacter (current i)
  current_initialSet : ∀ i, G.initialSet (current i) = G.source
  current_links : ∀ i, LinksToTarget G (current i) (sources i)
  prior : List (Index kappa → Set G.DPath)
  prior_isWarp : ∀ j i, G.IsWarp ((prior.get j) i)
  prior_initialSet : ∀ j i,
    G.initialSet ((prior.get j) i) = G.source

namespace FiniteHistoryState

variable {G : DWeb V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}

/-- The current simultaneous row followed by all earlier rows. -/
def rows
    (S : FiniteHistoryState G kappa huncountable hsingular) :
    List (Index kappa → Set G.DPath) :=
  S.current :: S.prior

theorem rows_isWarp
    (S : FiniteHistoryState G kappa huncountable hsingular) (j) (i) :
    G.IsWarp ((S.rows.get j) i) := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · change G.IsWarp (S.current i)
    exact S.current_isWarp i
  · change G.IsWarp ((S.prior.get k) i)
    exact S.prior_isWarp k i

theorem rows_initialSet
    (S : FiniteHistoryState G kappa huncountable hsingular) (j) (i) :
    G.initialSet ((S.rows.get j) i) = G.source := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · change G.initialSet (S.current i) = G.source
    exact S.current_initialSet i
  · change G.initialSet ((S.prior.get k) i) = G.source
    exact S.prior_initialSet k i

/-- Close one current source row under the complete finite history. -/
def nextSources
    (S : FiniteHistoryState G kappa huncountable hsingular)
    (fixed : Set G.DPath) (i : Index kappa) : Set V :=
  S.sources i ∪
    G.competitorClosure (fixed ∪ listFamily S.rows) (S.sources i)

/-- Every source produced by the finite closing step is still an ambient
source, provided the fixed family and every historical row start there. -/
theorem nextSources_subset
    (S : FiniteHistoryState G kappa huncountable hsingular)
    {fixed : Set G.DPath}
    (hfixedInitial : G.initialSet fixed ⊆ G.source) (i : Index kappa) :
    S.nextSources fixed i ⊆ G.source := by
  rintro b (hb | ⟨_a, _ha, _p, _hp, _hpa, q, hq, hqb, _hpq⟩)
  · exact S.sources_subset i hb
  · rw [← hqb]
    rcases hq with hq | hq
    · exact hfixedInitial ⟨q, hq, rfl⟩
    · obtain ⟨j, hq⟩ := Set.mem_iUnion.1 hq
      obtain ⟨c, hq⟩ := Set.mem_iUnion.1 hq
      rw [← S.rows_initialSet j c]
      exact ⟨q, hq, rfl⟩

/-- A finite number of historical rows over all singular columns still
has index cardinality bounded by every scale. -/
theorem mk_historyIndex_le
    (S : FiniteHistoryState G kappa huncountable hsingular)
    (i : Index kappa) :
    #(Fin S.rows.length × Index kappa) ≤
      scale kappa huncountable hsingular i := by
  rw [Cardinal.mk_prod]
  apply Cardinal.mul_le_of_le (scale_infinite kappa huncountable hsingular i)
  · rw [Cardinal.lift_mk_fin]
    exact (Cardinal.natCast_lt_aleph0 :
      (S.rows.length : Cardinal) < aleph0).le.trans
      (scale_infinite kappa huncountable hsingular i)
  · simpa only [Cardinal.lift_uzero] using
      scale_index_le kappa huncountable hsingular i

/-- The finite closing step preserves the exact cardinal of each singular
scale. -/
theorem mk_nextSources_eq
    (S : FiniteHistoryState G kappa huncountable hsingular)
    {fixed : Set G.DPath} (hfixed : G.IsWarp fixed)
    (i : Index kappa) :
    #(S.nextSources fixed i) = scale kappa huncountable hsingular i := by
  let W : Fin S.rows.length × Index kappa → Set G.DPath :=
    indexedListFamily S.rows
  have hW : ∀ z, G.IsWarp (W z) := fun z ↦ S.rows_isWarp z.1 z.2
  have hclosure :
      #(G.competitorClosure (fixed ∪ listFamily S.rows) (S.sources i)) ≤
        scale kappa huncountable hsingular i := by
    rw [← iUnion_indexedListFamily S.rows]
    apply G.mk_competitorClosure_fixed_iUnion_le fixed W (S.sources i)
    · exact hfixed
    · exact hW
    · exact scale_infinite kappa huncountable hsingular i
    · exact S.mk_historyIndex_le i
    · rw [S.sources_card i]
  apply le_antisymm
  · apply (Cardinal.mk_union_le _ _).trans
    exact Cardinal.add_le_of_le
      (scale_infinite kappa huncountable hsingular i)
      (S.sources_card i).le hclosure
  · rw [← S.sources_card i]
    exact Cardinal.mk_subtype_mono Set.subset_union_left

end FiniteHistoryState

/-- A genuine successor of a finite-history state: its sources are the
finite-history closure, and its prior list is exactly the old complete row
list. -/
structure FiniteHistoryExtension
    {G : DWeb V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    (fixed : Set G.DPath)
    (S T : FiniteHistoryState G kappa huncountable hsingular) : Prop where
  sources_eq : T.sources = S.nextSources fixed
  prior_eq : T.prior = S.rows

/-- Lower induction chooses the next bounded row after the complete finite
history has been absorbed into the source sets. -/
theorem exists_finiteHistoryExtension
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {fixed : Set G.DPath} {D : Set V}
    (hD : D ⊆ G.source)
    (hfixed : IsLinkageBetween G D G.target fixed)
    (S : FiniteHistoryState G kappa huncountable hsingular) :
    ∃ T, FiniteHistoryExtension fixed S T := by
  let next : Index kappa → Set V := S.nextSources fixed
  have hnextSubset : ∀ i, next i ⊆ G.source := by
    intro i
    apply S.nextSources_subset
    rw [hfixed.initialSet_eq]
    exact hD
  have hnextCard : ∀ i,
      #(next i) = scale kappa huncountable hsingular i := by
    intro i
    exact S.mk_nextSources_eq hfixed.isWarp i
  have hex : ∀ i : Index kappa, ∃ W : Set G.DPath,
      G.IsWarp W ∧ G.HasFiniteCharacter W ∧
        G.initialSet W = G.source ∧ LinksToTarget G W (next i) := by
    intro i
    apply exists_provisionalTargetRow_of_lower hlower G hG hNorm
    · exact hnextSubset i
    · rw [hnextCard i]
      exact scale_below kappa huncountable hsingular i
  let W : Index kappa → Set G.DPath :=
    fun i ↦ Classical.choose (hex i)
  have hW : ∀ i,
      G.IsWarp (W i) ∧ G.HasFiniteCharacter (W i) ∧
        G.initialSet (W i) = G.source ∧ LinksToTarget G (W i) (next i) :=
    fun i ↦ Classical.choose_spec (hex i)
  let T : FiniteHistoryState G kappa huncountable hsingular :=
    { sources := next
      sources_subset := hnextSubset
      sources_card := hnextCard
      current := W
      current_isWarp := fun i ↦ (hW i).1
      current_finiteCharacter := fun i ↦ (hW i).2.1
      current_initialSet := fun i ↦ (hW i).2.2.1
      current_links := fun i ↦ (hW i).2.2.2
      prior := S.rows
      prior_isWarp := fun j i ↦ S.rows_isWarp j i
      prior_initialSet := fun j i ↦ S.rows_initialSet j i }
  exact ⟨T, ⟨rfl, rfl⟩⟩

/-- The canonical singular layers have an initial finite-history state. -/
theorem exists_initialFiniteHistoryState
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa) :
    ∃ S : FiniteHistoryState G kappa huncountable hsingular,
      S.sources = sourceLayer A₀ kappa hcard huncountable hsingular := by
  let layer : Index kappa → Set V :=
    sourceLayer A₀ kappa hcard huncountable hsingular
  have hlayerSubset : ∀ i, layer i ⊆ G.source := by
    intro i
    exact (sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans
      hA₀
  have hlayerCard : ∀ i,
      #(layer i) = scale kappa huncountable hsingular i :=
    sourceLayer_card A₀ kappa hcard huncountable hsingular
  have hex : ∀ i : Index kappa, ∃ W : Set G.DPath,
      G.IsWarp W ∧ G.HasFiniteCharacter W ∧
        G.initialSet W = G.source ∧ LinksToTarget G W (layer i) := by
    intro i
    apply exists_provisionalTargetRow_of_lower hlower G hG hNorm
    · exact hlayerSubset i
    · rw [hlayerCard i]
      exact scale_below kappa huncountable hsingular i
  let W : Index kappa → Set G.DPath :=
    fun i ↦ Classical.choose (hex i)
  have hW : ∀ i,
      G.IsWarp (W i) ∧ G.HasFiniteCharacter (W i) ∧
        G.initialSet (W i) = G.source ∧ LinksToTarget G (W i) (layer i) :=
    fun i ↦ Classical.choose_spec (hex i)
  let S : FiniteHistoryState G kappa huncountable hsingular :=
    { sources := layer
      sources_subset := hlayerSubset
      sources_card := hlayerCard
      current := W
      current_isWarp := fun i ↦ (hW i).1
      current_finiteCharacter := fun i ↦ (hW i).2.1
      current_initialSet := fun i ↦ (hW i).2.2.1
      current_links := fun i ↦ (hW i).2.2.2
      prior := []
      prior_isWarp := fun j ↦ Fin.elim0 j
      prior_initialSet := fun j ↦ Fin.elim0 j }
  exact ⟨S, rfl⟩

namespace FiniteHistoryConstruction

variable {kappa : Cardinal.{u}}
variable (hlower : UniversalCardinalInductionBelow V kappa)
variable (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
variable {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
variable {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
variable {fixed : Set G.DPath} {D : Set V}
variable (hD : D ⊆ G.source)
variable (hfixed : IsLinkageBetween G D G.target fixed)

/-- A chosen initial finite-history state. -/
noncomputable def initialState :
    FiniteHistoryState G kappa huncountable hsingular :=
  Classical.choose (exists_initialFiniteHistoryState
    hlower huncountable hsingular hG hNorm hA₀ hcard)

theorem initialState_sources :
    (initialState hlower huncountable hsingular hG hNorm hA₀ hcard).sources =
      sourceLayer A₀ kappa hcard huncountable hsingular :=
  Classical.choose_spec (exists_initialFiniteHistoryState
    hlower huncountable hsingular hG hNorm hA₀ hcard)

/-- A chosen genuine finite-history successor. -/
noncomputable def nextState
    (S : FiniteHistoryState G kappa huncountable hsingular) :
    FiniteHistoryState G kappa huncountable hsingular :=
  Classical.choose (exists_finiteHistoryExtension
    hlower huncountable hsingular hG hNorm hD hfixed S)

theorem nextState_spec
    (S : FiniteHistoryState G kappa huncountable hsingular) :
    FiniteHistoryExtension fixed S
      (nextState hlower huncountable hsingular hG hNorm hD hfixed S) :=
  Classical.choose_spec (exists_finiteHistoryExtension
    hlower huncountable hsingular hG hNorm hD hfixed S)

/-- The recursively accumulated finite histories. -/
noncomputable def stateAt :
    ℕ → FiniteHistoryState G kappa huncountable hsingular
  | 0 => initialState hlower huncountable hsingular hG hNorm hA₀ hcard
  | n + 1 => nextState hlower huncountable hsingular hG hNorm hD hfixed
      (stateAt n)

@[simp] theorem stateAt_zero :
    stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed 0 =
      initialState hlower huncountable hsingular hG hNorm hA₀ hcard := rfl

@[simp] theorem stateAt_succ (n : ℕ) :
    stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed (n + 1) =
      nextState hlower huncountable hsingular hG hNorm hD hfixed
        (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n) :=
  rfl

/-- The successor source family is definitionally the finite-history
closing step on the preceding state. -/
theorem stateAt_sources_succ (n : ℕ) :
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed
      (n + 1)).sources =
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).nextSources
      fixed := by
  rw [stateAt_succ]
  exact (nextState_spec hlower huncountable hsingular hG hNorm hD hfixed _).sources_eq

/-- The old complete history is retained in the successor's prior list. -/
theorem stateAt_prior_succ (n : ℕ) :
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed
      (n + 1)).prior =
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).rows := by
  rw [stateAt_succ]
  exact (nextState_spec hlower huncountable hsingular hG hNorm hD hfixed _).prior_eq

/-- The represented finite path history grows at every successor. -/
theorem listFamily_stateAt_subset_succ (n : ℕ) :
    listFamily
        (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).rows ⊆
      listFamily
        (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed
          (n + 1)).rows := by
  let S := stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n
  let T := stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed (n + 1)
  have hprior : T.prior = S.rows := by
    simpa only [S, T] using
      stateAt_prior_succ hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n
  have hsub := listFamily_subset_cons T.current S.rows
  change listFamily S.rows ⊆ listFamily T.rows
  simpa only [FiniteHistoryState.rows, hprior] using hsub

/-- The complete represented history is monotone in the stage number. -/
theorem listFamily_stateAt_mono :
    Monotone (fun n ↦ listFamily
      (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).rows) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans (listFamily_stateAt_subset_succ
        hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n)

/-- Every explicitly indexed historical row through stage `n` occurs in
the finite list represented by the state at `n`. -/
theorem historyThrough_stateAt_subset (n : ℕ) :
    historyThrough
        (fun i m ↦
          (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed m).current i)
        n ⊆
      listFamily
        (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).rows := by
  intro p hp
  obtain ⟨m, hp⟩ := Set.mem_iUnion.1 hp
  obtain ⟨hmn, hp⟩ := Set.mem_iUnion.1 hp
  obtain ⟨i, hp⟩ := Set.mem_iUnion.1 hp
  apply listFamily_stateAt_mono
      hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed hmn
  exact row_subset_listFamily_cons
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed m).current
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed m).prior
    i hp

/-- The recursively chosen source sets form an increasing sequence. -/
theorem sources_stateAt_mono (i : Index kappa) :
    Monotone (fun n ↦
      (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).sources i) := by
  have hstep : ∀ n,
      (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).sources i ⊆
        (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed
          (n + 1)).sources i := by
    intro n
    rw [stateAt_sources_succ
      hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n]
    exact Set.subset_union_left
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih => exact ih.trans (hstep n)

/-- Forget the finite-list implementation.  This is the abstract
finite-history source/row system used by `HistoricalRows.toTargetRows`. -/
noncomputable def toHistoricalRows :
    HistoricalRows G fixed A₀ kappa huncountable hsingular hcard where
  sources i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).sources i
  paths i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).current i
  seed i := by
    rw [stateAt_zero, initialState_sources
      hlower huncountable hsingular hG hNorm hA₀ hcard]
  sources_subset i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).sources_subset i
  sources_mono := sources_stateAt_mono
    hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed
  isWarp i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).current_isWarp i
  finiteCharacter i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).current_finiteCharacter i
  initialSet i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).current_initialSet i
  links i n :=
    (stateAt hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n).current_links i
  close i n := by
    intro b hb
    rw [stateAt_sources_succ
      hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n]
    apply Or.inr
    apply G.competitorClosure_mono_paths _ hb
    apply Set.union_subset_union Set.Subset.rfl
    exact historyThrough_stateAt_subset
      hlower huncountable hsingular hG hNorm hA₀ hcard hD hfixed n

end FiniteHistoryConstruction

/-- Unconditional multi-scale finite-history rows constructed from the
lower induction hypothesis.  Their source unions are globally competitor
closed by `HistoricalRows.limitSources_closed`; the construction makes no
false claim that independently selected same-column rows have a warp as
their union. -/
noncomputable def historicalRowsOfLower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    HistoricalRows G fixed A₀ kappa huncountable hsingular hcard :=
  FiniteHistoryConstruction.toHistoricalRows
    hlower huncountable hsingular hG hNorm hA₀ hcard
      (fun _ hx ↦ hx.1) hfixed

/-! ## Exact strength of same-column historical coherence -/

/-- There is a finite-history row system whose accumulated paths form a
warp in every column. -/
def HasCoherentHistoricalRows
    (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) : Prop :=
  ∃ R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard,
    ∀ i, G.IsWarp (columnPaths R.paths i)

/-- A full linkage gives a constant coherent historical system.  This
converse is independent of lower induction and shows that the remaining
same-column union-warp field is not cardinal bookkeeping. -/
theorem coherentHistoricalRowsOfLinkage
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed)
    {P : Set G.DPath} (hP : IsLinkageBetween G G.source G.target P) :
    HasCoherentHistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard := by
  let R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard :=
    { sources := fun _ _ ↦ G.source
      paths := fun _ _ ↦ P
      seed := fun i ↦
        (sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans hA₀
      sources_subset := fun _ _ ↦ Set.Subset.rfl
      sources_mono := fun _ _ _ _ ↦ Set.Subset.rfl
      isWarp := fun _ _ ↦ hP.isWarp
      finiteCharacter := fun _ _ ↦ hP.finiteCharacter
      initialSet := fun _ _ ↦ hP.initialSet_eq
      links := fun _ _ ↦ linksToTarget_of_linkageToTarget hP
      close := by
        intro i n b hb
        obtain ⟨_a, _ha, _p, _hp, _hpa, q, hq, hqb, _hpq⟩ := hb
        rw [← hqb]
        rcases hq with hq | hq
        · have : q.initial ∈ G.initialSet fixed := ⟨q, hq, rfl⟩
          rw [hfixed.initialSet_eq] at this
          exact this.1
        · obtain ⟨m, hq⟩ := Set.mem_iUnion.1 hq
          obtain ⟨hmn, hq⟩ := Set.mem_iUnion.1 hq
          obtain ⟨j, hq⟩ := Set.mem_iUnion.1 hq
          have : q.initial ∈ G.initialSet P := ⟨q, hq, rfl⟩
          rw [hP.initialSet_eq] at this
          exact this }
  refine ⟨R, ?_⟩
  intro i
  have heq : columnPaths R.paths i = P := by
    apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨n, hp⟩ := Set.mem_iUnion.1 hp
      exact hp
    · intro p hp
      exact Set.mem_iUnion.2 ⟨0, hp⟩
  rw [heq]
  exact hP.isWarp

/-- Coherent historical rows are exactly as strong as the missing
linkability conclusion (in the normalized singular setup).  Thus shifted
least-column closure fully repairs the source-set "+1" issue, while proving
the per-column historical union is a warp remains the graph theorem itself. -/
theorem hasCoherentHistoricalRows_iff_isLinkable
    {G : DWeb V} (hNorm : G.IsNormalized)
    {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    HasCoherentHistoricalRows G fixed A₀ kappa
        huncountable hsingular hcard ↔
      IsLinkable G := by
  constructor
  · rintro ⟨R, hcoherent⟩
    exact SingularExtension.isLinkable_of_targetRows
      (R.toTargetRows hNorm hcoherent) hA₀ hfixed
  · rintro ⟨P, hP⟩
    exact coherentHistoricalRowsOfLinkage hA₀ hfixed hP

#print axioms HistoricalRows.limitSources_closed
#print axioms HistoricalRows.paths_eq_of_columnUnion_isWarp
#print axioms HistoricalRows.toClosedRows
#print axioms HistoricalRows.toTargetRows
#print axioms historicalRowsOfLower
#print axioms hasCoherentHistoricalRows_iff_isLinkable

end SingularHistoricalClosure
end CardinalInduction
end Erdos599
