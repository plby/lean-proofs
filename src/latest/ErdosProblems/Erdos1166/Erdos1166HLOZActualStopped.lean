import ErdosProblems.Erdos1166.Erdos1166HLOZReconstruction
import ErdosProblems.Erdos1166.Erdos1166HLOZEventIdentity

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

namespace Erdos1166.HLOZActualStopped

open HLOZDecomposition
open HLOZReconstruction

noncomputable local instance lazyEndDecidable
    (s : ℕ → Site) (k : ℕ) : Decidable (IsLazyEnd s k) :=
  Classical.propDecidable _

theorem thickSiteCount_eq_card_sitesAtLeastLevel
    (s : ℕ → Site) (m n : ℕ) :
    thickSiteCount s m n = (sitesAtLeastLevel s n m).card := by
  rfl

theorem firstThickCountAfterStopping_eq_firstExactly
    (m k : ℕ) (τ : (ℕ → Site) → WithTop ℕ) :
    firstThickCountAfterStopping m k τ =
      firstExactlyKSitesReachLevelAfterStopping m k τ := by
  rfl

/-- The stopping time introduced by the decomposition file is definitionally
the same literal recursive `T_m^k` already used by the source-event API. -/
theorem favoriteCreationTime_eq_recursiveExactlyKSitesReachLevel
    (m k : ℕ) :
    favoriteCreationTime m k = recursiveExactlyKSitesReachLevel m k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [favoriteCreationTime, recursiveExactlyKSitesReachLevel, ih]
      rfl

/-- For the paper range `m ≥ 2`, the decomposition's `T_m^k` is the direct
first time at which `k` sites reach local-time level `m`. -/
theorem favoriteCreationTime_eq_firstKSitesReachLevel
    (s : ℕ → Site) (m k : ℕ) (hm : 2 ≤ m) :
    favoriteCreationTime m (k + 1) s =
      firstKSitesReachLevel m (k + 1) s := by
  rw [favoriteCreationTime_eq_recursiveExactlyKSitesReachLevel,
    recursiveExactlyKSitesReachLevel_eq s m k hm,
    firstExactlyKSitesReachLevel_eq s m (k + 1) (by omega)]

noncomputable def completedPairBlockIndices
    (ω : ℕ → Direction) (N q : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun r ↦
    incrementPair r ω = distinguishedIncrementPair ∧
      2 * (terminalPairLabelsThrough ω r).length = q

theorem stoppedExcursionEnds_even_eq_pairBlock_image
    (ω : ℕ → Direction) (N q : ℕ) :
    stoppedExcursionEnds (simpleRandomWalk ω) (2 * N) q =
      (completedPairBlockIndices ω N q).image (fun r ↦ 2 * r + 2) := by
  classical
  ext k
  rw [mem_stoppedExcursionEnds_iff, Finset.mem_image]
  constructor
  · rintro ⟨hk2, hkN, hkLazy, hkClock⟩
    rcases hkLazy.2.1 with ⟨a, ha⟩
    have ha1 : 1 ≤ a := by omega
    refine ⟨a - 1, ?_, by omega⟩
    unfold completedPairBlockIndices
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · apply (isLazyEnd_simpleRandomWalk_pair_iff ω (a - 1)).mp
      convert hkLazy using 1 <;> omega
    · have hc := paperExternalClock_even_eq_external_length ω (a - 1)
      rw [show 2 * (a - 1) = k - 2 by omega, hkClock] at hc
      simpa using hc.symm
  · rintro ⟨r, hr, rfl⟩
    unfold completedPairBlockIndices at hr
    rw [Finset.mem_filter] at hr
    refine ⟨by omega, by have := Finset.mem_range.mp hr.1; omega, ?_, ?_⟩
    · exact (isLazyEnd_simpleRandomWalk_pair_iff ω r).mpr hr.2.1
    · rw [show 2 * r + 2 - 2 = 2 * r by omega,
        paperExternalClock_even_eq_external_length]
      simpa using hr.2.2

theorem stoppedExcursionBlock_even_eq_pairBlock_card
    (ω : ℕ → Direction) (N q : ℕ) :
    stoppedExcursionBlock (simpleRandomWalk ω) (2 * N) q =
      (completedPairBlockIndices ω N q).card := by
  unfold stoppedExcursionBlock
  rw [stoppedExcursionEnds_even_eq_pairBlock_image]
  exact Finset.card_image_of_injective _ (by
    intro a b h
    change 2 * a + 2 = 2 * b + 2 at h
    omega)

theorem stoppedExcursionEnds_odd_eq_even
    (s : ℕ → Site) (N q : ℕ) :
    stoppedExcursionEnds s (2 * N + 1) q =
      stoppedExcursionEnds s (2 * N) q := by
  ext k
  simp only [mem_stoppedExcursionEnds_iff]
  constructor
  · rintro ⟨hk2, hkN, hkLazy, hkClock⟩
    refine ⟨hk2, ?_, hkLazy, hkClock⟩
    rcases hkLazy.2.1 with ⟨a, ha⟩
    omega
  · rintro ⟨hk2, hkN, hkLazy, hkClock⟩
    exact ⟨hk2, by omega, hkLazy, hkClock⟩

theorem stoppedExcursionBlock_odd_eq_even
    (s : ℕ → Site) (N q : ℕ) :
    stoppedExcursionBlock s (2 * N + 1) q =
      stoppedExcursionBlock s (2 * N) q := by
  unfold stoppedExcursionBlock
  rw [stoppedExcursionEnds_odd_eq_even]

theorem stoppedExcursionBlock_odd_eq_pairBlock_card
    (ω : ℕ → Direction) (N q : ℕ) :
    stoppedExcursionBlock (simpleRandomWalk ω) (2 * N + 1) q =
      (completedPairBlockIndices ω N q).card := by
  rw [stoppedExcursionBlock_odd_eq_even,
    stoppedExcursionBlock_even_eq_pairBlock_card]

/-- The actual finite vector of stopped holding coordinates carried by the
first `N` complete increment pairs.  Its extra final coordinate is the
unfinished current external-clock block; no synthetic terminal label is
introduced for it. -/
noncomputable def stoppedPairRunVector (ω : ℕ → Direction) (N : ℕ) :
    Fin ((terminalPairLabelsThrough ω N).length + 1) → ℕ :=
  fun i ↦ (completedPairBlockIndices ω N (2 * i.val)).card

theorem stoppedExcursionBlock_even_eq_stoppedPairRunVector
    (ω : ℕ → Direction) (N : ℕ)
    (i : Fin ((terminalPairLabelsThrough ω N).length + 1)) :
    stoppedExcursionBlock (simpleRandomWalk ω) (2 * N) (2 * i.val) =
      stoppedPairRunVector ω N i := by
  exact stoppedExcursionBlock_even_eq_pairBlock_card ω N (2 * i.val)

theorem stoppedExcursionBlock_odd_eq_stoppedPairRunVector
    (ω : ℕ → Direction) (N : ℕ)
    (i : Fin ((terminalPairLabelsThrough ω N).length + 1)) :
    stoppedExcursionBlock (simpleRandomWalk ω) (2 * N + 1) (2 * i.val) =
      stoppedPairRunVector ω N i := by
  exact stoppedExcursionBlock_odd_eq_pairBlock_card ω N (2 * i.val)

theorem current_not_mem_completedLazyRemovedTimes_of_partial
    (s : ℕ → Site) (n : ℕ) (hpartial : IsLazyEnd s (n + 1)) :
    n ∉ completedLazyRemovedTimes s n := by
  intro hn
  unfold completedLazyRemovedTimes at hn
  rw [Finset.mem_biUnion] at hn
  rcases hn with ⟨k, hk, hnk⟩
  have hkIcc := (Finset.mem_filter.mp hk).1
  have hkLazy := (Finset.mem_filter.mp hk).2
  have hkLe : k ≤ n := (Finset.mem_Icc.mp hkIcc).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnk
  rcases hpartial.2.1 with ⟨a, ha⟩
  rcases hkLazy.2.1 with ⟨b, hb⟩
  rcases hnk with hnk | hnk <;> omega

/-- Exact one-step correction missing from the completed lazy local time.
This is the deterministic terminal indicator in HLOZ (4.7). -/
theorem paperLazyLocalTime_eq_completed_add_terminalIndicator
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    paperLazyLocalTime s n x = completedLazyLocalTime s n x +
      if IsLazyEnd s (n + 1) ∧ s n = x then 1 else 0 := by
  classical
  by_cases hpartial : IsLazyEnd s (n + 1)
  · unfold paperLazyLocalTime completedLazyLocalTime lazyRemovedTimes
      partialLazyRemovedTimes
    rw [if_pos hpartial, Finset.filter_union]
    by_cases hx : s n = x
    · have hn : n ∉
          (completedLazyRemovedTimes s n).filter (fun j ↦ s j = x) := by
        intro hn
        exact current_not_mem_completedLazyRemovedTimes_of_partial s n hpartial
          (Finset.mem_filter.mp hn).1
      simp only [hpartial, hx, and_self, if_true]
      have hfilter : {j ∈ ({n} : Finset ℕ) | s j = x} = {n} := by
        simp [hx]
      rw [hfilter]
      simpa [Finset.union_comm] using Finset.card_insert_of_notMem hn
    · simp only [hpartial, hx, and_false, if_false]
      have hfilter : {j ∈ ({n} : Finset ℕ) | s j = x} = ∅ := by
        simp [hx]
      rw [hfilter, Finset.union_empty, Nat.add_zero]
  · unfold paperLazyLocalTime completedLazyLocalTime lazyRemovedTimes
      partialLazyRemovedTimes
    simp [hpartial]

/-! ### Exact finite-prefix partition at the stopping time -/

theorem firstKSitesReachLevel_congr_prefix_of_eq
    {s t : ℕ → Site} {m k n : ℕ}
    (hst : ∀ j, j ≤ n → s j = t j)
    (hs : firstKSitesReachLevel m k s = n) :
    firstKSitesReachLevel m k t = n := by
  let u : ℕ → (ℕ → Site) → ℕ :=
    fun j z ↦ (sitesAtLeastLevel z j m).card
  have hu (j : ℕ) (hj : j ≤ n) : u j s = u j t := by
    exact thickSiteCount_congr_prefix
      (s := s) (t := t) (m := m) (n := j)
        (fun r hr ↦ hst r (hr.trans hj))
  have hsne : firstKSitesReachLevel m k s ≠ ⊤ := by simp [hs]
  have hsmem : u n s ∈ Set.Ici k := by
    have h := hittingAfter_mem_set_of_ne_top
      (u := u) (s := Set.Ici k) (n := 0) (ω := s) hsne
    have hsuntop : (firstKSitesReachLevel m k s).untopA = n := by
      rw [hs]
      rfl
    change u (firstKSitesReachLevel m k s).untopA s ∈ Set.Ici k at h
    rwa [hsuntop] at h
  have htmem : u n t ∈ Set.Ici k := by simpa [hu n le_rfl] using hsmem
  have htle : firstKSitesReachLevel m k t ≤ (n : WithTop ℕ) := by
    exact hittingAfter_le_of_mem (u := u) (s := Set.Ici k)
      (n := 0) (i := n) (ω := t) (Nat.zero_le n) htmem
  have htne : firstKSitesReachLevel m k t ≠ ⊤ := by
    intro ht
    rw [ht] at htle
    exact (not_le_of_gt (WithTop.coe_lt_top n)) htle
  have htge : (n : WithTop ℕ) ≤ firstKSitesReachLevel m k t := by
    by_contra hnot
    have htlt : firstKSitesReachLevel m k t < (n : WithTop ℕ) :=
      lt_of_not_ge hnot
    let j := (firstKSitesReachLevel m k t).untopA
    have hjcoe : (j : WithTop ℕ) = firstKSitesReachLevel m k t := by
      dsimp only [j]
      rw [WithTop.untopA_eq_untop htne]
      exact WithTop.coe_untop _ htne
    have hjn : j < n := by
      exact WithTop.coe_lt_coe.mp (hjcoe.trans_lt htlt)
    have htjmem : u j t ∈ Set.Ici k := by
      have h := hittingAfter_mem_set_of_ne_top
        (u := u) (s := Set.Ici k) (n := 0) (ω := t) htne
      simpa [firstKSitesReachLevel, u, j] using h
    have hsjmem : u j s ∈ Set.Ici k := by
      simpa [hu j hjn.le] using htjmem
    have hnotmem : u j s ∉ Set.Ici k := by
      apply notMem_of_lt_hittingAfter
        (u := u) (s := Set.Ici k) (n := 0) (ω := s)
      · rw [show hittingAfter u (Set.Ici k) 0 s =
          firstKSitesReachLevel m k s by rfl, hs]
        exact WithTop.coe_lt_coe.mpr hjn
      · exact Nat.zero_le j
    exact hnotmem hsjmem
  exact le_antisymm htle htge

def extendPrefix {n : ℕ} (w : Prefix n) : ℕ → Direction :=
  fun j ↦ if h : j < n then w ⟨j, Finset.mem_range.mpr h⟩ else 0

@[simp] theorem restrict_extendPrefix {n : ℕ} (w : Prefix n) :
    (Finset.range n).restrict (extendPrefix w) = w := by
  funext i
  have hi : (i : ℕ) < n := Finset.mem_range.mp i.property
  simp [extendPrefix, hi]

theorem simpleRandomWalk_congr_extendPrefix {n : ℕ}
    (w : Prefix n) (ω : ℕ → Direction)
    (hω : (Finset.range n).restrict ω = w) :
    ∀ j, j ≤ n →
      simpleRandomWalk ω j = simpleRandomWalk (extendPrefix w) j := by
  intro j hj
  unfold simpleRandomWalk
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  have hrj := Finset.mem_range.mp hr
  have hrn : r < n := hrj.trans_le hj
  have hcoord := congrFun hω ⟨r, Finset.mem_range.mpr hrn⟩
  simpa [extendPrefix, hrn] using hcoord

def IsFirstKPrefix (m k : ℕ) {n : ℕ} (w : Prefix n) : Prop :=
  firstKSitesReachLevel m k (simpleRandomWalk (extendPrefix w)) = n

def prefixAtom {n : ℕ} (w : Prefix n) : Set (ℕ → Direction) :=
  (Finset.range n).restrict ⁻¹' {w}

theorem prefixAtom_prob {n : ℕ} (w : Prefix n) :
    incrementLaw (prefixAtom w) = (4 : ℝ≥0∞)⁻¹ ^ n := by
  unfold prefixAtom
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton w),
    increment_restrict_map, prefixLaw_singleton]

theorem prefixAtom_subset_firstKSitesReachLevel_fiber
    {m k n : ℕ} {w : Prefix n} (hw : IsFirstKPrefix m k w) :
    prefixAtom w ⊆
      {ω | firstKSitesReachLevel m k (simpleRandomWalk ω) = n} := by
  intro ω hω
  change (Finset.range n).restrict ω = w at hω
  apply firstKSitesReachLevel_congr_prefix_of_eq
    (s := simpleRandomWalk (extendPrefix w))
  · intro j hj
    exact (simpleRandomWalk_congr_extendPrefix w ω hω j hj).symm
  · exact hw

abbrev StoppedPrefix := Σ n : ℕ, Prefix n

def stoppedPrefixAtom (p : StoppedPrefix) : Set (ℕ → Direction) :=
  prefixAtom p.2

def IsFirstKStoppedPrefix (m k : ℕ) (p : StoppedPrefix) : Prop :=
  IsFirstKPrefix m k p.2

noncomputable local instance isFirstKStoppedPrefixDecidable
    (m k : ℕ) (p : StoppedPrefix) :
    Decidable (IsFirstKStoppedPrefix m k p) :=
  Classical.propDecidable _

theorem stoppedPrefixAtom_pairwiseDisjoint_on_firstK
    (m k : ℕ) :
    {p : StoppedPrefix | IsFirstKStoppedPrefix m k p}.PairwiseDisjoint
      stoppedPrefixAtom := by
  intro p hp q hq hpq
  change Disjoint (stoppedPrefixAtom p) (stoppedPrefixAtom q)
  rw [Set.disjoint_left]
  intro ω hωp hωq
  have hTp := prefixAtom_subset_firstKSitesReachLevel_fiber hp hωp
  have hTq := prefixAtom_subset_firstKSitesReachLevel_fiber hq hωq
  have hlen : p.1 = q.1 := by
    exact WithTop.coe_eq_coe.mp (hTp.symm.trans hTq)
  apply hpq
  cases p with
  | mk pn pw =>
      cases q with
      | mk qn qw =>
          dsimp only at hlen hωp hωq ⊢
          subst qn
          have hpw : pw = qw := by
            exact (Set.mem_singleton_iff.mp hωp).symm.trans
              (Set.mem_singleton_iff.mp hωq)
          subst qw
          rfl

theorem measurableSet_stoppedPrefixAtom (p : StoppedPrefix) :
    MeasurableSet (stoppedPrefixAtom p) := by
  unfold stoppedPrefixAtom prefixAtom
  exact (show Measurable (Finset.range p.1).restrict by fun_prop)
    (measurableSet_singleton p.2)

theorem stoppedPrefixAtom_prob (p : StoppedPrefix) :
    incrementLaw (stoppedPrefixAtom p) =
      (4 : ℝ≥0∞)⁻¹ ^ p.1 := by
  exact prefixAtom_prob p.2

noncomputable def finiteStoppedPrefixEvent (E : Finset StoppedPrefix) :
    Set (ℕ → Direction) :=
  ⋃ p ∈ E, stoppedPrefixAtom p

/-- Exact probability of a finite collection of genuine stopped prefixes.
Disjointness is proved from the actual threshold time, rather than assumed
as a prefix-code premise. -/
theorem finiteStoppedPrefixEvent_prob
    (m k : ℕ) (E : Finset StoppedPrefix)
    (hE : ∀ p ∈ E, IsFirstKStoppedPrefix m k p) :
    incrementLaw (finiteStoppedPrefixEvent E) =
      ∑ p ∈ E, (4 : ℝ≥0∞)⁻¹ ^ p.1 := by
  unfold finiteStoppedPrefixEvent
  have hd : (E : Set StoppedPrefix).PairwiseDisjoint stoppedPrefixAtom := by
    intro p hp q hq hpq
    exact stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k
      (hE p hp) (hE q hq) hpq
  have hm : ∀ p ∈ E, MeasurableSet (stoppedPrefixAtom p) := by
    intro p _
    exact measurableSet_stoppedPrefixAtom p
  rw [measure_biUnion_finset hd hm]
  apply Finset.sum_congr rfl
  intro p _
  exact stoppedPrefixAtom_prob p

/-- Literal conditional atom for the finite stopped-prefix partition.  This
is the measure-theoretic shell needed for Proposition 4.3: the only remaining
step is to identify the source conditioning fiber with a concrete finite `E`
and factor the displayed prefix weights by stopped holding blocks. -/
theorem stoppedPrefixAtom_conditional_on_finiteEvent
    (m k : ℕ) (E : Finset StoppedPrefix)
    (hE : ∀ p ∈ E, IsFirstKStoppedPrefix m k p)
    (p : StoppedPrefix) :
    incrementLaw (stoppedPrefixAtom p) /
        incrementLaw (finiteStoppedPrefixEvent E) =
      ((4 : ℝ≥0∞)⁻¹ ^ p.1) /
        ∑ q ∈ E, (4 : ℝ≥0∞)⁻¹ ^ q.1 := by
  rw [stoppedPrefixAtom_prob, finiteStoppedPrefixEvent_prob m k E hE]

/-! ### Reconstruction with the genuinely unfinished terminal run -/

def completedRunsFromVector {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) : List PairRun :=
  List.ofFn fun i : Fin q ↦ (v i.castSucc, labels i)

def stoppedPairList {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    List IncrementPair :=
  expandPairRuns (completedRunsFromVector labels v) ++
    List.replicate (v (Fin.last q)) distinguishedIncrementPair

def stoppedDirectionList {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    List Direction :=
  flattenPairs (stoppedPairList labels v)

def prefixOfDirectionList (ds : List Direction) : Prefix ds.length :=
  fun i ↦ ds.get ⟨i, Finset.mem_range.mp i.property⟩

def stoppedPrefixOfDirectionList (ds : List Direction) : StoppedPrefix :=
  ⟨ds.length, prefixOfDirectionList ds⟩

def reconstructedStoppedPrefix {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    StoppedPrefix :=
  stoppedPrefixOfDirectionList (stoppedDirectionList labels v)

def stoppedPrefixDirections (p : StoppedPrefix) : List Direction :=
  List.ofFn fun i : Fin p.1 ↦
    p.2 ⟨i, Finset.mem_range.mpr i.isLt⟩

@[simp] theorem stoppedPrefixDirections_stoppedPrefixOfDirectionList
    (ds : List Direction) :
    stoppedPrefixDirections (stoppedPrefixOfDirectionList ds) = ds := by
  unfold stoppedPrefixDirections stoppedPrefixOfDirectionList prefixOfDirectionList
  exact List.ofFn_get ds

theorem decodePairRunsAux_replicate_distinguished (a t : ℕ) :
    decodePairRunsAux a
      (List.replicate t distinguishedIncrementPair) = [] := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
      simp only [List.replicate_succ, decodePairRunsAux]
      exact ih (a + 1)

theorem decodePairRuns_expand_append_replicate
    (runs : List PairRun) (u : ℕ)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair) :
    decodePairRuns (expandPairRuns runs ++
      List.replicate u distinguishedIncrementPair) = runs := by
  induction runs with
  | nil =>
      exact decodePairRunsAux_replicate_distinguished 0 u
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      have hp : p ≠ distinguishedIncrementPair :=
        hnondist (t, p) (by simp)
      have hruns : ∀ run ∈ runs,
          run.2 ≠ distinguishedIncrementPair := by
        intro run hrun
        exact hnondist run (by simp [hrun])
      simp only [expandPairRuns, List.append_assoc, decodePairRuns]
      change decodePairRunsAux 0
          (List.replicate t distinguishedIncrementPair ++
            p :: (expandPairRuns runs ++
              List.replicate u distinguishedIncrementPair)) =
        (t, p) :: runs
      rw [decodePairRunsAux_replicate_cons 0 t p _ hp]
      simp only [Nat.zero_add]
      congr 1
      change decodePairRuns
        (expandPairRuns runs ++
          List.replicate u distinguishedIncrementPair) = runs
      exact ih hruns

theorem decodePairRuns_stoppedPairList {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair) :
    decodePairRuns (stoppedPairList labels v) =
      completedRunsFromVector labels v := by
  unfold stoppedPairList
  apply decodePairRuns_expand_append_replicate
  intro run hrun
  rw [completedRunsFromVector, List.mem_ofFn] at hrun
  rcases hrun with ⟨i, rfl⟩
  exact hnondist i

theorem reconstructedStoppedPrefix_injective {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair) :
    Function.Injective (reconstructedStoppedPrefix labels) := by
  intro v w hpref
  have hdirs := congrArg stoppedPrefixDirections hpref
  simp only [reconstructedStoppedPrefix,
    stoppedPrefixDirections_stoppedPrefixOfDirectionList] at hdirs
  have hpairs : stoppedPairList labels v = stoppedPairList labels w :=
    flattenPairs_injective hdirs
  have hruns : completedRunsFromVector labels v =
      completedRunsFromVector labels w := by
    have := congrArg decodePairRuns hpairs
    simpa [decodePairRuns_stoppedPairList labels v hnondist,
      decodePairRuns_stoppedPairList labels w hnondist] using this
  have hlast : v (Fin.last q) = w (Fin.last q) := by
    unfold stoppedPairList at hpairs
    rw [hruns] at hpairs
    have hrep := List.append_cancel_left hpairs
    simpa using congrArg List.length hrep
  funext i
  refine Fin.lastCases hlast (fun j ↦ ?_) i
  have hlist := List.ofFn_injective hruns
  exact congrArg Prod.fst (congrFun hlist j)

theorem expandPairRuns_length (runs : List PairRun) :
    (expandPairRuns runs).length =
      (runs.map fun run ↦ run.1 + 1).sum := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [expandPairRuns, List.length_append, List.length_replicate,
        List.length_cons, List.map_cons, List.sum_cons, ih]
      omega
theorem flattenPairs_length (pairs : List IncrementPair) :
    (flattenPairs pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
      change (pairDirections p ++ flattenPairs pairs).length =
        2 * (p :: pairs).length
      rw [List.length_append, ih]
      have hp : (pairDirections p).length = 2 := by
        simp [pairDirections]
      rw [hp, List.length_cons]
      omega

theorem stoppedDirectionList_length {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    (stoppedDirectionList labels v).length =
      2 * (q + ∑ i, v i) := by
  unfold stoppedDirectionList stoppedPairList
  rw [flattenPairs_length, List.length_append, List.length_replicate,
    expandPairRuns_length]
  simp only [completedRunsFromVector, List.map_ofFn, Function.comp_apply,
    List.sum_ofFn]
  rw [Finset.sum_add_distrib]
  have hone : (∑ _ : Fin q, (1 : ℕ)) = q := by simp
  rw [hone]
  rw [Fin.sum_univ_castSucc]
  omega

theorem reconstructedStoppedPrefix_prob {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    incrementLaw (stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) =
      ((16 : ℝ≥0∞)⁻¹) ^ q *
        ∏ i, ((16 : ℝ≥0∞)⁻¹) ^ v i := by
  rw [stoppedPrefixAtom_prob]
  change (4 : ℝ≥0∞)⁻¹ ^ (stoppedDirectionList labels v).length = _
  rw [stoppedDirectionList_length]
  rw [pow_mul]
  have hbase : (4 : ℝ≥0∞)⁻¹ ^ 2 = (16 : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by finiteness) (by finiteness)).mp
    norm_num
  rw [hbase]
  rw [pow_add, Finset.prod_pow_eq_pow_sum]

noncomputable def actualAdmissibleStoppedVectors {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) : Finset (Fin (q + 1) → ℕ) :=
  E.filter fun v ↦
    IsFirstKStoppedPrefix m k (reconstructedStoppedPrefix labels v)

noncomputable def actualStoppedVectorEvent {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) : Set (ℕ → Direction) :=
  ⋃ v ∈ actualAdmissibleStoppedVectors m k labels E,
    stoppedPrefixAtom (reconstructedStoppedPrefix labels v)

/-- A finite collection of reconstructed vectors is filtered by the actual
threshold test, and hence its exact probability is a sum of the stopped
prefix masses.  No disjointness or stopping bridge is a caller premise. -/
theorem actualStoppedVectorEvent_prob {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    incrementLaw (actualStoppedVectorEvent m k labels E) =
      ((16 : ℝ≥0∞)⁻¹) ^ q *
        ∑ v ∈ actualAdmissibleStoppedVectors m k labels E,
          ∏ i, ((16 : ℝ≥0∞)⁻¹) ^ v i := by
  unfold actualStoppedVectorEvent
  have hd : ((actualAdmissibleStoppedVectors m k labels E :
      Finset (Fin (q + 1) → ℕ)) : Set (Fin (q + 1) → ℕ)).PairwiseDisjoint
        (fun v ↦ stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) := by
    intro v hv w hw hvw
    have hvstop : IsFirstKStoppedPrefix m k
        (reconstructedStoppedPrefix labels v) := by
      have hv' : v ∈ actualAdmissibleStoppedVectors m k labels E := hv
      exact (Finset.mem_filter.mp hv').2
    have hwstop : IsFirstKStoppedPrefix m k
        (reconstructedStoppedPrefix labels w) := by
      have hw' : w ∈ actualAdmissibleStoppedVectors m k labels E := hw
      exact (Finset.mem_filter.mp hw').2
    apply stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k hvstop hwstop
    exact fun hp ↦ hvw (reconstructedStoppedPrefix_injective labels hnondist hp)
  have hm : ∀ v ∈ actualAdmissibleStoppedVectors m k labels E,
      MeasurableSet
        (stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) := by
    intro v _
    exact measurableSet_stoppedPrefixAtom _
  rw [measure_biUnion_finset hd hm]
  calc
    ∑ v ∈ actualAdmissibleStoppedVectors m k labels E,
        incrementLaw
          (stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) =
        ∑ v ∈ actualAdmissibleStoppedVectors m k labels E,
          ((16 : ℝ≥0∞)⁻¹) ^ q *
            ∏ i, ((16 : ℝ≥0∞)⁻¹) ^ v i := by
      apply Finset.sum_congr rfl
      intro v _
      exact reconstructedStoppedPrefix_prob labels v
    _ = ((16 : ℝ≥0∞)⁻¹) ^ q *
        ∑ v ∈ actualAdmissibleStoppedVectors m k labels E,
          ∏ i, ((16 : ℝ≥0∞)⁻¹) ^ v i := by
      rw [Finset.mul_sum]

/-- Exact conditional atom law for the genuinely unfinished, actual-stopping
reconstruction.  The displayed Bernoulli weights differ from geometric
weights only by one constant per coordinate, which cancels after conditioning.
The remaining source-specific task is precisely to show that (4.7)--(4.8)
describe `actualAdmissibleStoppedVectors` for the fixed external path. -/
theorem reconstructedStoppedPrefix_conditional_on_actualEvent {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ)
    (_hv : v ∈ actualAdmissibleStoppedVectors m k labels E) :
    incrementLaw
        (stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) /
      incrementLaw (actualStoppedVectorEvent m k labels E) =
        (∏ i, ((16 : ℝ≥0∞)⁻¹) ^ v i) /
          ∑ w ∈ actualAdmissibleStoppedVectors m k labels E,
            ∏ i, ((16 : ℝ≥0∞)⁻¹) ^ w i := by
  rw [reconstructedStoppedPrefix_prob,
    actualStoppedVectorEvent_prob m k labels hnondist E]
  apply ENNReal.mul_div_mul_left
  · exact pow_ne_zero _ (by norm_num)
  · exact ENNReal.pow_ne_top (by norm_num)

noncomputable def stoppedBernoulliWeight {q : ℕ}
    (v : Fin (q + 1) → ℕ) : ℝ≥0∞ :=
  ∏ i, ((16 : ℝ≥0∞)⁻¹) ^ v i

noncomputable def stoppedGeometricWeight {q : ℕ}
    (v : Fin (q + 1) → ℕ) : ℝ≥0∞ :=
  ∏ i, ((15 : ℝ≥0∞) / 16) * ((16 : ℝ≥0∞)⁻¹) ^ v i

theorem stoppedGeometricWeight_eq_constant_mul_bernoulli {q : ℕ}
    (v : Fin (q + 1) → ℕ) :
    stoppedGeometricWeight v =
      ((15 : ℝ≥0∞) / 16) ^ (q + 1) * stoppedBernoulliWeight v := by
  unfold stoppedGeometricWeight stoppedBernoulliWeight
  rw [Finset.prod_mul_distrib]
  simp

theorem stoppedBernoulli_ratio_eq_geometric_ratio {q : ℕ}
    (A : Finset (Fin (q + 1) → ℕ)) (v : Fin (q + 1) → ℕ) :
    stoppedBernoulliWeight v / ∑ w ∈ A, stoppedBernoulliWeight w =
      stoppedGeometricWeight v / ∑ w ∈ A, stoppedGeometricWeight w := by
  rw [stoppedGeometricWeight_eq_constant_mul_bernoulli]
  simp_rw [stoppedGeometricWeight_eq_constant_mul_bernoulli]
  rw [← Finset.mul_sum]
  symm
  apply ENNReal.mul_div_mul_left
  · exact pow_ne_zero _ (by norm_num)
  · exact ENNReal.pow_ne_top (by finiteness)

/-- The actual stopped-prefix conditional atom in the literal geometric
mass used in HLOZ Proposition 4.3.  The final run remains unfinished in the
reconstruction; its missing success factor is common to all atoms and has
been cancelled by `stoppedBernoulli_ratio_eq_geometric_ratio`. -/
theorem reconstructedStoppedPrefix_conditional_geometric {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ)
    (hv : v ∈ actualAdmissibleStoppedVectors m k labels E) :
    incrementLaw
        (stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) /
      incrementLaw (actualStoppedVectorEvent m k labels E) =
        stoppedGeometricWeight v /
          ∑ w ∈ actualAdmissibleStoppedVectors m k labels E,
            stoppedGeometricWeight w := by
  rw [reconstructedStoppedPrefix_conditional_on_actualEvent
    m k labels hnondist E v hv]
  exact stoppedBernoulli_ratio_eq_geometric_ratio _ v

/-! ### Odd stopping horizons and the observed terminal pair -/

def IsFirstKPrefixAt (m k T : ℕ) {n : ℕ} (w : Prefix n) : Prop :=
  firstKSitesReachLevel m k (simpleRandomWalk (extendPrefix w)) = T

noncomputable local instance isFirstKPrefixAtDecidable
    (m k T n : ℕ) (w : Prefix n) :
    Decidable (IsFirstKPrefixAt m k T w) :=
  Classical.propDecidable _

theorem prefixAtom_subset_firstKSitesReachLevel_fiber_at
    {m k T n : ℕ} {w : Prefix n} (hTn : T ≤ n)
    (hw : IsFirstKPrefixAt m k T w) :
    prefixAtom w ⊆
      {ω | firstKSitesReachLevel m k (simpleRandomWalk ω) = T} := by
  intro ω hω
  change (Finset.range n).restrict ω = w at hω
  apply firstKSitesReachLevel_congr_prefix_of_eq
    (s := simpleRandomWalk (extendPrefix w))
  · intro j hj
    exact (simpleRandomWalk_congr_extendPrefix w ω hω j
      (hj.trans hTn)).symm
  · exact hw

def reconstructedOddStoppedPrefix {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) : StoppedPrefix :=
  stoppedPrefixOfDirectionList
    (flattenPairs (stoppedPairList labels v ++ [terminal]))

theorem reconstructedOddStoppedPrefix_length {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    (reconstructedOddStoppedPrefix labels v terminal).1 =
      2 * (q + ∑ i, v i + 1) := by
  unfold reconstructedOddStoppedPrefix stoppedPrefixOfDirectionList
  change (flattenPairs (stoppedPairList labels v ++ [terminal])).length = _
  rw [flattenPairs_length, List.length_append]
  simp only [List.length_singleton]
  unfold stoppedPairList
  rw [List.length_append, List.length_replicate, expandPairRuns_length]
  simp only [completedRunsFromVector, List.map_ofFn, Function.comp_apply,
    List.sum_ofFn]
  rw [Finset.sum_add_distrib]
  have hone : (∑ _ : Fin q, (1 : ℕ)) = q := by simp
  rw [hone, Fin.sum_univ_castSucc]
  omega

theorem reconstructedOddStoppedPrefix_threshold_odd {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    Odd ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) := by
  rw [reconstructedOddStoppedPrefix_length]
  use q + ∑ i, v i
  omega

theorem reconstructedOddStoppedPrefix_injective {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) :
    Function.Injective
      (fun v ↦ reconstructedOddStoppedPrefix labels v terminal) := by
  intro v w hpref
  have hdirs := congrArg stoppedPrefixDirections hpref
  simp only [reconstructedOddStoppedPrefix,
    stoppedPrefixDirections_stoppedPrefixOfDirectionList] at hdirs
  have hpairs : stoppedPairList labels v ++ [terminal] =
      stoppedPairList labels w ++ [terminal] :=
    flattenPairs_injective hdirs
  have hstopped : stoppedPairList labels v = stoppedPairList labels w :=
    (List.append_left_inj [terminal]).mp hpairs
  apply reconstructedStoppedPrefix_injective labels hnondist
  unfold reconstructedStoppedPrefix stoppedDirectionList
  rw [hstopped]

theorem reconstructedOddStoppedPrefix_prob {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    incrementLaw
        (stoppedPrefixAtom
          (reconstructedOddStoppedPrefix labels v terminal)) =
      ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) * stoppedBernoulliWeight v := by
  rw [stoppedPrefixAtom_prob]
  change (4 : ℝ≥0∞)⁻¹ ^
      (reconstructedOddStoppedPrefix labels v terminal).1 = _
  rw [reconstructedOddStoppedPrefix_length, pow_mul]
  have hbase : (4 : ℝ≥0∞)⁻¹ ^ 2 = (16 : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by finiteness) (by finiteness)).mp
    norm_num
  rw [hbase, pow_add, pow_add]
  unfold stoppedBernoulliWeight
  rw [Finset.prod_pow_eq_pow_sum]
  ring

noncomputable def actualAdmissibleOddStoppedVectors {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    Finset (Fin (q + 1) → ℕ) :=
  E.filter fun v ↦
    IsFirstKPrefixAt m k
      ((reconstructedOddStoppedPrefix labels v terminal).1 - 1)
      (reconstructedOddStoppedPrefix labels v terminal).2

noncomputable def actualOddStoppedVectorEvent {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    Set (ℕ → Direction) :=
  ⋃ v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E,
    stoppedPrefixAtom (reconstructedOddStoppedPrefix labels v terminal)

theorem actualOddStoppedVectorEvent_prob {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    incrementLaw (actualOddStoppedVectorEvent m k labels terminal E) =
      ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) *
        ∑ v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E,
          stoppedBernoulliWeight v := by
  unfold actualOddStoppedVectorEvent
  have hd : ((actualAdmissibleOddStoppedVectors m k labels terminal E :
      Finset (Fin (q + 1) → ℕ)) : Set (Fin (q + 1) → ℕ)).PairwiseDisjoint
        (fun v ↦ stoppedPrefixAtom
          (reconstructedOddStoppedPrefix labels v terminal)) := by
    intro v hv w hw hvw
    change Disjoint
      (stoppedPrefixAtom (reconstructedOddStoppedPrefix labels v terminal))
      (stoppedPrefixAtom (reconstructedOddStoppedPrefix labels w terminal))
    rw [Set.disjoint_left]
    intro ω hωv hωw
    have hv' : v ∈ actualAdmissibleOddStoppedVectors
        m k labels terminal E := hv
    have hw' : w ∈ actualAdmissibleOddStoppedVectors
        m k labels terminal E := hw
    have hvstop := (Finset.mem_filter.mp hv').2
    have hwstop := (Finset.mem_filter.mp hw').2
    have hTv := prefixAtom_subset_firstKSitesReachLevel_fiber_at
      (T := (reconstructedOddStoppedPrefix labels v terminal).1 - 1)
      (n := (reconstructedOddStoppedPrefix labels v terminal).1)
      (by omega) hvstop hωv
    have hTw := prefixAtom_subset_firstKSitesReachLevel_fiber_at
      (T := (reconstructedOddStoppedPrefix labels w terminal).1 - 1)
      (n := (reconstructedOddStoppedPrefix labels w terminal).1)
      (by omega) hwstop hωw
    have hT : (reconstructedOddStoppedPrefix labels v terminal).1 - 1 =
        (reconstructedOddStoppedPrefix labels w terminal).1 - 1 := by
      exact WithTop.coe_eq_coe.mp (hTv.symm.trans hTw)
    have hlen : (reconstructedOddStoppedPrefix labels v terminal).1 =
        (reconstructedOddStoppedPrefix labels w terminal).1 := by
      rw [reconstructedOddStoppedPrefix_length,
        reconstructedOddStoppedPrefix_length] at hT ⊢
      omega
    apply hvw
    apply reconstructedOddStoppedPrefix_injective labels hnondist terminal
    cases pv : reconstructedOddStoppedPrefix labels v terminal with
    | mk nv wv =>
      cases pw : reconstructedOddStoppedPrefix labels w terminal with
      | mk nw ww =>
        simp only [pv, pw] at hlen hωv hωw ⊢
        subst nw
        have hww : wv = ww := by
          exact (Set.mem_singleton_iff.mp hωv).symm.trans
            (Set.mem_singleton_iff.mp hωw)
        subst ww
        rfl
  have hm : ∀ v ∈ actualAdmissibleOddStoppedVectors
      m k labels terminal E,
      MeasurableSet
        (stoppedPrefixAtom
          (reconstructedOddStoppedPrefix labels v terminal)) := by
    intro v _
    exact measurableSet_stoppedPrefixAtom _
  rw [measure_biUnion_finset hd hm]
  calc
    ∑ v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E,
        incrementLaw
          (stoppedPrefixAtom
            (reconstructedOddStoppedPrefix labels v terminal)) =
        ∑ v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E,
          ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) * stoppedBernoulliWeight v := by
      apply Finset.sum_congr rfl
      intro v _
      exact reconstructedOddStoppedPrefix_prob labels v terminal
    _ = ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) *
        ∑ v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E,
          stoppedBernoulliWeight v := by
      rw [Finset.mul_sum]

/-- Odd-horizon analogue of the stopped geometric law.  The atom observes
the complete pair through `T+1` but tests `T_m^k=T`; taking `terminal` to be
the distinguished pair is exactly the terminal partial-pair case, while a
non-distinguished `terminal` is the external half-pair case. -/
theorem reconstructedOddStoppedPrefix_conditional_geometric {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ)
    (_hv : v ∈ actualAdmissibleOddStoppedVectors
      m k labels terminal E) :
    incrementLaw
        (stoppedPrefixAtom
          (reconstructedOddStoppedPrefix labels v terminal)) /
      incrementLaw (actualOddStoppedVectorEvent m k labels terminal E) =
        stoppedGeometricWeight v /
          ∑ w ∈ actualAdmissibleOddStoppedVectors
              m k labels terminal E,
            stoppedGeometricWeight w := by
  rw [reconstructedOddStoppedPrefix_prob,
    actualOddStoppedVectorEvent_prob m k labels hnondist terminal E]
  rw [ENNReal.mul_div_mul_left _ _
    (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))]
  exact stoppedBernoulli_ratio_eq_geometric_ratio _ v


end Erdos1166.HLOZActualStopped
