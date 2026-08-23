import ErdosProblems.Erdos1166.Erdos1166Core

namespace Erdos1166.HLOZDecomposition

open Filter MeasureTheory
open HLOZFoundation

/-! The unprimed lazy/external decomposition from HLOZ (2.12)--(2.14),
together with the stopped excursion blocks used in Propositions 4.2 and 4.3. -/

/-- The direction `e₁=(1,0)` singled out in HLOZ (2.12). -/
def paperE1 : Site := (1, 0)

/-- `k ∈ ℒ` in HLOZ (2.12): at even time `k` the path has just
completed the two-step excursion `(x,x+e₁,x)`. -/
def IsLazyEnd (s : ℕ → Site) (k : ℕ) : Prop :=
  2 ≤ k ∧ Even k ∧ s (k - 2) = s (k - 1) - paperE1 ∧ s k = s (k - 2)

noncomputable local instance (s : ℕ → Site) (k : ℕ) : Decidable (IsLazyEnd s k) :=
  Classical.propDecidable _

/-- The completed elements of `ℒ` through the original time `n`. -/
noncomputable def lazyEndsThrough (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (IsLazyEnd s)

/-- Original-time indices removed by completed two-step lazy excursions. -/
noncomputable def completedLazyRemovedTimes (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  (lazyEndsThrough s n).biUnion fun k ↦ {k - 1, k}

/-- If `n+1 ∈ ℒ`, the one-step terminal path at time `n` is removed too. -/
noncomputable def partialLazyRemovedTimes (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  if IsLazyEnd s (n + 1) then {n} else ∅

/-- All indices removed from `S_[0,n]` in the unprimed HLOZ deletion. -/
noncomputable def lazyRemovedTimes (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  completedLazyRemovedTimes s n ∪ partialLazyRemovedTimes s n

/-- Original indices retained in the external (jump-chain) path. -/
noncomputable def retainedTimes (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) \ lazyRemovedTimes s n

/-- Completed lazy local time through `n`. Unlike the full lazy local time,
this uses no one-step lookahead. -/
noncomputable def completedLazyLocalTime (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((completedLazyRemovedTimes s n).filter fun j ↦ s j = x).card

/-- The full local/lazy contribution in HLOZ (2.14), including the possible
one-step terminal excursion. -/
noncomputable def paperLazyLocalTime (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((lazyRemovedTimes s n).filter fun j ↦ s j = x).card

/-- The external local time `\widetilde\xi(x,N_n)`, represented directly on
the original path by retaining precisely the undeleted indices. -/
noncomputable def paperExternalLocalTime (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((retainedTimes s n).filter fun j ↦ s j = x).card

/-- The HLOZ external clock `N_n` from (2.13). -/
noncomputable def paperExternalClock (s : ℕ → Site) (n : ℕ) : ℕ :=
  n - 2 * (lazyEndsThrough s n).card - if IsLazyEnd s (n + 1) then 1 else 0

theorem lazyRemovedTimes_subset_range (s : ℕ → Site) (n : ℕ) :
    lazyRemovedTimes s n ⊆ Finset.range (n + 1) := by
  intro j hj
  rw [lazyRemovedTimes, Finset.mem_union] at hj
  rcases hj with hj | hj
  · rcases Finset.mem_biUnion.mp hj with ⟨k, hk, hjk⟩
    have hkIcc := (Finset.mem_filter.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hkIcc).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjk
    simp only [Finset.mem_range]
    rcases hjk with rfl | rfl <;> omega
  · simp only [partialLazyRemovedTimes] at hj
    split at hj
    · simp only [Finset.mem_singleton] at hj
      subst j
      simp
    · simp at hj

/-- The exact deterministic identity (2.14), without any probability input. -/
theorem localTime_eq_paperExternal_add_paperLazy
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    localTime s n x = paperExternalLocalTime s n x + paperLazyLocalTime s n x := by
  let all := (Finset.range (n + 1)).filter fun j ↦ s j = x
  let lazy := (lazyRemovedTimes s n).filter fun j ↦ s j = x
  have hlazy : lazy ⊆ all := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨lazyRemovedTimes_subset_range s n hj.1, hj.2⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hlazy
  have hdiff : all \ lazy =
      (retainedTimes s n).filter fun j ↦ s j = x := by
    ext j
    simp only [all, lazy, retainedTimes, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_range, and_assoc]
    tauto
  simpa [localTime, paperExternalLocalTime, paperLazyLocalTime, all, lazy, hdiff]
    using hcard.symm

theorem paperLazyLocalTime_eq_completed_of_ne_current
    (s : ℕ → Site) (n : ℕ) (x : Site) (hx : x ≠ s n) :
    paperLazyLocalTime s n x = completedLazyLocalTime s n x := by
  unfold paperLazyLocalTime completedLazyLocalTime lazyRemovedTimes partialLazyRemovedTimes
  split_ifs with h
  · apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hj | rfl, hjx⟩
      · exact ⟨hj, hjx⟩
      · exact (hx hjx.symm).elim
    · rintro ⟨hj, hjx⟩
      exact ⟨Or.inl hj, hjx⟩
  · simp

/-- A function depends only on coordinates through time `n`. -/
def PrefixDependent {β : Type*} (n : ℕ) (f : (ℕ → Site) → β) : Prop :=
  ∀ (s t : ℕ → Site), (∀ j, j ≤ n → s j = t j) → f s = f t

/-- Any discrete finite-prefix statistic is measurable in the natural
filtration at the end of that prefix. -/
theorem measurable_of_prefix {β : Type*} [MeasurableSpace β]
    {n : ℕ} {f : (ℕ → Site) → β} (hf : PrefixDependent n f) :
    Measurable[canonicalFiltration n] f := by
  let restrict : (ℕ → Site) → (Set.Iic n → Site) := fun s j ↦ s j
  let extend : (Set.Iic n → Site) → (ℕ → Site) := fun p j ↦
    if hj : j ≤ n then p ⟨j, hj⟩ else (0, 0)
  let g : (Set.Iic n → Site) → β := fun p ↦ f (extend p)
  have hfactor : f = g ∘ restrict := by
    funext s
    change f s = f (extend (restrict s))
    apply hf s
    intro j hj
    simp [restrict, extend, hj]
  rw [hfactor]
  have hrestrict : Measurable[canonicalFiltration n] restrict := by
    exact @measurable_pi_lambda (ℕ → Site) (Set.Iic n) (fun _ ↦ Site)
      (canonicalFiltration n) (fun _ ↦ inferInstance) restrict fun j ↦
        adapted_coordinateProcess.measurable_le j.property
  exact (measurable_of_countable g).comp hrestrict

theorem isLazyEnd_congr {s t : ℕ → Site} {q k : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hkq : k ≤ q) :
    IsLazyEnd s k ↔ IsLazyEnd t k := by
  by_cases hk2 : 2 ≤ k
  · simp only [IsLazyEnd, hk2, true_and]
    rw [hst (k - 2) (by omega), hst (k - 1) (by omega), hst k hkq]
  · simp [IsLazyEnd, hk2]

theorem lazyEndsThrough_congr {s t : ℕ → Site} {q n : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hnq : n ≤ q) :
    lazyEndsThrough s n = lazyEndsThrough t n := by
  ext k
  simp only [lazyEndsThrough, Finset.mem_filter, Finset.mem_Icc, and_congr_right_iff]
  intro hk
  exact isLazyEnd_congr hst (hk.2.trans hnq)

theorem lazyRemovedTimes_congr {s t : ℕ → Site} {q n : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hnq : n + 1 ≤ q) :
    lazyRemovedTimes s n = lazyRemovedTimes t n := by
  unfold lazyRemovedTimes completedLazyRemovedTimes partialLazyRemovedTimes
  rw [lazyEndsThrough_congr hst (by omega)]
  have hi := isLazyEnd_congr hst hnq
  by_cases hs : IsLazyEnd s (n + 1)
  · have ht := hi.mp hs
    simp [hs, ht]
  · have ht : ¬ IsLazyEnd t (n + 1) := fun ht ↦ hs (hi.mpr ht)
    simp [hs, ht]

theorem completedLazyRemovedTimes_congr {s t : ℕ → Site} {q n : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hnq : n ≤ q) :
    completedLazyRemovedTimes s n = completedLazyRemovedTimes t n := by
  unfold completedLazyRemovedTimes
  rw [lazyEndsThrough_congr hst hnq]

theorem measurable_paperLazyLocalTime_lookahead (n : ℕ) (x : Site) :
    Measurable[canonicalFiltration (n + 1)] (fun s ↦ paperLazyLocalTime s n x) := by
  apply measurable_of_prefix
  unfold PrefixDependent
  intro s t hst
  unfold paperLazyLocalTime
  change ((lazyRemovedTimes s n).filter fun j ↦ s j = x).card =
    ((lazyRemovedTimes t n).filter fun j ↦ t j = x).card
  rw [lazyRemovedTimes_congr hst le_rfl]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hj
  rw [hst j (by
    exact (lazyRemovedTimes_subset_range t n hj |> Finset.mem_range.mp).le)]

theorem measurable_completedLazyLocalTime (n : ℕ) (x : Site) :
    Measurable[canonicalFiltration n] (fun s ↦ completedLazyLocalTime s n x) := by
  apply measurable_of_prefix
  unfold PrefixDependent
  intro s t hst
  unfold completedLazyLocalTime
  change ((completedLazyRemovedTimes s n).filter fun j ↦ s j = x).card =
    ((completedLazyRemovedTimes t n).filter fun j ↦ t j = x).card
  rw [completedLazyRemovedTimes_congr hst le_rfl]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hj
  rcases Finset.mem_biUnion.mp hj with ⟨k, hk, hjk⟩
  have hkn := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hjk
  rw [hst j (by rcases hjk with rfl | rfl <;> omega)]

theorem measurable_paperExternalLocalTime_lookahead (n : ℕ) (x : Site) :
    Measurable[canonicalFiltration (n + 1)] (fun s ↦ paperExternalLocalTime s n x) := by
  have hlocal : Measurable[canonicalFiltration (n + 1)] (fun s ↦ localTime s n x) :=
    (adapted_localTime x).measurable_le (by omega)
  have hlazy := measurable_paperLazyLocalTime_lookahead n x
  have heq : (fun s ↦ paperExternalLocalTime s n x) =
      fun s ↦ localTime s n x - paperLazyLocalTime s n x := by
    funext s
    have h := localTime_eq_paperExternal_add_paperLazy s n x
    omega
  rw [heq]
  exact hlocal.sub hlazy

theorem measurable_paperExternalClock_lookahead (n : ℕ) :
    Measurable[canonicalFiltration (n + 1)] (fun s ↦ paperExternalClock s n) := by
  apply measurable_of_prefix
  unfold PrefixDependent
  intro s t hst
  unfold paperExternalClock
  change (n - 2 * (lazyEndsThrough s n).card - if IsLazyEnd s (n + 1) then 1 else 0) =
    (n - 2 * (lazyEndsThrough t n).card - if IsLazyEnd t (n + 1) then 1 else 0)
  rw [lazyEndsThrough_congr hst (by omega)]
  have hi := isLazyEnd_congr hst le_rfl
  by_cases hs : IsLazyEnd s (n + 1)
  · have ht := hi.mp hs
    simp [hs, ht]
  · have ht : ¬ IsLazyEnd t (n + 1) := fun ht ↦ hs (hi.mpr ht)
    simp [hs, ht]

/-- The completed lazy excursions attached to the external-clock state `q`.
This is the pathwise version of the block counted by `h_q` in HLOZ (4.5).
It is deliberately a set rather than a finite set: on an arbitrary element of
the canonical path space a clock state can contain infinitely many loops (a
null phenomenon under the simple-random-walk law). -/
def excursionEndSet (s : ℕ → Site) (q : ℕ) : Set ℕ :=
  {k | IsLazyEnd s k ∧ paperExternalClock s (k - 2) = q}

/-- `h_q`, with value `⊤` on exceptional paths having infinitely many lazy
excursions in the same external-time block. -/
noncomputable def paperHoldingTime (s : ℕ → Site) (q : ℕ) : ℕ∞ :=
  (excursionEndSet s q).encard

/-- Completed lazy excursions, stopped at original time `T`, which belong to
the external-time block `q`. This is the deterministic content of `\hat h_q`
in the proof of Proposition 4.3. -/
noncomputable def stoppedExcursionEnds (s : ℕ → Site) (T q : ℕ) : Finset ℕ :=
  (lazyEndsThrough s T).filter fun k ↦ paperExternalClock s (k - 2) = q

noncomputable def stoppedExcursionBlock (s : ℕ → Site) (T q : ℕ) : ℕ :=
  (stoppedExcursionEnds s T q).card

theorem paperExternalClock_congr {s t : ℕ → Site} {q n : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hnq : n + 1 ≤ q) :
    paperExternalClock s n = paperExternalClock t n := by
  unfold paperExternalClock
  rw [lazyEndsThrough_congr hst (by omega)]
  have hi := isLazyEnd_congr hst hnq
  by_cases hs : IsLazyEnd s (n + 1)
  · have ht := hi.mp hs
    simp [hs, ht]
  · have ht : ¬ IsLazyEnd t (n + 1) := fun ht ↦ hs (hi.mpr ht)
    simp [hs, ht]

theorem stoppedExcursionBlock_congr {s t : ℕ → Site} {T q : ℕ}
    (hst : ∀ j, j ≤ T → s j = t j) :
    stoppedExcursionBlock s T q = stoppedExcursionBlock t T q := by
  unfold stoppedExcursionBlock stoppedExcursionEnds
  rw [lazyEndsThrough_congr hst le_rfl]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hk
  have hkIcc := (Finset.mem_filter.mp hk).1
  have hk2 := (Finset.mem_Icc.mp hkIcc).1
  have hkT := (Finset.mem_Icc.mp hkIcc).2
  rw [paperExternalClock_congr hst (by omega)]

theorem adapted_stoppedExcursionBlock (q : ℕ) :
    Adapted canonicalFiltration (fun T s ↦ stoppedExcursionBlock s T q) := by
  intro T
  apply measurable_of_prefix
  unfold PrefixDependent
  intro s t hst
  exact stoppedExcursionBlock_congr hst

/-- A stopped excursion block evaluated at any stopping time is measurable in
the stopping-time sigma algebra. -/
theorem measurable_stoppedExcursionBlockAt
    (q : ℕ) {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime canonicalFiltration τ) :
    Measurable[hτ.measurableSpace]
      (stoppedValue (fun T s ↦ stoppedExcursionBlock s T q) τ) := by
  exact MeasureTheory.measurable_stoppedValue
    (adapted_stoppedExcursionBlock q).stronglyAdapted.isStronglyProgressive_of_discrete hτ

theorem mem_stoppedExcursionEnds_iff {s : ℕ → Site} {T q k : ℕ} :
    k ∈ stoppedExcursionEnds s T q ↔
      2 ≤ k ∧ k ≤ T ∧ IsLazyEnd s k ∧ paperExternalClock s (k - 2) = q := by
  simp [stoppedExcursionEnds, lazyEndsThrough, and_assoc, and_left_comm]

/-- Exact set-theoretic relation between the unstopped block `h_q` and its
cutoff `\hat h_q`: retain precisely the excursion endpoints no later than
the stopping horizon. -/
theorem coe_stoppedExcursionEnds (s : ℕ → Site) (T q : ℕ) :
    (stoppedExcursionEnds s T q : Set ℕ) = excursionEndSet s q ∩ Set.Iic T := by
  ext k
  rw [Set.mem_inter_iff, Set.mem_Iic]
  simp only [Finset.mem_coe, mem_stoppedExcursionEnds_iff, excursionEndSet,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, hkT, hkL, hkClock⟩
    exact ⟨⟨hkL, hkClock⟩, hkT⟩
  · rintro ⟨⟨hkL, hkClock⟩, hkT⟩
    exact ⟨hkL.1, hkT, hkL, hkClock⟩

theorem stoppedExcursionBlock_eq_ncard (s : ℕ → Site) (T q : ℕ) :
    stoppedExcursionBlock s T q =
      (excursionEndSet s q ∩ Set.Iic T).ncard := by
  unfold stoppedExcursionBlock
  rw [← coe_stoppedExcursionEnds]
  exact (Set.ncard_coe_finset _).symm

/-! ### The exact stopping time `T_m^k` from HLOZ (2.7) -/

/-- Number of sites whose local time has reached `m` by time `n`. -/
noncomputable def thickSiteCount (s : ℕ → Site) (m n : ℕ) : ℕ :=
  ((visitedSites s n).filter fun x ↦ m ≤ localTime s n x).card

theorem localTime_congr_prefix {s t : ℕ → Site} {n : ℕ}
    (hst : ∀ j, j ≤ n → s j = t j) (x : Site) :
    localTime s n x = localTime t n x := by
  unfold localTime
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, hx⟩
    refine ⟨hj, ?_⟩
    rw [← hst j (by simp only [Finset.mem_range] at hj; omega)]
    exact hx
  · rintro ⟨hj, hx⟩
    refine ⟨hj, ?_⟩
    rw [hst j (by simp only [Finset.mem_range] at hj; omega)]
    exact hx

theorem visitedSites_congr_prefix {s t : ℕ → Site} {n : ℕ}
    (hst : ∀ j, j ≤ n → s j = t j) :
    visitedSites s n = visitedSites t n := by
  ext x
  simp only [visitedSites, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (hst j (by omega)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, hst j (by omega)⟩

theorem thickSiteCount_congr_prefix {s t : ℕ → Site} {m n : ℕ}
    (hst : ∀ j, j ≤ n → s j = t j) :
    thickSiteCount s m n = thickSiteCount t m n := by
  unfold thickSiteCount
  rw [visitedSites_congr_prefix hst]
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  rw [localTime_congr_prefix hst]

theorem adapted_thickSiteCount (m : ℕ) :
    Adapted canonicalFiltration (fun n s ↦ thickSiteCount s m n) := by
  intro n
  apply measurable_of_prefix
  unfold PrefixDependent
  intro s t hst
  exact thickSiteCount_congr_prefix hst

/-- First time at or after a possibly infinite stopping time at which exactly
`k` sites have local time at least `m`. -/
noncomputable def firstThickCountAfterStopping (m k : ℕ)
    (τ : (ℕ → Site) → WithTop ℕ) : (ℕ → Site) → WithTop ℕ :=
  fun s ↦ if τ s = ⊤ then ⊤ else
    hittingAfter (fun n s ↦ thickSiteCount s m n) {k} (τ s).untopA s

theorem isStoppingTime_firstThickCountAfterStopping (m k : ℕ)
    {τ : (ℕ → Site) → WithTop ℕ} (hτ : IsStoppingTime canonicalFiltration τ) :
    IsStoppingTime canonicalFiltration (firstThickCountAfterStopping m k τ) := by
  intro n
  have hdet (r : ℕ) : IsStoppingTime canonicalFiltration
      (hittingAfter (fun n s ↦ thickSiteCount s m n) {k} r) :=
    (adapted_thickSiteCount m).isStoppingTime_hittingAfter (measurableSet_singleton k)
  have hset : {s | firstThickCountAfterStopping m k τ s ≤ n} =
      ⋃ r : ℕ, ⋃ (_ : r ≤ n),
        {s | τ s = r} ∩
          {s | hittingAfter (fun n s ↦ thickSiteCount s m n) {k} r s ≤ n} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases ht : τ s = ⊤
      · simp [firstThickCountAfterStopping, ht] at h
      · lift τ s to ℕ using ht with r hr
        have hhit : hittingAfter (fun n s ↦ thickSiteCount s m n) {k} r s ≤ n := by
          simpa [firstThickCountAfterStopping, ← hr] using h
        have hrn : r ≤ n := WithTop.coe_le_coe.mp
          ((le_hittingAfter (u := fun n s ↦ thickSiteCount s m n)
            (s := {k}) (n := r) s).trans hhit)
        exact ⟨r, hrn, rfl, hhit⟩
    · rintro ⟨r, hrn, hτr, hhit⟩
      have ht : τ s ≠ ⊤ := by simp [hτr]
      simpa [firstThickCountAfterStopping, ht, hτr] using hhit
  change MeasurableSet[canonicalFiltration n]
    {s | firstThickCountAfterStopping m k τ s ≤ n}
  rw [hset]
  refine MeasurableSet.iUnion fun r ↦ MeasurableSet.iUnion fun hrn ↦ ?_
  exact (canonicalFiltration.mono hrn _ (hτ.measurableSet_eq_of_countable r)).inter
    (hdet r n)

/-- HLOZ `T_m^k` from (2.7). -/
noncomputable def favoriteCreationTime (m : ℕ) :
    ℕ → (ℕ → Site) → WithTop ℕ
  | 0 => fun _ ↦ 0
  | k + 1 => firstThickCountAfterStopping m (k + 1)
      (fun s ↦ favoriteCreationTime m k s + 1)

theorem isStoppingTime_favoriteCreationTime (m k : ℕ) :
    IsStoppingTime canonicalFiltration (favoriteCreationTime m k) := by
  induction k with
  | zero => simpa [favoriteCreationTime] using
      isStoppingTime_const canonicalFiltration (0 : ℕ)
  | succ k ih =>
      rw [favoriteCreationTime]
      exact isStoppingTime_firstThickCountAfterStopping m (k + 1) (ih.add_const' 1)

/-- The stopped block `\hat h_q` at the exact HLOZ time `T_m^k`. -/
noncomputable def favoriteCreationExcursionBlock (m k q : ℕ) : (ℕ → Site) → ℕ :=
  stoppedValue (fun T s ↦ stoppedExcursionBlock s T q) (favoriteCreationTime m k)

theorem measurable_favoriteCreationExcursionBlock (m k q : ℕ) :
    Measurable[(isStoppingTime_favoriteCreationTime m k).measurableSpace]
      (favoriteCreationExcursionBlock m k q) := by
  exact measurable_stoppedExcursionBlockAt q (isStoppingTime_favoriteCreationTime m k)

end Erdos1166.HLOZDecomposition
