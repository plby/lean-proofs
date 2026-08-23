/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZEventIdentity

namespace Erdos1166

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Squared Euclidean lattice distance, kept in `ℕ` for exact finite-ball
enumeration. -/
def siteSquaredDistance (x y : Site) : ℕ :=
  (x.1 - y.1).natAbs ^ 2 + (x.2 - y.2).natAbs ^ 2

/-- The finite lattice ball `{x : |x-c|^2 ≤ D}`. The enclosing box is
deliberately coarse; the final filter is the exact squared-distance test. -/
noncomputable def hlozLatticeBallSq (D : ℕ) (c : Site) : Finset Site :=
  ((Finset.Icc (c.1 - D) (c.1 + D)).product
    (Finset.Icc (c.2 - D) (c.2 + D))).filter fun x ↦
      siteSquaredDistance x c ≤ D

/-- Sites visited during the closed integer interval `[a,b]`. -/
def visitedSitesBetween (s : ℕ → Site) (a b : ℕ) : Finset Site :=
  (Finset.Icc a b).image s

theorem visitedSitesBetween_mono_right {s : ℕ → Site} {a b c : ℕ}
    (hbc : b ≤ c) : visitedSitesBetween s a b ⊆ visitedSitesBetween s a c := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
  exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hbc⟩, rfl⟩

theorem measurable_visitedSitesBetween_canonical (a b : ℕ) :
    Measurable[HLOZFoundation.canonicalFiltration b]
      (fun s : ℕ → Site ↦ visitedSitesBetween s a b) := by
  let _ : MeasurableSpace (ℕ → Site) := HLOZFoundation.canonicalFiltration b
  change Measurable (fun s : ℕ → Site ↦ visitedSitesBetween s a b)
  rw [measurable_finset_iff]
  intro x
  simp only [visitedSitesBetween, Finset.mem_image]
  apply Measurable.exists
  intro n
  by_cases hn : n ∈ Finset.Icc a b
  · simp only [hn, true_and]
    exact measurableSet_setOfPred.mp (measurableSet_eq_fun
      (HLOZFoundation.adapted_coordinateProcess.measurable_le
        (Finset.mem_Icc.mp hn).2) measurable_const)
  · simp [hn]

/-- The finite candidate set `F_j`, with the geometric window abstracted as
a deterministic finite neighbourhood of the threshold location. Taking
`window c` to be the lattice points in the Euclidean ball around `c` gives
the set printed in the proof of HLOZ Lemma 4.10. -/
def hlozCandidateSitesAtTime (window : Site → Finset Site)
    (s : ℕ → Site) (t q : ℕ) : Finset Site :=
  (window (s t)).filter fun x ↦ q ≤ localTime s t x

theorem measurable_hlozCandidateSitesAtTime_canonical
    (window : Site → Finset Site) (t q : ℕ) :
    Measurable[HLOZFoundation.canonicalFiltration t]
      (fun s : ℕ → Site ↦ hlozCandidateSitesAtTime window s t q) := by
  let _ : MeasurableSpace (ℕ → Site) := HLOZFoundation.canonicalFiltration t
  change Measurable (fun s : ℕ → Site ↦ hlozCandidateSitesAtTime window s t q)
  rw [measurable_finset_iff]
  intro x
  simp only [hlozCandidateSitesAtTime, Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp
      ((measurable_of_countable window).comp
        (HLOZFoundation.adapted_coordinateProcess t))
  · exact measurableSet_setOfPred.mp
      (measurableSet_le measurable_const (HLOZFoundation.adapted_localTime x t))

/-- Candidate sites which have actually been encountered between `t` and
`n`. -/
def hlozVisitedCandidatesAtTime (window : Site → Finset Site)
    (s : ℕ → Site) (t q n : ℕ) : Finset Site :=
  (visitedSitesBetween s t n).filter fun x ↦
    x ∈ hlozCandidateSitesAtTime window s t q

theorem measurable_hlozVisitedCandidatesAtTime_canonical
    (window : Site → Finset Site) {t n q : ℕ} (htn : t ≤ n) :
    Measurable[HLOZFoundation.canonicalFiltration n]
      (fun s : ℕ → Site ↦ hlozVisitedCandidatesAtTime window s t q n) := by
  let _ : MeasurableSpace (ℕ → Site) := HLOZFoundation.canonicalFiltration n
  change Measurable
    (fun s : ℕ → Site ↦ hlozVisitedCandidatesAtTime window s t q n)
  rw [measurable_finset_iff]
  intro x
  simp only [hlozVisitedCandidatesAtTime, Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp
      (measurable_visitedSitesBetween_canonical t n)
  · exact (measurable_finset_mem x).comp
      ((measurable_hlozCandidateSitesAtTime_canonical window t q).mono
        (HLOZFoundation.canonicalFiltration.mono htn) le_rfl)

/-- Number of distinct candidates visited after the stopping time `τ` and
by time `n`. The finite sum over fibers `{τ=t}` makes its adaptedness
literal. -/
def hlozCandidateVisitCount (τ : (ℕ → Site) → WithTop ℕ)
    (window : Site → Finset Site) (q n : ℕ) (s : ℕ → Site) : ℕ :=
  ∑ t ∈ Finset.range (n + 1),
    if τ s = t then (hlozVisitedCandidatesAtTime window s t q n).card else 0

theorem hlozCandidateVisitCount_eq_of_eq
    {τ : (ℕ → Site) → WithTop ℕ} {window : Site → Finset Site}
    {q n t : ℕ} {s : ℕ → Site} (htn : t ≤ n) (hτ : τ s = t) :
    hlozCandidateVisitCount τ window q n s =
      (hlozVisitedCandidatesAtTime window s t q n).card := by
  unfold hlozCandidateVisitCount
  rw [Finset.sum_eq_single t]
  · simp [hτ]
  · intro b hb hbt
    simp only [ite_eq_right_iff]
    intro hτb
    have : (b : WithTop ℕ) = t := hτb.symm.trans hτ
    exact False.elim (hbt (WithTop.coe_inj.mp this))
  · simp [htn]

theorem hlozCandidateVisitCount_eq_zero_of_lt
    {τ : (ℕ → Site) → WithTop ℕ} {window : Site → Finset Site}
    {q n : ℕ} {s : ℕ → Site} (hnτ : (n : WithTop ℕ) < τ s) :
    hlozCandidateVisitCount τ window q n s = 0 := by
  unfold hlozCandidateVisitCount
  apply Finset.sum_eq_zero
  intro t ht
  rw [if_neg]
  intro hτ
  have htn : (t : WithTop ℕ) ≤ n := by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  exact (not_lt_of_ge htn) (hτ ▸ hnτ)

theorem adapted_hlozCandidateVisitCount
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ)
    (window : Site → Finset Site) (q : ℕ) :
    Adapted HLOZFoundation.canonicalFiltration
      (fun n s ↦ hlozCandidateVisitCount τ window q n s) := by
  intro n
  let _ : MeasurableSpace (ℕ → Site) := HLOZFoundation.canonicalFiltration n
  change Measurable (fun s : ℕ → Site ↦
    hlozCandidateVisitCount τ window q n s)
  unfold hlozCandidateVisitCount
  apply Finset.measurable_fun_sum
  intro t ht
  have htn : t ≤ n := by
    simp only [Finset.mem_range] at ht
    omega
  exact Measurable.ite
    (HLOZFoundation.canonicalFiltration.mono htn _
      (hτ.measurableSet_eq_of_countable t))
    ((measurable_of_countable fun F : Finset Site ↦ F.card).comp
      (measurable_hlozVisitedCandidatesAtTime_canonical window htn))
    measurable_const

/-- `σ_i`: the time at which the `i`-th distinct candidate is first hit.
The threshold-count definition is equivalent to HLOZ's recursive
"first new candidate" definition and exposes stopping-time measurability. -/
noncomputable def hlozCandidateTime
    (τ : (ℕ → Site) → WithTop ℕ) (window : Site → Finset Site)
    (q i : ℕ) : (ℕ → Site) → WithTop ℕ :=
  hittingAfter (fun n s ↦ hlozCandidateVisitCount τ window q n s)
    (Set.Ici i) 0

theorem isStoppingTime_hlozCandidateTime
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ)
    (window : Site → Finset Site) (q i : ℕ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (hlozCandidateTime τ window q i) := by
  exact (adapted_hlozCandidateVisitCount hτ window q).isStoppingTime_hittingAfter
    measurableSet_Ici

/-- The paper's `F_j` at `T_m^k`, totalized to the empty set if that
threshold is infinite. -/
noncomputable def hlozThresholdCandidateSites
    (window : Site → Finset Site) (m k q : ℕ) (s : ℕ → Site) : Finset Site :=
  if firstKSitesReachLevel m k s = ⊤ then ∅ else
    hlozCandidateSitesAtTime window s
      (firstKSitesReachLevel m k s).untopA q

theorem hlozThresholdCandidateSites_eq_of_finite
    (window : Site → Finset Site) (m k q : ℕ) (s : ℕ → Site)
    (hfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    hlozThresholdCandidateSites window m k q s =
      hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA q := by
  simp [hlozThresholdCandidateSites, hfinite]

/-- Paper notation `σ_i^j`, where `q_j` is the local-time cutoff defining
`F_j`. -/
noncomputable def hlozSigma
    (window : Site → Finset Site) (m k qj i : ℕ) :
    (ℕ → Site) → WithTop ℕ :=
  hlozCandidateTime (firstKSitesReachLevel m k) window qj i

theorem isStoppingTime_hlozSigma
    (window : Site → Finset Site) (m k qj i : ℕ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (hlozSigma window m k qj i) := by
  exact isStoppingTime_hlozCandidateTime
    (isStoppingTime_firstKSitesReachLevel m k) window qj i

theorem hlozVisitedCandidatesAtTime_subset_candidates
    (window : Site → Finset Site) (s : ℕ → Site) (t q n : ℕ) :
    hlozVisitedCandidatesAtTime window s t q n ⊆
      hlozCandidateSitesAtTime window s t q := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- Pathwise finiteness behind the paper's countable union: after the
`card F_j`-th enumerated point there are no further finite `σ_i^j`. -/
theorem hlozCandidateTime_eq_top_of_card_lt
    {τ : (ℕ → Site) → WithTop ℕ} {window : Site → Finset Site}
    {q i : ℕ} {s : ℕ → Site} (hτfinite : τ s ≠ ⊤)
    (hcard : (hlozCandidateSitesAtTime window s (τ s).untopA q).card < i) :
    hlozCandidateTime τ window q i s = ⊤ := by
  rw [hlozCandidateTime, hittingAfter_eq_top_iff]
  intro n _ hnmem
  have hiCount : i ≤ hlozCandidateVisitCount τ window q n s := hnmem
  by_cases hnτ : (n : WithTop ℕ) < τ s
  · rw [hlozCandidateVisitCount_eq_zero_of_lt hnτ] at hiCount
    omega
  · have hτn : τ s ≤ (n : WithTop ℕ) := by
      simpa only [not_lt] using hnτ
    have ht : (τ s).untopA ≤ n := by
      have hcoe : (((τ s).untopA : ℕ) : WithTop ℕ) = τ s := by
        rw [WithTop.untopA_eq_untop hτfinite]
        exact WithTop.coe_untop _ hτfinite
      exact WithTop.coe_le_coe.mp (hcoe.trans_le hτn)
    rw [hlozCandidateVisitCount_eq_of_eq ht (by
      rw [WithTop.untopA_eq_untop hτfinite]
      exact (WithTop.coe_untop _ hτfinite).symm)] at hiCount
    have hle := Finset.card_le_card
      (hlozVisitedCandidatesAtTime_subset_candidates
        window s (τ s).untopA q n)
    omega

theorem hlozVisitedCandidatesAtTime_mono_right
    {window : Site → Finset Site} {s : ℕ → Site} {t q a b : ℕ}
    (hab : a ≤ b) :
    hlozVisitedCandidatesAtTime window s t q a ⊆
      hlozVisitedCandidatesAtTime window s t q b := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxv, hxF⟩
  exact Finset.mem_filter.mpr
    ⟨visitedSitesBetween_mono_right hab hxv, hxF⟩

/-- Source notation `T(x,n,l)`: the first time `j ≥ l` at which the
post-`l` local-time increment at `x` is exactly `n`. -/
noncomputable def postNthHitTime (x : Site) (n l : ℕ) :
    (ℕ → Site) → WithTop ℕ :=
  hittingAfter (fun j s ↦ localTime s j x - localTime s l x) ({n} : Set ℕ) l

/-- First hit of a fixed site at or after a deterministic time. -/
noncomputable def postHitSiteTime (x : Site) (l : ℕ) :
    (ℕ → Site) → WithTop ℕ :=
  HLOZFoundation.firstHitAfter {x} l

/-- HLOZ's event `A(σ,β)`, with the integer `q` standing for
`m^β`: after `σ`, the current site receives `q` further visits before the
walk hits `L_m^k`. -/
def hlozPostHitRaceEvent (m k : ℕ)
    (σ : (ℕ → Site) → WithTop ℕ) (q : ℕ) : Set (ℕ → Site) :=
  {s | σ s ≠ ⊤ ∧
    postNthHitTime (s (σ s).untopA) q (σ s).untopA s <
      postHitSiteTime (levelCreationSite s m k) (σ s).untopA s}

/-- The first hit of a specified candidate after a possibly infinite
stopping time. -/
noncomputable def candidateFirstHitAfter
    (τ : (ℕ → Site) → WithTop ℕ) (x : Site) :
    (ℕ → Site) → WithTop ℕ :=
  fun s ↦ if τ s = ⊤ then ⊤ else postHitSiteTime x (τ s).untopA s

/-- If `x` is a candidate and is first hit at a finite time after `τ`,
that hit is exactly one of the enumerating stopping times `σ_i`. -/
theorem exists_hlozCandidateTime_eq_candidateFirstHit
    {τ : (ℕ → Site) → WithTop ℕ} {window : Site → Finset Site}
    {q : ℕ} {s : ℕ → Site} {x : Site}
    (hτfinite : τ s ≠ ⊤)
    (hxF : x ∈ hlozCandidateSitesAtTime window s (τ s).untopA q)
    (hxstart : s (τ s).untopA ≠ x)
    (hhitfinite : candidateFirstHitAfter τ x s ≠ ⊤) :
    ∃ i : ℕ, 1 ≤ i ∧
      hlozCandidateTime τ window q i s = candidateFirstHitAfter τ x s := by
  let t : ℕ := (τ s).untopA
  let H : WithTop ℕ := candidateFirstHitAfter τ x s
  let h : ℕ := H.untopA
  have hτcoe : (t : WithTop ℕ) = τ s := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hτfinite]
    exact WithTop.coe_untop _ hτfinite
  have hHdef : H = postHitSiteTime x t s := by
    simp [H, candidateFirstHitAfter, hτfinite, t]
  have hHcoe : (h : WithTop ℕ) = H := by
    dsimp only [h]
    rw [WithTop.untopA_eq_untop hhitfinite]
    exact WithTop.coe_untop _ hhitfinite
  have hth : t ≤ h := by
    have hle : (t : WithTop ℕ) ≤ postHitSiteTime x t s := by
      exact le_hittingAfter s
    rw [← hHdef, ← hHcoe] at hle
    exact WithTop.coe_le_coe.mp hle
  have hxAtH : s h = x := by
    have hm : HLOZFoundation.coordinateProcess
        (postHitSiteTime x t s).untopA s ∈ ({x} : Set Site) := by
      apply hittingAfter_mem_set_of_ne_top
      change postHitSiteTime x t s ≠ ⊤
      rw [← hHdef]
      exact hhitfinite
    have hu : (postHitSiteTime x t s).untopA = h := by
      rw [← hHdef, ← hHcoe]
      rfl
    simpa [HLOZFoundation.coordinateProcess, hu] using hm
  have htlth : t < h := by
    apply lt_of_le_of_ne hth
    intro heq
    apply hxstart
    simpa [t, heq] using hxAtH
  have hxVisited : x ∈ visitedSitesBetween s t h := by
    exact Finset.mem_image.mpr ⟨h, Finset.mem_Icc.mpr ⟨hth, le_refl h⟩, hxAtH⟩
  have hxLate : x ∈ hlozVisitedCandidatesAtTime window s t q h :=
    Finset.mem_filter.mpr ⟨hxVisited, by simpa [t] using hxF⟩
  let i : ℕ := (hlozVisitedCandidatesAtTime window s t q h).card
  have hi : 1 ≤ i := by
    dsimp only [i]
    have := Finset.card_pos.mpr ⟨x, hxLate⟩
    omega
  have hcountH : hlozCandidateVisitCount τ window q h s = i := by
    rw [hlozCandidateVisitCount_eq_of_eq hth (by simpa [t] using hτcoe.symm)]
  have hcountLt : ∀ n : ℕ, n < h →
      hlozCandidateVisitCount τ window q n s < i := by
    intro n hnh
    by_cases hnt : n < t
    · have hnτ : (n : WithTop ℕ) < τ s := by
        rw [← hτcoe]
        exact WithTop.coe_lt_coe.mpr hnt
      rw [hlozCandidateVisitCount_eq_zero_of_lt hnτ]
      exact hi
    · have htn : t ≤ n := by omega
      rw [hlozCandidateVisitCount_eq_of_eq htn (by simpa [t] using hτcoe.symm)]
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hlozVisitedCandidatesAtTime_mono_right hnh.le, ?_⟩
      intro heq
      have hxEarly : x ∈ hlozVisitedCandidatesAtTime window s t q n := by
        rw [heq]
        exact hxLate
      have hxEarlyVisited := (Finset.mem_filter.mp hxEarly).1
      rcases Finset.mem_image.mp hxEarlyVisited with ⟨r, hr, hrx⟩
      have hrH : (r : WithTop ℕ) < postHitSiteTime x t s := by
        rw [← hHdef, ← hHcoe]
        exact WithTop.coe_lt_coe.mpr ((Finset.mem_Icc.mp hr).2.trans_lt hnh)
      exact notMem_of_lt_hittingAfter hrH (Finset.mem_Icc.mp hr).1
        (by simpa [HLOZFoundation.coordinateProcess] using hrx)
  refine ⟨i, hi, ?_⟩
  have hle : hlozCandidateTime τ window q i s ≤ (h : WithTop ℕ) := by
    exact hittingAfter_le_of_mem (Nat.zero_le h) (by
      change i ≤ hlozCandidateVisitCount τ window q h s
      omega)
  have hge : (h : WithTop ℕ) ≤ hlozCandidateTime τ window q i s := by
    apply WithTop.coe_le_iff.mpr
    intro a ha
    by_contra hnot
    have hah : a < h := Nat.lt_of_not_ge hnot
    have hsigmafinite : hlozCandidateTime τ window q i s ≠ ⊤ := by
      rw [ha]
      simp
    have hmem := hittingAfter_mem_set_of_ne_top hsigmafinite
    change i ≤ hlozCandidateVisitCount τ window q
      (hlozCandidateTime τ window q i s).untopA s at hmem
    have hua : (hlozCandidateTime τ window q i s).untopA = a := by
      rw [ha]
      rfl
    rw [hua] at hmem
    exact (not_le_of_gt (hcountLt a hah)) hmem
  have hsigma : hlozCandidateTime τ window q i s = (h : WithTop ℕ) :=
    le_antisymm hle hge
  exact hsigma.trans hHcoe

/-- Abstract form of the paper's candidate-first-hit event: some member of
the finite set `F_j` is first encountered at a finite time, and the event
`A` holds at that first encounter. -/
def hlozCandidateFirstHitRaceEvent
    (τ : (ℕ → Site) → WithTop ℕ) (window : Site → Finset Site)
    (m k qCandidate qRace : ℕ) : Set (ℕ → Site) :=
  {s | ∃ x : Site,
    τ s ≠ ⊤ ∧
    x ∈ hlozCandidateSitesAtTime window s (τ s).untopA qCandidate ∧
    s (τ s).untopA ≠ x ∧
    candidateFirstHitAfter τ x s ≠ ⊤ ∧
    s ∈ hlozPostHitRaceEvent m k (candidateFirstHitAfter τ x) qRace}

/-- Deterministic countable-union decomposition underlying HLOZ Lemma 4.10:
the first hit of a candidate is one of the enumerating stopping times. -/
theorem hlozCandidateFirstHitRaceEvent_subset_iUnion
    (τ : (ℕ → Site) → WithTop ℕ) (window : Site → Finset Site)
    (m k qCandidate qRace : ℕ) :
    hlozCandidateFirstHitRaceEvent τ window m k qCandidate qRace ⊆
      ⋃ i : ℕ, ⋃ (_ : 1 ≤ i),
        hlozPostHitRaceEvent m k
          (hlozCandidateTime τ window qCandidate i) qRace := by
  intro s hs
  rcases hs with ⟨x, hτfinite, hxF, hxstart, hhitfinite, hA⟩
  obtain ⟨i, hi, hiEq⟩ := exists_hlozCandidateTime_eq_candidateFirstHit
    hτfinite hxF hxstart hhitfinite
  simp only [Set.mem_iUnion]
  refine ⟨i, hi, ?_⟩
  rcases hA with ⟨hfirstfinite, hRace⟩
  refine ⟨?_, ?_⟩
  · simpa [hiEq] using hfirstfinite
  · simpa only [hiEq] using hRace

/-- The source event `B'_j` stripped of the irrelevant conditioning event
`Π_m^k`. The finite window is the radius-`exp(m^α)` lattice ball and
`qCandidate = m-m^β_j`, `qRace = m^β_{j-1}` in the paper. -/
def hlozLemma410BPrimeEvent (window : Site → Finset Site)
    (m k qCandidate qRace : ℕ) : Set (ℕ → Site) :=
  {s | s ∈ hlozThresholdTimeEventK m (k + 1) ∧
    levelCreationSite s m (k + 1) ∈
      hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate ∧
    s ∈ hlozPostHitRaceEvent m k
      (candidateFirstHitAfter (firstKSitesReachLevel m k)
        (levelCreationSite s m (k + 1))) qRace}

private theorem lemma410_firstKSitesReachLevel_ne_top_of_le
    (s : ℕ → Site) (m : ℕ) {i k : ℕ} (hik : i ≤ k)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    firstKSitesReachLevel m i s ≠ ⊤ := by
  intro hitop
  have hle := firstKSitesReachLevel_mono_k s m hik
  rw [hitop] at hle
  exact hkfinite (top_unique hle)

theorem hlozLemma410BPrimeEvent_subset_candidateFirstHitRaceEvent
    (window : Site → Finset Site) (m k qCandidate qRace : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    hlozLemma410BPrimeEvent window m k qCandidate qRace ⊆
      hlozCandidateFirstHitRaceEvent (firstKSitesReachLevel m k) window
        m k qCandidate qRace := by
  intro s hs
  rcases hs with ⟨hMnext, hxF, hA⟩
  let Tk := firstKSitesReachLevel m k s
  let Tnext := firstKSitesReachLevel m (k + 1) s
  let x := levelCreationSite s m (k + 1)
  have hnextfinite : Tnext ≠ ⊤ := by
    exact ne_top_of_lt hMnext
  have hkfinite : Tk ≠ ⊤ := by
    exact lemma410_firstKSitesReachLevel_ne_top_of_le
      s m (Nat.le_succ k) hnextfinite
  have hdistinct : levelCreationSite s m k ≠ x := by
    exact levelCreationSite_ne_of_lt s m hm hk (Nat.lt_succ_self k) hnextfinite
  have hxstart : s Tk.untopA ≠ x := by
    change levelCreationSite s m k ≠ x
    exact hdistinct
  have hkCoe : (Tk.untopA : WithTop ℕ) = Tk := by
    rw [WithTop.untopA_eq_untop hkfinite]
    exact WithTop.coe_untop _ hkfinite
  have hnextCoe : (Tnext.untopA : WithTop ℕ) = Tnext := by
    rw [WithTop.untopA_eq_untop hnextfinite]
    exact WithTop.coe_untop _ hnextfinite
  have htimeLe : Tk.untopA ≤ Tnext.untopA := by
    have hle := firstKSitesReachLevel_mono_k s m (Nat.le_succ k)
    exact WithTop.coe_le_coe.mp (hkCoe.trans_le (hle.trans_eq hnextCoe.symm))
  have hxAtNext : s Tnext.untopA = x := rfl
  have hhitfinite :
      candidateFirstHitAfter (firstKSitesReachLevel m k) x s ≠ ⊤ := by
    have hle : postHitSiteTime x Tk.untopA s ≤
        (Tnext.untopA : WithTop ℕ) := by
      apply hittingAfter_le_of_mem htimeLe
      simpa [HLOZFoundation.coordinateProcess] using hxAtNext
    have hpostfinite : postHitSiteTime x Tk.untopA s ≠ ⊤ := by
      intro htop
      rw [htop] at hle
      simp at hle
    simpa [candidateFirstHitAfter, hkfinite, Tk, x] using hpostfinite
  refine ⟨x, hkfinite, ?_, hxstart, hhitfinite, ?_⟩
  · simpa [Tk, x] using hxF
  · simpa [x] using hA

/-- Paper-shaped decomposition from Lemma 4.10: `B'_j`, intersected with any context
event `P` (in particular `Π_m^k`), is covered by the countable union of
`{A(σ_i^j,β_{j-1}), M_m^k, P}`. All `σ_i^j` are stopping times by
`isStoppingTime_hlozCandidateTime`; only the subsequent probability/hitting
estimate remains. -/
theorem hlozLemma410BPrimeEvent_inter_subset_iUnion
    (window : Site → Finset Site) (m k qCandidate qRace : ℕ)
    (hm : 0 < m) (hk : 0 < k) (P : Set (ℕ → Site)) :
    hlozLemma410BPrimeEvent window m k qCandidate qRace ∩ P ⊆
      ⋃ i : ℕ, ⋃ (_ : 1 ≤ i),
        (hlozPostHitRaceEvent m k
          (hlozCandidateTime (firstKSitesReachLevel m k)
            window qCandidate i) qRace ∩
          hlozThresholdTimeEventK m k ∩ P) := by
  intro s hs
  rcases hs with ⟨hB, hP⟩
  have hcandidate := hlozLemma410BPrimeEvent_subset_candidateFirstHitRaceEvent
    window m k qCandidate qRace hm hk hB
  have hunion := hlozCandidateFirstHitRaceEvent_subset_iUnion
    (firstKSitesReachLevel m k) window m k qCandidate qRace hcandidate
  simp only [Set.mem_iUnion] at hunion ⊢
  rcases hunion with ⟨i, hi, hAi⟩
  refine ⟨i, hi, ?_⟩
  have hMnext : s ∈ hlozThresholdTimeEventK m (k + 1) := hB.1
  have hMk : s ∈ hlozThresholdTimeEventK m k := by
    change firstKSitesReachLevel m k s < firstKSitesReachLevel (m + 1) 1 s
    exact (firstKSitesReachLevel_mono_k s m (Nat.le_succ k)).trans_lt hMnext
  exact ⟨⟨hAi, hMk⟩, hP⟩

/-- The sole probabilistic input left after the deterministic decomposition:
a uniform bound for each post-stopping-time race `A(σ_i^j,β_{j-1})`.
HLOZ obtain this from the strong Markov property and their planar hitting
estimate; no such bound is assumed in the covering theorem above. -/
def HasHLOZLemma410PostHitRaceEstimate
    (μ : Measure (ℕ → Site)) (window : Site → Finset Site)
    (m k qCandidate qRace : ℕ) (bound : ℕ → ENNReal) : Prop :=
  ∀ i : ℕ, 1 ≤ i →
    μ (hlozPostHitRaceEvent m k
      (hlozSigma window m k qCandidate i) qRace) ≤ bound i

end Erdos1166
