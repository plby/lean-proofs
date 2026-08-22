/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Recurrence
import ErdosProblems.Erdos1165.Tilings

/-!
# Deterministic and Borel--Cantelli steps in the HLOZ upper bound

This file isolates the unconditional endgame of the planar upper bound.  It
does not postulate any random-walk estimate.  Instead, it proves the general
implications which turn a *proved* summability estimate for the level events
into the almost-sure assertion that at most three favorite sites remain.

It also records the finite-union argument used after the six domino tilings.
The missing input is therefore localized precisely: a proof that the six
screened event families have summable probabilities, together with recurrence
(divergence of the maximal local time).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165

/-! ## The change from ordinary time to maximal-local-time levels -/

/-- The event that at some time whose maximal local time is exactly `m`, at
least four sites are simultaneous favorites. -/
def fourFavoriteLevelEvent (m : ℕ) : Set WalkPath :=
  {s | ∃ n, maxLocalTime s n = m ∧ 4 ≤ favoriteCount s n}

lemma measurable_favoriteSites (n : ℕ) :
    Measurable fun s : WalkPath ↦ favoriteSites s n := by
  exact (measurable_of_countable
    (fun u : Fin (n + 1) → Point ↦ favoritePrefix u)).comp (measurable_pathPrefix n)

lemma measurableSet_fourFavoriteLevelEvent (m : ℕ) :
    MeasurableSet (fourFavoriteLevelEvent m) := by
  change MeasurableSet {s : WalkPath | ∃ n, maxLocalTime s n = m ∧ 4 ≤ favoriteCount s n}
  rw [show {s : WalkPath | ∃ n, maxLocalTime s n = m ∧ 4 ≤ favoriteCount s n} =
      ⋃ n, {s | maxLocalTime s n = m ∧ 4 ≤ favoriteCount s n} by
        ext s
        simp]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_eq_fun (measurable_maxLocalTime n) measurable_const).inter
      (measurableSet_le measurable_const (measurable_favoriteCount n))

/-- If the maximal local time tends to infinity, infinitely many ordinary
times with at least four favorites produce infinitely many distinct local-time
levels at which this happens.  This is the deterministic content of the
ordinary-time/level-clock transition needed for the upper bound. -/
theorem frequently_fourFavoriteLevelEvent_of_frequently_time
    (s : WalkPath)
    (hmax : Tendsto (maxLocalTime s) atTop atTop)
    (hfour : ∃ᶠ n in atTop, 4 ≤ favoriteCount s n) :
    ∃ᶠ m in atTop, s ∈ fourFavoriteLevelEvent m := by
  rw [frequently_atTop]
  intro M
  have hlevel : ∀ᶠ n in atTop, M ≤ maxLocalTime s n := tendsto_atTop.mp hmax M
  obtain ⟨n, hnFour, hnLevel⟩ := (hfour.and_eventually hlevel).exists
  exact ⟨maxLocalTime s n, hnLevel, n, rfl, hnFour⟩

/-- The pointwise Borel--Cantelli endgame: if only finitely many four-favorite
levels occur and the maximal local time diverges, then eventually every time
has at most three favorites. -/
theorem eventually_favoriteCount_le_three_of_level_events
    (s : WalkPath)
    (hmax : Tendsto (maxLocalTime s) atTop atTop)
    (hfinite : ∀ᶠ m in atTop, s ∉ fourFavoriteLevelEvent m) :
    ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  by_contra hnot
  rw [not_eventually] at hnot
  have hfour : ∃ᶠ n in atTop, 4 ≤ favoriteCount s n :=
    hnot.mono fun n hn ↦ by omega
  have hlevels := frequently_fourFavoriteLevelEvent_of_frequently_time s hmax hfour
  obtain ⟨m, hm, hmnot⟩ := (hlevels.and_eventually hfinite).exists
  exact hmnot hm

/-- First Borel--Cantelli, followed by the deterministic level-clock
transition.  The premise is deliberately the abstract summability conclusion;
no HLOZ estimate is postulated about the canonical walk. -/
theorem ae_eventually_favoriteCount_le_three_of_level_summable
    {μ : Measure WalkPath}
    (hsum : ∑' m, μ (fourFavoriteLevelEvent m) ≠ ∞)
    (hmax : ∀ᵐ s ∂μ, Tendsto (maxLocalTime s) atTop atTop) :
    ∀ᵐ s ∂μ, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  filter_upwards [ae_eventually_notMem hsum, hmax] with s hfinite hsMax
  exact eventually_favoriteCount_le_three_of_level_events s hsMax hfinite

/-- Canonical planar-walk specialization of the level-summability endgame.
Recurrence supplies maximal-local-time divergence, so summability is the only
remaining premise. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_level_summable
    (hsum : ∑' m, simpleRandomWalk (fourFavoriteLevelEvent m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 :=
  ae_eventually_favoriteCount_le_three_of_level_summable
    hsum simpleRandomWalk_maxLocalTime_tendsto

/-! ## The finite union over six domino tilings -/

/-- Index type for the six pairings used by HLOZ: four checkerboard-oriented
pairings and the two column-parity horizontal pairings. -/
abbrev DominoTiling := Tilings.Tiling

/-- Four labeled points are separated by a pairing when none of the six
unordered pairs shares a domino. -/
def fourPointsSeparated (t : DominoTiling) (a b c d : Point) : Prop :=
  ¬Tilings.sameDomino t a b ∧ ¬Tilings.sameDomino t a c ∧
    ¬Tilings.sameDomino t a d ∧ ¬Tilings.sameDomino t b c ∧
    ¬Tilings.sameDomino t b d ∧ ¬Tilings.sameDomino t c d

/-- The elementary six-tiling lemma used after HLOZ Proposition 4.7: every
four distinct lattice points are separated by at least one of the four
checkerboard-oriented pairings or the two column-parity pairings. -/
theorem exists_dominoTiling_separating_four
    (a b c d : Point)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ t : DominoTiling, fourPointsSeparated t a b c d := by
  let p : Fin 4 → Point := ![a, b, c, d]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  obtain ⟨t, ht⟩ := Tilings.exists_tiling_separating_four_distinct_points p hp
  refine ⟨t, ?_⟩
  unfold fourPointsSeparated
  constructor
  · simpa [p] using ht 0 1 (by decide)
  constructor
  · simpa [p] using ht 0 2 (by decide)
  constructor
  · simpa [p] using ht 0 3 (by decide)
  constructor
  · simpa [p] using ht 1 2 (by decide)
  constructor
  · simpa [p] using ht 1 3 (by decide)
  · simpa [p] using ht 2 3 (by decide)

/-- The level event additionally records four distinct favorite sites which
are separated by a specified domino tiling. -/
def separatedFourFavoriteLevelEvent (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  {s | ∃ n a b c d,
    maxLocalTime s n = m ∧
    a ∈ favoriteSites s n ∧ b ∈ favoriteSites s n ∧
    c ∈ favoriteSites s n ∧ d ∈ favoriteSites s n ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    fourPointsSeparated t a b c d}

lemma measurableSet_separatedFourFavoriteLevelEvent (t : DominoTiling) (m : ℕ) :
    MeasurableSet (separatedFourFavoriteLevelEvent t m) := by
  change MeasurableSet {s : WalkPath | ∃ n a b c d,
    maxLocalTime s n = m ∧
    a ∈ favoriteSites s n ∧ b ∈ favoriteSites s n ∧
    c ∈ favoriteSites s n ∧ d ∈ favoriteSites s n ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    fourPointsSeparated t a b c d}
  rw [show {s : WalkPath | ∃ n a b c d,
      maxLocalTime s n = m ∧
      a ∈ favoriteSites s n ∧ b ∈ favoriteSites s n ∧
      c ∈ favoriteSites s n ∧ d ∈ favoriteSites s n ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      fourPointsSeparated t a b c d} =
      ⋃ n, ⋃ a, ⋃ b, ⋃ c, ⋃ d,
        {s | maxLocalTime s n = m ∧
          a ∈ favoriteSites s n ∧ b ∈ favoriteSites s n ∧
          c ∈ favoriteSites s n ∧ d ∈ favoriteSites s n ∧
          a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
          fourPointsSeparated t a b c d} by
        ext s
        simp]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun a ↦
    MeasurableSet.iUnion fun b ↦ MeasurableSet.iUnion fun c ↦
      MeasurableSet.iUnion fun d ↦ ?_
  have hlevel : MeasurableSet {s : WalkPath | maxLocalTime s n = m} :=
    measurableSet_eq_fun (measurable_maxLocalTime n) measurable_const
  have hmem (x : Point) : MeasurableSet {s : WalkPath | x ∈ favoriteSites s n} := by
    exact measurable_favoriteSites n
      ((Set.to_countable {A : Finset Point | x ∈ A}).measurableSet)
  have hgeometry : MeasurableSet { _s : WalkPath |
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        fourPointsSeparated t a b c d} := by
    by_cases h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        fourPointsSeparated t a b c d
    · have heq : { _s : WalkPath |
          a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            fourPointsSeparated t a b c d} = Set.univ := by ext; simp [h]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : { _s : WalkPath |
          a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            fourPointsSeparated t a b c d} = ∅ := by ext; simp [h]
      rw [heq]
      exact MeasurableSet.empty
  simpa only [inter_def, mem_ofPred_eq] using
    hlevel.inter ((hmem a).inter ((hmem b).inter
      ((hmem c).inter ((hmem d).inter hgeometry))))

/-- Deterministic coverage of the four-favorite level event by the six
separated versions. -/
theorem fourFavoriteLevelEvent_subset_six_tilings (m : ℕ) :
    fourFavoriteLevelEvent m ⊆ ⋃ t, separatedFourFavoriteLevelEvent t m := by
  intro s hs
  obtain ⟨n, hnLevel, hnFour⟩ := hs
  have hcard : 3 < (favoriteSites s n).card := by
    change 4 ≤ (favoriteSites s n).card at hnFour
    omega
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card_iff.mp hcard
  obtain ⟨t, ht⟩ := exists_dominoTiling_separating_four a b c d hab hac had hbc hbd hcd
  rw [mem_iUnion]
  exact ⟨t, n, a, b, c, d, hnLevel, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, ht⟩

/-- The measure-theoretic union bound for the six screened events.  The
geometric argument supplies `hcover`; this lemma performs exactly the union
step and nothing analytic. -/
theorem measure_le_sum_six_tilings
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {bad : Set Ω} {screened : DominoTiling → Set Ω}
    (hcover : bad ⊆ ⋃ t, screened t) :
    μ bad ≤ ∑ t, μ (screened t) := by
  calc
    μ bad ≤ μ (⋃ t, screened t) := measure_mono hcover
    _ ≤ ∑' t, μ (screened t) := measure_iUnion_le screened
    _ = ∑ t, μ (screened t) := tsum_fintype _

/-- The concrete union bound obtained from the six-tiling lemma. -/
theorem measure_fourFavoriteLevelEvent_le_six_tilings (m : ℕ) :
    simpleRandomWalk (fourFavoriteLevelEvent m) ≤
      ∑ t, simpleRandomWalk (separatedFourFavoriteLevelEvent t m) := by
  exact measure_le_sum_six_tilings simpleRandomWalk
    (fourFavoriteLevelEvent_subset_six_tilings m)

/-- Summability is preserved by the six-tiling cover.  This is the exact
series manipulation after the geometric tiling lemma and before the first
Borel--Cantelli lemma. -/
theorem level_event_summable_of_six_tilings
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {bad : ℕ → Set Ω} {screened : DominoTiling → ℕ → Set Ω}
    (hcover : ∀ m, bad m ⊆ ⋃ t, screened t m)
    (hscreened : ∀ t, ∑' m, μ (screened t m) ≠ ∞) :
    ∑' m, μ (bad m) ≠ ∞ := by
  have hpoint : ∀ m, μ (bad m) ≤ ∑ t, μ (screened t m) := fun m ↦
    measure_le_sum_six_tilings μ (hcover m)
  have hle : (∑' m, μ (bad m)) ≤ ∑' m, ∑ t, μ (screened t m) :=
    ENNReal.summable.tsum_le_tsum hpoint ENNReal.summable
  have hswap : (∑' m, ∑ t, μ (screened t m)) =
      ∑ t, ∑' m, μ (screened t m) := by
    simpa only [Finset.sum_attach, Finset.mem_univ, forall_const] using
      (Summable.tsum_finsetSum
        (s := Finset.univ)
        (f := fun t m ↦ μ (screened t m))
        (fun _ _ ↦ ENNReal.summable))
  rw [hswap] at hle
  apply ne_top_of_le_ne_top _ hle
  simp [hscreened]

/-- The complete formal endgame available once the screened six-tiling series
and maximal-local-time divergence have been proved. -/
theorem ae_eventually_favoriteCount_le_three_of_six_tilings
    {screened : DominoTiling → ℕ → Set WalkPath}
    (hcover : ∀ m, fourFavoriteLevelEvent m ⊆ ⋃ t, screened t m)
    (hscreened : ∀ t, ∑' m, simpleRandomWalk (screened t m) ≠ ∞)
    (hmax : ∀ᵐ s ∂simpleRandomWalk, Tendsto (maxLocalTime s) atTop atTop) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply ae_eventually_favoriteCount_le_three_of_level_summable
  · exact level_event_summable_of_six_tilings simpleRandomWalk hcover hscreened
  · exact hmax

/-- Canonical planar-walk six-tiling endgame.  It does not assert a screening
estimate: the six summable screened-event series remain the sole input. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_six_tilings
    {screened : DominoTiling → ℕ → Set WalkPath}
    (hcover : ∀ m, fourFavoriteLevelEvent m ⊆ ⋃ t, screened t m)
    (hscreened : ∀ t, ∑' m, simpleRandomWalk (screened t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 :=
  ae_eventually_favoriteCount_le_three_of_six_tilings
    hcover hscreened simpleRandomWalk_maxLocalTime_tendsto

/-- Concrete specialization of the preceding endgame to the six lattice
pairings formalized in this file. -/
theorem ae_eventually_favoriteCount_le_three_of_separated_level_summable
    (hscreened : ∀ t, ∑' m,
      simpleRandomWalk (separatedFourFavoriteLevelEvent t m) ≠ ∞)
    (hmax : ∀ᵐ s ∂simpleRandomWalk, Tendsto (maxLocalTime s) atTop atTop) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  exact ae_eventually_favoriteCount_le_three_of_six_tilings
    fourFavoriteLevelEvent_subset_six_tilings hscreened hmax

/-- Fully concrete recurrence-integrated endgame for the six lattice pairings.
The specialized screened-event summability estimates are intentionally left
as premises. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_separated_level_summable
    (hscreened : ∀ t, ∑' m,
      simpleRandomWalk (separatedFourFavoriteLevelEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 :=
  ae_eventually_favoriteCount_le_three_of_separated_level_summable
    hscreened simpleRandomWalk_maxLocalTime_tendsto

end Erdos1165
