/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZDecomposition
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Parameters

/-!
The expectation-counting and Markov step in Hao--Li--Okada--Zheng,
Proposition 4.4.  The paper applies this argument to the external path
`\widetilde S`.  The decomposition file constructs its finite deleted-path
counterpart.  We first record the unrestricted stationary-increments lemma,
then the source-faithful version: only chessboard-even sites are counted and
the path is restarted only at even times.  The latter asks only for
stationarity under translations at times `2j`; no arbitrary-shift
stationarity of the deleted path is asserted here.

No many-site estimate is assumed.  The probabilistic input is a bound for
the local time of the origin, corresponding to HLOZ (2.19).
-/

namespace Erdos1166.HLOZProp44

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

open HLOZFoundation
open HLOZDecomposition
open HLOZProp47Parameters

/-! ### Source scales -/

/-- `1 - 2κ₁`, the exponent in HLOZ (4.13). -/
noncomputable def prop44RateExponent : ℝ := 1 - 2 * kappaOne

/-- `3 - 4κ₁`, the value of `β` used in HLOZ (2.19). -/
noncomputable def prop44Beta : ℝ := 3 - 4 * kappaOne

@[simp] theorem prop44RateExponent_eq : prop44RateExponent = (8 : ℝ) / 25 := by
  norm_num [prop44RateExponent, kappaOne]

@[simp] theorem prop44Beta_eq : prop44Beta = (41 : ℝ) / 25 := by
  norm_num [prop44Beta, kappaOne]

theorem prop44RateExponent_pos : 0 < prop44RateExponent := by
  norm_num [prop44RateExponent_eq]

theorem prop44Beta_between : 1 < prop44Beta ∧ prop44Beta < 2 := by
  norm_num [prop44Beta_eq]

/-- The real time scale in HLOZ (4.10), with the corrected concrete `κ₁`. -/
noncomputable def prop44PsiReal (m : ℕ) : ℝ :=
  Real.exp
    (Real.sqrt Real.pi * Real.sqrt (m : ℝ) +
      Real.pi ^ (2 - 2 * kappaOne) * (m : ℝ) ^ prop44RateExponent)

/-- A discrete external-time horizon.  Rounding upward is convenient for
the upper-tail/counting argument and changes the source scale by at most one.
-/
noncomputable def prop44Psi (m : ℕ) : ℕ := Nat.ceil (prop44PsiReal m)

theorem prop44PsiReal_pos (m : ℕ) : 0 < prop44PsiReal m := by
  exact Real.exp_pos _

theorem prop44Psi_pos (m : ℕ) : 0 < prop44Psi m := by
  exact Nat.ceil_pos.mpr (prop44PsiReal_pos m)

/-- The exact threshold `K₂(β)` from HLOZ Lemma 2.5, equation (2.19). -/
noncomputable def lemma25ExternalThreshold (n : ℕ) : ℝ :=
  15 / (16 * Real.pi) * Real.log (n : ℝ) ^ 2 -
    2 * Real.log (n : ℝ) ^ prop44Beta

/-- The real right side in HLOZ (2.19). -/
noncomputable def lemma25ExternalTail (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ *
    Real.exp (8 * Real.log (n : ℝ) ^ (prop44Beta - 1))

/-- The high-external-local-time threshold in HLOZ (4.13). -/
noncomputable def prop44SiteThreshold (m : ℕ) : ℝ :=
  (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ)

/-! ### Deterministic first-visit counting -/

/-- Restart a path at time `j` and translate its position there to the
origin. -/
def shiftedPath (s : ℕ → Site) (j : ℕ) : ℕ → Site :=
  fun q ↦ s (j + q) - s j

@[simp] theorem shiftedPath_zero (s : ℕ → Site) (j : ℕ) :
    shiftedPath s j 0 = (0, 0) := by
  ext <;> simp [shiftedPath]

/-- Sites visited through `n` whose local time is at least the real
threshold `u`. -/
noncomputable def sitesAtLeastReal
    (s : ℕ → Site) (n : ℕ) (u : ℝ) : Finset Site :=
  (visitedSites s n).filter fun x ↦ u ≤ (localTime s n x : ℝ)

/-- The chessboard-even sublattice `\mathbb Z^2_e` used in the proof of
HLOZ Proposition 4.4. -/
def isEvenSite (x : Site) : Prop := HLOZPairing.chessEven x

theorem isEvenSite_iff_chessEven (x : Site) :
    isEvenSite x ↔ HLOZPairing.chessEven x := Iff.rfl

noncomputable local instance : DecidablePred isEvenSite :=
  Classical.decPred isEvenSite

/-- High-local-time sites in the chessboard-even sublattice. -/
noncomputable def evenSitesAtLeastReal
    (s : ℕ → Site) (n : ℕ) (u : ℝ) : Finset Site :=
  (sitesAtLeastReal s n u).filter isEvenSite

/-- The parity property used in HLOZ: an even site can be occupied only at
an even time.  (For a nearest-neighbour path started at the origin the
converse holds as well, but this one direction is all the counting proof
needs.) -/
def EvenSitesAtEvenTimes (s : ℕ → Site) : Prop :=
  ∀ t : ℕ, isEvenSite (s t) → Even t

/-- Start times whose length-`n` restarted path spends local time at least
`u` at its origin. -/
noncomputable def goodStartTimes
    (s : ℕ → Site) (n : ℕ) (u : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun j ↦
    u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)

/-- The source-faithful restart indices: HLOZ restarts the external chain
only at the even times `2j`. -/
noncomputable def evenGoodStartTimes
    (s : ℕ → Site) (n : ℕ) (u : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun j ↦
    Even j ∧ u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)

/-- The first visit to `x` through `n`, with the irrelevant default `0` for
an unvisited site. -/
noncomputable def firstVisitIndex (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  if h : ∃ j, j ≤ n ∧ s j = x then Nat.find h else 0

theorem firstVisitIndex_spec {s : ℕ → Site} {n : ℕ} {x : Site}
    (hx : x ∈ visitedSites s n) :
    firstVisitIndex s n x ≤ n ∧ s (firstVisitIndex s n x) = x := by
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
  have hjn : j ≤ n := by
    have : j < n + 1 := Finset.mem_range.mp hj
    omega
  have h : ∃ q, q ≤ n ∧ s q = x := ⟨j, hjn, hjx⟩
  simp only [firstVisitIndex, dif_pos h]
  exact Nat.find_spec h

theorem firstVisitIndex_le_of_eq {s : ℕ → Site} {n t : ℕ} {x : Site}
    (htn : t ≤ n) (htx : s t = x) : firstVisitIndex s n x ≤ t := by
  have h : ∃ q, q ≤ n ∧ s q = x := ⟨t, htn, htx⟩
  simp only [firstVisitIndex, dif_pos h]
  exact Nat.find_min' h ⟨htn, htx⟩

private theorem localTime_le_shifted_at_firstVisit
    {s : ℕ → Site} {n : ℕ} {x : Site}
    (hx : x ∈ visitedSites s n) :
    localTime s n x ≤
      localTime (shiftedPath s (firstVisitIndex s n x)) n (0, 0) := by
  let j := firstVisitIndex s n x
  have hj := firstVisitIndex_spec hx
  let A := (Finset.range (n + 1)).filter fun t ↦ s t = x
  let B := (Finset.range (n + 1)).filter fun q ↦
    shiftedPath s j q = (0, 0)
  change A.card ≤ B.card
  apply Finset.card_le_card_of_injOn (fun t ↦ t - j)
  · intro t ht
    change t ∈ A at ht
    change t - j ∈ B
    simp only [A, Finset.mem_filter, Finset.mem_range] at ht
    simp only [B, Finset.mem_filter, Finset.mem_range]
    have hjt : j ≤ t := firstVisitIndex_le_of_eq (Nat.le_of_lt_succ ht.1) ht.2
    refine ⟨by omega, ?_⟩
    simp only [shiftedPath]
    rw [Nat.add_sub_of_le hjt, ht.2, hj.2]
    apply Prod.ext <;> simp
  · intro a ha b hb hab
    change a ∈ A at ha
    change b ∈ A at hb
    simp only [A, Finset.mem_filter, Finset.mem_range] at ha hb
    have hja : j ≤ a := firstVisitIndex_le_of_eq (Nat.le_of_lt_succ ha.1) ha.2
    have hjb : j ≤ b := firstVisitIndex_le_of_eq (Nat.le_of_lt_succ hb.1) hb.2
    change a - j = b - j at hab
    omega

/-- Every high site is injected into the time of its first visit; all its
visits then occur in the following length-`n` window.  This is the pathwise
counting inequality used in the expectation line of HLOZ Proposition 4.4.
-/
theorem card_sitesAtLeastReal_le_goodStartTimes
    (s : ℕ → Site) (n : ℕ) (u : ℝ) :
    (sitesAtLeastReal s n u).card ≤ (goodStartTimes s n u).card := by
  classical
  apply Finset.card_le_card_of_injOn (firstVisitIndex s n)
  · intro x hx
    change x ∈ sitesAtLeastReal s n u at hx
    change firstVisitIndex s n x ∈ goodStartTimes s n u
    have hx' := Finset.mem_filter.mp hx
    simp only [goodStartTimes, Finset.mem_filter, Finset.mem_range]
    have hspec := firstVisitIndex_spec hx'.1
    refine ⟨Nat.lt_succ_of_le hspec.1, hx'.2.trans ?_⟩
    exact_mod_cast localTime_le_shifted_at_firstVisit hx'.1
  · intro x hx y hy hxy
    change x ∈ sitesAtLeastReal s n u at hx
    change y ∈ sitesAtLeastReal s n u at hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxspec := (firstVisitIndex_spec hx'.1).2
    have hyspec := (firstVisitIndex_spec hy'.1).2
    rw [hxy] at hxspec
    exact hxspec.symm.trans hyspec

/-- The parity-correct deterministic injection in the source proof.  A high
even site is sent to its first visit.  The path-parity assumption makes this
an even restart time, and the remaining visits fit in the following
length-`n` window. -/
theorem card_evenSitesAtLeastReal_le_evenGoodStartTimes
    (s : ℕ → Site) (n : ℕ) (u : ℝ)
    (hparity : EvenSitesAtEvenTimes s) :
    (evenSitesAtLeastReal s n u).card ≤
      (evenGoodStartTimes s n u).card := by
  classical
  apply Finset.card_le_card_of_injOn (firstVisitIndex s n)
  · intro x hx
    change x ∈ evenSitesAtLeastReal s n u at hx
    change firstVisitIndex s n x ∈ evenGoodStartTimes s n u
    have hx' := Finset.mem_filter.mp hx
    have hxHigh := Finset.mem_filter.mp hx'.1
    have hspec := firstVisitIndex_spec hxHigh.1
    simp only [evenGoodStartTimes, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le hspec.1, ?_, hxHigh.2.trans ?_⟩
    · exact hparity _ (hspec.2.symm ▸ hx'.2)
    · exact_mod_cast localTime_le_shifted_at_firstVisit hxHigh.1
  · intro x hx y hy hxy
    change x ∈ evenSitesAtLeastReal s n u at hx
    change y ∈ evenSitesAtLeastReal s n u at hy
    have hxVisited := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hx).1).1
    have hyVisited := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hy).1).1
    have hxspec := (firstVisitIndex_spec hxVisited).2
    have hyspec := (firstVisitIndex_spec hyVisited).2
    rw [hxy] at hxspec
    exact hxspec.symm.trans hyspec

/-! ### Measurability and the Markov estimate -/

theorem measurable_shiftedLocalTime (j n : ℕ) :
    Measurable fun s : ℕ → Site ↦
      localTime (shiftedPath s j) n (0, 0) := by
  unfold localTime
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro q _hq
  apply Measurable.ite
  · exact measurableSet_eq_fun
      ((measurable_pi_apply (j + q)).sub (measurable_pi_apply j)) measurable_const
  · exact measurable_const
  · exact measurable_const

theorem measurableSet_shiftedLocalTime_ge (j n : ℕ) (u : ℝ) :
    MeasurableSet
      {s : ℕ → Site | u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)} := by
  exact measurableSet_le measurable_const
    ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp
      (measurable_shiftedLocalTime j n))

theorem measurable_goodStartTimes (n : ℕ) (u : ℝ) :
    Measurable fun s : ℕ → Site ↦ goodStartTimes s n u := by
  rw [measurable_finset_iff]
  intro j
  by_cases hj : j < n + 1
  · simp only [goodStartTimes, Finset.mem_filter, Finset.mem_range, hj, true_and]
    exact measurableSet_setOfPred.mp (measurableSet_shiftedLocalTime_ge j n u)
  · simp only [goodStartTimes, Finset.mem_filter, Finset.mem_range, hj, false_and]
    exact measurable_const

theorem measurable_card_goodStartTimes (n : ℕ) (u : ℝ) :
    Measurable fun s : ℕ → Site ↦ (goodStartTimes s n u).card :=
  (measurable_of_countable fun t : Finset ℕ ↦ t.card).comp
    (measurable_goodStartTimes n u)

theorem measurable_evenGoodStartTimes (n : ℕ) (u : ℝ) :
    Measurable fun s : ℕ → Site ↦ evenGoodStartTimes s n u := by
  rw [measurable_finset_iff]
  intro j
  by_cases hjn : j < n + 1
  · by_cases hj : Even j
    · simp only [evenGoodStartTimes, Finset.mem_filter, Finset.mem_range,
        hjn, hj, true_and]
      exact measurableSet_setOfPred.mp (measurableSet_shiftedLocalTime_ge j n u)
    · simpa [evenGoodStartTimes, hjn, hj] using
        (measurable_const : Measurable (fun _ : ℕ → Site ↦ False))
  · simpa [evenGoodStartTimes, hjn] using
      (measurable_const : Measurable (fun _ : ℕ → Site ↦ False))

theorem measurable_card_evenGoodStartTimes (n : ℕ) (u : ℝ) :
    Measurable fun s : ℕ → Site ↦ (evenGoodStartTimes s n u).card :=
  (measurable_of_countable fun t : Finset ℕ ↦ t.card).comp
    (measurable_evenGoodStartTimes n u)

/-- Stationarity of the translated restart maps.  This is the structural
law enjoyed by a random walk with stationary independent increments. -/
def HasStationaryIncrements (μ : Measure (ℕ → Site)) : Prop :=
  ∀ j : ℕ, Measure.map (fun s ↦ shiftedPath s j) μ = μ

/-- The exact invariance used in Proposition 4.4: translated restarts are
required only at even times.  This is the appropriate interface for the
even-time external chain. -/
def HasStationaryEvenIncrements (μ : Measure (ℕ → Site)) : Prop :=
  ∀ j : ℕ, Measure.map (fun s ↦ shiftedPath s (2 * j)) μ = μ

theorem measurable_shiftedPath (j : ℕ) :
    Measurable fun s : ℕ → Site ↦ shiftedPath s j := by
  apply measurable_pi_lambda
  intro q
  exact (measurable_pi_apply (j + q)).sub (measurable_pi_apply j)

theorem measure_shiftedLocalTime_ge_eq
    {μ : Measure (ℕ → Site)} (hstationary : HasStationaryIncrements μ)
    (j n : ℕ) (u : ℝ) :
    μ {s | u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)} =
      μ {s | u ≤ (localTime s n (0, 0) : ℝ)} := by
  let E : Set (ℕ → Site) :=
    {s | u ≤ (localTime s n (0, 0) : ℝ)}
  have hE : MeasurableSet E := by
    exact measurableSet_le measurable_const
      ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp
        (measurable_localTime_eval n (0, 0)))
  calc
    μ {s | u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)} =
        (Measure.map (fun s ↦ shiftedPath s j) μ) E := by
      rw [Measure.map_apply (measurable_shiftedPath j) hE]
      rfl
    _ = μ E := by rw [hstationary j]
    _ = μ {s | u ≤ (localTime s n (0, 0) : ℝ)} := rfl

theorem measure_evenShiftedLocalTime_ge_eq
    {μ : Measure (ℕ → Site)}
    (hstationary : HasStationaryEvenIncrements μ)
    (j n : ℕ) (hj : Even j) (u : ℝ) :
    μ {s | u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)} =
      μ {s | u ≤ (localTime s n (0, 0) : ℝ)} := by
  obtain ⟨q, hq⟩ := hj
  have hjq : j = 2 * q := by omega
  let E : Set (ℕ → Site) :=
    {s | u ≤ (localTime s n (0, 0) : ℝ)}
  have hE : MeasurableSet E := by
    exact measurableSet_le measurable_const
      ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp
        (measurable_localTime_eval n (0, 0)))
  calc
    μ {s | u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)} =
        (Measure.map (fun s ↦ shiftedPath s j) μ) E := by
      rw [Measure.map_apply (measurable_shiftedPath j) hE]
      rfl
    _ = μ E := by rw [hjq, hstationary q]
    _ = μ {s | u ≤ (localTime s n (0, 0) : ℝ)} := rfl

/-- Finite expectation/counting plus Markov.  This is the abstract core of
the passage from the one-site estimate (2.19) to the many-site estimate
(4.13). -/
theorem measure_many_sites_le_of_one_site
    (μ : Measure (ℕ → Site))
    (hstationary : HasStationaryIncrements μ)
    (n : ℕ) (u : ℝ) (B p : ℝ)
    (hB : 0 < B)
    (hone : μ {s | u ≤ (localTime s n (0, 0) : ℝ)} ≤ ENNReal.ofReal p) :
    μ {s | B < ((sitesAtLeastReal s n u).card : ℝ)} ≤
      (n + 1 : ℝ≥0∞) * ENNReal.ofReal p / ENNReal.ofReal B := by
  let count : (ℕ → Site) → ℝ≥0∞ :=
    fun s ↦ ∑ j ∈ Finset.range (n + 1),
      if u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ) then 1 else 0
  have hcount : Measurable count := by
    apply Finset.measurable_sum
    intro j hj
    apply Measurable.ite
    · exact measurableSet_shiftedLocalTime_ge j n u
    · exact measurable_const
    · exact measurable_const
  have hcount_eq (s : ℕ → Site) :
      count s = ((goodStartTimes s n u).card : ℝ≥0∞) := by
    simp only [count, goodStartTimes, Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> rfl
  have hsubset : {s | B < ((sitesAtLeastReal s n u).card : ℝ)} ⊆
      {s | ENNReal.ofReal B ≤ count s} := by
    intro s hs
    have hcard := card_sitesAtLeastReal_le_goodStartTimes s n u
    have hreal : B ≤ ((goodStartTimes s n u).card : ℝ) :=
      hs.le.trans (by exact_mod_cast hcard)
    have henn := ENNReal.ofReal_le_ofReal hreal
    calc
      ENNReal.ofReal B ≤ ((goodStartTimes s n u).card : ℝ≥0∞) := by
        simpa using henn
      _ = count s := (hcount_eq s).symm
  calc
    μ {s | B < ((sitesAtLeastReal s n u).card : ℝ)} ≤
        μ {s | ENNReal.ofReal B ≤ count s} := measure_mono hsubset
    _ ≤ (∫⁻ s, count s ∂μ) / ENNReal.ofReal B :=
      meas_ge_le_lintegral_div hcount.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr hB) ENNReal.ofReal_ne_top
    _ ≤ (n + 1 : ℝ≥0∞) * ENNReal.ofReal p / ENNReal.ofReal B := by
      gcongr
      rw [show count = fun s ↦
          ∑ j ∈ Finset.range (n + 1),
            {t : ℕ → Site |
              u ≤ (localTime (shiftedPath t j) n (0, 0) : ℝ)}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) s by
        funext s
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hgood :
            u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)
        · simp [count, hgood]
        · simp [count, hgood], lintegral_finsetSum]
      · calc
          ∑ j ∈ Finset.range (n + 1),
              ∫⁻ s,
                {t : ℕ → Site |
                  u ≤ (localTime (shiftedPath t j) n (0, 0) : ℝ)}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) s ∂μ ≤
              ∑ _j ∈ Finset.range (n + 1), ENNReal.ofReal p := by
                gcongr with j hj
                rw [lintegral_indicator
                  (measurableSet_shiftedLocalTime_ge j n u), lintegral_const]
                simpa [measure_shiftedLocalTime_ge_eq hstationary j n u] using hone
          _ = (n + 1 : ℝ≥0∞) * ENNReal.ofReal p := by
            simp [nsmul_eq_mul]
      · intro j hj
        exact measurable_const.indicator
          (measurableSet_shiftedLocalTime_ge j n u)

/-- The parity-correct expectation/counting and Markov step of HLOZ
Proposition 4.4.  The only probabilistic tail input is the one-site estimate
at the origin.  The other probabilistic hypotheses merely package the two
structural facts of the external chain: path parity almost surely, and
translation invariance when restarted at an even time.

The factor `n+1` is the harmless upper bound on the number of possible even
first-visit times through `n` (the paper makes the same estimate on its
rounded external-time horizon). -/
theorem measure_many_even_sites_le_of_one_site
    (μ : Measure (ℕ → Site))
    (hstationary : HasStationaryEvenIncrements μ)
    (hparity : ∀ᵐ s ∂μ, EvenSitesAtEvenTimes s)
    (n : ℕ) (u : ℝ) (B p : ℝ)
    (hB : 0 < B)
    (hone : μ {s | u ≤ (localTime s n (0, 0) : ℝ)} ≤ ENNReal.ofReal p) :
    μ {s | B < ((evenSitesAtLeastReal s n u).card : ℝ)} ≤
      (n + 1 : ℝ≥0∞) * ENNReal.ofReal p / ENNReal.ofReal B := by
  let count : (ℕ → Site) → ℝ≥0∞ :=
    fun s ↦ ∑ j ∈ Finset.range (n + 1),
      if Even j ∧ u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)
      then 1 else 0
  have hcount : Measurable count := by
    apply Finset.measurable_sum
    intro j hjRange
    apply Measurable.ite
    · by_cases hj : Even j
      · simpa only [hj, true_and] using
          (measurableSet_shiftedLocalTime_ge j n u)
      · simp only [hj, false_and, Set.setOf_false]
        exact MeasurableSet.empty
    · exact measurable_const
    · exact measurable_const
  have hcount_eq (s : ℕ → Site) :
      count s = ((evenGoodStartTimes s n u).card : ℝ≥0∞) := by
    simp only [count, evenGoodStartTimes, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> rfl
  have hsubset :
      {s | B < ((evenSitesAtLeastReal s n u).card : ℝ)} ≤ᵐ[μ]
        {s | ENNReal.ofReal B ≤ count s} := by
    filter_upwards [hparity] with s hsParity
    intro hs
    have hcard :=
      card_evenSitesAtLeastReal_le_evenGoodStartTimes s n u hsParity
    have hreal : B ≤ ((evenGoodStartTimes s n u).card : ℝ) :=
      hs.le.trans (by exact_mod_cast hcard)
    have henn := ENNReal.ofReal_le_ofReal hreal
    calc
      ENNReal.ofReal B ≤ ((evenGoodStartTimes s n u).card : ℝ≥0∞) := by
        simpa using henn
      _ = count s := (hcount_eq s).symm
  calc
    μ {s | B < ((evenSitesAtLeastReal s n u).card : ℝ)} ≤
        μ {s | ENNReal.ofReal B ≤ count s} := measure_mono_ae hsubset
    _ ≤ (∫⁻ s, count s ∂μ) / ENNReal.ofReal B :=
      meas_ge_le_lintegral_div hcount.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr hB) ENNReal.ofReal_ne_top
    _ ≤ (n + 1 : ℝ≥0∞) * ENNReal.ofReal p / ENNReal.ofReal B := by
      gcongr
      rw [show count = fun s ↦
          ∑ j ∈ Finset.range (n + 1),
            {t : ℕ → Site |
              Even j ∧
                u ≤ (localTime (shiftedPath t j) n (0, 0) : ℝ)}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s by
        funext s
        apply Finset.sum_congr rfl
        intro j hjRange
        by_cases hgood :
            Even j ∧ u ≤ (localTime (shiftedPath s j) n (0, 0) : ℝ)
        · simp [count, hgood]
        · simp [count, hgood], lintegral_finsetSum]
      · calc
          ∑ j ∈ Finset.range (n + 1),
              ∫⁻ s,
                {t : ℕ → Site |
                  Even j ∧
                    u ≤ (localTime (shiftedPath t j) n (0, 0) : ℝ)}.indicator
                      (fun _ ↦ (1 : ℝ≥0∞)) s ∂μ ≤
              ∑ _j ∈ Finset.range (n + 1), ENNReal.ofReal p := by
                gcongr with j hjRange
                by_cases hj : Even j
                · rw [lintegral_indicator]
                  · rw [lintegral_const]
                    simpa [hj,
                      measure_evenShiftedLocalTime_ge_eq hstationary j n hj u]
                      using hone
                  · simpa only [hj, true_and] using
                      (measurableSet_shiftedLocalTime_ge j n u)
                · simp only [hj, false_and, Set.setOf_false,
                    Set.indicator_empty, lintegral_zero]
                  exact bot_le
          _ = (n + 1 : ℝ≥0∞) * ENNReal.ofReal p := by
            simp [nsmul_eq_mul]
      · intro j hjRange
        by_cases hj : Even j
        · exact measurable_const.indicator <| by
            simpa only [hj, true_and] using
              (measurableSet_shiftedLocalTime_ge j n u)
        · simp only [hj, false_and, Set.setOf_false]
          exact measurable_const.indicator MeasurableSet.empty

/-! ### Source-facing specialization to (2.19) and (4.13) -/

/-- The elementary exponent calculation in the last line of the proof of
HLOZ (4.13).  The displayed hypothesis is precisely the deterministic
logarithmic comparison needed after inserting the one-point estimate
(2.19); all remaining factors, including the rounding loss `(n+1)/n`, are
handled here. -/
theorem prop44_markov_real_ratio_le
    (m n : ℕ) (hn : 1 ≤ n)
    (hlog :
      Real.log 2 +
          8 * Real.log (n : ℝ) ^ (prop44Beta - 1) ≤
        15 * (m : ℝ) ^ prop44RateExponent) :
    ((n + 1 : ℝ) * lemma25ExternalTail n) /
        Real.exp (16 * (m : ℝ) ^ prop44RateExponent) ≤
      Real.exp (-(m : ℝ) ^ prop44RateExponent) := by
  let a : ℝ := (m : ℝ) ^ prop44RateExponent
  let E : ℝ := 8 * Real.log (n : ℝ) ^ (prop44Beta - 1)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hratio : ((n + 1 : ℝ) / (n : ℝ)) ≤ 2 := by
    rw [div_le_iff₀ hnReal]
    norm_num
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hexp : Real.exp (E - 16 * a) ≥ 0 := (Real.exp_pos _).le
  have hrewrite :
      ((n + 1 : ℝ) * lemma25ExternalTail n) / Real.exp (16 * a) =
        ((n + 1 : ℝ) / (n : ℝ)) * Real.exp (E - 16 * a) := by
    rw [lemma25ExternalTail]
    simp only [E, div_eq_mul_inv, Real.exp_sub, mul_assoc]
  rw [show (m : ℝ) ^ prop44RateExponent = a by rfl, hrewrite]
  calc
    ((n + 1 : ℝ) / (n : ℝ)) * Real.exp (E - 16 * a) ≤
        2 * Real.exp (E - 16 * a) :=
      mul_le_mul_of_nonneg_right hratio hexp
    _ = Real.exp (Real.log 2) * Real.exp (E - 16 * a) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (Real.log 2 + (E - 16 * a)) := by
      rw [Real.exp_add]
    _ = Real.exp (Real.log 2 + E - 16 * a) := by ring_nf
    _ ≤ Real.exp (-a) := by
      apply Real.exp_le_exp.mpr
      dsimp only [E, a] at hlog ⊢
      linarith

/-- ENNReal form of `prop44_markov_real_ratio_le`, matching the codomain of
probability measures. -/
theorem prop44_markov_ennreal_ratio_le
    (m n : ℕ) (hn : 1 ≤ n)
    (hlog :
      Real.log 2 +
          8 * Real.log (n : ℝ) ^ (prop44Beta - 1) ≤
        15 * (m : ℝ) ^ prop44RateExponent) :
    (n + 1 : ℝ≥0∞) * ENNReal.ofReal (lemma25ExternalTail n) /
        ENNReal.ofReal (Real.exp (16 * (m : ℝ) ^ prop44RateExponent)) ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) ^ prop44RateExponent)) := by
  have hreal := prop44_markov_real_ratio_le m n hn hlog
  have hnum : (0 : ℝ) ≤ n + 1 := by positivity
  have hden : 0 < Real.exp (16 * (m : ℝ) ^ prop44RateExponent) :=
    Real.exp_pos _
  have hcast : (n + 1 : ℝ≥0∞) = ENNReal.ofReal (n + 1 : ℝ) := by
    rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (Nat.cast_nonneg n) (by norm_num)]
  rw [hcast]
  rw [← ENNReal.ofReal_mul hnum]
  rw [← ENNReal.ofReal_div_of_pos hden]
  exact ENNReal.ofReal_le_ofReal hreal

/-- HLOZ Proposition 4.4, equation (4.13), reduced to its exact one-site
input (2.19).  `hthreshold` and `hlog` are deterministic comparisons for the
rounded value `prop44Psi m`; in particular, no many-site probability bound
is assumed. -/
theorem prop44_many_even_sites_bound_of_lemma25
    (μ : Measure (ℕ → Site))
    (hstationary : HasStationaryEvenIncrements μ)
    (hparity : ∀ᵐ s ∂μ, EvenSitesAtEvenTimes s)
    (m : ℕ)
    (hthreshold :
      lemma25ExternalThreshold (prop44Psi m) ≤ prop44SiteThreshold m)
    (hlog :
      Real.log 2 +
          8 * Real.log (prop44Psi m : ℝ) ^ (prop44Beta - 1) ≤
        15 * (m : ℝ) ^ prop44RateExponent)
    (hone :
      μ {s |
        lemma25ExternalThreshold (prop44Psi m) ≤
          (localTime s (prop44Psi m) (0, 0) : ℝ)} ≤
        ENNReal.ofReal (lemma25ExternalTail (prop44Psi m))) :
    μ {s |
        Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
          ((evenSitesAtLeastReal s (prop44Psi m)
            (prop44SiteThreshold m)).card : ℝ)} ≤
      ENNReal.ofReal
        (Real.exp (-(m : ℝ) ^ prop44RateExponent)) := by
  have honeHigh :
      μ {s |
        prop44SiteThreshold m ≤
          (localTime s (prop44Psi m) (0, 0) : ℝ)} ≤
        ENNReal.ofReal (lemma25ExternalTail (prop44Psi m)) := by
    refine (measure_mono ?_).trans hone
    intro s hs
    exact hthreshold.trans hs
  refine (measure_many_even_sites_le_of_one_site μ hstationary hparity
    (prop44Psi m) (prop44SiteThreshold m)
    (Real.exp (16 * (m : ℝ) ^ prop44RateExponent))
    (lemma25ExternalTail (prop44Psi m)) (Real.exp_pos _) honeHigh).trans ?_
  exact prop44_markov_ennreal_ratio_le m (prop44Psi m)
    (prop44Psi_pos m) hlog

end Erdos1166.HLOZProp44
