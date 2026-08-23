/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410
import ErdosProblems.Erdos1166.Erdos1166HLOZGreenBounds

namespace Erdos1166

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HLOZLemma410Race

open KilledGreen

/-- A finite excursion which starts at `x`, avoids `y`, and makes its first
positive return to `x` at the end of the block. -/
def blockStrictReturnBeforeHit (x y : Site) (n : ℕ) :
    Set (Fin n → Direction) :=
  {η | (∀ r : Fin (n + 1), blockWalkFrom x η r ≠ y) ∧
    blockWalkFrom x η ⟨n, by omega⟩ = x ∧ 0 < n ∧
    ∀ r : Fin (n + 1), 0 < (r : ℕ) → (r : ℕ) < n →
      blockWalkFrom x η r ≠ x}

theorem measurableSet_blockStrictReturnBeforeHit (x y : Site) (n : ℕ) :
    MeasurableSet (blockStrictReturnBeforeHit x y n) :=
  MeasurableSet.of_discrete

theorem iidBlock_zero_preimage_blockStrictReturnBeforeHit
    (x y : Site) (n : ℕ) :
    iidBlock (X := Direction) 0 n ⁻¹' blockStrictReturnBeforeHit x y n =
      strictReturnEvent ({y}ᶜ : Set Site) x n := by
  ext ω
  simp only [Set.mem_preimage, blockStrictReturnBeforeHit, Set.mem_ofPred_eq,
    strictReturnEvent, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨havoidY, hend, hn, hfirst⟩
    refine ⟨?_, ?_, hn, ?_⟩
    · intro r hr
      let r' : Fin (n + 1) := ⟨r, by omega⟩
      rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x n ω r']
      exact havoidY r'
    · rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x n ω ⟨n, by omega⟩]
      exact hend
    · intro r hrpos hrn
      let r' : Fin (n + 1) := ⟨r, by omega⟩
      rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x n ω r']
      exact hfirst r' hrpos hrn
  · rintro ⟨havoidY, hend, hn, hfirst⟩
    refine ⟨?_, ?_, hn, ?_⟩
    · intro r
      rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x n ω r]
      exact havoidY r (Nat.le_of_lt_succ r.isLt)
    · rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x n ω ⟨n, by omega⟩]
      exact hend
    · intro r hrpos hrn
      rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x n ω r]
      exact hfirst r hrpos hrn

theorem finitePi_blockStrictReturnBeforeHit_eq
    (x y : Site) (n : ℕ) :
    (Measure.infinitePi fun _ : Fin n ↦ directionLaw)
        (blockStrictReturnBeforeHit x y n) =
      strictReturnWeight ({y}ᶜ : Set Site) x n := by
  rw [← iidBlock_map directionLaw 0 n]
  rw [Measure.map_apply (measurable_iidBlock 0 n)
    (measurableSet_blockStrictReturnBeforeHit x y n)]
  exact congrArg incrementLaw
    (iidBlock_zero_preimage_blockStrictReturnBeforeHit x y n)

/-- A first hit of `y` at time `n`, with no earlier hit of `y` and no
positive return to the starting point `x` through that time. -/
def firstHitBeforePositiveReturnAt (x y : Site) (n : ℕ) :
    Set (ℕ → Direction) :=
  {ω | walkFrom x ω n = y ∧
    (∀ r, r < n → walkFrom x ω r ≠ y) ∧
    ∀ r, 0 < r → r ≤ n → walkFrom x ω r ≠ x}

theorem measurableSet_firstHitBeforePositiveReturnAt
    (x y : Site) (n : ℕ) :
    MeasurableSet (firstHitBeforePositiveReturnAt x y n) := by
  have hend : MeasurableSet {ω : ℕ → Direction | walkFrom x ω n = y} :=
    measurableSet_eq_fun
      ((measurable_walkFrom_iidHistory x le_rfl).mono
        (ProbabilityTheory.iidHistory_le n) le_rfl) measurable_const
  have havoidY : MeasurableSet
      {ω : ℕ → Direction | ∀ r, r < n → walkFrom x ω r ≠ y} := by
    rw [show {ω : ℕ → Direction | ∀ r, r < n → walkFrom x ω r ≠ y} =
        ⋂ r : ℕ, ⋂ (_ : r < n), {ω | walkFrom x ω r ≠ y} by ext; simp]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      (measurableSet_eq_fun
        ((measurable_walkFrom_iidHistory x hr.le).mono
          (ProbabilityTheory.iidHistory_le n) le_rfl) measurable_const).compl
  have havoidX : MeasurableSet
      {ω : ℕ → Direction |
        ∀ r, 0 < r → r ≤ n → walkFrom x ω r ≠ x} := by
    rw [show {ω : ℕ → Direction |
          ∀ r, 0 < r → r ≤ n → walkFrom x ω r ≠ x} =
        ⋂ r : ℕ, ⋂ (_ : 0 < r), ⋂ (_ : r ≤ n),
          {ω | walkFrom x ω r ≠ x} by ext; simp]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦
      MeasurableSet.iInter fun hr ↦
        (measurableSet_eq_fun
          ((measurable_walkFrom_iidHistory x hr).mono
            (ProbabilityTheory.iidHistory_le n) le_rfl) measurable_const).compl
  exact hend.inter (havoidY.inter havoidX)

/-- The exact off-origin event needed in HLOZ Lemma 4.10: starting at `x`,
the walk hits `y` before its first positive return to `x`. -/
def hitBeforePositiveReturnEvent (x y : Site) : Set (ℕ → Direction) :=
  ⋃ n : ℕ, firstHitBeforePositiveReturnAt x y n

theorem measurableSet_hitBeforePositiveReturnEvent (x y : Site) :
    MeasurableSet (hitBeforePositiveReturnEvent x y) :=
  MeasurableSet.iUnion fun n ↦ measurableSet_firstHitBeforePositiveReturnAt x y n

theorem disjoint_returnBeforeExit_hitBeforePositiveReturn (x y : Site) :
    Disjoint (returnBeforeExitEvent ({y}ᶜ : Set Site) x)
      (hitBeforePositiveReturnEvent x y) := by
  rw [Set.disjoint_left]
  intro ω hreturn hhit
  rcases Set.mem_iUnion.mp hreturn with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hhit with ⟨n, hn⟩
  rcases hk with ⟨hstay, hendX, _hkpos, _hfirstX⟩
  rcases hn with ⟨hendY, _hfirstY, havoidX⟩
  rcases le_total n (k + 1) with hnk | hkn
  · exact (hstay n hnk) hendY
  · exact havoidX (k + 1) (by omega) hkn hendX

/-- The exact missing potential-kernel estimate.  For sites separated by at
most `R`, it asks for a uniform lower bound on hitting the other site before
returning to the starting site. -/
def HasOffOriginHitBeforeReturnLowerBound
    (R : ℕ) (p : ℝ≥0∞) : Prop :=
  ∀ x y : Site, x ≠ y → siteSquaredDistance x y ≤ R ^ 2 →
    p ≤ incrementLaw (hitBeforePositiveReturnEvent x y)

theorem returnBeforeHitProbability_le_one_sub
    {R : ℕ} {p : ℝ≥0∞}
    (hoff : HasOffOriginHitBeforeReturnLowerBound R p)
    {x y : Site} (hxy : x ≠ y)
    (hdist : siteSquaredDistance x y ≤ R ^ 2) :
    incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) ≤ 1 - p := by
  let E := returnBeforeExitEvent ({y}ᶜ : Set Site) x
  let H := hitBeforePositiveReturnEvent x y
  have hpH : p ≤ incrementLaw H := hoff x y hxy hdist
  have hsum : incrementLaw E + incrementLaw H ≤ 1 := by
    calc
      incrementLaw E + incrementLaw H = incrementLaw (E ∪ H) := by
        symm
        exact measure_union
          (disjoint_returnBeforeExit_hitBeforePositiveReturn x y)
          (measurableSet_hitBeforePositiveReturnEvent x y)
      _ ≤ incrementLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hsum' : incrementLaw E + p ≤ 1 :=
    (add_le_add_right hpH (incrementLaw E)).trans hsum
  exact ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hpH.trans
      (by simpa only [measure_univ] using
        (measure_mono (μ := incrementLaw) (Set.subset_univ H))))) hsum'

/-- The post-stopping-time union of all possible finite first-return blocks.
This is an increment-space event because it is the form to which iid restart
applies directly. -/
def incrementReturnBeforeHitAfter
    (τ : (ℕ → Site) → WithTop ℕ) (x y : Site) :
    Set (ℕ → Direction) :=
  ⋃ n : ℕ,
    iidBlockAfter (X := Direction)
      (fun ω ↦ (τ (simpleRandomWalk ω)).untopA) (n + 1) ⁻¹'
        blockStrictReturnBeforeHit x y (n + 1)

/-- Strong Markov at an unbounded stopping time, for one whole
return-before-hit excursion.  This is obtained only from `IIDRestart`, by
summing over the possible finite excursion lengths. -/
theorem incrementLaw_inter_incrementReturnBeforeHitAfter_le_mul
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ)
    {A : Set (ℕ → Site)} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hA_finite : A ⊆ {s | τ s ≠ ⊤}) (x y : Site) :
    incrementLaw
        (simpleRandomWalk ⁻¹' A ∩ incrementReturnBeforeHitAfter τ x y) ≤
      incrementLaw (simpleRandomWalk ⁻¹' A) *
        incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) := by
  rw [incrementReturnBeforeHitAfter, Set.inter_iUnion]
  calc
    incrementLaw
        (⋃ n : ℕ, simpleRandomWalk ⁻¹' A ∩
          iidBlockAfter (X := Direction)
            (fun ω ↦ (τ (simpleRandomWalk ω)).untopA) (n + 1) ⁻¹'
              blockStrictReturnBeforeHit x y (n + 1)) ≤
        ∑' n : ℕ, incrementLaw
          (simpleRandomWalk ⁻¹' A ∩
            iidBlockAfter (X := Direction)
              (fun ω ↦ (τ (simpleRandomWalk ω)).untopA) (n + 1) ⁻¹'
                blockStrictReturnBeforeHit x y (n + 1)) :=
      measure_iUnion_le _
    _ = ∑' n : ℕ, incrementLaw (simpleRandomWalk ⁻¹' A) *
        (Measure.infinitePi fun _ : Fin (n + 1) ↦ directionLaw)
          (blockStrictReturnBeforeHit x y (n + 1)) := by
      apply tsum_congr
      intro n
      exact HLOZFoundation.incrementLaw_inter_blockAfter_stopping_eq_mul
        hτ hA hA_finite (n + 1)
          (measurableSet_blockStrictReturnBeforeHit x y (n + 1))
    _ = incrementLaw (simpleRandomWalk ⁻¹' A) *
        ∑' n : ℕ, strictReturnWeight ({y}ᶜ : Set Site) x (n + 1) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro n
      exact finitePi_blockStrictReturnBeforeHit_eq x y (n + 1)
    _ = incrementLaw (simpleRandomWalk ⁻¹' A) *
        incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) := by
      rw [← returnWeight_eq_measure_returnBeforeExit]
      rfl

/-- On a fiber where the local time at the initial stopping time is `a`, the
`q`-th subsequent return time is the first absolute local-time threshold
`a+q`.  Taking a maximum with `σ` makes the definition a stopping time even
away from that fiber. -/
noncomputable def postReturnLevelTime
    (σ : (ℕ → Site) → WithTop ℕ) (x : Site) (a : ℕ) :
    ℕ → (ℕ → Site) → WithTop ℕ
  | 0 => σ
  | q + 1 => fun s ↦ max (σ s)
      (HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s)

theorem isStoppingTime_postReturnLevelTime
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    (x : Site) (a q : ℕ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (postReturnLevelTime σ x a q) := by
  cases q with
  | zero => simpa [postReturnLevelTime] using hσ
  | succ q =>
      simpa [postReturnLevelTime] using hσ.max
        (HLOZFoundation.isStoppingTime_firstLocalTimeGEAfter
          x (a + q + 1) 0)

theorem postReturnLevelTime_ge
    (σ : (ℕ → Site) → WithTop ℕ) (x : Site) (a q : ℕ) (s : ℕ → Site) :
    σ s ≤ postReturnLevelTime σ x a q s := by
  cases q <;> simp [postReturnLevelTime]

/-- The target hitting time used in the race, starting at `σ`. -/
noncomputable def targetHitAfter
    (σ : (ℕ → Site) → WithTop ℕ) (y : Site) :
    (ℕ → Site) → WithTop ℕ :=
  HLOZFoundation.firstHitAfterStopping {y} σ

theorem isStoppingTime_targetHitAfter
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    (y : Site) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (targetHitAfter σ y) :=
  HLOZFoundation.isStoppingTime_firstHitAfterStopping
    (measurableSet_singleton y) hσ

theorem measurable_stoppedLocalTime
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    (x : Site) :
    Measurable[hσ.measurableSpace]
      (fun s ↦ localTime s (σ s).untopA x) := by
  let u : ℕ → (ℕ → Site) → ℕ := fun n s ↦ localTime s n x
  have hu : StronglyAdapted HLOZFoundation.canonicalFiltration u := by
    intro n
    exact (HLOZFoundation.adapted_localTime x n).stronglyMeasurable
  change Measurable[hσ.measurableSpace] (stoppedValue u σ)
  exact measurable_stoppedValue hu.isStronglyProgressive_of_discrete hσ

theorem measurable_stoppedCoordinate
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ) :
    Measurable[hσ.measurableSpace]
      (fun s ↦ s (σ s).untopA) := by
  let u := HLOZFoundation.coordinateProcess
  have hu : StronglyAdapted HLOZFoundation.canonicalFiltration u :=
    HLOZFoundation.adapted_coordinateProcess.stronglyAdapted
  have hprog := hu.isStronglyProgressive_of_discrete
  change Measurable[hσ.measurableSpace] (stoppedValue u σ)
  exact measurable_stoppedValue hprog hσ

/-- A countable past-measurable fiber fixing the current site, target site,
and current local time at `σ`. -/
def raceBaseFiber
    (σ : (ℕ → Site) → WithTop ℕ) (Y : (ℕ → Site) → Site)
    (x y : Site) (a : ℕ) : Set (ℕ → Site) :=
  {s | σ s ≠ ⊤ ∧ s (σ s).untopA = x ∧ Y s = y ∧
    localTime s (σ s).untopA x = a}

theorem measurableSet_raceBaseFiber
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    {Y : (ℕ → Site) → Site} (hY : Measurable[hσ.measurableSpace] Y)
    (x y : Site) (a : ℕ) :
    MeasurableSet[hσ.measurableSpace] (raceBaseFiber σ Y x y a) := by
  have hfinite : MeasurableSet[hσ.measurableSpace] {s | σ s ≠ ⊤} := by
    exact ((measurableSet_singleton (⊤ : WithTop ℕ)).preimage hσ.measurable).compl
  have hcoord : MeasurableSet[hσ.measurableSpace]
      {s | s (σ s).untopA = x} :=
    measurableSet_eq_fun (measurable_stoppedCoordinate hσ) measurable_const
  have htarget : MeasurableSet[hσ.measurableSpace] {s | Y s = y} :=
    measurableSet_eq_fun hY measurable_const
  have hlocal : MeasurableSet[hσ.measurableSpace]
      {s | localTime s (σ s).untopA x = a} :=
    measurableSet_eq_fun (measurable_stoppedLocalTime hσ x) measurable_const
  rw [show raceBaseFiber σ Y x y a =
      {s | σ s ≠ ⊤} ∩ ({s | s (σ s).untopA = x} ∩
        ({s | Y s = y} ∩ {s | localTime s (σ s).untopA x = a})) by
    ext s
    simp [raceBaseFiber]]
  exact hfinite.inter (hcoord.inter (htarget.inter hlocal))

/-- The fixed-fiber event that the `q`-th subsequent return to `x` occurs
before the post-`σ` hit of `y`. -/
def fixedFiberReturnRaceEvent
    (σ : (ℕ → Site) → WithTop ℕ) (Y : (ℕ → Site) → Site)
    (x y : Site) (a q : ℕ) : Set (ℕ → Site) :=
  raceBaseFiber σ Y x y a ∩
    {s | postReturnLevelTime σ x a q s < targetHitAfter σ y s}

theorem measurableSet_fixedFiberReturnRaceEvent
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    {Y : (ℕ → Site) → Site} (hY : Measurable[hσ.measurableSpace] Y)
    (x y : Site) (a q : ℕ) :
    MeasurableSet[(isStoppingTime_postReturnLevelTime hσ x a q).measurableSpace]
      (fixedFiberReturnRaceEvent σ Y x y a q) := by
  let ρ := postReturnLevelTime σ x a q
  have hρ := isStoppingTime_postReturnLevelTime hσ x a q
  have hbaseσ := measurableSet_raceBaseFiber hσ hY x y a
  have hbaseρ : MeasurableSet[hρ.measurableSpace]
      (raceBaseFiber σ Y x y a) :=
    (IsStoppingTime.measurableSpace_mono hσ hρ
      (postReturnLevelTime_ge σ x a q)) _ hbaseσ
  have htarget := isStoppingTime_targetHitAfter hσ y
  have hle : MeasurableSet[hρ.measurableSpace]
      {s | targetHitAfter σ y s ≤ ρ s} :=
    IsStoppingTime.measurableSet_stopping_time_le htarget hρ
  have hlt : MeasurableSet[hρ.measurableSpace]
      {s | ρ s < targetHitAfter σ y s} := by
    rw [show {s | ρ s < targetHitAfter σ y s} =
        {s | ¬ targetHitAfter σ y s ≤ ρ s} by
      ext s
      simp]
    exact hle.compl
  exact hbaseρ.inter hlt

theorem fixedFiberReturnRaceEvent_time_finite
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} :
    fixedFiberReturnRaceEvent σ Y x y a q ⊆
      {s | postReturnLevelTime σ x a q s ≠ ⊤} := by
  intro s hs htop
  have hlt := hs.2
  change postReturnLevelTime σ x a q s < targetHitAfter σ y s at hlt
  rw [htop] at hlt
  exact not_top_lt hlt

private theorem firstLocalTimeGEAfter_zero_ge_stopping_on_base
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} {s : ℕ → Site}
    (hbase : s ∈ raceBaseFiber σ Y x y a) :
    σ s ≤ HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s := by
  let U := HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s
  by_cases hUtop : U = ⊤
  · simp [U, hUtop]
  · have hσtop : σ s ≠ ⊤ := hbase.1
    let t : ℕ := (σ s).untopA
    let u : ℕ := U.untopA
    have hσcoe : (t : WithTop ℕ) = σ s := by
      dsimp only [t]
      rw [WithTop.untopA_eq_untop hσtop]
      exact WithTop.coe_untop _ hσtop
    have hUcoe : (u : WithTop ℕ) = U := by
      dsimp only [u]
      rw [WithTop.untopA_eq_untop hUtop]
      exact WithTop.coe_untop _ hUtop
    change σ s ≤ U
    rw [← hσcoe, ← hUcoe]
    apply WithTop.coe_le_coe.mpr
    by_contra hnot
    have hut : u < t := Nat.lt_of_not_ge hnot
    have hmem : a + q + 1 ≤ localTime s u x := by
      have := hittingAfter_mem_set_of_ne_top
        (u := fun n s ↦ localTime s n x) (s := Set.Ici (a + q + 1))
        (n := 0) (ω := s) hUtop
      change a + q + 1 ≤ localTime s U.untopA x at this
      simpa [u] using this
    have hmono : localTime s u x ≤ localTime s t x :=
      localTime_mono hut.le x
    have hlocal : localTime s t x = a := by
      simpa [t] using hbase.2.2.2
    omega

theorem postReturnLevelTime_succ_eq_threshold_on_base
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} {s : ℕ → Site}
    (hbase : s ∈ raceBaseFiber σ Y x y a) :
    postReturnLevelTime σ x a (q + 1) s =
      HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s := by
  rw [postReturnLevelTime]
  exact max_eq_right
    (firstLocalTimeGEAfter_zero_ge_stopping_on_base hbase)

private theorem localTime_and_position_at_firstLocalTimeGEAfter_zero
    {x : Site} {b : ℕ} {s : ℕ → Site}
    (hfinite : HLOZFoundation.firstLocalTimeGEAfter x b 0 s ≠ ⊤)
    (hpos : 0 < (HLOZFoundation.firstLocalTimeGEAfter x b 0 s).untopA) :
    localTime s
        (HLOZFoundation.firstLocalTimeGEAfter x b 0 s).untopA x = b ∧
      s (HLOZFoundation.firstLocalTimeGEAfter x b 0 s).untopA = x := by
  let U := HLOZFoundation.firstLocalTimeGEAfter x b 0 s
  let u : ℕ := U.untopA
  have huPos : 0 < u := by simpa [u, U] using hpos
  have hUcoe : (u : WithTop ℕ) = U := by
    dsimp only [u, U]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have hmem : b ≤ localTime s u x := by
    have := hittingAfter_mem_set_of_ne_top
      (u := fun n s ↦ localTime s n x) (s := Set.Ici b)
      (n := 0) (ω := s) hfinite
    simpa [HLOZFoundation.firstLocalTimeGEAfter, U, u] using this
  let v : ℕ := u - 1
  have hvSucc : v + 1 = u := by
    dsimp only [v]
    exact Nat.sub_add_cancel (by omega)
  have hvU : (v : WithTop ℕ) < U := by
    rw [← hUcoe]
    apply WithTop.coe_lt_coe.mpr
    simpa [v] using Nat.sub_lt huPos (by omega : 0 < (1 : ℕ))
  have hvnot : localTime s v x < b := by
    have := notMem_of_lt_hittingAfter
      (u := fun n s ↦ localTime s n x) (s := Set.Ici b)
      (n := 0) (ω := s) hvU (Nat.zero_le v)
    change localTime s v x ∉ Set.Ici b at this
    simpa only [Set.mem_Ici, not_le] using this
  have hstep := localTime_succ s v x
  rw [hvSucc] at hstep
  have heq : localTime s u x = b := by
    split_ifs at hstep <;> omega
  refine ⟨heq, ?_⟩
  by_contra hne
  rw [if_neg hne, add_zero] at hstep
  omega

theorem postReturnLevelTime_localTime_position_on_base
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} {s : ℕ → Site}
    (hbase : s ∈ raceBaseFiber σ Y x y a)
    (hfinite : postReturnLevelTime σ x a q s ≠ ⊤) :
    localTime s (postReturnLevelTime σ x a q s).untopA x = a + q ∧
      s (postReturnLevelTime σ x a q s).untopA = x := by
  cases q with
  | zero =>
      simp only [postReturnLevelTime, Nat.add_zero]
      exact ⟨hbase.2.2.2, hbase.2.1⟩
  | succ q =>
      have heq := postReturnLevelTime_succ_eq_threshold_on_base
        (q := q) hbase
      have hthresholdFinite :
          HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s ≠ ⊤ := by
        simpa [heq] using hfinite
      have hstrict : σ s <
          HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s := by
        have hle := firstLocalTimeGEAfter_zero_ge_stopping_on_base
          (q := q) hbase
        apply lt_of_le_of_ne hle
        intro heqTime
        have hmem : a + q + 1 ≤
            localTime s (σ s).untopA x := by
          have hm := hittingAfter_mem_set_of_ne_top
            (u := fun n s ↦ localTime s n x) (s := Set.Ici (a + q + 1))
            (n := 0) (ω := s) hthresholdFinite
          have hu :
              (HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s).untopA =
                (σ s).untopA := congrArg WithTop.untopA heqTime.symm
          change a + q + 1 ≤ localTime s
            (HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s).untopA x at hm
          simpa only [hu] using hm
        rw [hbase.2.2.2] at hmem
        omega
      have hpos : 0 <
          (HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s).untopA := by
        have hσnonneg : (0 : WithTop ℕ) ≤ σ s := bot_le
        have hzeroLt : (0 : WithTop ℕ) <
            HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s :=
          hσnonneg.trans_lt hstrict
        have hcoe :
            (((HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s).untopA : ℕ) :
              WithTop ℕ) =
              HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s := by
          rw [WithTop.untopA_eq_untop hthresholdFinite]
          exact WithTop.coe_untop _ hthresholdFinite
        rw [← hcoe] at hzeroLt
        exact WithTop.coe_lt_coe.mp hzeroLt
      have h := localTime_and_position_at_firstLocalTimeGEAfter_zero
        hthresholdFinite hpos
      simpa [heq, Nat.add_assoc] using h

theorem postReturnLevelTime_le_succ_on_base
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} {s : ℕ → Site}
    (hbase : s ∈ raceBaseFiber σ Y x y a)
    (hnextFinite : postReturnLevelTime σ x a (q + 1) s ≠ ⊤) :
    postReturnLevelTime σ x a q s ≤
      postReturnLevelTime σ x a (q + 1) s := by
  cases q with
  | zero =>
      change σ s ≤ postReturnLevelTime σ x a 1 s
      exact postReturnLevelTime_ge σ x a 1 s
  | succ q =>
      let next := postReturnLevelTime σ x a (q + 2) s
      have hnextCount := postReturnLevelTime_localTime_position_on_base
        hbase hnextFinite
      have hnextCoe : (next.untopA : WithTop ℕ) = next := by
        dsimp only [next]
        rw [WithTop.untopA_eq_untop hnextFinite]
        exact WithTop.coe_untop _ hnextFinite
      have hthresholdLe :
          HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s ≤ next := by
        have hle : HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s ≤
            (next.untopA : WithTop ℕ) := by
          apply hittingAfter_le_of_mem (Nat.zero_le _)
          change a + q + 1 ≤ localTime s next.untopA x
          have hcount : localTime s next.untopA x = a + (q + 2) := by
            simpa [next, Nat.add_assoc] using hnextCount.1
          rw [hcount]
          omega
        exact hle.trans_eq hnextCoe
      rw [postReturnLevelTime, postReturnLevelTime]
      exact max_le
        (postReturnLevelTime_ge σ x a (q + 2) s)
        hthresholdLe

theorem postReturnLevelTime_lt_succ_on_base
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} {s : ℕ → Site}
    (hbase : s ∈ raceBaseFiber σ Y x y a)
    (hnextFinite : postReturnLevelTime σ x a (q + 1) s ≠ ⊤) :
    postReturnLevelTime σ x a q s <
      postReturnLevelTime σ x a (q + 1) s := by
  have hle := postReturnLevelTime_le_succ_on_base hbase hnextFinite
  apply lt_of_le_of_ne hle
  intro heq
  have hprevFinite : postReturnLevelTime σ x a q s ≠ ⊤ := by
    intro htop
    apply hnextFinite
    rw [← heq, htop]
  have hprev := postReturnLevelTime_localTime_position_on_base
    hbase hprevFinite
  have hnext := postReturnLevelTime_localTime_position_on_base
    hbase hnextFinite
  have hUntop :
      (postReturnLevelTime σ x a q s).untopA =
        (postReturnLevelTime σ x a (q + 1) s).untopA :=
    congrArg WithTop.untopA heq
  rw [hUntop] at hprev
  omega

/-- One more successful return-before-hit race is one fresh strict-return
block after the preceding return time. -/
theorem fixedFiberReturnRaceEvent_succ_preimage_subset
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site}
    {x y : Site} {a q : ℕ} :
    simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a (q + 1) ⊆
      simpleRandomWalk ⁻¹' fixedFiberReturnRaceEvent σ Y x y a q ∩
        incrementReturnBeforeHitAfter
          (postReturnLevelTime σ x a q) x y := by
  intro ω hnext
  let s := simpleRandomWalk ω
  let prev := postReturnLevelTime σ x a q s
  let next := postReturnLevelTime σ x a (q + 1) s
  have hbase : s ∈ raceBaseFiber σ Y x y a := hnext.1
  have hnextLt : next < targetHitAfter σ y s := hnext.2
  have hnextFinite : next ≠ ⊤ := ne_top_of_lt hnextLt
  have hprevNext : prev < next :=
    postReturnLevelTime_lt_succ_on_base hbase hnextFinite
  have hprevFinite : prev ≠ ⊤ := ne_top_of_lt hprevNext
  have hprevLt : prev < targetHitAfter σ y s := hprevNext.trans hnextLt
  refine ⟨⟨hbase, hprevLt⟩, ?_⟩
  let t : ℕ := prev.untopA
  let u : ℕ := next.untopA
  have hprevCoe : (t : WithTop ℕ) = prev := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hprevFinite]
    exact WithTop.coe_untop _ hprevFinite
  have hnextCoe : (u : WithTop ℕ) = next := by
    dsimp only [u]
    rw [WithTop.untopA_eq_untop hnextFinite]
    exact WithTop.coe_untop _ hnextFinite
  have htu : t < u := by
    exact WithTop.coe_lt_coe.mp (hprevCoe.trans_lt (hprevNext.trans_eq hnextCoe.symm))
  let d : ℕ := u - t
  have hdpos : 0 < d := by dsimp only [d]; omega
  let n : ℕ := d - 1
  have hnSucc : n + 1 = d := by
    dsimp only [n]
    exact Nat.sub_add_cancel (by omega)
  rw [incrementReturnBeforeHitAfter]
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  change iidBlockAfter (X := Direction)
      (fun ω ↦ (postReturnLevelTime σ x a q
        (simpleRandomWalk ω)).untopA) (n + 1) ω ∈
      blockStrictReturnBeforeHit x y (n + 1)
  rw [hnSucc]
  have hprevState := postReturnLevelTime_localTime_position_on_base
    hbase hprevFinite
  have hnextState := postReturnLevelTime_localTime_position_on_base
    hbase hnextFinite
  have htd : t + d = u := by dsimp only [d]; omega
  have hblock (r : Fin (d + 1)) :
      blockWalkFrom x
          (iidBlockAfter (X := Direction)
            (fun ω ↦ (postReturnLevelTime σ x a q
              (simpleRandomWalk ω)).untopA) d ω) r =
        s (t + r) := by
    have hstart : walkFrom 0 ω t = x := by
      simpa [walkFrom, s, t, prev] using hprevState.2
    have hblockEq :
        iidBlockAfter (X := Direction)
            (fun ω ↦ (postReturnLevelTime σ x a q
              (simpleRandomWalk ω)).untopA) d ω =
          iidBlock (X := Direction) t d ω := by
      funext i
      simp [iidBlockAfter, iidBlock, t, prev, s]
    have heq := blockWalkFrom_iidBlock_eq_walkFrom 0 t d ω r
    rw [hstart] at heq
    rw [hblockEq]
    simpa [s, walkFrom] using heq
  refine ⟨?_, ?_, hdpos, ?_⟩
  · intro r
    rw [hblock r]
    have hσfinite : σ s ≠ ⊤ := hbase.1
    have hσt : (σ s).untopA ≤ t := by
      have hle := postReturnLevelTime_ge σ x a q s
      have hσcoe : (((σ s).untopA : ℕ) : WithTop ℕ) = σ s := by
        rw [WithTop.untopA_eq_untop hσfinite]
        exact WithTop.coe_untop _ hσfinite
      exact WithTop.coe_le_coe.mp (hσcoe.trans_le (hle.trans_eq hprevCoe.symm))
    have hjle : t + (r : ℕ) ≤ u := by omega
    have hjTarget : ((t + (r : ℕ) : ℕ) : WithTop ℕ) <
        targetHitAfter σ y s := by
      exact (WithTop.coe_le_coe.mpr hjle).trans_lt
        (hnextCoe.trans_lt hnextLt)
    have hnot := notMem_of_lt_hittingAfter
      (u := HLOZFoundation.coordinateProcess) (s := ({y} : Set Site))
      (n := (σ s).untopA) (ω := s) ?_ (hσt.trans (Nat.le_add_right t r))
    · simpa [HLOZFoundation.coordinateProcess] using hnot
    · simpa [targetHitAfter, HLOZFoundation.firstHitAfterStopping,
        hσfinite] using hjTarget
  · rw [hblock ⟨d, by omega⟩, htd]
    simpa [u, next] using hnextState.2
  · intro r hrpos hrlt
    rw [hblock r]
    intro hrx
    have hjlt : t + (r : ℕ) < u := by omega
    have hlocalGrow : localTime s t x < localTime s (t + (r : ℕ)) x :=
      localTime_lt_of_visit_Ioc s x (by omega) le_rfl hrx
    have hthresholdEq := postReturnLevelTime_succ_eq_threshold_on_base
      (q := q) hbase
    have hjThreshold : ((t + (r : ℕ) : ℕ) : WithTop ℕ) <
        HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s := by
      calc
        ((t + (r : ℕ) : ℕ) : WithTop ℕ) < next := by
          rw [← hnextCoe]
          exact WithTop.coe_lt_coe.mpr hjlt
        _ = HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s :=
          hthresholdEq
    have hbelow := notMem_of_lt_hittingAfter
      (u := fun n s ↦ localTime s n x) (s := Set.Ici (a + q + 1))
      (n := 0) (ω := s) hjThreshold (Nat.zero_le _)
    have hbelow' : localTime s (t + (r : ℕ)) x < a + q + 1 := by
      change localTime s (t + (r : ℕ)) x ∉ Set.Ici (a + q + 1) at hbelow
      simpa only [Set.mem_Ici, not_le] using hbelow
    have hprevLocal : localTime s t x = a + q := by
      simpa [t, prev] using hprevState.1
    omega

theorem measure_fixedFiberReturnRaceEvent_succ_le_mul
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    {Y : (ℕ → Site) → Site} (hY : Measurable[hσ.measurableSpace] Y)
    (x y : Site) (a q : ℕ) :
    incrementLaw (simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a (q + 1)) ≤
      incrementLaw (simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a q) *
        incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) := by
  let ρ := postReturnLevelTime σ x a q
  have hρ := isStoppingTime_postReturnLevelTime hσ x a q
  have hA := measurableSet_fixedFiberReturnRaceEvent hσ hY x y a q
  calc
    incrementLaw (simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a (q + 1)) ≤
      incrementLaw
        (simpleRandomWalk ⁻¹' fixedFiberReturnRaceEvent σ Y x y a q ∩
          incrementReturnBeforeHitAfter ρ x y) :=
      measure_mono fixedFiberReturnRaceEvent_succ_preimage_subset
    _ ≤ incrementLaw (simpleRandomWalk ⁻¹'
          fixedFiberReturnRaceEvent σ Y x y a q) *
        incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) :=
      incrementLaw_inter_incrementReturnBeforeHitAfter_le_mul
        hρ hA fixedFiberReturnRaceEvent_time_finite x y

theorem measure_fixedFiberReturnRaceEvent_le_geometric
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    {Y : (ℕ → Site) → Site} (hY : Measurable[hσ.measurableSpace] Y)
    (x y : Site) (a q : ℕ) :
    incrementLaw (simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a q) ≤
      incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a) *
        (incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x)) ^ q := by
  induction q with
  | zero =>
      simpa using measure_mono
        (Set.preimage_mono Set.inter_subset_left :
          simpleRandomWalk ⁻¹' fixedFiberReturnRaceEvent σ Y x y a 0 ⊆
            simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a)
  | succ q ih =>
      calc
        incrementLaw (simpleRandomWalk ⁻¹'
            fixedFiberReturnRaceEvent σ Y x y a (q + 1)) ≤
          incrementLaw (simpleRandomWalk ⁻¹'
            fixedFiberReturnRaceEvent σ Y x y a q) *
              incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) :=
          measure_fixedFiberReturnRaceEvent_succ_le_mul hσ hY x y a q
        _ ≤ (incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a) *
              (incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x)) ^ q) *
              incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x) := by
          exact mul_le_mul_left ih _
        _ = incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a) *
              (incrementLaw (returnBeforeExitEvent ({y}ᶜ : Set Site) x)) ^ (q + 1) := by
          rw [pow_succ]
          ac_rfl

theorem measure_fixedFiberReturnRaceEvent_le_one_sub_pow
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    {Y : (ℕ → Site) → Site} (hY : Measurable[hσ.measurableSpace] Y)
    {R : ℕ} {p : ℝ≥0∞}
    (hoff : HasOffOriginHitBeforeReturnLowerBound R p)
    {x y : Site} (hxy : x ≠ y)
    (hdist : siteSquaredDistance x y ≤ R ^ 2)
    (a q : ℕ) :
    incrementLaw (simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a q) ≤
      incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a) *
        (1 - p) ^ q := by
  refine (measure_fixedFiberReturnRaceEvent_le_geometric
    hσ hY x y a q).trans ?_
  exact mul_le_mul_right (pow_le_pow_left'
    (returnBeforeHitProbability_le_one_sub hoff hxy hdist) q) _

/-- The source race event is covered by the countable fibers used in the
geometric iteration.  The extra index `a` records the local time at `σ`. -/
theorem hlozPostHitRaceEvent_subset_iUnion_fixedFiber
    (m k : ℕ) (σ : (ℕ → Site) → WithTop ℕ) (q : ℕ) :
    hlozPostHitRaceEvent m k σ q ⊆
      ⋃ x : Site, ⋃ y : Site, ⋃ a : ℕ,
        fixedFiberReturnRaceEvent σ (fun s ↦ levelCreationSite s m k)
          x y a q := by
  intro s hs
  rcases hs with ⟨hσfinite, hRace⟩
  let t : ℕ := (σ s).untopA
  let x : Site := s t
  let y : Site := levelCreationSite s m k
  let a : ℕ := localTime s t x
  let H : WithTop ℕ := postNthHitTime x q t s
  have hHlt : H < postHitSiteTime y t s := by
    simpa [H, x, y, t] using hRace
  have hHfinite : H ≠ ⊤ := ne_top_of_lt hHlt
  have hσcoe : (t : WithTop ℕ) = σ s := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hσfinite]
    exact WithTop.coe_untop _ hσfinite
  have htH : (t : WithTop ℕ) ≤ H := by
    exact le_hittingAfter s
  let h : ℕ := H.untopA
  have hHcoe : (h : WithTop ℕ) = H := by
    dsimp only [h]
    rw [WithTop.untopA_eq_untop hHfinite]
    exact WithTop.coe_untop _ hHfinite
  have hth : t ≤ h :=
    WithTop.coe_le_coe.mp (htH.trans_eq hHcoe.symm)
  have hHmem : localTime s h x - localTime s t x = q := by
    have hm := hittingAfter_mem_set_of_ne_top
      (u := fun j s ↦ localTime s j x - localTime s t x)
      (s := ({q} : Set ℕ)) (n := t) (ω := s) hHfinite
    change localTime s H.untopA x - localTime s t x = q at hm
    simpa [h] using hm
  have hlocalH : localTime s h x = a + q := by
    have hmono := localTime_mono (s := s) hth x
    dsimp only [a]
    omega
  have hρH : postReturnLevelTime σ x a q s ≤ H := by
    cases q with
    | zero =>
        simpa [postReturnLevelTime] using hσcoe.symm.trans_le htH
    | succ q =>
        have hthreshold :
            HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s ≤ H := by
          have hle :
              HLOZFoundation.firstLocalTimeGEAfter x (a + q + 1) 0 s ≤
                (h : WithTop ℕ) := by
            apply hittingAfter_le_of_mem (Nat.zero_le _)
            change a + q + 1 ≤ localTime s h x
            simpa only [Nat.add_assoc] using le_of_eq hlocalH.symm
          exact hle.trans_eq hHcoe
        rw [postReturnLevelTime]
        exact max_le (hσcoe.symm.trans_le htH) hthreshold
  have htargetEq : targetHitAfter σ y s = postHitSiteTime y t s := by
    simp [targetHitAfter, HLOZFoundation.firstHitAfterStopping,
      postHitSiteTime, HLOZFoundation.firstHitAfter, hσfinite, t]
  simp only [Set.mem_iUnion]
  refine ⟨x, y, a, ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hσfinite, rfl, rfl, rfl⟩
  · change postReturnLevelTime σ x a q s < targetHitAfter σ y s
    rw [htargetEq]
    exact hρH.trans_lt hHlt

theorem iUnion_fixedFiber_subset_hlozPostHitRaceEvent
    (m k : ℕ) (σ : (ℕ → Site) → WithTop ℕ) (q : ℕ) :
    (⋃ x : Site, ⋃ y : Site, ⋃ a : ℕ,
        fixedFiberReturnRaceEvent σ (fun s ↦ levelCreationSite s m k)
          x y a q) ⊆ hlozPostHitRaceEvent m k σ q := by
  intro s hs
  simp only [Set.mem_iUnion] at hs
  rcases hs with ⟨x, y, a, hfixed⟩
  rcases hfixed with ⟨hbase, hρTarget⟩
  rcases hbase with ⟨hσfinite, hx, hy, ha⟩
  have hbase' : s ∈ raceBaseFiber σ
      (fun s ↦ levelCreationSite s m k) x y a :=
    ⟨hσfinite, hx, hy, ha⟩
  change postReturnLevelTime σ x a q s < targetHitAfter σ y s at hρTarget
  let t : ℕ := (σ s).untopA
  let ρ := postReturnLevelTime σ x a q s
  have hρfinite : ρ ≠ ⊤ := ne_top_of_lt hρTarget
  have hρstate := postReturnLevelTime_localTime_position_on_base
    hbase' hρfinite
  have hσρ : σ s ≤ ρ := postReturnLevelTime_ge σ x a q s
  have hσcoe : (t : WithTop ℕ) = σ s := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hσfinite]
    exact WithTop.coe_untop _ hσfinite
  have hρcoe : (ρ.untopA : WithTop ℕ) = ρ := by
    rw [WithTop.untopA_eq_untop hρfinite]
    exact WithTop.coe_untop _ hρfinite
  have htρ : t ≤ ρ.untopA :=
    WithTop.coe_le_coe.mp (hσcoe.trans_le (hσρ.trans_eq hρcoe.symm))
  have hinc : localTime s ρ.untopA x - localTime s t x = q := by
    have hstart : localTime s t x = a := by simpa [t] using ha
    have hfinish : localTime s ρ.untopA x = a + q := hρstate.1
    rw [hstart, hfinish]
    omega
  have hpostLe : postNthHitTime x q t s ≤ ρ := by
    have hle : postNthHitTime x q t s ≤ (ρ.untopA : WithTop ℕ) := by
      apply hittingAfter_le_of_mem htρ
      simpa only [Set.mem_singleton_iff] using hinc
    exact hle.trans_eq hρcoe
  have htargetEq : targetHitAfter σ y s = postHitSiteTime y t s := by
    simp [targetHitAfter, HLOZFoundation.firstHitAfterStopping,
      postHitSiteTime, HLOZFoundation.firstHitAfter, hσfinite, t]
  refine ⟨hσfinite, ?_⟩
  simpa [t, hx, hy, htargetEq] using hpostLe.trans_lt hρTarget

theorem hlozPostHitRaceEvent_eq_iUnion_fixedFiber
    (m k : ℕ) (σ : (ℕ → Site) → WithTop ℕ) (q : ℕ) :
    hlozPostHitRaceEvent m k σ q =
      ⋃ x : Site, ⋃ y : Site, ⋃ a : ℕ,
        fixedFiberReturnRaceEvent σ (fun s ↦ levelCreationSite s m k)
          x y a q :=
  Set.Subset.antisymm
    (hlozPostHitRaceEvent_subset_iUnion_fixedFiber m k σ q)
    (iUnion_fixedFiber_subset_hlozPostHitRaceEvent m k σ q)

theorem measurableSet_hlozPostHitRaceEvent
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    (m k q : ℕ)
    (hY : Measurable[hσ.measurableSpace]
      (fun s ↦ levelCreationSite s m k)) :
    MeasurableSet (hlozPostHitRaceEvent m k σ q) := by
  rw [hlozPostHitRaceEvent_eq_iUnion_fixedFiber]
  exact MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun y ↦
    MeasurableSet.iUnion fun a ↦
      (isStoppingTime_postReturnLevelTime hσ x a q).measurableSpace_le _
        (measurableSet_fixedFiberReturnRaceEvent hσ hY x y a q)

theorem fixedFiberReturnRaceEvent_eq_empty_of_eq
    (σ : (ℕ → Site) → WithTop ℕ) (Y : (ℕ → Site) → Site)
    (x y : Site) (hxy : x = y) (a q : ℕ) :
    fixedFiberReturnRaceEvent σ Y x y a q = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hσfinite, hx, _hy, _ha⟩, hrace⟩
  have htargetLe : targetHitAfter σ y s ≤ σ s := by
    let t : ℕ := (σ s).untopA
    have hσcoe : (t : WithTop ℕ) = σ s := by
      dsimp only [t]
      rw [WithTop.untopA_eq_untop hσfinite]
      exact WithTop.coe_untop _ hσfinite
    have hhit : HLOZFoundation.firstHitAfter {y} t s ≤ (t : WithTop ℕ) := by
      apply hittingAfter_le_of_mem (Nat.le_refl t)
      simpa [Set.mem_singleton_iff, HLOZFoundation.coordinateProcess, t] using
        hx.trans hxy
    simpa [targetHitAfter, HLOZFoundation.firstHitAfterStopping,
      HLOZFoundation.firstHitAfter, hσfinite, hσcoe] using hhit
  exact (not_lt_of_ge (postReturnLevelTime_ge σ x a q s))
    (hrace.trans_le htargetLe)

theorem pairwise_disjoint_preimage_raceBaseFiber
    {σ : (ℕ → Site) → WithTop ℕ} {Y : (ℕ → Site) → Site} :
    Pairwise fun z z' : Site × (Site × ℕ) ↦
      Disjoint (simpleRandomWalk ⁻¹'
        raceBaseFiber σ Y z.1 z.2.1 z.2.2)
        (simpleRandomWalk ⁻¹'
          raceBaseFiber σ Y z'.1 z'.2.1 z'.2.2) := by
  rintro ⟨x, y, a⟩ ⟨x', y', a'⟩ hne
  rw [Set.disjoint_left]
  intro ω h h'
  rcases h with ⟨_hfinite, hx, hy, ha⟩
  rcases h' with ⟨_hfinite', hx', hy', ha'⟩
  apply hne
  have hxx : x = x' := hx.symm.trans hx'
  subst x'
  have hyy : y = y' := hy.symm.trans hy'
  subst y'
  have haa : a = a' := ha.symm.trans ha'
  subst a'
  rfl

/-- The complete geometric-race deduction, conditional only on the exact
off-origin hitting inequality isolated above.  All stopping-time,
strong-Markov, and countable-fiber steps are included here. -/
theorem simpleRandomWalkLaw_hlozPostHitRaceEvent_le_one_sub_pow
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    (m k q R : ℕ) (p : ℝ≥0∞)
    (hY : Measurable[hσ.measurableSpace]
      (fun s ↦ levelCreationSite s m k))
    (hgeom : ∀ s, σ s ≠ ⊤ →
      siteSquaredDistance (s (σ s).untopA) (levelCreationSite s m k) ≤ R ^ 2)
    (hoff : HasOffOriginHitBeforeReturnLowerBound R p) :
    simpleRandomWalkLaw (hlozPostHitRaceEvent m k σ q) ≤ (1 - p) ^ q := by
  let Y : (ℕ → Site) → Site := fun s ↦ levelCreationSite s m k
  let B : Site × (Site × ℕ) → Set (ℕ → Direction) := fun z ↦
    simpleRandomWalk ⁻¹' raceBaseFiber σ Y z.1 z.2.1 z.2.2
  have hBmeas : ∀ z, MeasurableSet (B z) := by
    intro z
    rcases z with ⟨x, y, a⟩
    apply MeasurableSet.preimage
    · exact hσ.measurableSpace_le _
        (measurableSet_raceBaseFiber hσ hY x y a)
    · exact measurable_simpleRandomWalk
  have hBsum : ∑' z, incrementLaw (B z) ≤ 1 := by
    simpa only [measure_univ] using
      (tsum_measure_le_measure_univ (μ := incrementLaw) (s := B)
        (fun z ↦ (hBmeas z).nullMeasurableSet)
        (fun i j hij ↦
          (pairwise_disjoint_preimage_raceBaseFiber
            (σ := σ) (Y := Y) hij).aedisjoint))
  have hfiber : ∀ x y a,
      incrementLaw (simpleRandomWalk ⁻¹'
        fixedFiberReturnRaceEvent σ Y x y a q) ≤
      incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a) *
        (1 - p) ^ q := by
    intro x y a
    by_cases hxy : x = y
    · rw [fixedFiberReturnRaceEvent_eq_empty_of_eq σ Y x y hxy a q]
      simp only [Set.preimage_empty, measure_empty, zero_le]
    · by_cases hbase : (raceBaseFiber σ Y x y a).Nonempty
      · rcases hbase with ⟨s, hs⟩
        have hdist := hgeom s hs.1
        change siteSquaredDistance (s (σ s).untopA) (Y s) ≤ R ^ 2 at hdist
        have hdist' : siteSquaredDistance x y ≤ R ^ 2 := by
          simpa [hs.2.1, hs.2.2.1] using hdist
        exact measure_fixedFiberReturnRaceEvent_le_one_sub_pow
          hσ hY hoff hxy hdist' a q
      · have hempty : raceBaseFiber σ Y x y a = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hbase
        have hevent : fixedFiberReturnRaceEvent σ Y x y a q = ∅ := by
          rw [fixedFiberReturnRaceEvent, hempty, Set.empty_inter]
        rw [hevent, hempty]
        simp
  have hmeas := measurableSet_hlozPostHitRaceEvent hσ m k q hY
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk hmeas,
    hlozPostHitRaceEvent_eq_iUnion_fixedFiber]
  simp only [Set.preimage_iUnion]
  calc
    incrementLaw (⋃ x, ⋃ y, ⋃ a,
        simpleRandomWalk ⁻¹' fixedFiberReturnRaceEvent σ Y x y a q) ≤
        ∑' x, ∑' y, ∑' a,
          incrementLaw (simpleRandomWalk ⁻¹'
            fixedFiberReturnRaceEvent σ Y x y a q) :=
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun x ↦
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun y ↦
          measure_iUnion_le _))
    _ ≤ ∑' x, ∑' y, ∑' a,
          incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a) *
            (1 - p) ^ q :=
      ENNReal.tsum_le_tsum fun x ↦ ENNReal.tsum_le_tsum fun y ↦
        ENNReal.tsum_le_tsum fun a ↦ hfiber x y a
    _ = (∑' x, ∑' y, ∑' a,
          incrementLaw (simpleRandomWalk ⁻¹' raceBaseFiber σ Y x y a)) *
            (1 - p) ^ q := by
      simp only [ENNReal.tsum_mul_right]
    _ = (∑' z, incrementLaw (B z)) * (1 - p) ^ q := by
      apply congrArg (fun u ↦ u * (1 - p) ^ q)
      have houter :
          (∑' z : Site × (Site × ℕ), incrementLaw (B z)) =
            ∑' x : Site, ∑' ya : Site × ℕ,
              incrementLaw (B (x, ya)) := ENNReal.tsum_prod'
      have hinner (x : Site) :
          (∑' ya : Site × ℕ, incrementLaw (B (x, ya))) =
            ∑' y : Site, ∑' a : ℕ,
              incrementLaw (B (x, (y, a))) := ENNReal.tsum_prod'
      calc
        (∑' x, ∑' y, ∑' a,
            incrementLaw (simpleRandomWalk ⁻¹'
              raceBaseFiber σ Y x y a)) =
            ∑' x, ∑' ya : Site × ℕ,
              incrementLaw (B (x, ya)) := by
          exact tsum_congr fun x ↦ (hinner x).symm
        _ = ∑' z, incrementLaw (B z) := houter.symm
    _ ≤ 1 * (1 - p) ^ q := by
      simpa only [mul_comm] using mul_le_mul_right hBsum ((1 - p) ^ q)
    _ = (1 - p) ^ q := one_mul _

theorem firstKSitesReachLevel_le_hlozSigma_of_pos
    (window : Site → Finset Site) (m k q i : ℕ) (hi : 1 ≤ i) :
    firstKSitesReachLevel m k ≤ hlozSigma window m k q i := by
  intro s
  let T := firstKSitesReachLevel m k
  let σ := hlozSigma window m k q i
  by_cases hσfinite : σ s = ⊤
  · change T s ≤ σ s
    rw [hσfinite]
    exact le_top
  · have hmem := hittingAfter_mem_set_of_ne_top
        (u := fun n s ↦ hlozCandidateVisitCount T window q n s)
        (s := Set.Ici i) (n := 0) (ω := s) hσfinite
    have hiCount : i ≤ hlozCandidateVisitCount T window q (σ s).untopA s := by
      change i ≤ hlozCandidateVisitCount T window q (σ s).untopA s at hmem
      exact hmem
    by_contra hnot
    have hσltT : σ s < T s := lt_of_not_ge hnot
    have hσcoe : (((σ s).untopA : ℕ) : WithTop ℕ) = σ s := by
      rw [WithTop.untopA_eq_untop hσfinite]
      exact WithTop.coe_untop _ hσfinite
    have hzero : hlozCandidateVisitCount T window q (σ s).untopA s = 0 :=
      hlozCandidateVisitCount_eq_zero_of_lt (hσcoe.trans_lt hσltT)
    rw [hzero] at hiCount
    omega

theorem measurable_levelCreationSite_at_hlozSigma
    (window : Site → Finset Site) (m k q i : ℕ) (hi : 1 ≤ i) :
    Measurable[(isStoppingTime_hlozSigma window m k q i).measurableSpace]
      (fun s ↦ levelCreationSite s m k) := by
  let T := firstKSitesReachLevel m k
  have hT := isStoppingTime_firstKSitesReachLevel m k
  have hσ := isStoppingTime_hlozSigma window m k q i
  have hTσ : T ≤ hlozSigma window m k q i :=
    firstKSitesReachLevel_le_hlozSigma_of_pos window m k q i hi
  change Measurable[hσ.measurableSpace]
    (fun s ↦ s (T s).untopA)
  exact (measurable_stoppedCoordinate hT).mono
    (hT.measurableSpace_mono hσ hTσ) le_rfl

theorem hlozSigma_current_mem_window
    (window : Site → Finset Site) (m k q i : ℕ) (hi : 1 ≤ i)
    (s : ℕ → Site)
    (hσfinite : hlozSigma window m k q i s ≠ ⊤) :
    s (hlozSigma window m k q i s).untopA ∈
      window (levelCreationSite s m k) := by
  let T := firstKSitesReachLevel m k
  let σ := hlozSigma window m k q i
  let n : ℕ := (σ s).untopA
  have hTσ := firstKSitesReachLevel_le_hlozSigma_of_pos
    window m k q i hi s
  have hTfinite : T s ≠ ⊤ := ne_top_of_le_ne_top hσfinite hTσ
  let t : ℕ := (T s).untopA
  have hTcoe : (t : WithTop ℕ) = T s := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hTfinite]
    exact WithTop.coe_untop _ hTfinite
  have hσcoe : (n : WithTop ℕ) = σ s := by
    dsimp only [n]
    rw [WithTop.untopA_eq_untop hσfinite]
    exact WithTop.coe_untop _ hσfinite
  have htn : t ≤ n :=
    WithTop.coe_le_coe.mp (hTcoe.trans_le (hTσ.trans_eq hσcoe.symm))
  have hmem := hittingAfter_mem_set_of_ne_top
    (u := fun n s ↦ hlozCandidateVisitCount T window q n s)
    (s := Set.Ici i) (n := 0) (ω := s) hσfinite
  have hiCount : i ≤ hlozCandidateVisitCount T window q n s := by
    change i ≤ hlozCandidateVisitCount T window q (σ s).untopA s at hmem
    simpa only [n] using hmem
  have hTt : T s = t := hTcoe.symm
  have hiCard : i ≤
      (hlozVisitedCandidatesAtTime window s t q n).card := by
    rw [hlozCandidateVisitCount_eq_of_eq htn hTt] at hiCount
    exact hiCount
  have hcurrentCandidate :
      s n ∈ hlozCandidateSitesAtTime window s t q := by
    by_contra hnotCandidate
    rcases lt_or_eq_of_le htn with htnlt | htneq
    · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le t) htnlt
      have hpredlt : ((n - 1 : ℕ) : WithTop ℕ) < σ s := by
        rw [← hσcoe]
        exact WithTop.coe_lt_coe.mpr
          (Nat.sub_lt hnpos Nat.zero_lt_one)
      have hprevNot := notMem_of_lt_hittingAfter
        (u := fun n s ↦ hlozCandidateVisitCount T window q n s)
        (s := Set.Ici i) (n := 0) (ω := s) hpredlt (Nat.zero_le _)
      have hprevCount : hlozCandidateVisitCount T window q (n - 1) s < i := by
        change ¬ i ≤ hlozCandidateVisitCount T window q (n - 1) s at hprevNot
        omega
      have htpred : t ≤ n - 1 := by omega
      have hsubset :
          hlozVisitedCandidatesAtTime window s t q n ⊆
            hlozVisitedCandidatesAtTime window s t q (n - 1) := by
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzVisited, hzCandidate⟩
        rcases Finset.mem_image.mp hzVisited with ⟨r, hr, hsr⟩
        have hrne : r ≠ n := by
          intro hrn
          apply hnotCandidate
          subst r
          rw [hsr]
          exact hzCandidate
        have hrpred : r ≤ n - 1 := by
          have hrn := (Finset.mem_Icc.mp hr).2
          omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨r, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hrpred⟩,
            hsr⟩, hzCandidate⟩
      have hcardLe := Finset.card_le_card hsubset
      have hprevEq := hlozCandidateVisitCount_eq_of_eq
        (s := s) (window := window) (q := q) htpred hTt
      rw [hprevEq] at hprevCount
      omega
    · have hempty :
          hlozVisitedCandidatesAtTime window s t q n = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzVisited, hzCandidate⟩
        rcases Finset.mem_image.mp hzVisited with ⟨r, hr, hsr⟩
        have hrn : r = n := by
          have hr' := Finset.mem_Icc.mp hr
          omega
        subst r
        apply hnotCandidate
        rw [hsr]
        exact hzCandidate
      rw [hempty] at hiCard
      simp only [Finset.card_empty] at hiCard
      omega
  have hwindow : s n ∈ window (s t) :=
    (Finset.mem_filter.mp hcurrentCandidate).1
  simpa [n, t, T, levelCreationSite] using hwindow

theorem hlozSigma_geometry
    (window : Site → Finset Site) (R m k q i : ℕ) (hi : 1 ≤ i)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2)
    (s : ℕ → Site)
    (hσfinite : hlozSigma window m k q i s ≠ ⊤) :
    siteSquaredDistance
      (s (hlozSigma window m k q i s).untopA)
      (levelCreationSite s m k) ≤ R ^ 2 :=
  hwindow _ _ (hlozSigma_current_mem_window window m k q i hi s hσfinite)

/-- Instantiation of the precise probabilistic interface left by the
deterministic HLOZ Lemma 4.10 decomposition. -/
theorem hasHLOZLemma410PostHitRaceEstimate_of_offOriginHitBeforeReturn
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (p : ℝ≥0∞)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2)
    (hoff : HasOffOriginHitBeforeReturnLowerBound R p) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace (fun _ ↦ (1 - p) ^ qRace) := by
  intro i hi
  exact simpleRandomWalkLaw_hlozPostHitRaceEvent_le_one_sub_pow
    (isStoppingTime_hlozSigma window m k qCandidate i)
    m k qRace R p
    (measurable_levelCreationSite_at_hlozSigma
      window m k qCandidate i hi)
    (hlozSigma_geometry window R m k qCandidate i hi hwindow)
    hoff

theorem simpleRandomWalkLaw_hlozPostHitRaceEvent_le_exp
    {σ : (ℕ → Site) → WithTop ℕ}
    (hσ : IsStoppingTime HLOZFoundation.canonicalFiltration σ)
    (m k q R : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hY : Measurable[hσ.measurableSpace]
      (fun s ↦ levelCreationSite s m k))
    (hgeom : ∀ s, σ s ≠ ⊤ →
      siteSquaredDistance (s (σ s).untopA) (levelCreationSite s m k) ≤ R ^ 2)
    (hoff : HasOffOriginHitBeforeReturnLowerBound R (ENNReal.ofReal ε)) :
    simpleRandomWalkLaw (hlozPostHitRaceEvent m k σ q) ≤
      ENNReal.ofReal (Real.exp (-((q : ℝ) * ε))) := by
  refine (simpleRandomWalkLaw_hlozPostHitRaceEvent_le_one_sub_pow
    hσ m k q R (ENNReal.ofReal ε) hY hgeom hoff).trans ?_
  calc
    (1 - ENNReal.ofReal ε) ^ q = ENNReal.ofReal ((1 - ε) ^ q) := by
      rw [ENNReal.ofReal_pow (sub_nonneg.mpr hε1),
        ENNReal.ofReal_sub 1 hε0, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal ((Real.exp (-ε)) ^ q) := by
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (sub_nonneg.mpr hε1)
          (Real.one_sub_le_exp_neg ε) q)
    _ = ENNReal.ofReal (Real.exp (-((q : ℝ) * ε))) := by
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Exponential version of the HLOZ Lemma 4.10 probabilistic interface.
For the source application one takes `ε = c / log R`; proving the corresponding
`hoff` is precisely the remaining potential-kernel estimate. -/
theorem hasHLOZLemma410PostHitRaceEstimate_exp_of_offOriginHitBeforeReturn
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2)
    (hoff : HasOffOriginHitBeforeReturnLowerBound R (ENNReal.ofReal ε)) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal (Real.exp (-((qRace : ℝ) * ε)))) := by
  intro i hi
  exact simpleRandomWalkLaw_hlozPostHitRaceEvent_le_exp
    (isStoppingTime_hlozSigma window m k qCandidate i)
    m k qRace R ε hε0 hε1
    (measurable_levelCreationSite_at_hlozSigma
      window m k qCandidate i hi)
    (hlozSigma_geometry window R m k qCandidate i hi hwindow)
    hoff

/-- The source-shaped logarithmic specialization.  Any explicit universal
constant `c` supplied by the potential-kernel calculation yields the desired
`exp (-c*q/log R)` race bound. -/
theorem hasHLOZLemma410PostHitRaceEstimate_log_of_offOriginHitBeforeReturn
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (c : ℝ) (hε0 : 0 ≤ c / Real.log R) (hε1 : c / Real.log R ≤ 1)
    (hwindow : ∀ z x, x ∈ window z → siteSquaredDistance x z ≤ R ^ 2)
    (hoff : HasOffOriginHitBeforeReturnLowerBound R
      (ENNReal.ofReal (c / Real.log R))) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal
        (Real.exp (-((qRace : ℝ) * (c / Real.log R))))) :=
  hasHLOZLemma410PostHitRaceEstimate_exp_of_offOriginHitBeforeReturn
    window m k qCandidate qRace R (c / Real.log R) hε0 hε1 hwindow hoff

end HLOZLemma410Race
end Erdos1166
