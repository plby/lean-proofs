/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166Core

namespace Erdos1166.KilledGreen

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The canonical walk started from `x`. -/
def walkFrom (x : Site) (ω : ℕ → Direction) (n : ℕ) : Site :=
  x + simpleRandomWalk ω n

/-- Partial walk of a finite increment block, including its starting point. -/
def blockWalkFrom {m : ℕ} (x : Site) (η : Fin m → Direction)
    (r : Fin (m + 1)) : Site :=
  x + ∑ i : Fin r, directionStep (η ⟨i, by omega⟩)

/-- The walk stays in `D` through time `n` and is at `y` at time `n`. -/
def killedEndpointEvent (D : Set Site) (x y : Site) (n : ℕ) :
    Set (ℕ → Direction) :=
  {ω | (∀ r, r ≤ n → walkFrom x ω r ∈ D) ∧ walkFrom x ω n = y}

/-- The first visit to `y` occurs at time `n`, before leaving `D`. -/
def firstEntranceEvent (D : Set Site) (x y : Site) (n : ℕ) :
    Set (ℕ → Direction) :=
  {ω | (∀ r, r ≤ n → walkFrom x ω r ∈ D) ∧
    walkFrom x ω n = y ∧ ∀ r, r < n → walkFrom x ω r ≠ y}

/-- Finite-block form of a killed endpoint event. -/
def blockKilledEndpoint (D : Set Site) (x y : Site) (m : ℕ) :
    Set (Fin m → Direction) :=
  {η | (∀ r : Fin (m + 1), blockWalkFrom x η r ∈ D) ∧
    blockWalkFrom x η ⟨m, by omega⟩ = y}

theorem measurableSet_blockKilledEndpoint (D : Set Site) (x y : Site) (m : ℕ) :
    MeasurableSet (blockKilledEndpoint D x y m) :=
  MeasurableSet.of_discrete

theorem blockWalkFrom_iidBlock (x : Site) (j m : ℕ) (ω : ℕ → Direction)
    (r : Fin (m + 1)) :
    blockWalkFrom x (iidBlock (X := Direction) j m ω) r =
      x + walkAfter j ω (j + r) := by
  unfold blockWalkFrom iidBlock walkAfter
  congr 1
  change (∑ i : Fin r, directionStep (ω (j + (i : ℕ)))) =
    ∑ k ∈ Finset.Ico j (j + r), directionStep (ω k)
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ directionStep (ω (j + i))) r]
  rw [Finset.sum_Ico_eq_sum_range]
  simp

theorem blockWalkFrom_iidBlock_eq_walkFrom
    (x : Site) (j m : ℕ) (ω : ℕ → Direction) (r : Fin (m + 1)) :
    blockWalkFrom (walkFrom x ω j) (iidBlock (X := Direction) j m ω) r =
      walkFrom x ω (j + r) := by
  rw [blockWalkFrom_iidBlock]
  unfold walkFrom
  rw [simpleRandomWalk_eq_add_walkAfter (Nat.le_add_right j r) ω]
  abel

theorem blockWalkFrom_iidBlock_zero_eq_walkFrom
    (x : Site) (m : ℕ) (ω : ℕ → Direction) (r : Fin (m + 1)) :
    blockWalkFrom x (iidBlock (X := Direction) 0 m ω) r =
      walkFrom x ω r := by
  simpa [walkFrom, simpleRandomWalk] using
    blockWalkFrom_iidBlock_eq_walkFrom x 0 m ω r

theorem iidBlock_zero_preimage_blockKilledEndpoint
    (D : Set Site) (x y : Site) (m : ℕ) :
    iidBlock (X := Direction) 0 m ⁻¹' blockKilledEndpoint D x y m =
      killedEndpointEvent D x y m := by
  ext ω
  simp only [Set.mem_preimage, blockKilledEndpoint, Set.mem_ofPred_eq,
    killedEndpointEvent]
  constructor
  · rintro ⟨hstay, hend⟩
    constructor
    · intro r hr
      let r' : Fin (m + 1) := ⟨r, by omega⟩
      rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω r']
      exact hstay r'
    · rw [← blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω ⟨m, by omega⟩]
      exact hend
  · rintro ⟨hstay, hend⟩
    constructor
    · intro r
      have hr : (r : ℕ) ≤ m := Nat.le_of_lt_succ r.isLt
      rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω r]
      exact hstay r hr
    · rw [blockWalkFrom_iidBlock_zero_eq_walkFrom x m ω ⟨m, by omega⟩]
      exact hend

theorem finitePi_blockKilledEndpoint_eq
    (D : Set Site) (x y : Site) (m : ℕ) :
    (Measure.infinitePi fun _ : Fin m ↦ directionLaw)
        (blockKilledEndpoint D x y m) =
      incrementLaw (killedEndpointEvent D x y m) := by
  rw [← iidBlock_map directionLaw 0 m]
  rw [Measure.map_apply (measurable_iidBlock 0 m)
    (measurableSet_blockKilledEndpoint D x y m)]
  exact congrArg incrementLaw
    (iidBlock_zero_preimage_blockKilledEndpoint D x y m)

noncomputable def killedWeight (D : Set Site) (x y : Site) (n : ℕ) : ℝ≥0∞ :=
  incrementLaw (killedEndpointEvent D x y n)

noncomputable def entranceWeight (D : Set Site) (x y : Site) (n : ℕ) : ℝ≥0∞ :=
  incrementLaw (firstEntranceEvent D x y n)

theorem measurable_walkFrom_iidHistory (x : Site) {r n : ℕ} (hrn : r ≤ n) :
    Measurable[iidHistory (X := Direction) n] (fun ω ↦ walkFrom x ω r) := by
  exact measurable_const.add
    (HLOZFoundation.measurable_simpleRandomWalk_time_iidHistory hrn)

theorem measurableSet_firstEntranceEvent_iidHistory
    (D : Set Site) (x y : Site) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (firstEntranceEvent D x y n) := by
  have hstay : MeasurableSet[iidHistory (X := Direction) n]
      {ω : ℕ → Direction | ∀ r, r ≤ n → walkFrom x ω r ∈ D} := by
    have heq : {ω : ℕ → Direction | ∀ r, r ≤ n → walkFrom x ω r ∈ D} =
        ⋂ r : ℕ, ⋂ (_ : r ≤ n), {ω | walkFrom x ω r ∈ D} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      (Set.to_countable D).measurableSet.preimage
        (measurable_walkFrom_iidHistory x hr)
  have hend : MeasurableSet[iidHistory (X := Direction) n]
      {ω : ℕ → Direction | walkFrom x ω n = y} :=
    measurableSet_eq_fun (measurable_walkFrom_iidHistory x le_rfl) measurable_const
  have havoid : MeasurableSet[iidHistory (X := Direction) n]
      {ω : ℕ → Direction | ∀ r, r < n → walkFrom x ω r ≠ y} := by
    have heq : {ω : ℕ → Direction | ∀ r, r < n → walkFrom x ω r ≠ y} =
        ⋂ r : ℕ, ⋂ (_ : r < n), {ω | walkFrom x ω r ≠ y} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      (measurableSet_eq_fun (measurable_walkFrom_iidHistory x hr.le)
        measurable_const).compl
  exact hstay.inter (hend.inter havoid)

/-- Decomposition summand: first enter `y` at `j`, then make a killed loop
from `y` of length `n-j`. -/
def entranceThenLoopEvent (D : Set Site) (x y : Site) (n j : ℕ) :
    Set (ℕ → Direction) :=
  firstEntranceEvent D x y j ∩
    iidBlock (X := Direction) j (n - j) ⁻¹'
      blockKilledEndpoint D y y (n - j)

theorem measure_entranceThenLoopEvent {D : Set Site} {x y : Site} {n j : ℕ}
    (_hjn : j ≤ n) :
    incrementLaw (entranceThenLoopEvent D x y n j) =
      entranceWeight D x y j * killedWeight D y y (n - j) := by
  have h := measure_inter_iidBlock_eq_mul directionLaw j (n - j)
    (measurableSet_firstEntranceEvent_iidHistory D x y j)
    (measurableSet_blockKilledEndpoint D y y (n - j))
  rw [finitePi_blockKilledEndpoint_eq] at h
  simpa [incrementLaw, entranceThenLoopEvent, entranceWeight, killedWeight] using h

theorem entranceThenLoopEvent_disjoint_of_lt
    {D : Set Site} {x y : Site} {n i j : ℕ} (hij : i < j) :
    Disjoint (entranceThenLoopEvent D x y n i)
      (entranceThenLoopEvent D x y n j) := by
  rw [Set.disjoint_left]
  intro ω hi hj
  have hiy : walkFrom x ω i = y := hi.1.2.1
  have hne : walkFrom x ω i ≠ y := hj.1.2.2 i hij
  exact hne hiy

theorem pairwiseDisjoint_entranceThenLoopEvent
    (D : Set Site) (x y : Site) (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (n + 1)))
      (entranceThenLoopEvent D x y n) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact entranceThenLoopEvent_disjoint_of_lt hij
  · exact (entranceThenLoopEvent_disjoint_of_lt hji).symm

theorem iUnion_entranceThenLoopEvent
    (D : Set Site) (x y : Site) (n : ℕ) :
    (⋃ j ∈ Finset.range (n + 1), entranceThenLoopEvent D x y n j) =
      killedEndpointEvent D x y n := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hjnRange, hj⟩
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hjnRange)
    rcases hj with ⟨hfirst, hsuffix⟩
    rcases hfirst with ⟨hstayFirst, hjy, havoid⟩
    rcases hsuffix with ⟨hstaySuffix, hendSuffix⟩
    constructor
    · intro r hrn
      by_cases hrj : r ≤ j
      · exact hstayFirst r hrj
      · let q : Fin (n - j + 1) := ⟨r - j, by omega⟩
        have hblock := hstaySuffix q
        have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q
        rw [hjy] at heq
        have hjq : j + (q : ℕ) = r := by
          dsimp only [q]
          omega
        rw [hjq] at heq
        exact heq ▸ hblock
    · let q : Fin (n - j + 1) := ⟨n - j, by omega⟩
      have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q
      rw [hjy] at heq
      have hjq : j + (q : ℕ) = n := by
        dsimp only [q]
        omega
      rw [hjq] at heq
      exact heq ▸ hendSuffix
  · intro hω
    rcases hω with ⟨hstay, hny⟩
    let Z := (Finset.range (n + 1)).filter fun j ↦ walkFrom x ω j = y
    have hZ : Z.Nonempty := by
      refine ⟨n, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨by simp, hny⟩
    let j := Z.min' hZ
    have hjZ : j ∈ Z := Z.min'_mem hZ
    have hjn : j ≤ n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hjZ).1)
    have hjy : walkFrom x ω j = y := (Finset.mem_filter.mp hjZ).2
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    constructor
    · refine ⟨fun r hr ↦ hstay r (hr.trans hjn), hjy, ?_⟩
      intro r hrj hry
      have hrZ : r ∈ Z := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (by omega), hry⟩
      exact (not_le_of_gt hrj) (Z.min'_le r hrZ)
    · constructor
      · intro q
        have htime : j + (q : ℕ) ≤ n := by omega
        have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q
        rw [hjy] at heq
        exact heq ▸ hstay (j + q) htime
      · let q : Fin (n - j + 1) := ⟨n - j, by omega⟩
        have heq := blockWalkFrom_iidBlock_eq_walkFrom x j (n - j) ω q
        rw [hjy] at heq
        have hjq : j + (q : ℕ) = n := by
          dsimp only [q]
          omega
        rw [hjq] at heq
        exact heq ▸ hny

theorem measurableSet_entranceThenLoopEvent
    (D : Set Site) (x y : Site) (n j : ℕ) :
    MeasurableSet (entranceThenLoopEvent D x y n j) := by
  exact (ProbabilityTheory.iidHistory_le j _
      (measurableSet_firstEntranceEvent_iidHistory D x y j)).inter
    ((measurable_iidBlock j (n - j))
      (measurableSet_blockKilledEndpoint D y y (n - j)))

/-- Exact finite renewal identity for the killed walk. -/
theorem killedWeight_eq_firstEntrance_convolution
    (D : Set Site) (x y : Site) (n : ℕ) :
    killedWeight D x y n =
      ∑ j ∈ Finset.range (n + 1),
        entranceWeight D x y j * killedWeight D y y (n - j) := by
  calc
    killedWeight D x y n = incrementLaw
        (⋃ j ∈ Finset.range (n + 1), entranceThenLoopEvent D x y n j) := by
      rw [iUnion_entranceThenLoopEvent]
      rfl
    _ = ∑ j ∈ Finset.range (n + 1),
        incrementLaw (entranceThenLoopEvent D x y n j) := by
      exact measure_biUnion_finset
        (pairwiseDisjoint_entranceThenLoopEvent D x y n)
        (fun j _ ↦ measurableSet_entranceThenLoopEvent D x y n j)
    _ = ∑ j ∈ Finset.range (n + 1),
        entranceWeight D x y j * killedWeight D y y (n - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact measure_entranceThenLoopEvent
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

/-- Green mass of visits to `y` before the walk leaves `D`.  This is kept in
`ENNReal`, so the renewal identity does not need a prior finiteness proof. -/
noncomputable def killedGreen (D : Set Site) (x y : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, killedWeight D x y n

/-- Total first-entrance mass of `y` before leaving `D`. -/
noncomputable def hittingWeight (D : Set Site) (x y : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, entranceWeight D x y n

/-- The path event that `y` is reached before the killed walk leaves `D`. -/
def hitBeforeExitEvent (D : Set Site) (x y : Site) : Set (ℕ → Direction) :=
  ⋃ n : ℕ, firstEntranceEvent D x y n

theorem firstEntranceEvent_disjoint_of_lt
    {D : Set Site} {x y : Site} {i j : ℕ} (hij : i < j) :
    Disjoint (firstEntranceEvent D x y i) (firstEntranceEvent D x y j) := by
  rw [Set.disjoint_left]
  intro ω hi hj
  exact hj.2.2 i hij hi.2.1

theorem pairwiseDisjoint_firstEntranceEvent (D : Set Site) (x y : Site) :
    Pairwise fun i j ↦
      Disjoint (firstEntranceEvent D x y i) (firstEntranceEvent D x y j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact firstEntranceEvent_disjoint_of_lt hij
  · exact (firstEntranceEvent_disjoint_of_lt hji).symm

theorem measurableSet_firstEntranceEvent
    (D : Set Site) (x y : Site) (n : ℕ) :
    MeasurableSet (firstEntranceEvent D x y n) :=
  ProbabilityTheory.iidHistory_le n _
    (measurableSet_firstEntranceEvent_iidHistory D x y n)

/-- `hittingWeight` really is the probability of the corresponding hitting
event, not merely a formal sum of finite-time masses. -/
theorem hittingWeight_eq_measure_hitBeforeExit
    (D : Set Site) (x y : Site) :
    hittingWeight D x y = incrementLaw (hitBeforeExitEvent D x y) := by
  rw [hitBeforeExitEvent,
    measure_iUnion (pairwiseDisjoint_firstEntranceEvent D x y)
      (measurableSet_firstEntranceEvent D x y)]
  rfl

theorem ennreal_tsum_mul_tsum_eq_tsum_sum_range (f g : ℕ → ℝ≥0∞) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  calc
    (∑' n, f n) * (∑' n, g n) =
        ∑' j, f j * (∑' n, g n) := ENNReal.tsum_mul_right.symm
    _ = ∑' j, ∑' k, f j * g k := by
      apply tsum_congr
      intro j
      exact ENNReal.tsum_mul_left.symm
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 := ENNReal.tsum_prod.symm
    _ = ∑' p : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n),
        f (p.2 : ℕ × ℕ).1 * g (p.2 : ℕ × ℕ).2 := by
      exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
        (fun p : ℕ × ℕ ↦ f p.1 * g p.2)).symm
    _ = ∑' n, ∑' p : Finset.HasAntidiagonal.antidiagonal n,
        f p.val.1 * g p.val.2 := by
      exact ENNReal.tsum_sigma
        (fun n (p : Finset.HasAntidiagonal.antidiagonal n) ↦
          f p.val.1 * g p.val.2)
    _ = ∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        f p.1 * g p.2 := by
      apply tsum_congr
      intro n
      rw [tsum_fintype]
      exact Finset.sum_finset_coe
        (fun p : ℕ × ℕ ↦ f p.1 * g p.2)
        (Finset.HasAntidiagonal.antidiagonal n)
    _ = ∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
      apply tsum_congr
      intro n
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k l ↦ f k * g l) n

/-- Exact Green/first-entrance factorization, valid even when one of the
Green masses is infinite. -/
theorem killedGreen_eq_hittingWeight_mul_diagonal
    (D : Set Site) (x y : Site) :
    killedGreen D x y = hittingWeight D x y * killedGreen D y y := by
  unfold killedGreen hittingWeight
  rw [show (∑' n : ℕ, killedWeight D x y n) =
      ∑' n : ℕ, ∑ j ∈ Finset.range (n + 1),
        entranceWeight D x y j * killedWeight D y y (n - j) by
    apply tsum_congr
    exact killedWeight_eq_firstEntrance_convolution D x y]
  symm
  exact ennreal_tsum_mul_tsum_eq_tsum_sum_range _ _

theorem killedWeight_zero_self {D : Set Site} {y : Site} (hy : y ∈ D) :
    killedWeight D y y 0 = 1 := by
  have hevent : killedEndpointEvent D y y 0 = Set.univ := by
    ext ω
    simp [killedEndpointEvent, walkFrom, simpleRandomWalk, hy]
  rw [killedWeight, hevent]
  simp

theorem one_le_killedGreen_diagonal {D : Set Site} {y : Site} (hy : y ∈ D) :
    1 ≤ killedGreen D y y := by
  calc
    1 = killedWeight D y y 0 := (killedWeight_zero_self hy).symm
    _ ≤ ∑' n : ℕ, killedWeight D y y n := ENNReal.le_tsum 0
    _ = killedGreen D y y := rfl

theorem killedGreen_diagonal_ne_zero {D : Set Site} {y : Site} (hy : y ∈ D) :
    killedGreen D y y ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_killedGreen_diagonal hy))

/-- Exact Green-ratio formula.  The only extra premise is finiteness of the
diagonal Green mass; bounded domains should discharge it by a geometric
exit-tail estimate. -/
theorem hittingWeight_eq_green_div {D : Set Site} {x y : Site}
    (hy : y ∈ D) (hfinite : killedGreen D y y ≠ ∞) :
    hittingWeight D x y = killedGreen D x y / killedGreen D y y := by
  apply (ENNReal.eq_div_iff (killedGreen_diagonal_ne_zero hy) hfinite).2
  rw [mul_comm]
  exact (killedGreen_eq_hittingWeight_mul_diagonal D x y).symm

/-- A finite square in the `ℓ∞` lattice metric. -/
noncomputable def squareDisk (R : ℕ) : Finset Site :=
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).product
    (Finset.Icc (-(R : ℤ)) (R : ℤ))

noncomputable def diskGreen (R : ℕ) (x y : Site) : ℝ≥0∞ :=
  killedGreen (squareDisk R : Set Site) x y

noncomputable def diskHittingWeight (R : ℕ) (x y : Site) : ℝ≥0∞ :=
  hittingWeight (squareDisk R : Set Site) x y

theorem diskHittingWeight_eq_green_div {R : ℕ} {x y : Site}
    (hy : y ∈ squareDisk R) (hfinite : diskGreen R y y ≠ ∞) :
    diskHittingWeight R x y = diskGreen R x y / diskGreen R y y := by
  exact hittingWeight_eq_green_div hy hfinite

/-- A strictly positive first return to `y`, before leaving `D`. -/
def strictReturnEvent (D : Set Site) (y : Site) (k : ℕ) :
    Set (ℕ → Direction) :=
  {ω | (∀ r, r ≤ k → walkFrom y ω r ∈ D) ∧ walkFrom y ω k = y ∧
    0 < k ∧ ∀ r, 0 < r → r < k → walkFrom y ω r ≠ y}

noncomputable def strictReturnWeight (D : Set Site) (y : Site) (k : ℕ) : ℝ≥0∞ :=
  incrementLaw (strictReturnEvent D y k)

theorem measurableSet_strictReturnEvent_iidHistory
    (D : Set Site) (y : Site) (k : ℕ) :
    MeasurableSet[iidHistory (X := Direction) k] (strictReturnEvent D y k) := by
  have hstay : MeasurableSet[iidHistory (X := Direction) k]
      {ω : ℕ → Direction | ∀ r, r ≤ k → walkFrom y ω r ∈ D} := by
    have heq : {ω : ℕ → Direction | ∀ r, r ≤ k → walkFrom y ω r ∈ D} =
        ⋂ r : ℕ, ⋂ (_ : r ≤ k), {ω | walkFrom y ω r ∈ D} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      (Set.to_countable D).measurableSet.preimage
        (measurable_walkFrom_iidHistory y hr)
  have hend : MeasurableSet[iidHistory (X := Direction) k]
      {ω : ℕ → Direction | walkFrom y ω k = y} :=
    measurableSet_eq_fun (measurable_walkFrom_iidHistory y le_rfl) measurable_const
  have havoid : MeasurableSet[iidHistory (X := Direction) k]
      {ω : ℕ → Direction | ∀ r, 0 < r → r < k → walkFrom y ω r ≠ y} := by
    have heq : {ω : ℕ → Direction |
        ∀ r, 0 < r → r < k → walkFrom y ω r ≠ y} =
        ⋂ r : ℕ, ⋂ (_ : 0 < r), ⋂ (_ : r < k),
          {ω | walkFrom y ω r ≠ y} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦
      MeasurableSet.iInter fun hr ↦
        (measurableSet_eq_fun (measurable_walkFrom_iidHistory y hr.le)
          measurable_const).compl
  exact hstay.inter (hend.inter (MeasurableSet.const (0 < k) |>.inter havoid))

def returnThenLoopEvent (D : Set Site) (y : Site) (n j : ℕ) :
    Set (ℕ → Direction) :=
  strictReturnEvent D y (j + 1) ∩
    iidBlock (X := Direction) (j + 1) (n - j) ⁻¹'
      blockKilledEndpoint D y y (n - j)

theorem measure_returnThenLoopEvent {D : Set Site} {y : Site} {n j : ℕ}
    (_hjn : j ≤ n) :
    incrementLaw (returnThenLoopEvent D y n j) =
      strictReturnWeight D y (j + 1) * killedWeight D y y (n - j) := by
  have h := measure_inter_iidBlock_eq_mul directionLaw (j + 1) (n - j)
    (measurableSet_strictReturnEvent_iidHistory D y (j + 1))
    (measurableSet_blockKilledEndpoint D y y (n - j))
  rw [finitePi_blockKilledEndpoint_eq] at h
  simpa [incrementLaw, returnThenLoopEvent, strictReturnWeight, killedWeight] using h

theorem returnThenLoopEvent_disjoint_of_lt
    {D : Set Site} {y : Site} {n i j : ℕ} (hij : i < j) :
    Disjoint (returnThenLoopEvent D y n i) (returnThenLoopEvent D y n j) := by
  rw [Set.disjoint_left]
  intro ω hi hj
  have hiy : walkFrom y ω (i + 1) = y := hi.1.2.1
  have hne : walkFrom y ω (i + 1) ≠ y := hj.1.2.2.2 (i + 1) (by omega) (by omega)
  exact hne hiy

theorem pairwiseDisjoint_returnThenLoopEvent (D : Set Site) (y : Site) (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (n + 1))) (returnThenLoopEvent D y n) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact returnThenLoopEvent_disjoint_of_lt hij
  · exact (returnThenLoopEvent_disjoint_of_lt hji).symm

theorem iUnion_returnThenLoopEvent (D : Set Site) (y : Site) (n : ℕ) :
    (⋃ j ∈ Finset.range (n + 1), returnThenLoopEvent D y n j) =
      killedEndpointEvent D y y (n + 1) := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hjnRange, hj⟩
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hjnRange)
    rcases hj with ⟨hfirst, hsuffix⟩
    rcases hfirst with ⟨hstayFirst, hjy, hjpos, havoid⟩
    rcases hsuffix with ⟨hstaySuffix, hendSuffix⟩
    constructor
    · intro r hrn
      by_cases hrj : r ≤ j + 1
      · exact hstayFirst r hrj
      · let q : Fin (n - j + 1) := ⟨r - (j + 1), by omega⟩
        have hblock := hstaySuffix q
        have heq := blockWalkFrom_iidBlock_eq_walkFrom y (j + 1) (n - j) ω q
        rw [hjy] at heq
        have hjq : j + 1 + (q : ℕ) = r := by
          dsimp only [q]
          omega
        rw [hjq] at heq
        exact heq ▸ hblock
    · let q : Fin (n - j + 1) := ⟨n - j, by omega⟩
      have heq := blockWalkFrom_iidBlock_eq_walkFrom y (j + 1) (n - j) ω q
      rw [hjy] at heq
      have hjq : j + 1 + (q : ℕ) = n + 1 := by
        dsimp only [q]
        omega
      rw [hjq] at heq
      exact heq ▸ hendSuffix
  · intro hω
    rcases hω with ⟨hstay, hny⟩
    let Z := (Finset.range (n + 1)).filter fun j ↦ walkFrom y ω (j + 1) = y
    have hZ : Z.Nonempty := by
      refine ⟨n, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨by simp, hny⟩
    let j := Z.min' hZ
    have hjZ : j ∈ Z := Z.min'_mem hZ
    have hjn : j ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hjZ).1)
    have hjy : walkFrom y ω (j + 1) = y := (Finset.mem_filter.mp hjZ).2
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    constructor
    · refine ⟨fun r hr ↦ hstay r (hr.trans (by omega)), hjy, by omega, ?_⟩
      intro r hrpos hrj hry
      let q := r - 1
      have hqj : q < j := by
        dsimp only [q]
        omega
      have hqZ : q ∈ Z := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_range.mpr (by omega)
        · have hqr : q + 1 = r := by
            dsimp only [q]
            omega
          simpa [hqr] using hry
      exact (not_le_of_gt hqj) (Z.min'_le q hqZ)
    · constructor
      · intro q
        have htime : j + 1 + (q : ℕ) ≤ n + 1 := by omega
        have heq := blockWalkFrom_iidBlock_eq_walkFrom y (j + 1) (n - j) ω q
        rw [hjy] at heq
        exact heq ▸ hstay (j + 1 + q) htime
      · let q : Fin (n - j + 1) := ⟨n - j, by omega⟩
        have heq := blockWalkFrom_iidBlock_eq_walkFrom y (j + 1) (n - j) ω q
        rw [hjy] at heq
        have hjq : j + 1 + (q : ℕ) = n + 1 := by
          dsimp only [q]
          omega
        rw [hjq] at heq
        exact heq ▸ hny

theorem measurableSet_returnThenLoopEvent (D : Set Site) (y : Site) (n j : ℕ) :
    MeasurableSet (returnThenLoopEvent D y n j) := by
  exact (ProbabilityTheory.iidHistory_le (j + 1) _
      (measurableSet_strictReturnEvent_iidHistory D y (j + 1))).inter
    ((measurable_iidBlock (j + 1) (n - j))
      (measurableSet_blockKilledEndpoint D y y (n - j)))

theorem killedWeight_succ_eq_strictReturn_convolution
    (D : Set Site) (y : Site) (n : ℕ) :
    killedWeight D y y (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        strictReturnWeight D y (j + 1) * killedWeight D y y (n - j) := by
  calc
    killedWeight D y y (n + 1) = incrementLaw
        (⋃ j ∈ Finset.range (n + 1), returnThenLoopEvent D y n j) := by
      rw [iUnion_returnThenLoopEvent]
      rfl
    _ = ∑ j ∈ Finset.range (n + 1), incrementLaw (returnThenLoopEvent D y n j) := by
      exact measure_biUnion_finset (pairwiseDisjoint_returnThenLoopEvent D y n)
        (fun j _ ↦ measurableSet_returnThenLoopEvent D y n j)
    _ = ∑ j ∈ Finset.range (n + 1),
        strictReturnWeight D y (j + 1) * killedWeight D y y (n - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact measure_returnThenLoopEvent
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

noncomputable def returnWeight (D : Set Site) (y : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, strictReturnWeight D y (n + 1)

/-- A positive return to `y` before exit from `D`. -/
def returnBeforeExitEvent (D : Set Site) (y : Site) : Set (ℕ → Direction) :=
  ⋃ n : ℕ, strictReturnEvent D y (n + 1)

theorem strictReturnEvent_succ_disjoint_of_lt
    {D : Set Site} {y : Site} {i j : ℕ} (hij : i < j) :
    Disjoint (strictReturnEvent D y (i + 1))
      (strictReturnEvent D y (j + 1)) := by
  rw [Set.disjoint_left]
  intro ω hi hj
  exact hj.2.2.2 (i + 1) (by omega) (by omega) hi.2.1

theorem pairwiseDisjoint_strictReturnEvent_succ (D : Set Site) (y : Site) :
    Pairwise fun i j ↦
      Disjoint (strictReturnEvent D y (i + 1))
        (strictReturnEvent D y (j + 1)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact strictReturnEvent_succ_disjoint_of_lt hij
  · exact (strictReturnEvent_succ_disjoint_of_lt hji).symm

theorem measurableSet_strictReturnEvent (D : Set Site) (y : Site) (k : ℕ) :
    MeasurableSet (strictReturnEvent D y k) :=
  ProbabilityTheory.iidHistory_le k _
    (measurableSet_strictReturnEvent_iidHistory D y k)

theorem returnWeight_eq_measure_returnBeforeExit (D : Set Site) (y : Site) :
    returnWeight D y = incrementLaw (returnBeforeExitEvent D y) := by
  rw [returnBeforeExitEvent,
    measure_iUnion (pairwiseDisjoint_strictReturnEvent_succ D y)
      (fun n ↦ measurableSet_strictReturnEvent D y (n + 1))]
  rfl

theorem killedGreen_diagonal_eq_one_add_returnWeight_mul
    {D : Set Site} {y : Site} (hy : y ∈ D) :
    killedGreen D y y = 1 + returnWeight D y * killedGreen D y y := by
  change (∑' n : ℕ, killedWeight D y y n) =
    1 + (∑' n : ℕ, strictReturnWeight D y (n + 1)) *
      (∑' n : ℕ, killedWeight D y y n)
  calc
    (∑' n : ℕ, killedWeight D y y n) =
        killedWeight D y y 0 + ∑' n : ℕ, killedWeight D y y (n + 1) :=
      tsum_eq_zero_add' ENNReal.summable
    _ = 1 + ∑' n : ℕ, killedWeight D y y (n + 1) := by
      rw [killedWeight_zero_self hy]
    _ = 1 + (∑' n : ℕ, strictReturnWeight D y (n + 1)) *
        (∑' n : ℕ, killedWeight D y y n) := by
      congr 1
      rw [show (∑' n : ℕ, killedWeight D y y (n + 1)) =
          ∑' n : ℕ, ∑ j ∈ Finset.range (n + 1),
            strictReturnWeight D y (j + 1) * killedWeight D y y (n - j) by
        apply tsum_congr
        exact killedWeight_succ_eq_strictReturn_convolution D y]
      exact (ennreal_tsum_mul_tsum_eq_tsum_sum_range _ _).symm

noncomputable def escapeWeight (D : Set Site) (y : Site) : ℝ≥0∞ :=
  1 - returnWeight D y

/-- The killed-walk escape event in its renewal-theoretic form: there is no
positive return to `y` while the path remains in `D`.  For a finite disk,
the geometric exit tail below shows that the only additional possibility
(remaining in the disk forever) is null. -/
def escapeBeforeReturnEvent (D : Set Site) (y : Site) : Set (ℕ → Direction) :=
  (returnBeforeExitEvent D y)ᶜ

theorem measurableSet_returnBeforeExitEvent (D : Set Site) (y : Site) :
    MeasurableSet (returnBeforeExitEvent D y) :=
  MeasurableSet.iUnion fun n ↦ measurableSet_strictReturnEvent D y (n + 1)

theorem escapeWeight_eq_measure_escapeBeforeReturn
    (D : Set Site) (y : Site) :
    escapeWeight D y = incrementLaw (escapeBeforeReturnEvent D y) := by
  rw [escapeWeight, returnWeight_eq_measure_returnBeforeExit,
    escapeBeforeReturnEvent,
    measure_compl (measurableSet_returnBeforeExitEvent D y)
      (measure_ne_top incrementLaw _), measure_univ]

theorem returnWeight_le_one_of_green_finite
    {D : Set Site} {y : Site} (hy : y ∈ D)
    (hfinite : killedGreen D y y ≠ ∞) :
    returnWeight D y ≤ 1 := by
  have hG0 := killedGreen_diagonal_ne_zero hy
  have hrenew := killedGreen_diagonal_eq_one_add_returnWeight_mul hy
  have hmul : returnWeight D y * killedGreen D y y ≤ killedGreen D y y := by
    calc
      returnWeight D y * killedGreen D y y ≤
          1 + returnWeight D y * killedGreen D y y := le_add_left le_rfl
      _ = killedGreen D y y := hrenew.symm
  have hdiv :
      returnWeight D y * killedGreen D y y / killedGreen D y y ≤ 1 :=
    (ENNReal.div_le_iff hG0 hfinite).2 (by simpa using hmul)
  simpa [ENNReal.mul_div_cancel_right hG0 hfinite] using hdiv

/-- Exact escape/Green identity: the probability mass of being killed before
a positive return is the reciprocal diagonal Green mass. -/
theorem escapeWeight_eq_inv_killedGreen
    {D : Set Site} {y : Site} (hy : y ∈ D)
    (hfinite : killedGreen D y y ≠ ∞) :
    escapeWeight D y = (killedGreen D y y)⁻¹ := by
  let G := killedGreen D y y
  let R := returnWeight D y
  have hG0 : G ≠ 0 := killedGreen_diagonal_ne_zero hy
  have hRle : R ≤ 1 := returnWeight_le_one_of_green_finite hy hfinite
  have hRfinite : R ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hRle
  have hprod : R * G ≠ ∞ := ENNReal.mul_ne_top hRfinite hfinite
  have hrenew : G = 1 + R * G := killedGreen_diagonal_eq_one_add_returnWeight_mul hy
  have hreal : G.toReal = 1 + R.toReal * G.toReal := by
    calc
      G.toReal = (1 + R * G).toReal := congrArg ENNReal.toReal hrenew
      _ = 1 + R.toReal * G.toReal := by
        rw [ENNReal.toReal_add ENNReal.one_ne_top hprod, ENNReal.toReal_one,
          ENNReal.toReal_mul]
  have hGreal : 0 < G.toReal := ENNReal.toReal_pos hG0 hfinite
  have hrealEscape : (1 - R).toReal = G⁻¹.toReal := by
    rw [ENNReal.toReal_sub_of_le hRle ENNReal.one_ne_top, ENNReal.toReal_one,
      ENNReal.toReal_inv]
    rw [← one_div]
    apply (eq_div_iff hGreal.ne').2
    nlinarith
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    (ENNReal.inv_ne_top.mpr hG0)).mp
  simpa [escapeWeight, G, R] using hrealEscape

noncomputable def diskEscapeWeight (R : ℕ) (y : Site) : ℝ≥0∞ :=
  escapeWeight (squareDisk R : Set Site) y

theorem diskEscapeWeight_eq_inv_green {R : ℕ} {y : Site}
    (hy : y ∈ squareDisk R) (hfinite : diskGreen R y y ≠ ∞) :
    diskEscapeWeight R y = (diskGreen R y y)⁻¹ := by
  exact escapeWeight_eq_inv_killedGreen hy hfinite

def diskExitBlockLength (R : ℕ) : ℕ := 2 * R + 1

def allEastBlock (m : ℕ) : Set (Fin m → Direction) :=
  {η | ∀ i, η i = 0}

theorem repeatedEast_exits_squareDisk (R : ℕ) {z : Site}
    (hz : z ∈ squareDisk R) {η : Fin (diskExitBlockLength R) → Direction}
    (hη : η ∈ allEastBlock (diskExitBlockLength R)) :
    blockWalkFrom z η ⟨diskExitBlockLength R, by omega⟩ ∉ squareDisk R := by
  have hzlow : -(R : ℤ) ≤ z.1 := by
    simpa [squareDisk] using (Finset.mem_product.mp hz).1 |> Finset.mem_Icc.mp |>.1
  have hcoord :
      (blockWalkFrom z η ⟨diskExitBlockLength R, by omega⟩).1 =
        z.1 + diskExitBlockLength R := by
    simp only [blockWalkFrom, Prod.fst_add]
    rw [show (∑ i : Fin (diskExitBlockLength R), directionStep (η i)) =
        ∑ _i : Fin (diskExitBlockLength R), (1, 0) by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hη i]
      rfl]
    simp
  intro hmem
  have hzup :
      (blockWalkFrom z η ⟨diskExitBlockLength R, by omega⟩).1 ≤ (R : ℤ) := by
    simpa [squareDisk] using (Finset.mem_product.mp hmem).1 |> Finset.mem_Icc.mp |>.2
  rw [hcoord] at hzup
  dsimp only [diskExitBlockLength] at hzup
  omega

/-! A uniform finite-domain exit tail.  This is deliberately elementary: in
each block of `2R+1` increments, the all-east word forces exit from the square
from every possible starting site in the square. -/

def survivalEvent (D : Set Site) (x : Site) (n : ℕ) : Set (ℕ → Direction) :=
  {ω | ∀ r, r ≤ n → walkFrom x ω r ∈ D}

noncomputable def survivalWeight (D : Set Site) (x : Site) (n : ℕ) : ℝ≥0∞ :=
  incrementLaw (survivalEvent D x n)

theorem measurableSet_survivalEvent_iidHistory
    (D : Set Site) (x : Site) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n] (survivalEvent D x n) := by
  have heq : survivalEvent D x n =
      ⋂ r : ℕ, ⋂ (_ : r ≤ n), {ω | walkFrom x ω r ∈ D} := by
    ext ω
    simp [survivalEvent]
  rw [heq]
  exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
    (Set.to_countable D).measurableSet.preimage
      (measurable_walkFrom_iidHistory x hr)

theorem killedEndpointEvent_subset_survivalEvent
    (D : Set Site) (x y : Site) (n : ℕ) :
    killedEndpointEvent D x y n ⊆ survivalEvent D x n := by
  intro ω hω
  exact hω.1

theorem killedWeight_le_survivalWeight
    (D : Set Site) (x y : Site) (n : ℕ) :
    killedWeight D x y n ≤ survivalWeight D x n := by
  exact measure_mono (killedEndpointEvent_subset_survivalEvent D x y n)

theorem allEastBlock_eq_singleton (m : ℕ) :
    allEastBlock m = {(fun _ : Fin m ↦ (0 : Direction))} := by
  ext η
  simp [allEastBlock, funext_iff]

theorem finitePi_allEastBlock (m : ℕ) :
    (Measure.infinitePi fun _ : Fin m ↦ directionLaw) (allEastBlock m) =
      (4 : ℝ≥0∞)⁻¹ ^ m := by
  rw [allEastBlock_eq_singleton, Measure.infinitePi_singleton_of_fintype]
  simp [directionLaw]

theorem survival_succBlock_subset (R k : ℕ) (x : Site) :
    survivalEvent (squareDisk R : Set Site) x (k + diskExitBlockLength R) ⊆
      survivalEvent (squareDisk R : Set Site) x k ∩
        iidBlock (X := Direction) k (diskExitBlockLength R) ⁻¹'
          (allEastBlock (diskExitBlockLength R))ᶜ := by
  intro ω hω
  constructor
  · intro r hr
    exact hω r (by omega)
  · intro hEast
    have hxk : walkFrom x ω k ∈ squareDisk R := hω k (by omega)
    have hExit := repeatedEast_exits_squareDisk R hxk hEast
    have heq := blockWalkFrom_iidBlock_eq_walkFrom x k
      (diskExitBlockLength R) ω
      ⟨diskExitBlockLength R, by omega⟩
    apply hExit
    rw [heq]
    exact hω (k + diskExitBlockLength R) le_rfl

theorem survivalWeight_succBlock_le (R k : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x
        (k + diskExitBlockLength R) ≤
      survivalWeight (squareDisk R : Set Site) x k *
        (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) := by
  calc
    survivalWeight (squareDisk R : Set Site) x
        (k + diskExitBlockLength R) ≤
        incrementLaw
          (survivalEvent (squareDisk R : Set Site) x k ∩
            iidBlock (X := Direction) k (diskExitBlockLength R) ⁻¹'
              (allEastBlock (diskExitBlockLength R))ᶜ) :=
      measure_mono (survival_succBlock_subset R k x)
    _ = survivalWeight (squareDisk R : Set Site) x k *
        (Measure.infinitePi fun _ : Fin (diskExitBlockLength R) ↦ directionLaw)
          ((allEastBlock (diskExitBlockLength R))ᶜ) := by
      exact measure_inter_iidBlock_eq_mul directionLaw k (diskExitBlockLength R)
        (measurableSet_survivalEvent_iidHistory _ _ k)
        (MeasurableSet.of_discrete :
          MeasurableSet ((allEastBlock (diskExitBlockLength R))ᶜ))
    _ = survivalWeight (squareDisk R : Set Site) x k *
        (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) := by
      congr 1
      rw [measure_compl (MeasurableSet.of_discrete)
        (by rw [finitePi_allEastBlock]; simp)]
      rw [finitePi_allEastBlock]
      simp

theorem survivalEvent_antitone {D : Set Site} {x : Site} {m n : ℕ}
    (hmn : m ≤ n) : survivalEvent D x n ⊆ survivalEvent D x m := by
  intro ω hω r hr
  exact hω r (hr.trans hmn)

theorem survivalWeight_antitone {D : Set Site} {x : Site} {m n : ℕ}
    (hmn : m ≤ n) : survivalWeight D x n ≤ survivalWeight D x m :=
  measure_mono (survivalEvent_antitone hmn)

theorem survivalWeight_mulBlock_le (R m : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x
        (m * diskExitBlockLength R) ≤
      (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) ^ m := by
  induction m with
  | zero =>
      simp only [zero_mul, pow_zero]
      calc
        survivalWeight (squareDisk R : Set Site) x 0 ≤ incrementLaw Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  | succ m ih =>
      calc
        survivalWeight (squareDisk R : Set Site) x
            ((m + 1) * diskExitBlockLength R) =
            survivalWeight (squareDisk R : Set Site) x
              (m * diskExitBlockLength R + diskExitBlockLength R) := by
                rw [Nat.add_mul]
                simp
        _ ≤ survivalWeight (squareDisk R : Set Site) x
              (m * diskExitBlockLength R) *
              (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) :=
          survivalWeight_succBlock_le R (m * diskExitBlockLength R) x
        _ ≤ (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) ^ m *
              (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) :=
          mul_le_mul ih le_rfl zero_le zero_le
        _ = (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) ^ (m + 1) := by
          rw [pow_succ]

theorem survivalWeight_le_blockGeometric (R n : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x n ≤
      (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) ^
        (n / diskExitBlockLength R) := by
  calc
    survivalWeight (squareDisk R : Set Site) x n ≤
        survivalWeight (squareDisk R : Set Site) x
          ((n / diskExitBlockLength R) * diskExitBlockLength R) := by
      apply survivalWeight_antitone
      exact Nat.div_mul_le_self n (diskExitBlockLength R)
    _ ≤ (1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R) ^
        (n / diskExitBlockLength R) :=
      survivalWeight_mulBlock_le R (n / diskExitBlockLength R) x

theorem tsum_pow_div_lt_top (L : ℕ) (hL : 0 < L) (q : ℝ≥0∞) (hq : q < 1) :
    (∑' n : ℕ, q ^ (n / L)) < ∞ := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have heq : (∑' n : ℕ, q ^ (n / L)) =
      (L : ℝ≥0∞) * (∑' m : ℕ, q ^ m) := by
    calc
      (∑' n : ℕ, q ^ (n / L)) =
          ∑' p : ℕ × Fin L, q ^ p.1 := by
        simpa using (Nat.divModEquiv L).tsum_eq (fun p : ℕ × Fin L ↦ q ^ p.1)
      _ = ∑' m : ℕ, ∑' _r : Fin L, q ^ m := by
        change (∑' p : ℕ × Fin L, (fun m (_r : Fin L) ↦ q ^ m) p.1 p.2) = _
        exact @ENNReal.tsum_prod ℕ (Fin L) (fun m _r ↦ q ^ m)
      _ = ∑' m : ℕ, (L : ℝ≥0∞) * q ^ m := by
        apply tsum_congr
        intro m
        simp [tsum_fintype]
      _ = (L : ℝ≥0∞) * (∑' m : ℕ, q ^ m) :=
        ENNReal.tsum_mul_left
  rw [heq]
  exact ENNReal.mul_lt_top (by simp) (tsum_geometric_lt_top.2 hq)

theorem diskGreen_lt_top (R : ℕ) (x y : Site) : diskGreen R x y < ∞ := by
  let q : ℝ≥0∞ := 1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R
  have hq : q < 1 := by
    apply ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
    simp [diskExitBlockLength]
  have hmajorant :
      (∑' n : ℕ, q ^ (n / diskExitBlockLength R)) < ∞ :=
    tsum_pow_div_lt_top (diskExitBlockLength R)
      (by simp [diskExitBlockLength]) q hq
  apply lt_of_le_of_lt _ hmajorant
  unfold diskGreen killedGreen
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    killedWeight (squareDisk R : Set Site) x y n ≤
        survivalWeight (squareDisk R : Set Site) x n :=
      killedWeight_le_survivalWeight _ _ _ _
    _ ≤ q ^ (n / diskExitBlockLength R) := by
      exact survivalWeight_le_blockGeometric R n x

theorem diskGreen_ne_top (R : ℕ) (x y : Site) : diskGreen R x y ≠ ∞ :=
  ne_of_lt (diskGreen_lt_top R x y)

/-- The finite-square Green ratio, with no finiteness hypothesis left over. -/
theorem diskHittingWeight_eq_green_div_finiteDisk
    {R : ℕ} {x y : Site} (hy : y ∈ squareDisk R) :
    diskHittingWeight R x y = diskGreen R x y / diskGreen R y y :=
  diskHittingWeight_eq_green_div hy (diskGreen_ne_top R y y)

/-- The finite-square escape/diagonal-Green identity, again unconditional
apart from the natural requirement that the starting site lies in the disk. -/
theorem diskEscapeWeight_eq_inv_green_finiteDisk
    {R : ℕ} {y : Site} (hy : y ∈ squareDisk R) :
    diskEscapeWeight R y = (diskGreen R y y)⁻¹ :=
  diskEscapeWeight_eq_inv_green hy (diskGreen_ne_top R y y)

/-- The path eventually leaves `D`. -/
def eventuallyExitEvent (D : Set Site) (x : Site) : Set (ℕ → Direction) :=
  {ω | ∃ n : ℕ, walkFrom x ω n ∉ D}

/-- The standard finite-domain escape event: exit eventually, with no positive
return to the starting point before the killing boundary is crossed. -/
def exitBeforeReturnEvent (D : Set Site) (y : Site) : Set (ℕ → Direction) :=
  escapeBeforeReturnEvent D y ∩ eventuallyExitEvent D y

def neverExitEvent (D : Set Site) (x : Site) : Set (ℕ → Direction) :=
  (eventuallyExitEvent D x)ᶜ

theorem neverExitEvent_subset_survivalEvent (D : Set Site) (x : Site) (n : ℕ) :
    neverExitEvent D x ⊆ survivalEvent D x n := by
  intro ω hω r hr
  by_contra hout
  exact hω ⟨r, hout⟩

theorem measure_neverExitEvent_squareDisk_eq_zero (R : ℕ) (x : Site) :
    incrementLaw (neverExitEvent (squareDisk R : Set Site) x) = 0 := by
  let q : ℝ≥0∞ := 1 - (4 : ℝ≥0∞)⁻¹ ^ diskExitBlockLength R
  have hq : q < 1 := by
    apply ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
    simp [diskExitBlockLength]
  apply ENNReal.eq_zero_of_le_mul_pow (ε := 1) hq
  intro m
  simpa using
    (calc
      incrementLaw (neverExitEvent (squareDisk R : Set Site) x) ≤
          survivalWeight (squareDisk R : Set Site) x
            (m * diskExitBlockLength R) :=
        measure_mono (neverExitEvent_subset_survivalEvent _ _ _)
      _ ≤ q ^ m := survivalWeight_mulBlock_le R m x)

theorem measure_exitBeforeReturnEvent_eq_escapeWeight
    (R : ℕ) (y : Site) :
    incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) y) =
      diskEscapeWeight R y := by
  rw [diskEscapeWeight, escapeWeight_eq_measure_escapeBeforeReturn]
  apply measure_eq_measure_of_null_sdiff Set.inter_subset_left
  apply measure_mono_null _ (measure_neverExitEvent_squareDisk_eq_zero R y)
  intro ω hω
  have hEscape :
      ω ∈ escapeBeforeReturnEvent (squareDisk R : Set Site) y := hω.1
  have hNotExit :
      ω ∉ eventuallyExitEvent (squareDisk R : Set Site) y := by
    intro hExit
    exact hω.2 ⟨hEscape, hExit⟩
  exact hNotExit

/-- Event-level finite-disk hitting formula. -/
theorem measure_hitBeforeExitEvent_eq_green_div
    {R : ℕ} {x y : Site} (hy : y ∈ squareDisk R) :
    incrementLaw (hitBeforeExitEvent (squareDisk R : Set Site) x y) =
      diskGreen R x y / diskGreen R y y := by
  rw [← hittingWeight_eq_measure_hitBeforeExit]
  exact diskHittingWeight_eq_green_div_finiteDisk hy

/-- Event-level finite-disk escape formula. -/
theorem measure_escapeBeforeReturnEvent_eq_inv_green
    {R : ℕ} {y : Site} (hy : y ∈ squareDisk R) :
    incrementLaw (escapeBeforeReturnEvent (squareDisk R : Set Site) y) =
      (diskGreen R y y)⁻¹ := by
  rw [← escapeWeight_eq_measure_escapeBeforeReturn]
  exact diskEscapeWeight_eq_inv_green_finiteDisk hy

/-- The usual finite-disk exit-before-positive-return probability. -/
theorem measure_exitBeforeReturnEvent_eq_inv_green
    {R : ℕ} {y : Site} (hy : y ∈ squareDisk R) :
    incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) y) =
      (diskGreen R y y)⁻¹ := by
  rw [measure_exitBeforeReturnEvent_eq_escapeWeight]
  exact diskEscapeWeight_eq_inv_green_finiteDisk hy

/-! Translation invariance and domain monotonicity. -/

def translateDomain (a : Site) (D : Set Site) : Set Site :=
  {z | z - a ∈ D}

@[simp] theorem mem_translateDomain_add (a z : Site) (D : Set Site) :
    a + z ∈ translateDomain a D ↔ z ∈ D := by
  simp [translateDomain]

theorem walkFrom_add (a x : Site) (ω : ℕ → Direction) (n : ℕ) :
    walkFrom (a + x) ω n = a + walkFrom x ω n := by
  simp [walkFrom, add_assoc]

theorem killedEndpointEvent_translate (a x y : Site) (D : Set Site) (n : ℕ) :
    killedEndpointEvent (translateDomain a D) (a + x) (a + y) n =
      killedEndpointEvent D x y n := by
  ext ω
  simp only [killedEndpointEvent, Set.mem_ofPred_eq, walkFrom_add,
    mem_translateDomain_add, add_left_cancel_iff]

theorem firstEntranceEvent_translate (a x y : Site) (D : Set Site) (n : ℕ) :
    firstEntranceEvent (translateDomain a D) (a + x) (a + y) n =
      firstEntranceEvent D x y n := by
  ext ω
  simp only [firstEntranceEvent, Set.mem_ofPred_eq, walkFrom_add,
    mem_translateDomain_add, add_left_cancel_iff]
  constructor
  · rintro ⟨hstay, hend, havoid⟩
    exact ⟨hstay, hend, fun r hr hry ↦ havoid r hr (congrArg (a + ·) hry)⟩
  · rintro ⟨hstay, hend, havoid⟩
    exact ⟨hstay, hend, fun r hr hry ↦ havoid r hr (add_left_cancel hry)⟩

theorem killedWeight_translate (a x y : Site) (D : Set Site) (n : ℕ) :
    killedWeight (translateDomain a D) (a + x) (a + y) n =
      killedWeight D x y n := by
  simp only [killedWeight, killedEndpointEvent_translate]

theorem entranceWeight_translate (a x y : Site) (D : Set Site) (n : ℕ) :
    entranceWeight (translateDomain a D) (a + x) (a + y) n =
      entranceWeight D x y n := by
  simp only [entranceWeight, firstEntranceEvent_translate]

theorem killedGreen_translate (a x y : Site) (D : Set Site) :
    killedGreen (translateDomain a D) (a + x) (a + y) = killedGreen D x y := by
  unfold killedGreen
  apply tsum_congr
  exact killedWeight_translate a x y D

theorem hittingWeight_translate (a x y : Site) (D : Set Site) :
    hittingWeight (translateDomain a D) (a + x) (a + y) = hittingWeight D x y := by
  unfold hittingWeight
  apply tsum_congr
  exact entranceWeight_translate a x y D

theorem killedEndpointEvent_mono {D E : Set Site} (hDE : D ⊆ E)
    (x y : Site) (n : ℕ) :
    killedEndpointEvent D x y n ⊆ killedEndpointEvent E x y n := by
  intro ω hω
  exact ⟨fun r hr ↦ hDE (hω.1 r hr), hω.2⟩

theorem firstEntranceEvent_mono {D E : Set Site} (hDE : D ⊆ E)
    (x y : Site) (n : ℕ) :
    firstEntranceEvent D x y n ⊆ firstEntranceEvent E x y n := by
  intro ω hω
  exact ⟨fun r hr ↦ hDE (hω.1 r hr), hω.2⟩

theorem killedWeight_mono {D E : Set Site} (hDE : D ⊆ E)
    (x y : Site) (n : ℕ) :
    killedWeight D x y n ≤ killedWeight E x y n :=
  measure_mono (killedEndpointEvent_mono hDE x y n)

theorem entranceWeight_mono {D E : Set Site} (hDE : D ⊆ E)
    (x y : Site) (n : ℕ) :
    entranceWeight D x y n ≤ entranceWeight E x y n :=
  measure_mono (firstEntranceEvent_mono hDE x y n)

theorem killedGreen_mono {D E : Set Site} (hDE : D ⊆ E) (x y : Site) :
    killedGreen D x y ≤ killedGreen E x y := by
  exact ENNReal.tsum_le_tsum fun n ↦ killedWeight_mono hDE x y n

theorem hittingWeight_mono {D E : Set Site} (hDE : D ⊆ E) (x y : Site) :
    hittingWeight D x y ≤ hittingWeight E x y := by
  exact ENNReal.tsum_le_tsum fun n ↦ entranceWeight_mono hDE x y n

theorem squareDisk_mono {r R : ℕ} (hrR : r ≤ R) :
    (squareDisk r : Set Site) ⊆ (squareDisk R : Set Site) := by
  intro z hz
  change z ∈ squareDisk r at hz
  change z ∈ squareDisk R
  rcases Finset.mem_product.mp hz with ⟨hz1, hz2⟩
  rcases Finset.mem_Icc.mp hz1 with ⟨hz1l, hz1u⟩
  rcases Finset.mem_Icc.mp hz2 with ⟨hz2l, hz2u⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega

theorem diskGreen_mono {r R : ℕ} (hrR : r ≤ R) (x y : Site) :
    diskGreen r x y ≤ diskGreen R x y :=
  killedGreen_mono (squareDisk_mono hrR) x y

theorem diskHittingWeight_mono {r R : ℕ} (hrR : r ≤ R) (x y : Site) :
    diskHittingWeight r x y ≤ diskHittingWeight R x y :=
  hittingWeight_mono (squareDisk_mono hrR) x y

end Erdos1166.KilledGreen
