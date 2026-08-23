import ErdosProblems.Erdos1166.Erdos1166HLOZGreenBounds

namespace Erdos1166.KilledGreen

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical Topology

def firstStepThenKilledEvent
    (D : Set Site) (x y : Site) (n : ℕ) (d : Direction) :
    Set (ℕ → Direction) :=
  {ω | ω 0 = d} ∩
    iidBlock (X := Direction) 1 n ⁻¹' blockKilledEndpoint D
      (x + directionStep d) y n

theorem measurableSet_firstDirection_iidHistory (d : Direction) :
    MeasurableSet[iidHistory (X := Direction) 1]
      {ω : ℕ → Direction | ω 0 = d} := by
  let _ : MeasurableSpace (ℕ → Direction) := iidHistory (X := Direction) 1
  apply measurableSet_eq_fun _ measurable_const
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le 0 (le_iSup_of_le (by omega) le_rfl)

theorem measurableSet_firstStepThenKilledEvent
    (D : Set Site) (x y : Site) (n : ℕ) (d : Direction) :
    MeasurableSet (firstStepThenKilledEvent D x y n d) := by
  exact (iidHistory_le 1 _ (measurableSet_firstDirection_iidHistory d)).inter
    ((measurable_iidBlock 1 n) (measurableSet_blockKilledEndpoint D
      (x + directionStep d) y n))

theorem measure_firstStepThenKilledEvent
    (D : Set Site) (x y : Site) (n : ℕ) (d : Direction) :
    incrementLaw (firstStepThenKilledEvent D x y n d) =
      (4 : ℝ≥0∞)⁻¹ * killedWeight D (x + directionStep d) y n := by
  have h := measure_inter_iidBlock_eq_mul directionLaw 1 n
    (measurableSet_firstDirection_iidHistory d)
    (measurableSet_blockKilledEndpoint D (x + directionStep d) y n)
  rw [finitePi_blockKilledEndpoint_eq] at h
  have hdir : (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
      {ω : ℕ → Direction | ω 0 = d} = (4 : ℝ≥0∞)⁻¹ := by
    simpa [incrementLaw] using increment_direction_prob 0 d
  rw [hdir] at h
  simpa [incrementLaw, firstStepThenKilledEvent, killedWeight] using h

theorem walkFrom_one (x : Site) (ω : ℕ → Direction) :
    walkFrom x ω 1 = x + directionStep (ω 0) := by
  simp [walkFrom, simpleRandomWalk]

theorem iUnion_firstStepThenKilledEvent
    (D : Set Site) (x y : Site) (n : ℕ) (hx : x ∈ D) :
    (⋃ d : Direction, firstStepThenKilledEvent D x y n d) =
      killedEndpointEvent D x y (n + 1) := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨d, hd, hsuffix⟩
    have hstart : walkFrom x ω 1 = x + directionStep d := by
      rw [walkFrom_one, hd]
    constructor
    · intro r hr
      by_cases hr0 : r = 0
      · simpa [hr0, walkFrom, simpleRandomWalk] using hx
      · let q : Fin (n + 1) := ⟨r - 1, by omega⟩
        have hblock := hsuffix.1 q
        have heq := blockWalkFrom_iidBlock_eq_walkFrom x 1 n ω q
        rw [hstart] at heq
        have htime : 1 + (q : ℕ) = r := by
          dsimp only [q]
          omega
        rw [htime] at heq
        exact heq ▸ hblock
    · let q : Fin (n + 1) := ⟨n, by omega⟩
      have heq := blockWalkFrom_iidBlock_eq_walkFrom x 1 n ω q
      rw [hstart] at heq
      have htime : 1 + (q : ℕ) = n + 1 := by
        dsimp only [q]
        omega
      rw [htime] at heq
      exact heq ▸ hsuffix.2
  · intro hω
    apply Set.mem_iUnion.mpr
    refine ⟨ω 0, rfl, ?_⟩
    have hstart : walkFrom x ω 1 = x + directionStep (ω 0) := walkFrom_one x ω
    constructor
    · intro q
      have heq := blockWalkFrom_iidBlock_eq_walkFrom x 1 n ω q
      rw [hstart] at heq
      exact heq ▸ hω.1 (1 + q) (by omega)
    · let q : Fin (n + 1) := ⟨n, by omega⟩
      have heq := blockWalkFrom_iidBlock_eq_walkFrom x 1 n ω q
      rw [hstart] at heq
      have htime : 1 + (q : ℕ) = n + 1 := by
        dsimp only [q]
        omega
      rw [htime] at heq
      exact heq ▸ hω.2

theorem pairwiseDisjoint_firstStepThenKilledEvent
    (D : Set Site) (x y : Site) (n : ℕ) :
    Pairwise fun d e ↦ Disjoint
      (firstStepThenKilledEvent D x y n d)
      (firstStepThenKilledEvent D x y n e) := by
  intro d e hde
  rw [Set.disjoint_left]
  intro ω hd he
  exact hde (hd.1.symm.trans he.1)

theorem killedEndpointEvent_empty_of_start_not_mem
    {D : Set Site} {x y : Site} {n : ℕ} (hx : x ∉ D) :
    killedEndpointEvent D x y n = ∅ := by
  ext ω
  simp only [killedEndpointEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hω
  exact hx (by simpa [walkFrom, simpleRandomWalk] using hω.1 0 (Nat.zero_le n))

theorem killedWeight_succ_eq_step_sum
    (D : Set Site) (x y : Site) (n : ℕ) :
    killedWeight D x y (n + 1) =
      if x ∈ D then
        ∑ d : Direction,
          (4 : ℝ≥0∞)⁻¹ * killedWeight D (x + directionStep d) y n
      else 0 := by
  classical
  by_cases hx : x ∈ D
  · rw [if_pos hx, killedWeight, ← iUnion_firstStepThenKilledEvent D x y n hx]
    rw [measure_iUnion (pairwiseDisjoint_firstStepThenKilledEvent D x y n)
      (measurableSet_firstStepThenKilledEvent D x y n)]
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    exact measure_firstStepThenKilledEvent D x y n d
  · rw [if_neg hx, killedWeight, killedEndpointEvent_empty_of_start_not_mem hx]
    exact measure_empty

theorem killedWeight_zero_eq_indicator (D : Set Site) (x y : Site) :
    killedWeight D x y 0 = if x ∈ D ∧ x = y then 1 else 0 := by
  classical
  by_cases hx : x ∈ D
  · by_cases hxy : x = y
    · subst y
      rw [killedWeight_zero_self hx]
      simp [hx]
    · have hevent : killedEndpointEvent D x y 0 = ∅ := by
        ext ω
        simp [killedEndpointEvent, walkFrom, simpleRandomWalk, hxy]
      rw [killedWeight, hevent, measure_empty]
      simp [hx, hxy]
  · rw [killedWeight, killedEndpointEvent_empty_of_start_not_mem hx,
      measure_empty]
    simp [hx]

theorem killedGreen_eq_indicator_add_step_sum
    (D : Set Site) (x y : Site) (hx : x ∈ D) :
    killedGreen D x y =
      (if x = y then 1 else 0) +
        (4 : ℝ≥0∞)⁻¹ * ∑ d : Direction,
          killedGreen D (x + directionStep d) y := by
  classical
  unfold killedGreen
  calc
    (∑' n : ℕ, killedWeight D x y n) =
        killedWeight D x y 0 + ∑' n : ℕ, killedWeight D x y (n + 1) :=
      tsum_eq_zero_add' ENNReal.summable
    _ = (if x = y then 1 else 0) +
        ∑' n : ℕ, ∑ d : Direction,
          (4 : ℝ≥0∞)⁻¹ * killedWeight D (x + directionStep d) y n := by
      rw [killedWeight_zero_eq_indicator]
      simp only [hx, true_and]
      apply congrArg ((if x = y then 1 else 0) + ·)
      apply tsum_congr
      intro n
      rw [killedWeight_succ_eq_step_sum, if_pos hx]
    _ = (if x = y then 1 else 0) +
        (4 : ℝ≥0∞)⁻¹ * ∑ d : Direction,
          ∑' n : ℕ, killedWeight D (x + directionStep d) y n := by
      congr 1
      calc
        (∑' n : ℕ, ∑ d : Direction,
            (4 : ℝ≥0∞)⁻¹ * killedWeight D (x + directionStep d) y n) =
            ∑' n : ℕ, ∑' d : Direction,
              (4 : ℝ≥0∞)⁻¹ * killedWeight D (x + directionStep d) y n := by
          apply tsum_congr
          intro n
          rw [tsum_fintype]
        _ = ∑' d : Direction, ∑' n : ℕ,
              (4 : ℝ≥0∞)⁻¹ * killedWeight D (x + directionStep d) y n :=
          ENNReal.tsum_comm
        _ = ∑ d : Direction,
              (4 : ℝ≥0∞)⁻¹ *
                (∑' n : ℕ, killedWeight D (x + directionStep d) y n) := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro d hd
          exact ENNReal.tsum_mul_left
        _ = (4 : ℝ≥0∞)⁻¹ * ∑ d : Direction,
              ∑' n : ℕ, killedWeight D (x + directionStep d) y n := by
          rw [Finset.mul_sum]

theorem diskGreen_toReal_eq_indicator_add_step_average
    (R : ℕ) (x y : Site) (hx : x ∈ squareDisk R) :
    (diskGreen R x y).toReal =
      (if x = y then 1 else 0) +
        (1 / 4 : ℝ) * ∑ d : Direction,
          (diskGreen R (x + directionStep d) y).toReal := by
  have h := killedGreen_eq_indicator_add_step_sum
    (squareDisk R : Set Site) x y hx
  have hsum : (∑ d : Direction,
      diskGreen R (x + directionStep d) y) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro d hd
    exact diskGreen_ne_top R _ _
  have hmul : (4 : ℝ≥0∞)⁻¹ * ∑ d : Direction,
      diskGreen R (x + directionStep d) y ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hsum
  have hindicator : (if x = y then (1 : ℝ≥0∞) else 0) ≠ ∞ := by
    split_ifs <;> simp
  have hreal := congrArg ENNReal.toReal h
  change (diskGreen R x y).toReal =
    ((if x = y then 1 else 0) +
      (4 : ℝ≥0∞)⁻¹ * ∑ d : Direction,
        diskGreen R (x + directionStep d) y).toReal at hreal
  rw [ENNReal.toReal_add hindicator hmul, ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun d hd ↦ diskGreen_ne_top R _ _)] at hreal
  norm_num at hreal
  by_cases hxy : x = y <;> simp [hxy] at hreal ⊢ <;> exact hreal

noncomputable def stepAverage (u : Site → ℝ) (x : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction, u (x + directionStep d)

theorem stepAverage_eq_four_neighbors (u : Site → ℝ) (x : Site) :
    stepAverage u x = (1 / 4 : ℝ) *
      (u (x + (1, 0)) + u (x + (-1, 0)) +
        u (x + (0, 1)) + u (x + (0, -1))) := by
  simp [stepAverage, directionStep, Fin.sum_univ_succ]
  ring

theorem add_directionStep_mem_squareDisk_succ
    {R : ℕ} {x : Site} (hx : x ∈ squareDisk R) (d : Direction) :
    x + directionStep d ∈ squareDisk (R + 1) := by
  change x ∈ squareDisk R at hx
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  rcases Finset.mem_Icc.mp hx1 with ⟨hx1l, hx1u⟩
  rcases Finset.mem_Icc.mp hx2 with ⟨hx2l, hx2u⟩
  unfold squareDisk
  apply Finset.mem_product.mpr
  fin_cases d <;> simp [directionStep] <;> omega

theorem east_step_of_harmonic_at_square_max
    {R : ℕ} {u : Site → ℝ} {B : ℝ} {z : Site}
    (hz : z ∈ squareDisk R)
    (hmax : ∀ w ∈ squareDisk R, u w ≤ u z)
    (hboundary : ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R → u w ≤ B)
    (hBz : B < u z) (hharm : u z = stepAverage u z) :
    z + (1, 0) ∈ squareDisk R ∧ u (z + (1, 0)) = u z := by
  have hneighbor (d : Direction) : u (z + directionStep d) ≤ u z := by
    by_cases hd : z + directionStep d ∈ squareDisk R
    · exact hmax _ hd
    · exact (hboundary _ (add_directionStep_mem_squareDisk_succ hz d) hd).trans hBz.le
  have h0 := hneighbor (0 : Direction)
  have h1 := hneighbor (1 : Direction)
  have h2 := hneighbor (2 : Direction)
  have h3 := hneighbor (3 : Direction)
  have hfour := stepAverage_eq_four_neighbors u z
  rw [hfour] at hharm
  simp [directionStep] at h0 h1 h2 h3
  have heq : u (z + (1, 0)) = u z := by
    nlinarith
  refine ⟨?_, heq⟩
  by_contra hout
  have hle := hboundary (z + (1, 0))
    (by simpa [directionStep] using
      add_directionStep_mem_squareDisk_succ hz (0 : Direction)) hout
  linarith

/-- Maximum principle on the finite square, proved by propagating an interior
maximum along east edges until it would leave the square. -/
theorem square_maximum_principle
    {R : ℕ} {u : Site → ℝ} {B : ℝ}
    (hharm : ∀ z ∈ squareDisk R, u z = stepAverage u z)
    (hboundary : ∀ z ∈ squareDisk (R + 1), z ∉ squareDisk R → u z ≤ B) :
    ∀ x ∈ squareDisk R, u x ≤ B := by
  intro x hx
  by_contra hnot
  have hBx : B < u x := lt_of_not_ge hnot
  have hnonempty : (squareDisk R).Nonempty := by
    refine ⟨0, ?_⟩
    simp [squareDisk]
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (squareDisk R) u hnonempty
  have hxle : u x ≤ u z := hmax x hx
  have hBz : B < u z := hBx.trans_le hxle
  have hprop : ∀ k : ℕ, k ≤ 2 * R + 1 →
      z + ((k : ℤ), 0) ∈ squareDisk R ∧
        u (z + ((k : ℤ), 0)) = u z := by
    intro k hk
    induction k with
    | zero =>
        have hz0 : z + (((0 : ℕ) : ℤ), 0) = z := by
          ext <;> simp
        constructor
        · rw [hz0]
          exact hz
        · rw [hz0]
    | succ k ih =>
        have hk' : k ≤ 2 * R + 1 := by omega
        rcases ih hk' with ⟨hmem, heq⟩
        have hmax' : ∀ w ∈ squareDisk R,
            u w ≤ u (z + ((k : ℤ), 0)) := by
          intro w hw
          simpa [heq] using hmax w hw
        have hB' : B < u (z + ((k : ℤ), 0)) := by simpa [heq] using hBz
        have hstep := east_step_of_harmonic_at_square_max hmem hmax'
          hboundary hB' (hharm _ hmem)
        have hadd : z + (((k + 1 : ℕ) : ℤ), 0) =
            (z + ((k : ℤ), 0)) + (1, 0) := by
          ext
          · change z.1 + ((k + 1 : ℕ) : ℤ) = z.1 + (k : ℤ) + 1
            push_cast
            ring
          · simp
        rw [hadd]
        exact ⟨hstep.1, hstep.2.trans heq⟩
  have hfar := (hprop (2 * R + 1) le_rfl).1
  change z + (((2 * R + 1 : ℕ) : ℤ), 0) ∈ squareDisk R at hfar
  change z ∈ squareDisk R at hz
  rcases Finset.mem_product.mp hz with ⟨hz1, hz2⟩
  rcases Finset.mem_Icc.mp hz1 with ⟨hz1l, hz1u⟩
  rcases Finset.mem_product.mp hfar with ⟨hf1, hf2⟩
  rcases Finset.mem_Icc.mp hf1 with ⟨hf1l, hf1u⟩
  simp at hf1u
  omega

theorem killedGreen_eq_zero_of_start_not_mem
    {D : Set Site} {x y : Site} (hx : x ∉ D) :
    killedGreen D x y = 0 := by
  unfold killedGreen
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  rw [killedWeight, killedEndpointEvent_empty_of_start_not_mem hx, measure_empty]

theorem diskGreen_eq_zero_of_start_not_mem
    {R : ℕ} {x y : Site} (hx : x ∉ squareDisk R) :
    diskGreen R x y = 0 := by
  exact killedGreen_eq_zero_of_start_not_mem hx

theorem stepAverage_add (u v : Site → ℝ) (x : Site) :
    stepAverage (fun z ↦ u z + v z) x = stepAverage u x + stepAverage v x := by
  simp only [stepAverage, Finset.sum_add_distrib]
  ring

/-- The discrete Poisson equation characterizing the planar potential kernel.
The normalization is fixed separately; the comparison theorem below only needs
this equation. -/
def IsPlanarPotentialKernel (a : Site → ℝ) : Prop :=
  ∀ x, stepAverage a x = a x + if x = 0 then 1 else 0

/-- Adding a potential kernel to the killed Green column cancels its point
source, leaving a harmonic function in the square. -/
theorem diskGreen_add_potential_harmonic
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {x : Site} (hx : x ∈ squareDisk R) :
    (diskGreen R x 0).toReal + a x =
      stepAverage (fun z ↦ (diskGreen R z 0).toReal + a z) x := by
  rw [stepAverage_add]
  have hG := diskGreen_toReal_eq_indicator_add_step_average R x 0 hx
  change (diskGreen R x 0).toReal =
    (if x = 0 then 1 else 0) +
      stepAverage (fun z ↦ (diskGreen R z 0).toReal) x at hG
  rw [ha x]
  linarith

/-- Potential-kernel comparison for a square-killed Green column.  Thus a
boundary upper bound for `a`, together with a lower bound at `y`, is exactly
the remaining spatial input for an off-diagonal Green estimate. -/
theorem diskGreen_toReal_le_boundary_sub_potential
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a) {B : ℝ}
    (hboundary : ∀ z ∈ squareDisk (R + 1), z ∉ squareDisk R → a z ≤ B)
    {y : Site} (hy : y ∈ squareDisk R) :
    (diskGreen R y 0).toReal ≤ B - a y := by
  let u : Site → ℝ := fun z ↦ (diskGreen R z 0).toReal + a z
  have hharm : ∀ z ∈ squareDisk R, u z = stepAverage u z := by
    intro z hz
    exact diskGreen_add_potential_harmonic ha hz
  have hubound : ∀ z ∈ squareDisk (R + 1), z ∉ squareDisk R → u z ≤ B := by
    intro z hz hzo
    have hzero : diskGreen R z 0 = 0 := diskGreen_eq_zero_of_start_not_mem hzo
    change (diskGreen R z 0).toReal + a z ≤ B
    rw [hzero]
    simpa using hboundary z hz hzo
  have hmax := square_maximum_principle hharm hubound y hy
  change (diskGreen R y 0).toReal + a y ≤ B at hmax
  linarith

theorem diskGreen_toReal_le_potential_oscillation
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {upper lower : ℝ}
    (hboundary : ∀ z ∈ squareDisk (R + 1), z ∉ squareDisk R → a z ≤ upper)
    {y : Site} (hy : y ∈ squareDisk R) (hlower : lower ≤ a y) :
    (diskGreen R y 0).toReal ≤ upper - lower := by
  have h := diskGreen_toReal_le_boundary_sub_potential ha hboundary hy
  linarith

/-- The potential oscillation estimate plugged directly into the previously
proved diagonal Green lower bound. -/
theorem hitZeroBeforeExit_real_le_potential_oscillation_div_log
    {R : ℕ} (hR : 2 ≤ R) {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {upper lower : ℝ}
    (hboundary : ∀ z ∈ squareDisk (R + 1), z ∉ squareDisk R → a z ≤ upper)
    {y : Site} (hy : y ∈ squareDisk R) (hlower : lower ≤ a y) :
    incrementLaw.real
        (hitBeforeExitEvent (squareDisk R : Set Site) y 0) ≤
      8 * (upper - lower) / Real.log (R : ℝ) := by
  apply hitZeroBeforeExit_real_le_of_diskGreen_le hR y
  exact diskGreen_toReal_le_potential_oscillation ha hboundary hy hlower

/-- The unrestricted `n`-step transition weight from `x` to the origin. -/
noncomputable def freeOriginWeight (x : Site) (n : ℕ) : ℝ≥0∞ :=
  killedWeight Set.univ x 0 n

theorem freeOriginWeight_ne_top (x : Site) (n : ℕ) :
    freeOriginWeight x n ≠ ∞ := by
  exact measure_ne_top incrementLaw _

/-- The backward heat equation for unrestricted transition weights. -/
theorem freeOriginWeight_toReal_succ (x : Site) (n : ℕ) :
    (freeOriginWeight x (n + 1)).toReal =
      stepAverage (fun z ↦ (freeOriginWeight z n).toReal) x := by
  have h := killedWeight_succ_eq_step_sum (Set.univ : Set Site) x 0 n
  rw [if_pos (Set.mem_univ x)] at h
  change freeOriginWeight x (n + 1) =
    ∑ d : Direction, (4 : ℝ≥0∞)⁻¹ *
      freeOriginWeight (x + directionStep d) n at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun d hd ↦ ENNReal.mul_ne_top (by simp)
    (freeOriginWeight_ne_top (x + directionStep d) n))] at hr
  simp_rw [ENNReal.toReal_mul] at hr
  norm_num at hr
  simpa [stepAverage, Finset.mul_sum] using hr

/-- Finite truncations of the potential-kernel series
`sum_n (p_n(0,0) - p_n(x,0))`. -/
noncomputable def finitePotentialKernel (N : ℕ) (x : Site) : ℝ :=
  ∑ n ∈ Finset.range N,
    ((freeOriginWeight 0 n).toReal - (freeOriginWeight x n).toReal)

theorem stepAverage_zero : stepAverage (fun _ : Site ↦ (0 : ℝ)) = 0 := by
  funext x
  rw [stepAverage_eq_four_neighbors]
  simp

theorem stepAverage_const (c : ℝ) (x : Site) :
    stepAverage (fun _ : Site ↦ c) x = c := by
  rw [stepAverage_eq_four_neighbors]
  ring

theorem stepAverage_sub (u v : Site → ℝ) (x : Site) :
    stepAverage (fun z ↦ u z - v z) x = stepAverage u x - stepAverage v x := by
  simp only [stepAverage, Finset.sum_sub_distrib]
  ring

theorem stepAverage_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Site → ℝ) (x : Site) :
    stepAverage (fun z ↦ ∑ i ∈ s, f i z) x =
      ∑ i ∈ s, stepAverage (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stepAverage_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [stepAverage_add, ih]

theorem stepAverage_finitePotentialKernel (N : ℕ) (x : Site) :
    stepAverage (finitePotentialKernel N) x =
      ∑ n ∈ Finset.range N,
        ((freeOriginWeight 0 n).toReal - (freeOriginWeight x (n + 1)).toReal) := by
  unfold finitePotentialKernel
  rw [stepAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [stepAverage_sub, stepAverage_const, ← freeOriginWeight_toReal_succ]

theorem freeOriginWeight_zero_toReal (x : Site) :
    (freeOriginWeight x 0).toReal = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst x
    norm_num [freeOriginWeight, killedWeight_zero_eq_indicator]
  · norm_num [freeOriginWeight, killedWeight_zero_eq_indicator, hx]

/-- Every finite potential-kernel truncation satisfies the Poisson equation
up to the single explicit heat-kernel remainder at time `N`. -/
theorem finitePotentialKernel_poisson_defect (N : ℕ) (x : Site) :
    stepAverage (finitePotentialKernel N) x =
      finitePotentialKernel N x + (if x = 0 then 1 else 0) -
        (freeOriginWeight x N).toReal := by
  rw [stepAverage_finitePotentialKernel]
  unfold finitePotentialKernel
  have hsplit :
      (∑ n ∈ Finset.range N,
        ((freeOriginWeight 0 n).toReal - (freeOriginWeight x (n + 1)).toReal)) =
        (∑ n ∈ Finset.range N,
          ((freeOriginWeight 0 n).toReal - (freeOriginWeight x n).toReal)) +
        ∑ n ∈ Finset.range N,
          ((freeOriginWeight x n).toReal - (freeOriginWeight x (n + 1)).toReal) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hsplit, Finset.sum_range_sub', freeOriginWeight_zero_toReal]
  ring

theorem tendsto_stepAverage {ι : Type*} {l : Filter ι}
    {u : ι → Site → ℝ} {a : Site → ℝ}
    (h : ∀ z, Filter.Tendsto (fun i ↦ u i z) l (𝓝 (a z))) (x : Site) :
    Filter.Tendsto (fun i ↦ stepAverage (u i) x) l (𝓝 (stepAverage a x)) := by
  unfold stepAverage
  exact (tendsto_finsetSum Finset.univ fun d hd ↦ h (x + directionStep d)).const_mul _

/-- Pointwise convergence of the finite potential series, together with decay
of its explicit transition-probability defect, produces a genuine potential
kernel.  No optional-stopping or interchange of infinite sums is hidden here. -/
theorem isPlanarPotentialKernel_of_finite_tendsto
    {a : Site → ℝ}
    (ha : ∀ x, Filter.Tendsto (fun N ↦ finitePotentialKernel N x)
      Filter.atTop (𝓝 (a x)))
    (hdecay : ∀ x, Filter.Tendsto (fun N ↦ (freeOriginWeight x N).toReal)
      Filter.atTop (𝓝 0)) :
    IsPlanarPotentialKernel a := by
  intro x
  have hlhs := tendsto_stepAverage ha x
  have hrhs : Filter.Tendsto
      (fun N ↦ finitePotentialKernel N x + (if x = 0 then 1 else 0) -
        (freeOriginWeight x N).toReal)
      Filter.atTop
      (𝓝 (a x + (if x = 0 then 1 else 0) - 0)) :=
    ((ha x).add_const _).sub (hdecay x)
  have heq : (fun N ↦ stepAverage (finitePotentialKernel N) x) =
      fun N ↦ finitePotentialKernel N x + (if x = 0 then 1 else 0) -
        (freeOriginWeight x N).toReal := by
    funext N
    exact finitePotentialKernel_poisson_defect N x
  rw [heq] at hlhs
  have hlimit := tendsto_nhds_unique hlhs hrhs
  simpa using hlimit

theorem finitePotentialKernel_zero (N : ℕ) : finitePotentialKernel N 0 = 0 := by
  simp [finitePotentialKernel]

theorem finitePotentialKernel_limit_zero
    {a : Site → ℝ}
    (ha : ∀ x, Filter.Tendsto (fun N ↦ finitePotentialKernel N x)
      Filter.atTop (𝓝 (a x))) :
    a 0 = 0 := by
  have hzero : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds
  have hconv := ha 0
  simp only [finitePotentialKernel_zero] at hconv
  exact tendsto_nhds_unique hconv hzero


def FreeOriginWeightDecays (x : Site) : Prop :=
  Filter.Tendsto (fun n ↦ (freeOriginWeight x n).toReal)
    Filter.atTop (𝓝 0)

theorem freeOriginWeight_neighbor_le_four_succ
    (z : Site) (d : Direction) (n : ℕ) :
    (freeOriginWeight (z + directionStep d) n).toReal ≤
      4 * (freeOriginWeight z (n + 1)).toReal := by
  have hrec := freeOriginWeight_toReal_succ z n
  have hterm :
      (freeOriginWeight (z + directionStep d) n).toReal ≤
        ∑ e : Direction, (freeOriginWeight (z + directionStep e) n).toReal := by
    exact Finset.single_le_sum
      (f := fun e : Direction ↦
        (freeOriginWeight (z + directionStep e) n).toReal)
      (fun e he ↦ ENNReal.toReal_nonneg) (Finset.mem_univ d)
  unfold stepAverage at hrec
  nlinarith

theorem freeOriginWeight_decays_neighbor
    {z : Site} (hz : FreeOriginWeightDecays z) (d : Direction) :
    FreeOriginWeightDecays (z + directionStep d) := by
  have hshift : Filter.Tendsto
      (fun n ↦ (freeOriginWeight z (n + 1)).toReal)
      Filter.atTop (𝓝 0) := by
    apply hz.comp
    exact Filter.tendsto_add_atTop_nat 1
  have hupper : Filter.Tendsto
      (fun n ↦ 4 * (freeOriginWeight z (n + 1)).toReal)
      Filter.atTop (𝓝 0) := by
    simpa using hshift.const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0) from
      tendsto_const_nhds)
    hupper
  · exact Filter.Eventually.of_forall fun n ↦ ENNReal.toReal_nonneg
  · exact Filter.Eventually.of_forall fun n ↦
      freeOriginWeight_neighbor_le_four_succ z d n

theorem freeOriginWeight_zero_eq_return_real (n : ℕ) :
    (freeOriginWeight 0 n).toReal =
      incrementLaw.real {ω | simpleRandomWalk ω n = (0, 0)} := by
  have hevent : killedEndpointEvent (Set.univ : Set Site) 0 0 n =
      {ω | simpleRandomWalk ω n = (0, 0)} := by
    ext ω
    simp [killedEndpointEvent, walkFrom]
    rfl
  rw [freeOriginWeight, killedWeight, hevent]
  rfl

theorem freeOriginWeight_decays_zero : FreeOriginWeightDecays 0 := by
  have hbound (n : ℕ) :
      (freeOriginWeight 0 n).toReal ≤ 2 / (n + 1 : ℝ) := by
    rw [freeOriginWeight_zero_eq_return_real]
    exact Erdos1166.return_real_le_two_div_succ n
  have hden : Filter.Tendsto (fun n : ℕ ↦ (n + 1 : ℝ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop
  have hupper : Filter.Tendsto (fun n : ℕ ↦ 2 / (n + 1 : ℝ))
      Filter.atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun n ↦ ENNReal.toReal_nonneg
  · exact Filter.Eventually.of_forall hbound

theorem freeOriginWeight_decays_horizontal (a : ℤ) :
    FreeOriginWeightDecays (a, 0) := by
  induction a using Int.induction_on with
  | zero => exact freeOriginWeight_decays_zero
  | succ a ih =>
      have h := freeOriginWeight_decays_neighbor ih (0 : Direction)
      simpa [directionStep] using h
  | pred a ih =>
      have h := freeOriginWeight_decays_neighbor ih (1 : Direction)
      simpa [directionStep, sub_eq_add_neg] using h

theorem freeOriginWeight_decays (x : Site) : FreeOriginWeightDecays x := by
  rcases x with ⟨a, b⟩
  induction b using Int.induction_on with
  | zero => exact freeOriginWeight_decays_horizontal a
  | succ b ih =>
      have h := freeOriginWeight_decays_neighbor ih (2 : Direction)
      simpa [directionStep] using h
  | pred b ih =>
      have h := freeOriginWeight_decays_neighbor ih (3 : Direction)
      simpa [directionStep, sub_eq_add_neg] using h

/-- Consequently, pointwise convergence of the finite potential series is the
only hypothesis needed to obtain the exact potential-kernel equation. -/
theorem isPlanarPotentialKernel_of_finitePotentialKernel_tendsto
    {a : Site → ℝ}
    (ha : ∀ x, Filter.Tendsto (fun N ↦ finitePotentialKernel N x)
      Filter.atTop (𝓝 (a x))) :
    IsPlanarPotentialKernel a :=
  isPlanarPotentialKernel_of_finite_tendsto ha freeOriginWeight_decays

end Erdos1166.KilledGreen
