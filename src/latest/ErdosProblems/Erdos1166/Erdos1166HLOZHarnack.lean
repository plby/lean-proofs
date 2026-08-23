import ErdosProblems.Erdos1166.Erdos1166PotentialKernel
import ErdosProblems.Erdos1166.Erdos1166KilledGreenMarkov

/-!
# The exact exit kernel and the elementary Harnack chain

This file supplies the event-level last-step Green representation for the
first-exit distribution from a finite square.  It then derives, from the
killed-Green recursion, the elementary factor-four comparison across one
nearest-neighbor edge and the resulting `4 ^ n` comparison along an interior
chain.

The chain estimate is deliberately not advertised as Rosen's quantitative
Poisson-kernel Harnack estimate: the latter has relative error `O(r / R)`,
whereas the elementary argument below loses a factor four per edge.  The
remaining analytic input is therefore a sharp spatial oscillation estimate
for this exact kernel.
-/

namespace Erdos1166.KilledGreen

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- First exit from `D` occurs at time `n + 1`, at the site `y`. -/
def firstExitAtSuccEvent (D : Set Site) (x y : Site) (n : ℕ) :
    Set (ℕ → Direction) :=
  {ω | (∀ r, r ≤ n → walkFrom x ω r ∈ D) ∧
    walkFrom x ω (n + 1) = y ∧ y ∉ D}

def oneDirectionBlock (d : Direction) : Set (Fin 1 → Direction) :=
  {η | η 0 = d}

def killedThenExitDirectionEvent (D : Set Site) (x y : Site)
    (n : ℕ) (d : Direction) : Set (ℕ → Direction) :=
  killedEndpointEvent D x (y - directionStep d) n ∩
    iidBlock (X := Direction) n 1 ⁻¹' oneDirectionBlock d

theorem measurableSet_killedEndpointEvent_iidHistory
    (D : Set Site) (x y : Site) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (killedEndpointEvent D x y n) := by
  have heq : killedEndpointEvent D x y n =
      survivalEvent D x n ∩ {ω | walkFrom x ω n = y} := by
    ext ω
    simp [killedEndpointEvent, survivalEvent]
  rw [heq]
  exact (measurableSet_survivalEvent_iidHistory D x n).inter
    (measurableSet_eq_fun (measurable_walkFrom_iidHistory x le_rfl)
      measurable_const)

theorem measurableSet_oneDirectionBlock (d : Direction) :
    MeasurableSet (oneDirectionBlock d) :=
  MeasurableSet.of_discrete

theorem oneDirectionBlock_eq_singleton (d : Direction) :
    oneDirectionBlock d = {(fun _ : Fin 1 ↦ d)} := by
  ext η
  simp [oneDirectionBlock, funext_iff]

theorem finitePi_oneDirectionBlock (d : Direction) :
    (Measure.infinitePi fun _ : Fin 1 ↦ directionLaw)
        (oneDirectionBlock d) = (4 : ℝ≥0∞)⁻¹ := by
  rw [oneDirectionBlock_eq_singleton,
    Measure.infinitePi_singleton_of_fintype]
  simp [directionLaw]

theorem measure_killedThenExitDirectionEvent
    (D : Set Site) (x y : Site) (n : ℕ) (d : Direction) :
    incrementLaw (killedThenExitDirectionEvent D x y n d) =
      killedWeight D x (y - directionStep d) n * (4 : ℝ≥0∞)⁻¹ := by
  have h := measure_inter_iidBlock_eq_mul directionLaw n 1
    (measurableSet_killedEndpointEvent_iidHistory D x
      (y - directionStep d) n)
    (measurableSet_oneDirectionBlock d)
  rw [finitePi_oneDirectionBlock] at h
  simpa [incrementLaw, killedThenExitDirectionEvent, killedWeight] using h

theorem iUnion_killedThenExitDirectionEvent
    (D : Set Site) (x y : Site) (n : ℕ) (hy : y ∉ D) :
    (⋃ d : Direction, killedThenExitDirectionEvent D x y n d) =
      firstExitAtSuccEvent D x y n := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨d, hd⟩
    rcases hd with ⟨hkilled, hdir⟩
    refine ⟨hkilled.1, ?_, ?_⟩
    · rw [walkFrom_succ, hkilled.2]
      have hd' : ω n = d := by simpa [iidBlock, oneDirectionBlock] using hdir
      rw [hd']
      abel
    · exact hy
  · rintro ⟨hstay, hend, hy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨ω n, ?_⟩
    constructor
    · refine ⟨hstay, ?_⟩
      rw [walkFrom_succ] at hend
      rw [← hend]
      abel
    · simp [iidBlock, oneDirectionBlock]

theorem pairwiseDisjoint_killedThenExitDirectionEvent
    (D : Set Site) (x y : Site) (n : ℕ) :
    Pairwise fun d e ↦ Disjoint
      (killedThenExitDirectionEvent D x y n d)
      (killedThenExitDirectionEvent D x y n e) := by
  intro d e hde
  rw [Set.disjoint_left]
  intro ω hd he
  apply hde
  have hdd : ω n = d := by
    simpa [iidBlock, oneDirectionBlock] using hd.2
  have hee : ω n = e := by
    simpa [iidBlock, oneDirectionBlock] using he.2
  exact hdd.symm.trans hee

theorem measure_firstExitAtSuccEvent
    (D : Set Site) (x y : Site) (n : ℕ) (hy : y ∉ D) :
    incrementLaw (firstExitAtSuccEvent D x y n) =
      ∑ d : Direction,
        killedWeight D x (y - directionStep d) n * (4 : ℝ≥0∞)⁻¹ := by
  rw [← iUnion_killedThenExitDirectionEvent D x y n hy]
  rw [measure_iUnion (pairwiseDisjoint_killedThenExitDirectionEvent D x y n)]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    exact measure_killedThenExitDirectionEvent D x y n d
  · intro d
    exact (iidHistory_le n _ (measurableSet_killedEndpointEvent_iidHistory D x
      (y - directionStep d) n)).inter
      ((measurable_iidBlock n 1) (measurableSet_oneDirectionBlock d))

/-- The walk first leaves `D` at the site `y` (at some positive time). -/
def firstExitAtEvent (D : Set Site) (x y : Site) : Set (ℕ → Direction) :=
  ⋃ n : ℕ, firstExitAtSuccEvent D x y n

theorem pairwiseDisjoint_firstExitAtSuccEvent
    (D : Set Site) (x y : Site) :
    Pairwise fun n m ↦ Disjoint
      (firstExitAtSuccEvent D x y n) (firstExitAtSuccEvent D x y m) := by
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · rw [Set.disjoint_left]
    intro ω hn hm
    have hmem : walkFrom x ω (n + 1) ∈ D := hm.1 (n + 1) (by omega)
    exact hn.2.2 (hn.2.1 ▸ hmem)
  · exact (by
      rw [Set.disjoint_left]
      intro ω hn hm
      have hmem : walkFrom x ω (m + 1) ∈ D := hn.1 (m + 1) (by omega)
      exact hm.2.2 (hm.2.1 ▸ hmem))

theorem measurableSet_firstExitAtSuccEvent
    (D : Set Site) (x y : Site) (n : ℕ) (hy : y ∉ D) :
    MeasurableSet (firstExitAtSuccEvent D x y n) := by
  rw [← iUnion_killedThenExitDirectionEvent D x y n hy]
  exact MeasurableSet.iUnion fun d ↦
    (iidHistory_le n _ (measurableSet_killedEndpointEvent_iidHistory D x
      (y - directionStep d) n)).inter
      ((measurable_iidBlock n 1) (measurableSet_oneDirectionBlock d))

/-- Total mass of paths, started at `x`, whose first exit from `D` is at
`y`.  The time index records the last in-domain time. -/
noncomputable def firstExitAtWeight (D : Set Site) (x y : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, incrementLaw (firstExitAtSuccEvent D x y n)

theorem firstExitAtWeight_eq_measure (D : Set Site) (x y : Site)
    (hy : y ∉ D) :
    firstExitAtWeight D x y = incrementLaw (firstExitAtEvent D x y) := by
  unfold firstExitAtWeight firstExitAtEvent
  rw [measure_iUnion (pairwiseDisjoint_firstExitAtSuccEvent D x y)
    (fun n ↦ measurableSet_firstExitAtSuccEvent D x y n hy)]

theorem firstExitAtWeight_eq_green_lastStep (D : Set Site) (x y : Site)
    (hy : y ∉ D) :
    firstExitAtWeight D x y =
      ∑ d : Direction, killedGreen D x (y - directionStep d) *
        (4 : ℝ≥0∞)⁻¹ := by
  unfold firstExitAtWeight
  simp_rw [measure_firstExitAtSuccEvent D x y _ hy]
  calc
    (∑' n : ℕ, ∑ d : Direction,
        killedWeight D x (y - directionStep d) n * (4 : ℝ≥0∞)⁻¹) =
      ∑' d : Direction, ∑' n : ℕ,
        killedWeight D x (y - directionStep d) n * (4 : ℝ≥0∞)⁻¹ := by
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comm :
            (∑' n : ℕ, ∑' d : Direction,
              killedWeight D x (y - directionStep d) n * (4 : ℝ≥0∞)⁻¹) = _)
    _ = ∑ d : Direction, killedGreen D x (y - directionStep d) *
          (4 : ℝ≥0∞)⁻¹ := by
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro d hd
        rw [ENNReal.tsum_mul_right]
        rfl

theorem killedGreen_eq_zero_of_target_not_mem
    {D : Set Site} {x y : Site} (hy : y ∉ D) :
    killedGreen D x y = 0 := by
  unfold killedGreen
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  rw [killedWeight]
  have heq : killedEndpointEvent D x y n = ∅ := by
    ext ω
    simp only [killedEndpointEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    intro hω
    exact hy (hω.2 ▸ hω.1 n le_rfl)
  rw [heq, measure_empty]

/-- ENNReal-valued last-step Green kernel. -/
noncomputable def squareGreenExitKernelENNReal
    (R : ℕ) (x y : Site) : ℝ≥0∞ :=
  (4 : ℝ≥0∞)⁻¹ * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      diskGreen R x (y - directionStep d)
    else 0

theorem firstExitAtWeight_square_eq_kernel (R : ℕ) (x y : Site)
    (hy : y ∉ squareDisk R) :
    firstExitAtWeight (squareDisk R : Set Site) x y =
      squareGreenExitKernelENNReal R x y := by
  rw [firstExitAtWeight_eq_green_lastStep _ _ _ hy]
  unfold squareGreenExitKernelENNReal diskGreen
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hpred : y - directionStep d ∈ squareDisk R
  · simp only [if_pos hpred]
    ac_rfl
  · simp only [if_neg hpred]
    rw [killedGreen_eq_zero_of_target_not_mem hpred]
    simp

/-- The last-step Green representation of the mass of exiting the square at
`y`.  Only predecessors lying in the square contribute. -/
noncomputable def squareGreenExitKernel (R : ℕ) (x y : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      (diskGreen R x (y - directionStep d)).toReal
    else 0

theorem squareGreenExitKernelENNReal_toReal (R : ℕ) (x y : Site) :
    (squareGreenExitKernelENNReal R x y).toReal =
      squareGreenExitKernel R x y := by
  unfold squareGreenExitKernelENNReal squareGreenExitKernel
  rw [ENNReal.toReal_mul]
  norm_num
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro d hd
    by_cases hpred : y - directionStep d ∈ squareDisk R
    · simp [hpred]
    · simp [hpred]
  · intro d hd
    by_cases hpred : y - directionStep d ∈ squareDisk R
    · simp only [if_pos hpred]
      exact diskGreen_ne_top R x _
    · simp [hpred]

theorem squareGreenExitKernel_nonneg (R : ℕ) (x y : Site) :
    0 ≤ squareGreenExitKernel R x y := by
  unfold squareGreenExitKernel
  positivity

theorem squareGreenExitKernel_harmonic
    {R : ℕ} {x y : Site} (hx : x ∈ squareDisk R)
    (hfar : ∀ d : Direction, x ≠ y - directionStep d) :
    squareGreenExitKernel R x y =
      stepAverage (fun z ↦ squareGreenExitKernel R z y) x := by
  unfold squareGreenExitKernel
  unfold stepAverage
  have hterm (d : Direction) (hd : y - directionStep d ∈ squareDisk R) :
      (diskGreen R x (y - directionStep d)).toReal =
        (1 / 4 : ℝ) * ∑ e : Direction,
          (diskGreen R (x + directionStep e)
            (y - directionStep d)).toReal := by
    have h := diskGreen_toReal_eq_indicator_add_step_average
      R x (y - directionStep d) hx
    rw [if_neg (hfar d)] at h
    simpa using h
  calc
    (1 / 4 : ℝ) * (∑ d : Direction,
        (if y - directionStep d ∈ squareDisk R then
          (diskGreen R x (y - directionStep d)).toReal else 0)) =
      (1 / 4 : ℝ) * (∑ d : Direction,
        (if y - directionStep d ∈ squareDisk R then
          (1 / 4 : ℝ) * ∑ e : Direction,
            (diskGreen R (x + directionStep e)
              (y - directionStep d)).toReal else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hpred : y - directionStep d ∈ squareDisk R
        · simp only [if_pos hpred]
          exact hterm d hpred
        · simp [hpred]
    _ = (1 / 4 : ℝ) * (∑ e : Direction,
        ((1 / 4 : ℝ) * ∑ d : Direction,
          (if y - directionStep d ∈ squareDisk R then
            (diskGreen R (x + directionStep e)
              (y - directionStep d)).toReal else 0))) := by
        congr 1
        calc
          (∑ d : Direction,
              (if y - directionStep d ∈ squareDisk R then
                (1 / 4 : ℝ) * ∑ e : Direction,
                  (diskGreen R (x + directionStep e)
                    (y - directionStep d)).toReal else 0)) =
            ∑ d : Direction, ∑ e : Direction,
              (1 / 4 : ℝ) *
                (if y - directionStep d ∈ squareDisk R then
                  (diskGreen R (x + directionStep e)
                    (y - directionStep d)).toReal else 0) := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hpred : y - directionStep d ∈ squareDisk R
              · simp [hpred, Finset.mul_sum]
              · simp [hpred]
          _ = ∑ e : Direction, ∑ d : Direction,
              (1 / 4 : ℝ) *
                (if y - directionStep d ∈ squareDisk R then
                  (diskGreen R (x + directionStep e)
                    (y - directionStep d)).toReal else 0) :=
              Finset.sum_comm
          _ = ∑ e : Direction,
              ((1 / 4 : ℝ) * ∑ d : Direction,
                (if y - directionStep d ∈ squareDisk R then
                  (diskGreen R (x + directionStep e)
                    (y - directionStep d)).toReal else 0)) := by
              apply Finset.sum_congr rfl
              intro e he
              rw [Finset.mul_sum]

theorem squareGreenExitKernel_neighbor_le_four_mul
    {R : ℕ} {x y : Site} (hx : x ∈ squareDisk R)
    (hfar : ∀ d : Direction, x ≠ y - directionStep d)
    (e : Direction) :
    squareGreenExitKernel R (x + directionStep e) y ≤
      4 * squareGreenExitKernel R x y := by
  have hharm := squareGreenExitKernel_harmonic hx hfar
  rw [stepAverage] at hharm
  have hnonneg : ∀ d ∈ (Finset.univ : Finset Direction),
      0 ≤ squareGreenExitKernel R (x + directionStep d) y := by
    intro d hd
    exact squareGreenExitKernel_nonneg _ _ _
  have hle : squareGreenExitKernel R (x + directionStep e) y ≤
      ∑ d : Direction, squareGreenExitKernel R (x + directionStep d) y := by
    exact Finset.single_le_sum (fun d hd ↦ hnonneg d hd) (Finset.mem_univ e)
  nlinarith

theorem inner_point_not_exit_predecessor
    {r R : ℕ} {x y : Site} (hx : x ∈ squareDisk r)
    (hrR : r + 1 ≤ R) (hy : y ∉ squareDisk R) :
    ∀ d : Direction, x ≠ y - directionStep d := by
  intro d hxd
  apply hy
  have hstep : x + directionStep d ∈ squareDisk (r + 1) :=
    add_directionStep_mem_squareDisk_succ hx d
  have heq : y = x + directionStep d := by
    rw [hxd]
    abel
  rw [heq]
  exact squareDisk_mono hrR hstep

/-- A completely internal finite-square Harnack chain.  It is obtained from
the exact killed-Green last-step kernel and the one-step harmonic equation;
no analytic Harnack inequality is assumed.  Its factor `4^n` is intentionally
recorded explicitly. -/
theorem squareGreenExitKernel_chain_le
    {r R n : ℕ} {p : ℕ → Site} {η : ℕ → Direction} {y : Site}
    (hstep : ∀ k, k < n → p (k + 1) = p k + directionStep (η k))
    (hinner : ∀ k, k ≤ n → p k ∈ squareDisk r)
    (hrR : r + 1 ≤ R) (hy : y ∉ squareDisk R) :
    squareGreenExitKernel R (p n) y ≤
      (4 : ℝ) ^ n * squareGreenExitKernel R (p 0) y := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep' : ∀ k, k < n → p (k + 1) = p k + directionStep (η k) := by
        intro k hk
        exact hstep k (by omega)
      have hinner' : ∀ k, k ≤ n → p k ∈ squareDisk r := by
        intro k hk
        exact hinner k (by omega)
      have hih := ih hstep' hinner'
      have hpn : p n ∈ squareDisk r := hinner n (by omega)
      have hlocal := squareGreenExitKernel_neighbor_le_four_mul
        (R := R) (y := y) (squareDisk_mono (by omega : r ≤ R) hpn)
        (inner_point_not_exit_predecessor hpn hrR hy) (η n)
      rw [← hstep n (by omega)] at hlocal
      calc
        squareGreenExitKernel R (p (n + 1)) y ≤
            4 * squareGreenExitKernel R (p n) y := hlocal
        _ ≤ 4 * ((4 : ℝ) ^ n * squareGreenExitKernel R (p 0) y) := by
          exact mul_le_mul_of_nonneg_left hih (by norm_num)
        _ = (4 : ℝ) ^ (n + 1) * squareGreenExitKernel R (p 0) y := by
          rw [pow_succ]
          ring

end Erdos1166.KilledGreen
