import ErdosProblems.Erdos1166.Erdos1166HLOZHarnack
import ErdosProblems.Erdos1166.Erdos1166HeatKernel

/-!
# A potential-kernel reduction for the HLOZ Poisson-kernel estimate

The sharp input in HLOZ Appendix A is an oscillation estimate for the exit
distribution from a large disk.  This file makes the exact algebraic content
of that estimate available for the finite square model already developed in
`Erdos1166HLOZHarnack`.

For a planar potential kernel `a`, the function

`x \mapsto G_D(x,z) + a(x-z)`

is harmonic in the starting point.  Consequently, the difference of two
Poisson-kernel values is bounded by a finite sum of two explicitly displayed
quantities: differences of `a` and differences of this harmonic remainder.
After a lower bound for the comparison Poisson kernel is supplied, the same
finite sum controls the relative error.  Thus the only remaining analytic
input is a numerical estimate for these two finite sums and a denominator
lower bound; no asymptotic or Harnack assertion is assumed here.
-/

namespace Erdos1166.KilledGreen

open scoped BigOperators ENNReal

/-- Translation commutes with nearest-neighbor averaging. -/
theorem stepAverage_sub_right (a : Site → ℝ) (x z : Site) :
    stepAverage (fun w ↦ a (w - z)) x = stepAverage a (x - z) := by
  unfold stepAverage
  apply congrArg (fun t : ℝ ↦ (1 / 4 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg a
  abel

/-- The harmonic remainder in the potential-kernel representation of a
killed Green column. -/
noncomputable def diskGreenPotentialRemainder
    (R : ℕ) (a : Site → ℝ) (x z : Site) : ℝ :=
  (diskGreen R x z).toReal + a (x - z)

/-- The translated version of the exact Green-plus-potential cancellation.
Unlike an asymptotic Harnack estimate, this is an identity. -/
theorem diskGreenPotentialRemainder_harmonic
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {x z : Site} (hx : x ∈ squareDisk R) :
    diskGreenPotentialRemainder R a x z =
      stepAverage (fun w ↦ diskGreenPotentialRemainder R a w z) x := by
  rw [show stepAverage (fun w ↦ diskGreenPotentialRemainder R a w z) x =
      stepAverage (fun w ↦ (diskGreen R w z).toReal) x +
        stepAverage (fun w ↦ a (w - z)) x by
      simpa only [diskGreenPotentialRemainder] using
        stepAverage_add (fun w ↦ (diskGreen R w z).toReal)
          (fun w ↦ a (w - z)) x]
  rw [stepAverage_sub_right]
  have hG := diskGreen_toReal_eq_indicator_add_step_average R x z hx
  change (diskGreen R x z).toReal =
    (if x = z then 1 else 0) +
      stepAverage (fun w ↦ (diskGreen R w z).toReal) x at hG
  have ha' := ha (x - z)
  have hsource : (if x - z = 0 then (1 : ℝ) else 0) =
      if x = z then 1 else 0 := by
    by_cases hxz : x = z <;> simp [hxz, sub_eq_zero]
  rw [hsource] at ha'
  unfold diskGreenPotentialRemainder
  linarith

/-- A completely finite substitute for the potential-kernel identity.  The
failure of harmonicity is exactly one unrestricted transition probability;
there is no convergence hypothesis. -/
theorem diskGreenFinitePotentialRemainder_eq_average_add_defect
    (N : ℕ) {R : ℕ} {x z : Site} (hx : x ∈ squareDisk R) :
    diskGreenPotentialRemainder R (finitePotentialKernel N) x z =
      stepAverage
        (fun w ↦ diskGreenPotentialRemainder R (finitePotentialKernel N) w z) x +
        (freeOriginWeight (x - z) N).toReal := by
  rw [show stepAverage
      (fun w ↦ diskGreenPotentialRemainder R (finitePotentialKernel N) w z) x =
      stepAverage (fun w ↦ (diskGreen R w z).toReal) x +
        stepAverage (fun w ↦ finitePotentialKernel N (w - z)) x by
      simpa only [diskGreenPotentialRemainder] using
        stepAverage_add (fun w ↦ (diskGreen R w z).toReal)
          (fun w ↦ finitePotentialKernel N (w - z)) x]
  rw [stepAverage_sub_right]
  have hG := diskGreen_toReal_eq_indicator_add_step_average R x z hx
  change (diskGreen R x z).toReal =
    (if x = z then 1 else 0) +
      stepAverage (fun w ↦ (diskGreen R w z).toReal) x at hG
  have hN := finitePotentialKernel_poisson_defect N (x - z)
  have hsource : (if x - z = 0 then (1 : ℝ) else 0) =
      if x = z then 1 else 0 := by
    by_cases hxz : x = z <;> simp [hxz, sub_eq_zero]
  rw [hsource] at hN
  unfold diskGreenPotentialRemainder
  linarith

/-- The exact finite-truncation defect is bounded by the explicit Gaussian
heat-kernel majorant already proved for the planar walk. -/
theorem diskGreenFinitePotentialRemainder_le_average_add_heatKernel
    (N : ℕ) {R : ℕ} {x z : Site} (hx : x ∈ squareDisk R) :
    diskGreenPotentialRemainder R (finitePotentialKernel N) x z ≤
      stepAverage
        (fun w ↦ diskGreenPotentialRemainder R (finitePotentialKernel N) w z) x +
        HeatKernel.heatKernelBound (HeatKernel.siteNormInf (x - z)) N := by
  rw [diskGreenFinitePotentialRemainder_eq_average_add_defect N hx]
  apply add_le_add (le_refl _)
  simpa [freeOriginWeight, HeatKernel.heatKernelBound] using
    HeatKernel.killedWeight_toReal_le_heatKernel
      (Set.univ : Set Site) (x - z) N

theorem stepAverage_neg (u : Site → ℝ) (x : Site) :
    stepAverage (fun w ↦ -u w) x = -stepAverage u x := by
  unfold stepAverage
  simp [Finset.sum_neg_distrib]

/-- An upper boundary estimate for the potential kernel bounds the harmonic
remainder throughout the killed square. -/
theorem diskGreenPotentialRemainder_le_boundary_upper
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {z : Site} {upper : ℝ}
    (hupper : ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
      a (w - z) ≤ upper)
    {x : Site} (hx : x ∈ squareDisk R) :
    diskGreenPotentialRemainder R a x z ≤ upper := by
  apply square_maximum_principle
      (u := fun w ↦ diskGreenPotentialRemainder R a w z)
      (B := upper) (R := R) (fun w hw ↦
        diskGreenPotentialRemainder_harmonic ha hw) ?_ x hx
  intro w hwR hw
  rw [diskGreenPotentialRemainder]
  rw [diskGreen_eq_zero_of_start_not_mem hw]
  simpa using hupper w hwR hw

/-- A lower boundary estimate for the potential kernel bounds the harmonic
remainder throughout the killed square. -/
theorem boundary_lower_le_diskGreenPotentialRemainder
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {z : Site} {lower : ℝ}
    (hlower : ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
      lower ≤ a (w - z))
    {x : Site} (hx : x ∈ squareDisk R) :
    lower ≤ diskGreenPotentialRemainder R a x z := by
  let u : Site → ℝ := fun w ↦ -diskGreenPotentialRemainder R a w z
  have hharm : ∀ w ∈ squareDisk R, u w = stepAverage u w := by
    intro w hw
    change -diskGreenPotentialRemainder R a w z =
      stepAverage (fun q ↦ -diskGreenPotentialRemainder R a q z) w
    rw [stepAverage_neg, diskGreenPotentialRemainder_harmonic ha hw]
  have hboundary : ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
      u w ≤ -lower := by
    intro w hwR hw
    change -diskGreenPotentialRemainder R a w z ≤ -lower
    rw [diskGreenPotentialRemainder,
      diskGreen_eq_zero_of_start_not_mem hw]
    simpa using neg_le_neg (hlower w hwR hw)
  have h := square_maximum_principle hharm hboundary x hx
  change -diskGreenPotentialRemainder R a x z ≤ -lower at h
  linarith

/-- The oscillation of the harmonic remainder is no larger than the range of
the translated potential kernel on the one-step outer boundary. -/
theorem diskGreenPotentialRemainder_sub_abs_le_boundary_range
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {z : Site} {lower upper : ℝ}
    (hlower : ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
      lower ≤ a (w - z))
    (hupper : ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
      a (w - z) ≤ upper)
    {x x' : Site} (hx : x ∈ squareDisk R) (hx' : x' ∈ squareDisk R) :
    |diskGreenPotentialRemainder R a x z -
        diskGreenPotentialRemainder R a x' z| ≤ upper - lower := by
  have hxl := boundary_lower_le_diskGreenPotentialRemainder ha hlower hx
  have hxu := diskGreenPotentialRemainder_le_boundary_upper ha hupper hx
  have hx'l := boundary_lower_le_diskGreenPotentialRemainder ha hlower hx'
  have hx'u := diskGreenPotentialRemainder_le_boundary_upper ha hupper hx'
  rw [abs_le]
  constructor <;> linarith

/-- Exact decomposition of a killed-Green difference into the harmonic
remainder difference and the potential-kernel difference. -/
theorem diskGreen_difference_eq_remainder_sub_potential
    (R : ℕ) (a : Site → ℝ) (x x' z : Site) :
    (diskGreen R x z).toReal - (diskGreen R x' z).toReal =
      (diskGreenPotentialRemainder R a x z -
        diskGreenPotentialRemainder R a x' z) -
      (a (x - z) - a (x' - z)) := by
  unfold diskGreenPotentialRemainder
  ring

/-- The contribution of potential-kernel increments to the exit-kernel
oscillation.  There are only four terms, one for each possible last step. -/
noncomputable def squareExitPotentialDifference
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      |a (x - (y - directionStep d)) -
        a (x' - (y - directionStep d))|
    else 0

/-- The contribution of the harmonic remainders to the exit-kernel
oscillation. -/
noncomputable def squareExitRemainderDifference
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      |diskGreenPotentialRemainder R a x (y - directionStep d) -
        diskGreenPotentialRemainder R a x' (y - directionStep d)|
    else 0

/-- A finite outer-boundary range for each possible last-step predecessor. -/
noncomputable def squareExitBoundaryPotentialRange
    (R : ℕ) (lower upper : Site → ℝ) (y : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      upper (y - directionStep d) - lower (y - directionStep d)
    else 0

theorem squareExitPotentialDifference_nonneg
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) :
    0 ≤ squareExitPotentialDifference R a x x' y := by
  unfold squareExitPotentialDifference
  positivity

theorem squareExitRemainderDifference_nonneg
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) :
    0 ≤ squareExitRemainderDifference R a x x' y := by
  unfold squareExitRemainderDifference
  positivity

/-- Boundary potential-kernel ranges bound the explicit remainder term. -/
theorem squareExitRemainderDifference_le_boundaryPotentialRange
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {x x' y : Site} (hx : x ∈ squareDisk R) (hx' : x' ∈ squareDisk R)
    (lower upper : Site → ℝ)
    (hboundary : ∀ d : Direction,
      y - directionStep d ∈ squareDisk R →
      ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
        lower (y - directionStep d) ≤ a (w - (y - directionStep d)) ∧
        a (w - (y - directionStep d)) ≤ upper (y - directionStep d)) :
    squareExitRemainderDifference R a x x' y ≤
      squareExitBoundaryPotentialRange R lower upper y := by
  unfold squareExitRemainderDifference squareExitBoundaryPotentialRange
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro d hd
  by_cases hpred : y - directionStep d ∈ squareDisk R
  · simp only [if_pos hpred]
    apply diskGreenPotentialRemainder_sub_abs_le_boundary_range ha
        (x := x) (x' := x') (z := y - directionStep d)
        (lower := lower (y - directionStep d))
        (upper := upper (y - directionStep d)) ?_ ?_ hx hx'
    · intro w hwR hw
      exact (hboundary d hpred w hwR hw).1
    · intro w hwR hw
      exact (hboundary d hpred w hwR hw).2
  · simp [hpred]

/-- Exact finite reduction of Poisson-kernel oscillation to potential-kernel
and harmonic-remainder oscillation. -/
theorem squareGreenExitKernel_sub_abs_le_potential_add_remainder
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) :
    |squareGreenExitKernel R x y - squareGreenExitKernel R x' y| ≤
      squareExitPotentialDifference R a x x' y +
        squareExitRemainderDifference R a x x' y := by
  let p : Direction → ℝ := fun d ↦
    if y - directionStep d ∈ squareDisk R then
      |a (x - (y - directionStep d)) -
        a (x' - (y - directionStep d))|
    else 0
  let h : Direction → ℝ := fun d ↦
    if y - directionStep d ∈ squareDisk R then
      |diskGreenPotentialRemainder R a x (y - directionStep d) -
        diskGreenPotentialRemainder R a x' (y - directionStep d)|
    else 0
  let g : Site → Direction → ℝ := fun w d ↦
    if y - directionStep d ∈ squareDisk R then
      (diskGreen R w (y - directionStep d)).toReal
    else 0
  have hterm (d : Direction) : |g x d - g x' d| ≤ p d + h d := by
    by_cases hd : y - directionStep d ∈ squareDisk R
    · simp only [g, p, h, if_pos hd]
      rw [diskGreen_difference_eq_remainder_sub_potential]
      exact (abs_sub _ _).trans_eq (add_comm _ _)
    · simp [g, p, h, hd]
  have hsum : |∑ d : Direction, g x d - ∑ d : Direction, g x' d| ≤
      ∑ d : Direction, (p d + h d) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun d hd ↦ hterm d)
  change |(1 / 4 : ℝ) * ∑ d : Direction, g x d -
      (1 / 4 : ℝ) * ∑ d : Direction, g x' d| ≤
    (1 / 4 : ℝ) * ∑ d : Direction, p d +
      (1 / 4 : ℝ) * ∑ d : Direction, h d
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  calc
    (1 / 4 : ℝ) * |∑ d : Direction, g x d - ∑ d : Direction, g x' d| ≤
        (1 / 4 : ℝ) * ∑ d : Direction, (p d + h d) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 4 : ℝ) * ∑ d : Direction, p d +
        (1 / 4 : ℝ) * ∑ d : Direction, h d := by
      rw [Finset.sum_add_distrib]
      ring

/-- Elementary denominator lemma used to turn an additive estimate into a
relative error. -/
theorem ratio_sub_one_abs_le_of_abs_sub_le
    {p q delta lower : ℝ} (hlower : 0 < lower) (hden : lower ≤ q)
    (hdiff : |p - q| ≤ delta) :
    |p / q - 1| ≤ delta / lower := by
  have hq : 0 < q := hlower.trans_le hden
  have hdelta : 0 ≤ delta := (abs_nonneg (p - q)).trans hdiff
  have hid : p / q - 1 = (p - q) / q := by
    field_simp
  rw [hid, abs_div, abs_of_pos hq]
  exact (div_le_div_of_nonneg_right hdiff hq.le).trans
    (div_le_div_of_nonneg_left hdelta hlower hden)

/-- Relative-error form of the finite potential-kernel reduction.  The two
explicit four-term quantities in the numerator, together with `hden`, are
precisely the remaining numerical estimates needed for the sharp source
Poisson-kernel comparison. -/
theorem squareGreenExitKernel_ratio_sub_one_abs_le
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) {lower : ℝ}
    (hlower : 0 < lower)
    (hden : lower ≤ squareGreenExitKernel R x' y) :
    |squareGreenExitKernel R x y / squareGreenExitKernel R x' y - 1| ≤
      (squareExitPotentialDifference R a x x' y +
        squareExitRemainderDifference R a x x' y) / lower := by
  apply ratio_sub_one_abs_le_of_abs_sub_le hlower hden
  exact squareGreenExitKernel_sub_abs_le_potential_add_remainder R a x x' y

/-- The same comparison stated for the event-level first-exit weights. -/
theorem firstExitAtWeight_square_ratio_sub_one_abs_le
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) {lower : ℝ}
    (hy : y ∉ squareDisk R) (hlower : 0 < lower)
    (hden : lower ≤ squareGreenExitKernel R x' y) :
    |(firstExitAtWeight (squareDisk R : Set Site) x y).toReal /
        (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal - 1| ≤
      (squareExitPotentialDifference R a x x' y +
        squareExitRemainderDifference R a x x' y) / lower := by
  rw [firstExitAtWeight_square_eq_kernel R x y hy,
    firstExitAtWeight_square_eq_kernel R x' y hy,
    squareGreenExitKernelENNReal_toReal,
    squareGreenExitKernelENNReal_toReal]
  exact squareGreenExitKernel_ratio_sub_one_abs_le R a x x' y hlower hden

/-- A source-shaped corollary: explicit bounds `potentialBound` and
`remainderBound` imply the corresponding relative Poisson-kernel error. -/
theorem firstExitAtWeight_square_ratio_sub_one_abs_le_of_bounds
    (R : ℕ) (a : Site → ℝ) (x x' y : Site)
    {lower potentialBound remainderBound : ℝ}
    (hy : y ∉ squareDisk R) (hlower : 0 < lower)
    (hden : lower ≤ squareGreenExitKernel R x' y)
    (hpotential : squareExitPotentialDifference R a x x' y ≤ potentialBound)
    (hremainder : squareExitRemainderDifference R a x x' y ≤ remainderBound) :
    |(firstExitAtWeight (squareDisk R : Set Site) x y).toReal /
        (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal - 1| ≤
      (potentialBound + remainderBound) / lower := by
  calc
    |(firstExitAtWeight (squareDisk R : Set Site) x y).toReal /
          (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal - 1| ≤
        (squareExitPotentialDifference R a x x' y +
          squareExitRemainderDifference R a x x' y) / lower :=
      firstExitAtWeight_square_ratio_sub_one_abs_le R a x x' y
        hy hlower hden
    _ ≤ (potentialBound + remainderBound) / lower := by
      exact div_le_div_of_nonneg_right (add_le_add hpotential hremainder)
        hlower.le

/-- Fully potential-kernel form of the reduction.  Apart from the positive
denominator lower bound, every quantity on the right is a finite difference
or boundary range of `a`.  Quantitative planar potential-kernel estimates can
therefore be plugged into this theorem without any further probabilistic or
measure-theoretic argument. -/
theorem firstExitAtWeight_square_ratio_sub_one_abs_le_potential_boundary
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {x x' y : Site} (hx : x ∈ squareDisk R) (hx' : x' ∈ squareDisk R)
    (lowerBoundary upperBoundary : Site → ℝ) {denominatorLower : ℝ}
    (hy : y ∉ squareDisk R) (hdenominatorLower : 0 < denominatorLower)
    (hden : denominatorLower ≤ squareGreenExitKernel R x' y)
    (hboundary : ∀ d : Direction,
      y - directionStep d ∈ squareDisk R →
      ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
        lowerBoundary (y - directionStep d) ≤
            a (w - (y - directionStep d)) ∧
          a (w - (y - directionStep d)) ≤
            upperBoundary (y - directionStep d)) :
    |(firstExitAtWeight (squareDisk R : Set Site) x y).toReal /
        (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal - 1| ≤
      (squareExitPotentialDifference R a x x' y +
        squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y) /
          denominatorLower := by
  calc
    |(firstExitAtWeight (squareDisk R : Set Site) x y).toReal /
          (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal - 1| ≤
        (squareExitPotentialDifference R a x x' y +
          squareExitRemainderDifference R a x x' y) / denominatorLower :=
      firstExitAtWeight_square_ratio_sub_one_abs_le R a x x' y hy
        hdenominatorLower hden
    _ ≤ (squareExitPotentialDifference R a x x' y +
          squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y) /
          denominatorLower := by
      have hrem : squareExitRemainderDifference R a x x' y ≤
          squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y :=
        squareExitRemainderDifference_le_boundaryPotentialRange
          (R := R) (a := a) (x := x) (x' := x') (y := y)
          ha hx hx' lowerBoundary upperBoundary hboundary
      have hadd : squareExitPotentialDifference R a x x' y +
          squareExitRemainderDifference R a x x' y ≤
          squareExitPotentialDifference R a x x' y +
            squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y :=
        add_le_add (le_refl _) hrem
      exact div_le_div_of_nonneg_right hadd hdenominatorLower.le

end Erdos1166.KilledGreen
