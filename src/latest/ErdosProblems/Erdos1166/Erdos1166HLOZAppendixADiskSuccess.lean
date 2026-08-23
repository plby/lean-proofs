/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAShapeBridge
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAQuantitative
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixATwoPointSource
import ErdosProblems.Erdos1166.Erdos1166HLOZPoissonGradient

/-!
# The literal Euclidean-disk success estimate in HLOZ Appendix A

This file joins the finite profile first moment, the source separation-shell
geometry, and the checked second-moment/Paley--Zygmund calculation.  A
successful site is the finite union over the canonical corridor family
`sourceProfiles`.  Its atoms are the actual annular random-walk atoms; the
local-time witness is therefore an explicit structural premise, rather than
being inserted into the definition of success.

All finite-union, cardinality, separation-shell, close-pair, and
Paley--Zygmund bookkeeping is discharged below.  The remaining fields of
`EuclideanDiskSourceEstimates` are precisely the quantitative one-point
annular comparison, its matching upper bound, an exit-word two-point
certificate (either the legacy potential-boundary route or the
corner-normalized canonical-right column route), the large-count
absorption, and the final asymptotic budget.
-/

namespace Erdos1166.HLOZAppendixADiskSuccess

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open HLOZAppendixA
open HLOZAppendixAShapeBridge
open HLOZProp13FromAppendix
open HLOZAppendixAFirstMoment
open HLOZAppendixASecondMoment
open HLOZAppendixAExactExit
open HLOZAppendixATwoPoint
open HLOZAppendixATwoPointSource
open HLOZPropositionA7
open KilledGreen

/-- Integer rounding of the source radius `r_{n,0}=e^n n^9`. -/
noncomputable def sourceBoxRadius (n : ℕ) : ℕ :=
  ⌈appendixDiskScale n 0⌉₊

/-- The literal finite source box `U_n=[2r_{n,0},3r_{n,0}]²`, with the
radius rounded upward once. -/
noncomputable def sourceSiteBox (n : ℕ) : Finset Site :=
  appendixSiteBox (sourceBoxRadius n)

/-- Exact real cardinality scale of `sourceSiteBox`. -/
noncomputable def sourceBoxKsq (n : ℕ) : ℝ :=
  (((sourceBoxRadius n + 1) ^ 2 : ℕ) : ℝ)

/-- Universal shell constant after comparing `K_n=16r_{n,0}` with the
actual cardinality scale of the source box. -/
noncomputable def sourceShellConstant : ℝ :=
  49 * Real.exp 2 * 256

/-- Integer radius containing every close neighbor for which the disks are
still not separated at scale `n+1`. -/
noncomputable def sourceCloseRadius (n : ℕ) : ℕ :=
  ⌈2 * appendixDiskScale n (n + 1)⌉₊

/-- Exact lattice-square bound for the number of close neighbors. -/
noncomputable def sourceCloseCount (n : ℕ) : ℝ :=
  (((2 * sourceCloseRadius n + 1) ^ 2 : ℕ) : ℝ)

/-- The coefficient produced by the checked second-moment calculation with
the canonical box, shell constant, and cutoff `L=n+1`. -/
noncomputable def sourcePaleyCoefficient (n : ℕ) (c E : ℝ) : ℝ :=
  ((((n + 1) + 1 : ℕ) : ℝ)) * sourceShellConstant *
    Real.exp E * c ^ 2 + Real.exp E

/-- The explicit Paley--Zygmund coefficient is strictly positive, without
any sign assumption on the one-point comparison constant. -/
theorem sourcePaleyCoefficient_pos (n : ℕ) (c E : ℝ) :
    0 < sourcePaleyCoefficient n c E := by
  unfold sourcePaleyCoefficient
  have hmain : 0 ≤ ((((n + 1) + 1 : ℕ) : ℝ)) *
      sourceShellConstant * Real.exp E * c ^ 2 := by
    unfold sourceShellConstant
    positivity
  linarith [Real.exp_pos E]

/-- A linear factor times the Appendix exponent tends to zero.  This is
the sole analytic fact needed to make the final Paley--Zygmund budget
automatic when its constants are uniform in the disk scale. -/
theorem tendsto_natCast_mul_exp_neg_rpow
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / a) 1
      (by norm_num)).comp hpow
  apply hdecay.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrpow : ((n : ℝ) ^ a) ^ a⁻¹ = (n : ℝ) := by
    rw [← Real.rpow_mul hn0]
    field_simp
    simp
  simp [Function.comp_apply, hrpow]

/-- For fixed comparison constants the final Appendix-A
Paley--Zygmund budget is eventually automatic.  In particular this
inequality is not an additional random-walk estimate. -/
theorem eventually_sourcePaley_budget (c E : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) ^
          (3 / 5 + appendixEpsilon / 3 : ℝ))) <
        1 / sourcePaleyCoefficient n c E := by
  let a : ℝ := 3 / 5 + appendixEpsilon / 3
  have ha : 0 < a := by
    norm_num [a, appendixEpsilon]
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ ↦
      Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  have hlinear := tendsto_natCast_mul_exp_neg_rpow ha
  have hscaled : Tendsto (fun n : ℕ ↦
      sourcePaleyCoefficient n c E *
        Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) := by
    let A : ℝ := sourceShellConstant * Real.exp E * c ^ 2
    let B : ℝ := 2 * A + Real.exp E
    have hfirst : Tendsto (fun n : ℕ ↦
        A * ((n : ℝ) * Real.exp (-((n : ℝ) ^ a)))) atTop (nhds 0) :=
      by simpa using hlinear.const_mul A
    have hsecond : Tendsto (fun n : ℕ ↦
        B * Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) :=
      by simpa using hexp.const_mul B
    convert hfirst.add hsecond using 1
    · funext n
      unfold sourcePaleyCoefficient A B
      push_cast
      ring
    · norm_num
  have hlt := hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt] with n hn
  apply (lt_div_iff₀ (sourcePaleyCoefficient_pos n c E)).2
  simpa [a, mul_comm] using hn

/-- The profile-union event that a fixed site is successful. -/
def euclideanSuccessfulSiteEvent (delta : ℝ) (n : ℕ)
    (atom : Site → NatPath (n - 2) → Set (ℕ → Direction))
    (x : Site) : Set (ℕ → Direction) :=
  successfulProfileEvent (sourceProfiles delta n) (atom x)

/-- At least one site in the canonical source box is successful. -/
def euclideanSomeSuccessful (delta : ℝ) (n : ℕ)
    (atom : Site → NatPath (n - 2) → Set (ℕ → Direction)) :
    Set (ℕ → Direction) :=
  someSuccessful (sourceSiteBox n)
    (euclideanSuccessfulSiteEvent delta n atom)

theorem measurableSet_euclideanSuccessfulSiteEvent
    {delta : ℝ} {n : ℕ}
    {atom : Site → NatPath (n - 2) → Set (ℕ → Direction)} {x : Site}
    (hatom : ∀ q ∈ sourceProfiles delta n, MeasurableSet (atom x q)) :
    MeasurableSet (euclideanSuccessfulSiteEvent delta n atom x) := by
  rw [euclideanSuccessfulSiteEvent, successfulProfileEvent]
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : q ∈ sourceProfiles delta n
  · simpa [hq] using hatom q hq
  · simp [hq]

/-- A profile atom which supplies the source local-time threshold forces the
corresponding maximal-local-time disk event. -/
theorem euclideanSuccessfulSiteEvent_subset_diskGood
    {epsilon delta : ℝ} {n : ℕ}
    {atom : Site → NatPath (n - 2) → Set (ℕ → Direction)} {x : Site}
    (hlocal : ∀ q ∈ sourceProfiles delta n,
      atom x q ⊆ {ω | diskThreshold epsilon n ≤
        (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}) :
    euclideanSuccessfulSiteEvent delta n atom x ⊆
      euclideanDiskGood epsilon n := by
  intro ω hω
  rw [euclideanSuccessfulSiteEvent, successfulProfileEvent] at hω
  obtain ⟨q, hω⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hq, hωq⟩ := Set.mem_iUnion.mp hω
  have hthreshold := hlocal q hq hωq
  change diskThreshold epsilon n ≤
    (maxLocalTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) : ℝ)
  have hmax := localTime_le_maxLocalTime_any (simpleRandomWalk ω)
    (euclideanExitTime (K n) ω) x
  exact hthreshold.trans (by exact_mod_cast hmax)

/-- The finite union over all source sites is still contained in the literal
Euclidean-disk event (A.1). -/
theorem euclideanSomeSuccessful_subset_diskGood
    {epsilon delta : ℝ} {n : ℕ}
    {atom : Site → NatPath (n - 2) → Set (ℕ → Direction)}
    (hlocal : ∀ x ∈ sourceSiteBox n, ∀ q ∈ sourceProfiles delta n,
      atom x q ⊆ {ω | diskThreshold epsilon n ≤
        (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}) :
    euclideanSomeSuccessful delta n atom ⊆ euclideanDiskGood epsilon n := by
  intro ω hω
  change ω ∈ someSuccessful (sourceSiteBox n)
    (euclideanSuccessfulSiteEvent delta n atom) at hω
  rw [someSuccessful] at hω
  obtain ⟨x, hω⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx, hωx⟩ := Set.mem_iUnion.mp hω
  exact euclideanSuccessfulSiteEvent_subset_diskGood
    (hlocal x hx) hωx

theorem appendixDiskScale_zero_eq_shell_one (n : ℕ) :
    appendixDiskScale n 0 = appendixShellScale n 1 := by
  rw [appendixDiskScale, appendixShellScale]
  norm_num

theorem sourceBoxRadius_le_two_shell_one {n : ℕ} (hn : 1 ≤ n) :
    (sourceBoxRadius n : ℝ) ≤ 2 * appendixShellScale n 1 := by
  have hr1 : 1 ≤ appendixShellScale n 1 :=
    one_le_appendixShellScale hn (by omega)
  have hr0 : 0 ≤ appendixDiskScale n 0 := by
    unfold appendixDiskScale
    positivity
  have hceil : (sourceBoxRadius n : ℝ) < appendixDiskScale n 0 + 1 := by
    simpa [sourceBoxRadius] using Nat.ceil_lt_add_one hr0
  rw [appendixDiskScale_zero_eq_shell_one] at hceil
  linarith

theorem card_sourceSiteBox (n : ℕ) :
    ((sourceSiteBox n).card : ℝ) = sourceBoxKsq n := by
  rw [sourceSiteBox, card_appendixSiteBox]
  rfl

theorem sourceBoxKsq_pos (n : ℕ) : 0 < sourceBoxKsq n := by
  unfold sourceBoxKsq
  positivity

theorem appendixKScale_sq_le_sourceBoxKsq (n : ℕ) :
    appendixKScale n ^ 2 ≤ 256 * sourceBoxKsq n := by
  let r := appendixDiskScale n 0
  have hr0 : 0 ≤ r := by
    dsimp [r, appendixDiskScale]
    positivity
  have hrR : r ≤ (sourceBoxRadius n : ℝ) := by
    simpa [sourceBoxRadius, r] using Nat.le_ceil r
  have hscale : appendixKScale n = 16 * r := by
    dsimp [appendixKScale, r, appendixDiskScale]
    norm_num
    ring
  have hRcast : ((sourceBoxRadius n : ℝ) + 1) ^ 2 = sourceBoxKsq n := by
    simp [sourceBoxKsq, Nat.cast_add, Nat.cast_pow]
  rw [hscale]
  rw [← hRcast]
  nlinarith [sq_nonneg (r - ((sourceBoxRadius n : ℝ) + 1))]

theorem source_separationShell_card_le_box
    {n l : ℕ} {x : Site} (hn : 1 ≤ n) (hx : x ∈ sourceSiteBox n)
    (hl : l ≤ n + 1) :
    ((separationShell (sourceSiteBox n)
      (appendixSeparationLevel n) x l).card : ℝ) ≤
      sourceShellConstant * sourceBoxKsq n *
        Real.exp (-2 * (l : ℝ)) := by
  rcases Nat.eq_zero_or_pos l with rfl | hlpos
  · have hempty : separationShell (sourceSiteBox n)
        (appendixSeparationLevel n) x 0 = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨y, hy⟩
      have hlevel : appendixSeparationLevel n x y = 0 :=
        (Finset.mem_filter.mp hy).2
      have hspec := appendixSeparationLevel_spec_of_le
        (n := n) (x := x) (y := y) (by omega)
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold sourceShellConstant sourceBoxKsq
    positivity
  · have hsource := source_separationShell_card_le hn
      (show x ∈ appendixSiteBox (sourceBoxRadius n) by simpa [sourceSiteBox] using hx)
      hlpos hl (sourceBoxRadius_le_two_shell_one hn)
    have hK := appendixKScale_sq_le_sourceBoxKsq n
    calc
      ((separationShell (sourceSiteBox n)
          (appendixSeparationLevel n) x l).card : ℝ) ≤
          (49 * Real.exp 2) * appendixKScale n ^ 2 *
            Real.exp (-2 * (l : ℝ)) := by
        simpa [sourceSiteBox] using hsource
      _ ≤ (49 * Real.exp 2) * (256 * sourceBoxKsq n) *
            Real.exp (-2 * (l : ℝ)) := by
        gcongr
      _ = sourceShellConstant * sourceBoxKsq n *
            Real.exp (-2 * (l : ℝ)) := by
        rw [sourceShellConstant]
        ring

theorem not_appendixDisksSeparated_last_of_close
    {n : ℕ} {x y : Site}
    (hclose : n + 1 < appendixSeparationLevel n x y) :
    ¬ appendixDisksSeparated n (n + 1) x y := by
  classical
  intro hsep
  have hex : ∃ m : ℕ, 1 ≤ m ∧ appendixDisksSeparated n m x y :=
    ⟨n + 1, by omega, hsep⟩
  unfold appendixSeparationLevel at hclose
  rw [dif_pos hex] at hclose
  have hfind : Nat.find hex ≤ n + 1 := Nat.find_min' hex ⟨by omega, hsep⟩
  omega

private theorem mem_latticeSupBall_of_distance_le
    {x y : Site} {r : ℝ} {R : ℕ} (hr : 0 ≤ r) (hrR : r ≤ (R : ℝ))
    (hdist : (siteSquaredDistance x y : ℝ) ≤ r ^ 2) :
    y ∈ latticeSupBall x R := by
  have coordinate_le (z : ℤ)
      (hz : z.natAbs ^ 2 ≤ siteSquaredDistance x y) : z.natAbs ≤ R := by
    have hzsq : ((z.natAbs ^ 2 : ℕ) : ℝ) ≤ r ^ 2 := by
      exact (by exact_mod_cast hz : ((z.natAbs ^ 2 : ℕ) : ℝ) ≤
        (siteSquaredDistance x y : ℝ)) |>.trans hdist
    by_contra h
    have hRzNat : R < z.natAbs := Nat.lt_of_not_ge h
    have hRz : (R : ℝ) < z.natAbs := by exact_mod_cast hRzNat
    have hrz : r < (z.natAbs : ℝ) := hrR.trans_lt hRz
    have hz0 : 0 ≤ (z.natAbs : ℝ) := by positivity
    have hsquare : r ^ 2 < (z.natAbs : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (r + (z.natAbs : ℝ))]
    rw [Nat.cast_pow] at hzsq
    exact (not_lt_of_ge hzsq) hsquare
  have hxcoord : (x.1 - y.1).natAbs ≤ R := by
    apply coordinate_le
    rw [siteSquaredDistance]
    omega
  have hycoord : (x.2 - y.2).natAbs ≤ R := by
    apply coordinate_le
    rw [siteSquaredDistance]
    omega
  have hxabs : |x.1 - y.1| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hxcoord
  have hyabs : |x.2 - y.2| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hycoord
  rw [latticeSupBall]
  apply Finset.mem_product.mpr
  rcases abs_le.mp hxabs with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hyabs with ⟨hylo, hyhi⟩
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    constructor <;> omega

theorem close_neighbor_mem_sourceCloseRadius
    {n : ℕ} {x y : Site}
    (hclose : n + 1 < appendixSeparationLevel n x y) :
    y ∈ latticeSupBall x (sourceCloseRadius n) := by
  have hnot := not_appendixDisksSeparated_last_of_close hclose
  have hdist : (siteSquaredDistance x y : ℝ) ≤
      (2 * appendixDiskScale n (n + 1)) ^ 2 := by
    exact le_of_not_gt hnot
  apply mem_latticeSupBall_of_distance_le
    (r := 2 * appendixDiskScale n (n + 1))
    (R := sourceCloseRadius n)
  · unfold appendixDiskScale
    positivity
  · exact Nat.le_ceil _
  · exact hdist

theorem close_neighbor_card_le
    (n : ℕ) (x : Site) :
    (((sourceSiteBox n).filter
      (fun y ↦ n + 1 < appendixSeparationLevel n x y)).card : ℝ) ≤
      sourceCloseCount n := by
  have hsub : (sourceSiteBox n).filter
      (fun y ↦ n + 1 < appendixSeparationLevel n x y) ⊆
      latticeSupBall x (sourceCloseRadius n) := by
    intro y hy
    exact close_neighbor_mem_sourceCloseRadius (Finset.mem_filter.mp hy).2
  have hcard := Finset.card_le_card hsub
  rw [card_latticeSupBall] at hcard
  have hreal :
      (((sourceSiteBox n).filter
        (fun y ↦ n + 1 < appendixSeparationLevel n x y)).card : ℝ) ≤
        (((2 * sourceCloseRadius n + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  simpa [sourceCloseCount] using hreal

/-- The number of sites in the unresolved final separation shell is only
polynomial in the disk index. -/
theorem sourceCloseCount_le_polynomial {n : ℕ} (hn : 1 ≤ n) :
    sourceCloseCount n ≤ 49 * (n : ℝ) ^ 18 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn9 : (1 : ℝ) ≤ (n : ℝ) ^ 9 := one_le_pow₀ hnR
  have hscale : appendixDiskScale n (n + 1) =
      Real.exp (-1) * (n : ℝ) ^ 9 := by
    unfold appendixDiskScale
    push_cast
    congr 2
    ring
  have hexp : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hscale_le : 2 * appendixDiskScale n (n + 1) ≤
      2 * (n : ℝ) ^ 9 := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (by positivity) hexp) (by norm_num)
  have hceil : (sourceCloseRadius n : ℝ) <
      2 * appendixDiskScale n (n + 1) + 1 := by
    simpa [sourceCloseRadius] using
      Nat.ceil_lt_add_one
        (show 0 ≤ 2 * appendixDiskScale n (n + 1) by
          unfold appendixDiskScale
          positivity)
  have hradius : (sourceCloseRadius n : ℝ) ≤
      2 * (n : ℝ) ^ 9 + 1 := by
    linarith
  have hside : ((2 * sourceCloseRadius n + 1 : ℕ) : ℝ) ≤
      7 * (n : ℝ) ^ 9 := by
    push_cast
    nlinarith
  calc
    sourceCloseCount n = ((2 * sourceCloseRadius n + 1 : ℕ) : ℝ) ^ 2 := by
      simp [sourceCloseCount]
    _ ≤ (7 * (n : ℝ) ^ 9) ^ 2 := by gcongr
    _ = 49 * (n : ℝ) ^ 18 := by ring

/-- The canonical source box has its full exponential-in-`n` area. -/
theorem exp_two_mul_polynomial_le_sourceBoxKsq {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 18 ≤ sourceBoxKsq n := by
  have hscale0 : appendixDiskScale n 0 =
      Real.exp (n : ℝ) * (n : ℝ) ^ 9 := by
    simp [appendixDiskScale]
  have hradius : appendixDiskScale n 0 ≤ (sourceBoxRadius n : ℝ) := by
    simpa [sourceBoxRadius] using Nat.le_ceil (appendixDiskScale n 0)
  have hnonneg : 0 ≤ appendixDiskScale n 0 := by
    unfold appendixDiskScale
    positivity
  calc
    Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 18 =
        (appendixDiskScale n 0) ^ 2 := by
      rw [hscale0, sq, show 2 * (n : ℝ) = (n : ℝ) + n by ring,
        Real.exp_add]
      ring
    _ ≤ ((sourceBoxRadius n : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg ((sourceBoxRadius n : ℝ) + 1 -
        appendixDiskScale n 0)]
    _ = sourceBoxKsq n := by
      simp [sourceBoxKsq, Nat.cast_add, Nat.cast_pow]

/-- Quantitative form of the scale separation behind the close-pair
term: the final unresolved shell is an `exp (-2n)` fraction of the source
box, up to the explicit constant `49`. -/
theorem sourceCloseCount_le_exp_neg_two_mul_box {n : ℕ} (hn : 1 ≤ n) :
    sourceCloseCount n ≤
      49 * Real.exp (-2 * (n : ℝ)) * sourceBoxKsq n := by
  have hpoly := sourceCloseCount_le_polynomial hn
  have hbox := exp_two_mul_polynomial_le_sourceBoxKsq hn
  have hfactor : 0 ≤ 49 * Real.exp (-2 * (n : ℝ)) := by positivity
  calc
    sourceCloseCount n ≤ 49 * (n : ℝ) ^ 18 := hpoly
    _ = (49 * Real.exp (-2 * (n : ℝ))) *
        (Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 18) := by
      symm
      calc
        (49 * Real.exp (-2 * (n : ℝ))) *
            (Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 18) =
            49 * (Real.exp (-2 * (n : ℝ)) *
              Real.exp (2 * (n : ℝ))) * (n : ℝ) ^ 18 := by ring
        _ = 49 * (n : ℝ) ^ 18 := by
          rw [← Real.exp_add]
          ring_nf
          norm_num
    _ ≤ (49 * Real.exp (-2 * (n : ℝ))) * sourceBoxKsq n :=
      mul_le_mul_of_nonneg_left hbox hfactor
    _ = 49 * Real.exp (-2 * (n : ℝ)) * sourceBoxKsq n := by ring

/-- The exact first-moment scale supplied by the finite profile partition. -/
noncomputable def sourceOnePointScale
    (A7 cInitial cTerminal cAnnulus : ℝ) : ℝ :=
  cAnnulus * ((cInitial * cTerminal) * A7)

/-- The two scale-independent endpoint factors in the Appendix first moment. -/
noncomputable def appendixFixedEndpointFactor : ℝ :=
  sourceInitialLower appendixProfileDelta * (1 / 64)

theorem appendixFixedEndpointFactor_pos :
    0 < appendixFixedEndpointFactor := by
  unfold appendixFixedEndpointFactor
  exact mul_pos (sourceInitialLower_pos _) (by norm_num)

/-- A nonnegative exponential cost which is sufficient to pay the fixed
initial and terminal negative-binomial factors. -/
noncomputable def appendixFixedEndpointCost : ℝ :=
  max 0 (-Real.log appendixFixedEndpointFactor)

theorem appendixFixedEndpointCost_nonneg :
    0 ≤ appendixFixedEndpointCost := by
  unfold appendixFixedEndpointCost
  exact le_max_left _ _

/-- The fixed endpoint factor is bounded below by its logarithmic cost. -/
theorem exp_neg_appendixFixedEndpointCost_le :
    Real.exp (-appendixFixedEndpointCost) ≤
      appendixFixedEndpointFactor := by
  by_cases hp : appendixFixedEndpointFactor ≤ 1
  · have hlog : Real.log appendixFixedEndpointFactor ≤ 0 :=
      Real.log_nonpos appendixFixedEndpointFactor_pos.le hp
    rw [appendixFixedEndpointCost, max_eq_right (neg_nonneg.mpr hlog),
      neg_neg, Real.exp_log appendixFixedEndpointFactor_pos]
  · have hp1 : 1 ≤ appendixFixedEndpointFactor := le_of_lt (lt_of_not_ge hp)
    have hlog : 0 ≤ Real.log appendixFixedEndpointFactor :=
      Real.log_nonneg hp1
    rw [appendixFixedEndpointCost, max_eq_left (neg_nonpos.mpr hlog), neg_zero,
      Real.exp_zero]
    exact hp1

/-- The same endpoint bound after enlarging its fixed cost by the checked
positive power of the outer scale. -/
theorem exp_scaledEndpointCost_le
    {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-appendixFixedEndpointCost *
        (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      appendixFixedEndpointFactor := by
  apply (Real.exp_le_exp.mpr ?_).trans
    exp_neg_appendixFixedEndpointCost_le
  have hp : 1 ≤ (n : ℝ) ^ (753 / 1250 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hc := appendixFixedEndpointCost_nonneg
  nlinarith

/-- Complete one-point exponent after adding a supplied annular-comparison
cost to the now-proved A.7 and endpoint costs. -/
noncomputable def sourceOnePointCost (cAnnulusCost : ℝ) : ℝ :=
  appendixSourceA7CostConstant + appendixFixedEndpointCost + cAnnulusCost

theorem sourceOnePointCost_nonneg {cAnnulusCost : ℝ}
    (hAnnulusCost : 0 ≤ cAnnulusCost) :
    0 ≤ sourceOnePointCost cAnnulusCost := by
  unfold sourceOnePointCost
  positivity [appendixSourceA7CostConstant_nonneg,
    appendixFixedEndpointCost_nonneg, hAnnulusCost]

/-- A quantitative annular lower bound is the only remaining ingredient in
the lower order of the full one-point scale. -/
theorem sourceOnePointScale_quantitative_lower
    {n : ℕ} (hn : 1 ≤ n) {cAnnulus cAnnulusCost : ℝ}
    (hAnnulus : Real.exp (-cAnnulusCost *
      (n : ℝ) ^ (753 / 1250 : ℝ)) ≤ cAnnulus)
    (hA7 : Real.exp (-2 * (n : ℝ) -
      appendixSourceA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
        appendixSourceA7 n) :
    Real.exp (-2 * (n : ℝ) - sourceOnePointCost cAnnulusCost *
        (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64) cAnnulus := by
  have hendpoint := exp_scaledEndpointCost_le hn
  change Real.exp (-appendixFixedEndpointCost *
      (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
    sourceInitialLower appendixProfileDelta * (1 / 64) at hendpoint
  have hAnn0 : 0 ≤ cAnnulus :=
    (Real.exp_pos _).le.trans hAnnulus
  unfold sourceOnePointScale
  calc
    Real.exp (-2 * (n : ℝ) - sourceOnePointCost cAnnulusCost *
        (n : ℝ) ^ (753 / 1250 : ℝ)) =
      Real.exp (-cAnnulusCost * (n : ℝ) ^ (753 / 1250 : ℝ)) *
        (Real.exp (-appendixFixedEndpointCost *
            (n : ℝ) ^ (753 / 1250 : ℝ)) *
          Real.exp (-2 * (n : ℝ) - appendixSourceA7CostConstant *
            (n : ℝ) ^ (753 / 1250 : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold sourceOnePointCost
      congr 1
      ring
    _ ≤ cAnnulus *
        ((sourceInitialLower appendixProfileDelta * (1 / 64)) *
          appendixSourceA7 n) := by
      exact mul_le_mul hAnnulus
        (mul_le_mul hendpoint hA7 (Real.exp_pos _).le
          (appendixFixedEndpointFactor_pos.le))
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hAnn0

/-- Eventual source-facing version: an annular factor of order
`exp (-C n^(753/1250))` combines with the proved profile and endpoint factors
to give the exact `exp (-2n - C' n^(753/1250))` one-point lower order. -/
theorem eventually_sourceOnePointScale_quantitative_lower_of_annulus
    {cAnnulus : ℕ → ℝ} {cAnnulusCost : ℝ}
    (hAnnulus : ∀ᶠ n : ℕ in atTop,
      Real.exp (-cAnnulusCost * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
        cAnnulus n) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ) - sourceOnePointCost cAnnulusCost *
          (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
        sourceOnePointScale (appendixSourceA7 n)
          (sourceInitialLower appendixProfileDelta) (1 / 64) (cAnnulus n) := by
  filter_upwards [hAnnulus, eventually_appendixSourceA7_quantitative_lower,
    eventually_ge_atTop (1 : ℕ)] with n hAnn hA7 hn
  exact sourceOnePointScale_quantitative_lower hn hAnn hA7

/-- The exact second-moment coefficient before forcing the unresolved close
shell into a scale-independent constant.  The final quotient is the genuine
close-pair contribution. -/
noncomputable def sourceUnabsorbedPaleyCoefficient
    (n : ℕ) (c E q : ℝ) : ℝ :=
  sourcePaleyCoefficient n c E +
    sourceCloseCount n * c / (sourceBoxKsq n * q)

theorem sourceUnabsorbedPaleyCoefficient_pos
    (n : ℕ) (c E q : ℝ) (hc : 0 ≤ c) (hq : 0 < q) :
    0 < sourceUnabsorbedPaleyCoefficient n c E q := by
  unfold sourceUnabsorbedPaleyCoefficient
  have hclose : 0 ≤
      sourceCloseCount n * c / (sourceBoxKsq n * q) := by
    apply div_nonneg
    · exact mul_nonneg (by unfold sourceCloseCount; positivity) hc
    · exact mul_nonneg (sourceBoxKsq_pos n).le hq.le
  linarith [sourcePaleyCoefficient_pos n c E]

/-- A fixed multiple of a smaller natural-indexed real power is eventually
bounded by half of a larger power. -/
theorem eventually_const_mul_nat_rpow_le_half
    {C b a : ℝ} (hba : b < a) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ b ≤ (1 / 2 : ℝ) * (n : ℝ) ^ a := by
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hba)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (2 * C))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    C * (n : ℝ) ^ b ≤
        ((1 / 2 : ℝ) * (n : ℝ) ^ (a - b)) * (n : ℝ) ^ b := by
      gcongr
      linarith
    _ = (1 / 2 : ℝ) * (n : ℝ) ^ a := by
      calc
        ((1 / 2 : ℝ) * (n : ℝ) ^ (a - b)) * (n : ℝ) ^ b =
            (1 / 2 : ℝ) *
              ((n : ℝ) ^ (a - b) * (n : ℝ) ^ b) := by ring
        _ = (1 / 2 : ℝ) * (n : ℝ) ^ a := by
          rw [← Real.rpow_add hnpos]
          congr 2
          ring

/-- Exponentiating a fixed smaller-power loss against a larger negative
power still tends to zero. -/
theorem tendsto_exp_const_mul_rpow_sub_rpow
    {C b a : ℝ} (ha : 0 < a) (hba : b < a) :
    Tendsto (fun n : ℕ ↦
      Real.exp (C * (n : ℝ) ^ b - (n : ℝ) ^ a))
      atTop (nhds 0) := by
  have hdom := eventually_const_mul_nat_rpow_le_half (C := C) hba
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhalf : Tendsto (fun n : ℕ ↦
      (1 / 2 : ℝ) * (n : ℝ) ^ a) atTop atTop :=
    hpow.const_mul_atTop (by norm_num)
  have hmajor : Tendsto (fun n : ℕ ↦
      Real.exp (-((1 / 2 : ℝ) * (n : ℝ) ^ a)))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hhalf)
  apply squeeze_zero'
    (g := fun n : ℕ ↦ Real.exp (-((1 / 2 : ℝ) * (n : ℝ) ^ a)))
    (Eventually.of_forall fun n ↦ (Real.exp_pos _).le)
  · filter_upwards [hdom] with n hn
    exact Real.exp_le_exp.mpr (by linarith)
  · exact hmajor

/-- The close-shell quotient has the expected `exp (C n^b)` upper bound
once the one-point mass contains the deterministic `exp (-2n)` cost. -/
theorem sourceCloseCoefficient_le_exp_rpow
    {n : ℕ} (hn : 1 ≤ n) {q c C b : ℝ}
    (hc : 0 ≤ c)
    (hq : Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b) ≤ q) :
    sourceCloseCount n * c / (sourceBoxKsq n * q) ≤
      49 * c * Real.exp (C * (n : ℝ) ^ b) := by
  have hqpos : 0 < q := (Real.exp_pos _).trans_le hq
  have hboxpos : 0 < sourceBoxKsq n := sourceBoxKsq_pos n
  have hexpcancel :
      Real.exp (C * (n : ℝ) ^ b) *
          Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b) =
        Real.exp (-2 * (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_le_iff₀ (mul_pos hboxpos hqpos)]
  calc
    sourceCloseCount n * c ≤
        (49 * Real.exp (-2 * (n : ℝ)) * sourceBoxKsq n) * c :=
      mul_le_mul_of_nonneg_right
        (sourceCloseCount_le_exp_neg_two_mul_box hn) hc
    _ = (49 * c * Real.exp (C * (n : ℝ) ^ b)) *
          (sourceBoxKsq n *
            Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b)) := by
      symm
      calc
        (49 * c * Real.exp (C * (n : ℝ) ^ b)) *
            (sourceBoxKsq n *
              Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b)) =
            49 * c * sourceBoxKsq n *
              (Real.exp (C * (n : ℝ) ^ b) *
                Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b)) := by ring
        _ = 49 * Real.exp (-2 * (n : ℝ)) * sourceBoxKsq n * c := by
          rw [hexpcancel]
          ring
    _ ≤ (49 * c * Real.exp (C * (n : ℝ) ^ b)) *
          (sourceBoxKsq n * q) := by
      gcongr

/-- With a genuine `exp (-2n - C n^b)` one-point lower bound and
`b < 3/5+ε/3`, both the far-shell and close-shell contributions fit in
the final Paley--Zygmund budget. -/
theorem eventually_sourceUnabsorbedPaley_budget_of_onePoint_lower
    (q : ℕ → ℝ) (c E C b : ℝ) (hc : 0 ≤ c)
    (hb : b < 3 / 5 + appendixEpsilon / 3)
    (hq : ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b) ≤ q n) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) ^
          (3 / 5 + appendixEpsilon / 3 : ℝ))) <
        1 / sourceUnabsorbedPaleyCoefficient n c E (q n) := by
  let a : ℝ := 3 / 5 + appendixEpsilon / 3
  have ha : 0 < a := by norm_num [a, appendixEpsilon]
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ ↦
      Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  have hlinear := tendsto_natCast_mul_exp_neg_rpow ha
  have hfar : Tendsto (fun n : ℕ ↦
      sourcePaleyCoefficient n c E * Real.exp (-((n : ℝ) ^ a)))
      atTop (nhds 0) := by
    let A : ℝ := sourceShellConstant * Real.exp E * c ^ 2
    let B : ℝ := 2 * A + Real.exp E
    have hfirst : Tendsto (fun n : ℕ ↦
        A * ((n : ℝ) * Real.exp (-((n : ℝ) ^ a)))) atTop (nhds 0) :=
      by simpa using hlinear.const_mul A
    have hsecond : Tendsto (fun n : ℕ ↦
        B * Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) :=
      by simpa using hexp.const_mul B
    convert hfirst.add hsecond using 1
    · funext n
      unfold sourcePaleyCoefficient A B
      push_cast
      ring
    · norm_num
  have htail := tendsto_exp_const_mul_rpow_sub_rpow (C := C) ha
    (by simpa [a] using hb)
  have hmajor : Tendsto (fun n : ℕ ↦
      49 * c * Real.exp (C * (n : ℝ) ^ b - (n : ℝ) ^ a))
      atTop (nhds 0) := by simpa using htail.const_mul (49 * c)
  have hclose : Tendsto (fun n : ℕ ↦
      (sourceCloseCount n * c / (sourceBoxKsq n * q n)) *
        Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [hq] with n hn
      have hqpos : 0 < q n := (Real.exp_pos _).trans_le hn
      have hcoef : 0 ≤
          sourceCloseCount n * c / (sourceBoxKsq n * q n) := by
        apply div_nonneg
        · exact mul_nonneg (by unfold sourceCloseCount; positivity) hc
        · exact mul_nonneg (sourceBoxKsq_pos n).le hqpos.le
      exact mul_nonneg hcoef (Real.exp_pos _).le
    · filter_upwards [hq, eventually_ge_atTop (1 : ℕ)] with n hqn hn
      have hbound := sourceCloseCoefficient_le_exp_rpow hn hc hqn
      calc
        (sourceCloseCount n * c / (sourceBoxKsq n * q n)) *
            Real.exp (-((n : ℝ) ^ a)) ≤
          (49 * c * Real.exp (C * (n : ℝ) ^ b)) *
            Real.exp (-((n : ℝ) ^ a)) := by gcongr
        _ = 49 * c *
            Real.exp (C * (n : ℝ) ^ b - (n : ℝ) ^ a) := by
          calc
            (49 * c * Real.exp (C * (n : ℝ) ^ b)) *
                Real.exp (-((n : ℝ) ^ a)) =
              49 * c * (Real.exp (C * (n : ℝ) ^ b) *
                Real.exp (-((n : ℝ) ^ a))) := by ring
            _ = 49 * c *
                Real.exp (C * (n : ℝ) ^ b - (n : ℝ) ^ a) := by
              rw [← Real.exp_add]
              congr 2
    · exact hmajor
  have htotal : Tendsto (fun n : ℕ ↦
      sourceUnabsorbedPaleyCoefficient n c E (q n) *
        Real.exp (-((n : ℝ) ^ a))) atTop (nhds 0) := by
    convert hfar.add hclose using 1
    · funext n
      unfold sourceUnabsorbedPaleyCoefficient
      ring
    · norm_num
  have hlt := htotal.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hq, hlt] with n hqn hn
  have hqpos : 0 < q n := (Real.exp_pos _).trans_le hqn
  apply (lt_div_iff₀ (sourceUnabsorbedPaleyCoefficient_pos n c E (q n) hc hqpos)).2
  simpa [a, mul_comm] using hn

/-! ### Source exit-word certificates for the two-point input -/

/-- All source data for one invocation of the corrected exit-word reduction.
The two successful events, their separation level, and the final error
exponent are parameters; thus the structure cannot store the desired
two-point conclusion as a field. -/
structure SourceExitWordData
    (Ax Ay : Set (ℕ → Direction)) (l : ℕ) (E : ℝ)
    (β : Type) (N profileN : ℕ) where
  hprofileN : 2 ≤ profileN
  delta : ℝ
  outer : Set (ℕ → Direction)
  count : (ℕ → Direction) → ℕ
  cutoff : ℕ
  profiles : ℕ → Finset (NatPath N)
  innerAtom : ℕ → NatPath N → Set (ℕ → Direction)
  words : ℕ → Finset β
  radius : (m : ℕ) → β → Fin m → ℕ
  actualStart : (m : ℕ) → β → Fin m → Site
  referenceStart : (m : ℕ) → β → Fin m → Site
  exitSite : (m : ℕ) → β → Fin m → Site
  continuation : ℕ → β → NatPath N → ℝ
  potential : Site → ℝ
  potential_isPlanar : IsPlanarPotentialKernel potential
  lowerBoundary : (m : ℕ) → β → Fin m → Site → ℝ
  upperBoundary : (m : ℕ) → β → Fin m → Site → ℝ
  denominatorLower : (m : ℕ) → β → Fin m → ℝ
  innerBound : ℝ
  kernelError : ℝ
  Eh : ℝ
  Ei : ℝ
  Eo : ℝ
  Et : ℝ
  kernelError_nonneg : 0 ≤ kernelError
  innerBound_nonneg : 0 ≤ innerBound
  outer_measurable : MeasurableSet outer
  count_measurable : Measurable count
  boundedCount_in_profiles :
    Ax ∩ Ay ∩ {ω | count ω ≤ cutoff} ⊆
      truncatedAnnularPair profiles innerAtom outer count cutoff
  continuation_nonneg : ∀ m ≤ cutoff, ∀ b ∈ words m,
    ∀ q ∈ profiles m, 0 ≤ continuation m b q
  actualStart_mem : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    actualStart m b i ∈ squareDisk (radius m b i)
  referenceStart_mem : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    referenceStart m b i ∈ squareDisk (radius m b i)
  exitSite_not_mem : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    exitSite m b i ∉ squareDisk (radius m b i)
  denominatorLower_pos : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    0 < denominatorLower m b i
  denominatorLower_le : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    denominatorLower m b i ≤
      KilledGreen.squareGreenExitKernel (radius m b i)
        (referenceStart m b i) (exitSite m b i)
  boundary_bounds : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    ∀ d : Direction,
    exitSite m b i - directionStep d ∈ squareDisk (radius m b i) →
    ∀ w ∈ squareDisk (radius m b i + 1),
      w ∉ squareDisk (radius m b i) →
      lowerBoundary m b i (exitSite m b i - directionStep d) ≤
          potential (w - (exitSite m b i - directionStep d)) ∧
        potential (w - (exitSite m b i - directionStep d)) ≤
          upperBoundary m b i (exitSite m b i - directionStep d)
  potential_oscillation : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    (squareExitPotentialDifference (radius m b i) potential
        (actualStart m b i) (referenceStart m b i) (exitSite m b i) +
      squareExitBoundaryPotentialRange (radius m b i)
        (lowerBoundary m b i) (upperBoundary m b i) (exitSite m b i)) /
        denominatorLower m b i ≤ kernelError
  exact_strongMarkov_expansion : ∀ m ≤ cutoff,
    incrementLaw.real
        (annularProfileFiber (profiles m) (innerAtom m) ∩
          countedOuterFiber outer count m) =
      annularProfileWordKernelMass profileN delta (profiles m) (words m)
          (radius m) (actualStart m) (exitSite m) (continuation m) *
        incrementLaw.real (countedOuterFiber outer count m)
  reference_inner_firstMoment : ∀ m ≤ cutoff,
    annularProfileWordKernelMass profileN delta (profiles m) (words m)
        (radius m) (referenceStart m) (exitSite m) (continuation m) ≤
      innerBound
  harnack_factor : (1 + kernelError) ^ cutoff ≤ Real.exp Eh
  truncated_inner_firstMoment :
    innerBound ≤ Real.exp (2 * (l : ℝ) + Ei) * incrementLaw.real Ay
  outer_firstMoment : incrementLaw.real outer ≤ Real.exp Eo * incrementLaw.real Ax
  largeCount_tail :
    incrementLaw.real (largeCountPairTail Ax Ay count cutoff) ≤
      Real.exp (2 * (l : ℝ) + Et) * incrementLaw.real Ax * incrementLaw.real Ay
  error_budget : Real.exp (Eh + Ei + Eo) + Real.exp Et ≤ Real.exp E

/-- Existence of source exit-word data for one pair.  The boundary-word type
and profile length are allowed to depend on the pair. -/
def HasLegacySourceExitWordCertificate
    (Ax Ay : Set (ℕ → Direction)) (l : ℕ) (E : ℝ) : Prop :=
  ∃ (β : Type) (N profileN : ℕ),
    Nonempty (SourceExitWordData Ax Ay l E β N profileN)

/-- A source certificate yields exactly Proposition A.3(2), by the checked
potential-kernel/exit-word reduction. -/
theorem twoPoint_of_legacySourceExitWordCertificate
    {Ax Ay : Set (ℕ → Direction)} {l : ℕ} {E : ℝ}
    (h : HasLegacySourceExitWordCertificate Ax Ay l E) :
    incrementLaw.real (Ax ∩ Ay) ≤
      Real.exp (2 * (l : ℝ) + E) *
        incrementLaw.real Ax * incrementLaw.real Ay := by
  rcases h with ⟨β, N, profileN, ⟨D⟩⟩
  exact propA3_twoPoint_of_source_exit_words_and_potential_boundary
    incrementLaw D.hprofileN D.delta Ax Ay D.outer D.count D.cutoff l
    D.profiles D.innerAtom D.words D.radius D.actualStart D.referenceStart
    D.exitSite D.continuation D.potential D.potential_isPlanar
    D.lowerBoundary D.upperBoundary D.denominatorLower
    D.kernelError_nonneg D.innerBound_nonneg D.outer_measurable
    D.count_measurable D.boundedCount_in_profiles D.continuation_nonneg
    D.actualStart_mem D.referenceStart_mem D.exitSite_not_mem
    D.denominatorLower_pos D.denominatorLower_le D.boundary_bounds
    D.potential_oscillation D.exact_strongMarkov_expansion
    D.reference_inner_firstMoment D.harnack_factor
    D.truncated_inner_firstMoment D.outer_firstMoment D.largeCount_tail
    D.error_budget

/-- The deterministic exponent paid by the canonical-right Harnack chain.
The pointwise gradient constant is universal, so the complete power loss is
fixed by the profile length and the number of excursions; it is not source
data. -/
noncomputable def canonicalRightHarnackExponent
    (profileN cutoff : ℕ) : ℝ :=
  (102400 * Real.exp 10209) * (cutoff : ℝ) / (profileN : ℝ) ^ 3

/-- The canonical-right Harnack power is bounded by its deterministic
exponential cost. -/
theorem canonicalRightHarnackFactor_le_exp
    (profileN cutoff : ℕ) :
    (1 + (102400 * Real.exp 10209) / (profileN : ℝ) ^ 3) ^ cutoff ≤
      Real.exp (canonicalRightHarnackExponent profileN cutoff) := by
  let x : ℝ := (102400 * Real.exp 10209) / (profileN : ℝ) ^ 3
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hbase : 0 ≤ 1 + x := by positivity
  have hstep : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  calc
    (1 + x) ^ cutoff ≤ (Real.exp x) ^ cutoff :=
      pow_le_pow_left₀ hbase hstep cutoff
    _ = Real.exp ((cutoff : ℝ) * x) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (canonicalRightHarnackExponent profileN cutoff) := by
      congr 1
      dsimp [x, canonicalRightHarnackExponent]
      ring

/-- Denominator-free source data for the exit-word reduction.  In place of
the legacy potential-boundary denominator fields, this structure records a
nearest-neighbor path from the reference start to the actual start and the
single canonical-right signed-sum gradient estimate along the containing
inner square. -/
structure CanonicalRightSourceExitWordData
    (Ax Ay : Set (ℕ → Direction)) (l : ℕ) (E : ℝ)
    (β : Type) (N profileN : ℕ) where
  hprofileN : 2 ≤ profileN
  delta : ℝ
  outer : Set (ℕ → Direction)
  count : (ℕ → Direction) → ℕ
  cutoff : ℕ
  profiles : ℕ → Finset (NatPath N)
  innerAtom : ℕ → NatPath N → Set (ℕ → Direction)
  words : ℕ → Finset β
  innerRadius : (m : ℕ) → β → Fin m → ℕ
  radius : (m : ℕ) → β → Fin m → ℕ
  pathLength : (m : ℕ) → β → Fin m → ℕ
  path : (m : ℕ) → β → Fin m → ℕ → Site
  direction : (m : ℕ) → β → Fin m → ℕ → Direction
  exitSite : (m : ℕ) → β → Fin m → Site
  /-- The fresh profile continuation is intrinsically nonnegative.  Storing
  it in `NNReal` removes a redundant sign premise from the canonical literal
  certificate. -/
  continuation : ℕ → β → NatPath N → ℝ≥0
  Ei : ℝ
  Eo : ℝ
  Et : ℝ
  outer_measurable : MeasurableSet outer
  count_measurable : Measurable count
  boundedCount_in_profiles :
    Ax ∩ Ay ∩ {ω | count ω ≤ cutoff} ⊆
      truncatedAnnularPair profiles innerAtom outer count cutoff
  radius_large : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    19 ≤ radius m b i
  pathLength_le : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    pathLength m b i ≤ innerRadius m b i
  cubicScale : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    profileN ^ 3 * innerRadius m b i ≤ radius m b i
  path_step : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    ∀ k < pathLength m b i,
      path m b i (k + 1) =
        path m b i k + directionStep (direction m b i k)
  path_inner : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    ∀ k ≤ pathLength m b i,
      path m b i k ∈ squareDisk (innerRadius m b i)
  exitSite_not_mem : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
    exitSite m b i ∉ squareDisk (radius m b i)
  exact_strongMarkov_expansion : ∀ m ≤ cutoff,
    incrementLaw.real
        (annularProfileFiber (profiles m) (innerAtom m) ∩
          countedOuterFiber outer count m) =
      annularProfileWordKernelMass profileN delta (profiles m) (words m)
          (radius m) (fun b i ↦ path m b i (pathLength m b i))
            (exitSite m) (fun b q ↦ (continuation m b q : ℝ)) *
        incrementLaw.real (countedOuterFiber outer count m)
  reference_inner_firstMoment : ∀ m ≤ cutoff,
    annularProfileWordKernelMass profileN delta (profiles m) (words m)
        (radius m) (fun b i ↦ path m b i 0) (exitSite m)
          (fun b q ↦ (continuation m b q : ℝ)) ≤
      Real.exp (2 * (l : ℝ) + Ei) * incrementLaw.real Ay
  outer_firstMoment : incrementLaw.real outer ≤ Real.exp Eo * incrementLaw.real Ax
  largeCount_tail :
    incrementLaw.real (largeCountPairTail Ax Ay count cutoff) ≤
      Real.exp (2 * (l : ℝ) + Et) * incrementLaw.real Ax * incrementLaw.real Ay
  error_budget :
    Real.exp (canonicalRightHarnackExponent profileN cutoff + Ei + Eo) +
      Real.exp Et ≤ Real.exp E

/-- The canonical-right source certificate gives the two-point estimate
directly through the exact exit-word comparison.  Its only lower input is
for the complete corner-normalized reference column, rather than a separate
lower bound for each unnormalized boundary atom. -/
theorem twoPoint_of_canonicalRightSourceExitWordData
    {Ax Ay : Set (ℕ → Direction)} {l : ℕ} {E : ℝ}
    {β : Type} {N profileN : ℕ}
    (D : CanonicalRightSourceExitWordData Ax Ay l E β N profileN) :
    incrementLaw.real (Ax ∩ Ay) ≤
      Real.exp (2 * (l : ℝ) + E) *
        incrementLaw.real Ax * incrementLaw.real Ay := by
  let truncated := truncatedAnnularPair D.profiles D.innerAtom
    D.outer D.count D.cutoff
  let tail := largeCountPairTail Ax Ay D.count D.cutoff
  let innerFiber : ℕ → Set (ℕ → Direction) := fun m ↦
    annularProfileFiber (D.profiles m) (D.innerAtom m)
  let outerFiber : ℕ → Set (ℕ → Direction) := fun m ↦
    countedOuterFiber D.outer D.count m
  let kernelFactor : ℝ :=
    1 + (102400 * Real.exp 10209) / (profileN : ℝ) ^ 3
  let innerBudget : ℝ :=
    Real.exp (2 * (l : ℝ) + D.Ei) * incrementLaw.real Ay
  have hbase : (1 : ℝ) ≤ kernelFactor := by
    dsimp [kernelFactor]
    have hden : 0 ≤ (profileN : ℝ) ^ 3 := by positivity
    have := div_nonneg (by positivity : 0 ≤ 102400 * Real.exp 10209) hden
    linarith
  have hfactor0 : 0 ≤ kernelFactor ^ D.cutoff := by positivity
  have hinnerBudget0 : 0 ≤ innerBudget := by
    dsimp [innerBudget]
    positivity
  have hharnack : kernelFactor ^ D.cutoff ≤
      Real.exp (canonicalRightHarnackExponent profileN D.cutoff) := by
    simpa only [kernelFactor] using
      canonicalRightHarnackFactor_le_exp profileN D.cutoff
  have hconditional : ∀ m ≤ D.cutoff,
      incrementLaw.real (innerFiber m ∩ outerFiber m) ≤
        kernelFactor ^ D.cutoff * innerBudget *
          incrementLaw.real (outerFiber m) := by
    intro m hm
    have hradiusPos : ∀ b ∈ D.words m, ∀ i,
        0 < D.radius m b i := by
      intro b hb i
      exact lt_of_lt_of_le (by norm_num) (D.radius_large m hm b hb i)
    have hinnerRadiusLe : ∀ b ∈ D.words m, ∀ i,
        D.innerRadius m b i ≤ D.radius m b i := by
      intro b hb i
      have hcube : 1 ≤ profileN ^ 3 := by
        have hp := D.hprofileN
        nlinarith [Nat.mul_self_le_mul_self hp]
      calc
        D.innerRadius m b i = 1 * D.innerRadius m b i := by omega
        _ ≤ profileN ^ 3 * D.innerRadius m b i :=
          Nat.mul_le_mul_right _ hcube
        _ ≤ D.radius m b i := D.cubicScale m hm b hb i
    have hrefMem : ∀ b ∈ D.words m, ∀ i,
        D.path m b i 0 ∈ squareDisk (D.radius m b i) := by
      intro b hb i
      have hrefInner := D.path_inner m hm b hb i 0 (by omega)
      exact squareDisk_mono (hinnerRadiusLe b hb i) hrefInner
    have hgradient : ∀ b ∈ D.words m, ∀ i,
        HasUniformInnerExitPredecessorCanonicalRightNormalizedGradient
          (D.innerRadius m b i) (D.radius m b i)
          (D.path m b i 0) (D.exitSite m b i)
            (102400 * Real.exp 10209) := by
      intro b hb i
      have hprofileCube : 8 ≤ profileN ^ 3 := by
        have hp := D.hprofileN
        nlinarith [Nat.mul_self_le_mul_self hp]
      have htwo : 2 * D.innerRadius m b i ≤ D.radius m b i := by
        have hcubic := D.cubicScale m hm b hb i
        calc
          2 * D.innerRadius m b i ≤ 8 * D.innerRadius m b i :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ ≤ profileN ^ 3 * D.innerRadius m b i :=
            Nat.mul_le_mul_right _ hprofileCube
          _ ≤ D.radius m b i := hcubic
      have hrefInner : D.path m b i 0 ∈
          squareDisk (D.innerRadius m b i) := by
        exact D.path_inner m hm b hb i 0 (by omega)
      exact
        (hasUniformInnerExitPredecessorCanonicalRightGradient_iff_normalized).mp
          (hasUniformInnerExitPredecessorCanonicalRightGradient_of_lazyKernel
            (D.exitSite_not_mem m hm b hb i) hrefInner htwo
              (D.radius_large m hm b hb i))
    let continuation : β → NatPath N → ℝ :=
      fun b q ↦ (D.continuation m b q : ℝ)
    have hcontinuation : ∀ b ∈ D.words m, ∀ q ∈ D.profiles m,
        0 ≤ continuation b q := by
      intro b hb q hq
      exact (D.continuation m b q).2
    have hmassPath :=
      annularProfileWordKernelMass_le_of_canonicalRightNormalizedGradient_cubicScale
        (delta := D.delta) D.hprofileN (D.profiles m) (D.words m)
        (D.innerRadius m) (D.radius m) (D.pathLength m) (D.path m)
        (D.direction m) (fun b i ↦ D.path m b i 0) (D.exitSite m)
        continuation (by exact lt_of_lt_of_le (by norm_num) D.hprofileN)
        hcontinuation (D.exitSite_not_mem m hm)
        hradiusPos hinnerRadiusLe
        (D.pathLength_le m hm) (D.cubicScale m hm)
        (by positivity : 0 ≤ 102400 * Real.exp 10209) (by simp)
        (D.path_step m hm) (D.path_inner m hm)
        hrefMem
        hgradient
    have hmass :
        annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
            (D.radius m) (fun b i ↦ D.path m b i (D.pathLength m b i))
              (D.exitSite m) continuation ≤
          kernelFactor ^ m *
            annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
              (D.radius m) (fun b i ↦ D.path m b i 0) (D.exitSite m)
              continuation := by
      exact hmassPath
    have hpow : kernelFactor ^ m ≤ kernelFactor ^ D.cutoff :=
      pow_le_pow_right₀ hbase hm
    have hmassCutoff :
        annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
            (D.radius m) (fun b i ↦ D.path m b i (D.pathLength m b i))
              (D.exitSite m) continuation ≤
          kernelFactor ^ D.cutoff *
            annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
              (D.radius m) (fun b i ↦ D.path m b i 0) (D.exitSite m)
              continuation := by
      calc
        _ ≤ kernelFactor ^ m *
              annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
                (D.radius m) (fun b i ↦ D.path m b i 0) (D.exitSite m)
                continuation := hmass
        _ ≤ kernelFactor ^ D.cutoff *
              annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
                (D.radius m) (fun b i ↦ D.path m b i 0) (D.exitSite m)
                continuation := by
          apply mul_le_mul_of_nonneg_right hpow
          unfold annularProfileWordKernelMass
          apply Finset.sum_nonneg
          intro b hb
          apply mul_nonneg (annularExitWordWeight_nonneg _ _ _)
          apply Finset.sum_nonneg
          intro q hq
          exact mul_nonneg (successfulProfileWeight_nonneg D.delta D.hprofileN q)
            (hcontinuation b hb q hq)
    have houter0 : 0 ≤ incrementLaw.real (outerFiber m) := measureReal_nonneg
    calc
      incrementLaw.real (innerFiber m ∩ outerFiber m) =
          annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
              (D.radius m) (fun b i ↦ D.path m b i (D.pathLength m b i))
                (D.exitSite m) continuation *
            incrementLaw.real (outerFiber m) := D.exact_strongMarkov_expansion m hm
      _ ≤ (kernelFactor ^ D.cutoff *
          annularProfileWordKernelMass profileN D.delta (D.profiles m) (D.words m)
            (D.radius m) (fun b i ↦ D.path m b i 0) (D.exitSite m)
              continuation) *
          incrementLaw.real (outerFiber m) :=
        mul_le_mul_of_nonneg_right hmassCutoff houter0
      _ ≤ (kernelFactor ^ D.cutoff * innerBudget) *
          incrementLaw.real (outerFiber m) := by
        apply mul_le_mul_of_nonneg_right _ houter0
        exact mul_le_mul_of_nonneg_left
          (D.reference_inner_firstMoment m hm) hfactor0
      _ = kernelFactor ^ D.cutoff * innerBudget *
          incrementLaw.real (outerFiber m) := rfl
  exact propA3_twoPoint_of_conditional_decoupling incrementLaw Ax Ay
    truncated tail innerFiber outerFiber D.cutoff l hfactor0
    hinnerBudget0 measureReal_nonneg
    (pair_subset_truncated_union_largeCountPairTail Ax Ay truncated D.count D.cutoff
      D.boundedCount_in_profiles)
    (truncatedAnnularPair_fiber_cover D.profiles D.innerAtom
      D.outer D.count D.cutoff)
    hconditional
    (sum_countedOuterFiber_le incrementLaw D.cutoff
      D.outer_measurable D.count_measurable)
    hharnack le_rfl D.outer_firstMoment
    D.largeCount_tail D.error_budget

/-- Existence of a corner-normalized canonical-right source certificate. -/
def HasCanonicalRightSourceExitWordCertificate
    (Ax Ay : Set (ℕ → Direction)) (l : ℕ) (E : ℝ) : Prop :=
  ∃ (β : Type) (N profileN : ℕ),
    Nonempty (CanonicalRightSourceExitWordData Ax Ay l E β N profileN)

/-- Scale-faithful canonical-right certificate for the Appendix event at
scale `n`.  The profile length, profile scale, and corridor exponent are no
longer existentially unrelated to the successful-site events being bounded. -/
def HasCanonicalRightSourceExitWordCertificateAtScale
    (n : ℕ) (Ax Ay : Set (ℕ → Direction)) (l : ℕ) (E : ℝ) : Prop :=
  ∃ (β : Type), ∃ D : CanonicalRightSourceExitWordData
      Ax Ay l E β (n - 2) n,
    D.delta = appendixProfileDelta ∧
      ∀ m ≤ D.cutoff,
        D.profiles m ⊆ sourceProfiles appendixProfileDelta n

/-- Forgetting the source-scale identifications gives the generic
canonical-right certificate. -/
theorem hasCanonicalRightSourceExitWordCertificate_of_atScale
    {n : ℕ} {Ax Ay : Set (ℕ → Direction)} {l : ℕ} {E : ℝ}
    (h : HasCanonicalRightSourceExitWordCertificateAtScale n Ax Ay l E) :
    HasCanonicalRightSourceExitWordCertificate Ax Ay l E := by
  rcases h with ⟨β, D, hdelta, hprofiles⟩
  exact ⟨β, n - 2, n, ⟨D⟩⟩

/-- Public source certificates accept both the legacy potential-boundary
route and the corner-normalized canonical-right signed-sum route. -/
def HasSourceExitWordCertificate
    (Ax Ay : Set (ℕ → Direction)) (l : ℕ) (E : ℝ) : Prop :=
  HasLegacySourceExitWordCertificate Ax Ay l E ∨
    HasCanonicalRightSourceExitWordCertificate Ax Ay l E

/-- Either source certificate route yields Proposition A.3(2). -/
theorem twoPoint_of_sourceExitWordCertificate
    {Ax Ay : Set (ℕ → Direction)} {l : ℕ} {E : ℝ}
    (h : HasSourceExitWordCertificate Ax Ay l E) :
    incrementLaw.real (Ax ∩ Ay) ≤
      Real.exp (2 * (l : ℝ) + E) *
        incrementLaw.real Ax * incrementLaw.real Ay := by
  rcases h with hlegacy | hright
  · exact twoPoint_of_legacySourceExitWordCertificate hlegacy
  · rcases hright with ⟨β, N, profileN, ⟨D⟩⟩
    exact twoPoint_of_canonicalRightSourceExitWordData D

/-- The source-specific analytic inputs still required at one disk scale.
The field `twoPoint_source` accepts either corrected exit-word route: the
legacy potential-boundary certificate or the corner-normalized
canonical-right signed-sum certificate.  Both routes use the bounded-count
inclusion and `largeCountPairTail`.
Neither endpoint factor is a premise: `sourceInitialLower_le` supplies the
canonical initial factor, while `source_terminalMass_lower` supplies the
terminal constant `1/64` from `n_large` and `delta_le_one`.
-/
structure EuclideanDiskSourceEstimates
    (epsilon delta : ℝ) (n : ℕ)
    (atom : Site → NatPath (n - 2) → Set (ℕ → Direction)) where
  A7 : ℝ
  cAnnulus : ℝ
  c : ℝ
  E : ℝ
  n_large : 64 ≤ n
  delta_le_one : delta ≤ 1
  A7_nonneg : 0 ≤ A7
  cAnnulus_nonneg : 0 ≤ cAnnulus
  c_nonneg : 0 ≤ c
  q_pos : 0 <
    sourceOnePointScale A7 (sourceInitialLower delta) (1 / 64) cAnnulus
  A7_lower : A7 ≤ halfNegBinPathSum (sourceProfiles delta n)
  atom_measurable : ∀ x ∈ sourceSiteBox n, ∀ q ∈ sourceProfiles delta n,
    MeasurableSet (atom x q)
  atom_disjoint : ∀ x ∈ sourceSiteBox n,
    Set.PairwiseDisjoint
      (↑(sourceProfiles delta n) : Set (NatPath (n - 2))) (atom x)
  annulus_lower : ∀ x ∈ sourceSiteBox n, ∀ q ∈ sourceProfiles delta n,
    cAnnulus * successfulProfileWeight n delta q ≤ incrementLaw.real (atom x q)
  local_time_witness : ∀ x ∈ sourceSiteBox n, ∀ q ∈ sourceProfiles delta n,
    atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real (euclideanSuccessfulSiteEvent delta n atom x) ≤
      c * sourceOnePointScale A7 (sourceInitialLower delta) (1 / 64) cAnnulus
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent delta n atom x)
      (euclideanSuccessfulSiteEvent delta n atom y)
      (appendixSeparationLevel n x y) E
  close_absorb :
    sourceCloseCount n * c ≤ Real.exp E *
      (sourceBoxKsq n *
        sourceOnePointScale A7 (sourceInitialLower delta) (1 / 64) cAnnulus)
  paley_budget :
    Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      1 / sourcePaleyCoefficient n c E

/-! ### The literal stopped-annulus atom

The profile atom used in Appendix A is a first-exit event viewed after a
measurable outer stopping time.  Packaging that construction here removes
measurability and pairwise-disjointness from the list of quantitative
source estimates: both facts follow formally from the corresponding facts
for the fresh-walk profile tails. -/

/-- A finite prefix cylinder fixing the first `m` increments. -/
def sourcePrefixCylinder {m : ℕ} (w : Prefix m) : Set (ℕ → Direction) :=
  (Finset.range m).restrict ⁻¹' {w}

theorem measurableSet_sourcePrefixCylinder {m : ℕ} (w : Prefix m) :
    MeasurableSet (sourcePrefixCylinder w) := by
  exact (MeasurableSet.singleton w).preimage (by fun_prop)

/-- Every prescribed `m`-increment word has mass exactly `4⁻ᵐ`. -/
theorem incrementLaw_sourcePrefixCylinder {m : ℕ} (w : Prefix m) :
    incrementLaw (sourcePrefixCylinder w) = (4 : ENNReal)⁻¹ ^ m := by
  calc
    incrementLaw (sourcePrefixCylinder w) =
        (incrementLaw.map (Finset.range m).restrict) {w} := by
      rw [Measure.map_apply]
      · rfl
      · fun_prop
      · measurability
    _ = prefixLaw m {w} := by rw [increment_restrict_map]
    _ = (4 : ENNReal)⁻¹ ^ m := prefixLaw_singleton m w

theorem incrementLawReal_sourcePrefixCylinder {m : ℕ} (w : Prefix m) :
    incrementLaw.real (sourcePrefixCylinder w) =
      ((4 : ENNReal)⁻¹ ^ m).toReal := by
  rw [measureReal_def, incrementLaw_sourcePrefixCylinder]

theorem sourcePrefixCylinderMass_pos (m : ℕ) :
    0 < ((4 : ENNReal)⁻¹ ^ m).toReal :=
  ENNReal.toReal_pos (by norm_num) (by simp)

lemma halfNegBinMass_eq_nbMass (b t : ℕ) :
    HLOZAppendixA.halfNegBinMass b t =
      HLOZTerminalNegBin.nbMass (1 / 2) (1 / 2) b t := by
  unfold HLOZAppendixA.halfNegBinMass HLOZTerminalNegBin.nbMass
  norm_num [div_pow]
  rw [pow_add]
  field_simp

lemma halfNegBinMass_le_one {b t : ℕ} (hb : 1 ≤ b) :
    HLOZAppendixA.halfNegBinMass b t ≤ 1 := by
  rw [halfNegBinMass_eq_nbMass]
  have hsum := HLOZTerminalNegBin.nb_total_hasSum
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ)) hb (by norm_num) (by norm_num)
  calc
    HLOZTerminalNegBin.nbMass (1 / 2) (1 / 2) b t ≤
        ∑' j : ℕ, HLOZTerminalNegBin.nbMass (1 / 2) (1 / 2) b j :=
      hsum.summable.le_tsum t (fun j hj ↦ by
        rw [← halfNegBinMass_eq_nbMass]
        exact HLOZAppendixA.halfNegBinMass_nonneg b j)
    _ = 1 := hsum.tsum_eq

/-- Every coordinate of the canonical Appendix corridor is positive. -/
lemma sourceProfile_coordinate_one_le {n : ℕ}
    {q : NatPath (n - 2)}
    (hq : q ∈ sourceProfiles appendixProfileDelta n)
    (i : Fin ((n - 2) + 1)) : 1 ≤ q i := by
  let ell := 2 + (i : ℕ)
  have hell : 1 ≤ ell := by dsimp [ell]; omega
  have hcorr := (mem_sourceProfiles.mp hq) i
  change |centeredDeviation ell (q i)| ≤
    (HLOZLemmaA8.corridorRadius appendixProfileDelta ell : ℤ) at hcorr
  have hrpow : (ell : ℝ) ^ (1 + appendixProfileDelta) ≤
      (ell : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hell)
      (by norm_num [appendixProfileDelta])
  have hr : HLOZLemmaA8.corridorRadius appendixProfileDelta ell ≤ ell ^ 2 := by
    exact_mod_cast
      (HLOZLemmaA8.corridorRadius_cast_le_self appendixProfileDelta ell |>.trans
        (hrpow.trans_eq (Real.rpow_two _)))
  have hlower :
      -(HLOZLemmaA8.corridorRadius appendixProfileDelta ell : ℤ) ≤
        centeredDeviation ell (q i) := (abs_le.mp hcorr).1
  unfold centeredDeviation at hlower
  have hrZ : (HLOZLemmaA8.corridorRadius appendixProfileDelta ell : ℤ) ≤
      (ell : ℤ) ^ 2 := by exact_mod_cast hr
  have hellZ : (1 : ℤ) ≤ ell := by exact_mod_cast hell
  have hellsqZ : (1 : ℤ) ≤ (ell : ℤ) ^ 2 := by nlinarith
  omega

lemma terminalMass_le_one {n b : ℕ} (delta : ℝ) (hn : 2 ≤ n)
    (hb : 1 ≤ b) : terminalMass n delta b ≤ 1 := by
  have hp0 := topReturnProbability_pos hn
  have hp1 := topReturnProbability_lt_one hn
  have hsum := HLOZTerminalNegBin.nb_total_hasSum
    (p := topReturnProbability n) (q := 1 - topReturnProbability n) hb
      (by rw [abs_of_nonneg (sub_nonneg.mpr hp1.le)]; linarith)
      (by ring)
  unfold terminalMass
  calc
    ∑ t ∈ terminalCounts n delta, topNegBinMass n b t ≤
        ∑' t : ℕ, HLOZTerminalNegBin.nbMass
          (topReturnProbability n) (1 - topReturnProbability n) b t := by
      rw [show (∑ t ∈ terminalCounts n delta, topNegBinMass n b t) =
          ∑ t ∈ terminalCounts n delta, HLOZTerminalNegBin.nbMass
            (topReturnProbability n) (1 - topReturnProbability n) b t by
        apply Finset.sum_congr rfl
        intro t ht
        exact topNegBinMass_eq_nbMass n b t]
      exact hsum.summable.sum_le_tsum (terminalCounts n delta)
        (fun t ht ↦ by
          rw [← topNegBinMass_eq_nbMass]
          exact topNegBinMass_nonneg hn)
    _ = 1 := hsum.tsum_eq

/-- The exact auxiliary weight of each selected source profile is a
sub-probability. -/
lemma successfulProfileWeight_le_one {n : ℕ}
    {q : NatPath (n - 2)} (hn : 2 ≤ n)
    (hq : q ∈ sourceProfiles appendixProfileDelta n) :
    successfulProfileWeight n appendixProfileDelta q ≤ 1 := by
  have hi0 : 0 ≤ initialUpcrossingMass (q 0) := by
    rw [initialUpcrossingMass_eq]
    positivity
  have hi1 : initialUpcrossingMass (q 0) ≤ 1 := by
    apply halfNegBinMass_le_one
    norm_num
  have hp0 : 0 ≤ halfNegBinPathWeight q :=
    halfNegBinPathWeight_nonneg q
  have hp1 : halfNegBinPathWeight q ≤ 1 := by
    unfold halfNegBinPathWeight
    apply Finset.prod_le_one
    · intro i hi
      exact HLOZAppendixA.halfNegBinMass_nonneg _ _
    · intro i hi
      apply halfNegBinMass_le_one
      exact sourceProfile_coordinate_one_le hq i.castSucc
  have ht0 : 0 ≤ terminalMass n appendixProfileDelta (q (Fin.last (n - 2))) :=
    terminalMass_nonneg appendixProfileDelta hn
  have ht1 : terminalMass n appendixProfileDelta (q (Fin.last (n - 2))) ≤ 1 :=
    terminalMass_le_one appendixProfileDelta hn
      (sourceProfile_coordinate_one_le hq (Fin.last (n - 2)))
  unfold successfulProfileWeight
  calc
    initialUpcrossingMass (q 0) * halfNegBinPathWeight q *
        terminalMass n appendixProfileDelta (q (Fin.last (n - 2))) ≤
      (1 : ℝ) * 1 * 1 :=
        mul_le_mul (mul_le_mul hi1 hp1 hp0 (by norm_num)) ht1 ht0
          (by norm_num)
    _ = 1 := by norm_num

/-- A deliberately coarse finite upper budget for one successful-profile
weight.  Its only purpose is to normalize a common positive cylinder mass;
the sharp asymptotics continue to come from `appendixSourceA7`. -/
noncomputable def sourceProfileWeightBudget (n : ℕ) : ℝ :=
  1 + ∑ q ∈ sourceProfiles appendixProfileDelta n,
    successfulProfileWeight n appendixProfileDelta q

theorem sourceProfileWeightBudget_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < sourceProfileWeightBudget n := by
  unfold sourceProfileWeightBudget
  have hsum : 0 ≤ ∑ q ∈ sourceProfiles appendixProfileDelta n,
      successfulProfileWeight n appendixProfileDelta q := by
    apply Finset.sum_nonneg
    intro q hq
    exact successfulProfileWeight_nonneg appendixProfileDelta hn q
  linarith

theorem successfulProfileWeight_le_budget {n : ℕ} (hn : 2 ≤ n)
    {q : NatPath (n - 2)} (hq : q ∈ sourceProfiles appendixProfileDelta n) :
    successfulProfileWeight n appendixProfileDelta q ≤
      sourceProfileWeightBudget n := by
  unfold sourceProfileWeightBudget
  have hsum : successfulProfileWeight n appendixProfileDelta q ≤
      ∑ q ∈ sourceProfiles appendixProfileDelta n,
        successfulProfileWeight n appendixProfileDelta q := by
    exact Finset.single_le_sum
      (fun q hq ↦ successfulProfileWeight_nonneg appendixProfileDelta hn q) hq
  linarith

/-- Structural data defining the actual stopped-annulus profile atom at a
single disk scale.  Only the fresh-walk tails carry measurable/disjointness
assumptions; the stopped atom inherits them from the exact strong-Markov
construction. -/
structure EuclideanDiskStoppedAtomData (n : ℕ) where
  tau : Site → (ℕ → Direction) → ℕ
  radius : Site → ℕ
  start : Site → Site
  exitSites : Site → Finset Site
  profileTail : Site → Site → NatPath (n - 2) → Set (ℕ → Direction)
  tau_level_measurable : ∀ x ∈ sourceSiteBox n, ∀ k,
    MeasurableSet[ProbabilityTheory.iidHistory (X := Direction) k]
      {ω | tau x ω = k}
  exit_not_mem : ∀ x ∈ sourceSiteBox n, ∀ z ∈ exitSites x,
    z ∉ squareDisk (radius x)
  profileTail_measurable : ∀ x ∈ sourceSiteBox n, ∀ z ∈ exitSites x,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
      MeasurableSet (profileTail x z q)
  profileTail_disjoint : ∀ x ∈ sourceSiteBox n, ∀ z ∈ exitSites x,
    Set.PairwiseDisjoint
      (↑(sourceProfiles appendixProfileDelta n) : Set (NatPath (n - 2)))
      (profileTail x z)

namespace EuclideanDiskStoppedAtomData

/-- Adapted stopping-time fibers imply ordinary measurability of the
natural-valued stopping horizon. -/
theorem measurable_tau {n : ℕ} (D : EuclideanDiskStoppedAtomData n)
    (x : Site) (hx : x ∈ sourceSiteBox n) : Measurable (D.tau x) := by
  apply measurable_to_countable'
  intro k
  exact ProbabilityTheory.iidHistory_le k _ (D.tau_level_measurable x hx k)

/-- The literal stopped-annulus atom determined by `D`. -/
def atom {n : ℕ} (D : EuclideanDiskStoppedAtomData n)
    (x : Site) (q : NatPath (n - 2)) : Set (ℕ → Direction) :=
  sourceStoppedAnnularProfileAtom (D.tau x) (D.radius x) (D.start x)
    (D.exitSites x) (D.profileTail x) q

/-- Stopped-annulus atoms are measurable. -/
theorem atom_measurable {n : ℕ} (D : EuclideanDiskStoppedAtomData n)
    (x : Site) (hx : x ∈ sourceSiteBox n)
    (q : NatPath (n - 2)) (hq : q ∈ sourceProfiles appendixProfileDelta n) :
    MeasurableSet (D.atom x q) := by
  exact measurableSet_sourceStoppedAnnularProfileAtom
    (D.tau x) (D.radius x) (D.start x) (D.exitSites x) (D.profileTail x) q
    (D.measurable_tau x hx) (D.exit_not_mem x hx)
    (fun z hz ↦ D.profileTail_measurable x hx z hz q hq)

/-- Different profiles give disjoint stopped-annulus atoms. -/
theorem atom_disjoint {n : ℕ} (D : EuclideanDiskStoppedAtomData n)
    (x : Site) (hx : x ∈ sourceSiteBox n) :
    Set.PairwiseDisjoint
      (↑(sourceProfiles appendixProfileDelta n) : Set (NatPath (n - 2)))
      (D.atom x) := by
  exact pairwiseDisjoint_sourceStoppedAnnularProfileAtom
    (D.tau x) (D.radius x) (D.start x) (D.exitSites x)
    (sourceProfiles appendixProfileDelta n) (D.profileTail x)
    (D.profileTail_disjoint x hx)

/-- Exact one-profile strong-Markov mass formula for the stopped atom. -/
theorem atom_measure_eq {n : ℕ} (D : EuclideanDiskStoppedAtomData n)
    (x : Site) (hx : x ∈ sourceSiteBox n)
    (q : NatPath (n - 2)) (hq : q ∈ sourceProfiles appendixProfileDelta n) :
    incrementLaw.real (D.atom x q) =
      ∑ z ∈ D.exitSites x,
        (firstExitAtWeight (squareDisk (D.radius x) : Set Site)
          (D.start x) z).toReal *
            incrementLaw.real (D.profileTail x z q) := by
  have hENN : incrementLaw (D.atom x q) =
      ∑ z ∈ D.exitSites x,
        firstExitAtWeight (squareDisk (D.radius x) : Set Site)
          (D.start x) z * incrementLaw (D.profileTail x z q) := by
    simpa [atom] using
      (measure_stoppedAnnularProfileUnion (D.tau x) Set.univ
        (squareDisk (D.radius x) : Set Site) (D.start x) (D.exitSites x)
        {q} (D.profileTail x) (D.measurable_tau x hx)
        (fun k ↦ by simpa using D.tau_level_measurable x hx k)
        (D.exit_not_mem x hx)
        (fun z hz q' hq' ↦ by
          simpa only [Finset.mem_singleton.mp hq'] using
            D.profileTail_measurable x hx z hz q hq)
        (fun z hz ↦ by simp [Set.PairwiseDisjoint]))
  rw [measureReal_def, hENN, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [ENNReal.toReal_mul, measureReal_def]
  · intro z hz
    exact ENNReal.mul_ne_top
      (by
        rw [firstExitAtWeight_eq_measure
          (squareDisk (D.radius x) : Set Site) (D.start x) z
          (D.exit_not_mem x hx z hz)]
        exact measure_ne_top incrementLaw _)
      (measure_ne_top incrementLaw _)

end EuclideanDiskStoppedAtomData

/-- Concrete finite-cylinder witnesses for the two primitive positive-mass
claims.  A single fixed word length is used at a given scale, so the exact
product-measure calculation supplies a uniform constant over every site,
exit point, and selected profile. -/
structure EuclideanDiskFiniteCylinderData
    (n : ℕ) (D : EuclideanDiskStoppedAtomData n) where
  exitLength : ℕ
  exitTarget : Site → Site
  exitWord : Site → Prefix exitLength
  exitTarget_mem : ∀ x ∈ sourceSiteBox n, exitTarget x ∈ D.exitSites x
  exitCylinder_subset : ∀ x ∈ sourceSiteBox n,
    sourcePrefixCylinder (exitWord x) ⊆
      firstExitAtEvent (squareDisk (D.radius x) : Set Site)
        (D.start x) (exitTarget x)
  tailLength : ℕ
  tailWord : Site → Site → NatPath (n - 2) → Prefix tailLength
  tailCylinder_subset : ∀ x ∈ sourceSiteBox n, ∀ z ∈ D.exitSites x,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
      sourcePrefixCylinder (tailWord x z q) ⊆ D.profileTail x z q

/-- The two primitive lower estimates whose product is the annular
comparison constant: a lower bound for the allowed first-exit mass and a
uniform lower bound for each fresh profile tail. -/
structure EuclideanDiskStoppedAtomLowerBounds
    (n : ℕ) (D : EuclideanDiskStoppedAtomData n) where
  cExit : ℝ
  cTail : ℝ
  cExit_pos : 0 < cExit
  cTail_pos : 0 < cTail
  exit_lower : ∀ x ∈ sourceSiteBox n,
    cExit ≤ ∑ z ∈ D.exitSites x,
      (firstExitAtWeight (squareDisk (D.radius x) : Set Site)
        (D.start x) z).toReal
  tail_lower : ∀ x ∈ sourceSiteBox n, ∀ z ∈ D.exitSites x,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
      cTail * successfulProfileWeight n appendixProfileDelta q ≤
        incrementLaw.real (D.profileTail x z q)

namespace EuclideanDiskFiniteCylinderData

/-- Exact common mass of the witnessed exit cylinders. -/
noncomputable def exitMass {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (C : EuclideanDiskFiniteCylinderData n D) : ℝ :=
  ((4 : ENNReal)⁻¹ ^ C.exitLength).toReal

/-- The common tail-cylinder mass.  No profile normalization is needed:
every selected auxiliary profile weight is at most one. -/
noncomputable def tailFactor {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (C : EuclideanDiskFiniteCylinderData n D) : ℝ :=
  ((4 : ENNReal)⁻¹ ^ C.tailLength).toReal

/-- Finite prefix witnesses discharge both primitive lower-bound fields. -/
noncomputable def toLowerBounds
    {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (C : EuclideanDiskFiniteCylinderData n D) (hn : 2 ≤ n) :
    EuclideanDiskStoppedAtomLowerBounds n D where
  cExit := C.exitMass
  cTail := C.tailFactor
  cExit_pos := sourcePrefixCylinderMass_pos C.exitLength
  cTail_pos := sourcePrefixCylinderMass_pos C.tailLength
  exit_lower := by
    intro x hx
    let z := C.exitTarget x
    have hz : z ∈ D.exitSites x := C.exitTarget_mem x hx
    have hsingle : C.exitMass ≤
        (firstExitAtWeight (squareDisk (D.radius x) : Set Site)
          (D.start x) z).toReal := by
      rw [exitMass, ← incrementLawReal_sourcePrefixCylinder (C.exitWord x)]
      rw [firstExitAtWeight_eq_measure
        (squareDisk (D.radius x) : Set Site) (D.start x) z
        (D.exit_not_mem x hx z hz)]
      exact measureReal_mono (C.exitCylinder_subset x hx)
        (measure_ne_top incrementLaw _)
    exact hsingle.trans (Finset.single_le_sum
      (fun z hz ↦ ENNReal.toReal_nonneg) hz)
  tail_lower := by
    intro x hx z hz q hq
    have hweight := successfulProfileWeight_le_one hn hq
    have hcylinder : ((4 : ENNReal)⁻¹ ^ C.tailLength).toReal ≤
        incrementLaw.real (D.profileTail x z q) := by
      rw [← incrementLawReal_sourcePrefixCylinder (C.tailWord x z q)]
      exact measureReal_mono (C.tailCylinder_subset x hx z hz q hq)
        (measure_ne_top incrementLaw _)
    calc
      C.tailFactor * successfulProfileWeight n appendixProfileDelta q ≤
          ((4 : ENNReal)⁻¹ ^ C.tailLength).toReal * 1 :=
        mul_le_mul_of_nonneg_left hweight
          (sourcePrefixCylinderMass_pos C.tailLength).le
      _ = ((4 : ENNReal)⁻¹ ^ C.tailLength).toReal := mul_one _
      _ ≤ incrementLaw.real (D.profileTail x z q) := hcylinder

/-- The product of the two witnessed cylinder masses is exactly the
exponential cost of their total word length.  This turns the remaining
annular-mass hypothesis into a purely deterministic length estimate. -/
theorem exitMass_mul_tailFactor_eq_exp
    {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (C : EuclideanDiskFiniteCylinderData n D) :
    C.exitMass * C.tailFactor =
      Real.exp (-Real.log 4 *
        ((C.exitLength + C.tailLength : ℕ) : ℝ)) := by
  rw [exitMass, tailFactor, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]
  norm_num
  rw [← pow_add]
  rw [show (1 / 4 : ℝ) = Real.exp (-Real.log 4) by
    rw [Real.exp_neg, Real.exp_log] <;> norm_num]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end EuclideanDiskFiniteCylinderData

namespace EuclideanDiskStoppedAtomLowerBounds

/-- Positivity of the product annular comparison constant. -/
theorem product_pos {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (L : EuclideanDiskStoppedAtomLowerBounds n D) :
    0 < L.cExit * L.cTail :=
  mul_pos L.cExit_pos L.cTail_pos

/-- The exact strong-Markov mass identity turns the primitive exit and tail
bounds into the annular lower bound required by the first moment. -/
theorem annulus_lower {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (L : EuclideanDiskStoppedAtomLowerBounds n D) (hn : 2 ≤ n)
    (x : Site) (hx : x ∈ sourceSiteBox n)
    (q : NatPath (n - 2)) (hq : q ∈ sourceProfiles appendixProfileDelta n) :
    (L.cExit * L.cTail) * successfulProfileWeight n appendixProfileDelta q ≤
      incrementLaw.real (D.atom x q) := by
  have hweight : 0 ≤ successfulProfileWeight n appendixProfileDelta q :=
    successfulProfileWeight_nonneg appendixProfileDelta hn q
  rw [D.atom_measure_eq x hx q hq]
  calc
    (L.cExit * L.cTail) * successfulProfileWeight n appendixProfileDelta q =
        L.cExit *
          (L.cTail * successfulProfileWeight n appendixProfileDelta q) := by
            ring
    _ ≤ (∑ z ∈ D.exitSites x,
          (firstExitAtWeight (squareDisk (D.radius x) : Set Site)
            (D.start x) z).toReal) *
          (L.cTail * successfulProfileWeight n appendixProfileDelta q) :=
      mul_le_mul_of_nonneg_right (L.exit_lower x hx)
        (mul_nonneg L.cTail_pos.le hweight)
    _ = ∑ z ∈ D.exitSites x,
          (firstExitAtWeight (squareDisk (D.radius x) : Set Site)
            (D.start x) z).toReal *
          (L.cTail * successfulProfileWeight n appendixProfileDelta q) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ D.exitSites x,
          (firstExitAtWeight (squareDisk (D.radius x) : Set Site)
            (D.start x) z).toReal *
              incrementLaw.real (D.profileTail x z q) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (L.tail_lower x hx z hz q hq)
        ENNReal.toReal_nonneg

end EuclideanDiskStoppedAtomLowerBounds

/-! ### Source package after discharging Proposition A.7 -/

/-- The genuinely remaining one-scale source inputs after the finite
Gaussian/profile calculation has been closed.  Compared with
`EuclideanDiskSourceEstimates`, this structure has no `A7`, `A7_nonneg`,
`A7_lower`, `n_large`, `delta_le_one`, or `q_pos` field.  The canonical
`appendixSourceA7` and the positivity of the explicit endpoint factors
discharge all of them. -/
structure EuclideanDiskRemainingEstimates
    (epsilon : ℝ) (n : ℕ)
    (atom : Site → NatPath (n - 2) → Set (ℕ → Direction)) where
  cAnnulus : ℝ
  c : ℝ
  E : ℝ
  cAnnulus_pos : 0 < cAnnulus
  c_nonneg : 0 ≤ c
  atom_measurable : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n, MeasurableSet (atom x q)
  atom_disjoint : ∀ x ∈ sourceSiteBox n,
    Set.PairwiseDisjoint
      (↑(sourceProfiles appendixProfileDelta n) : Set (NatPath (n - 2)))
      (atom x)
  annulus_lower : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    cAnnulus * successfulProfileWeight n appendixProfileDelta q ≤
      incrementLaw.real (atom x q)
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64) cAnnulus
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent appendixProfileDelta n atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n atom y)
      (appendixSeparationLevel n x y) E
  close_absorb :
    sourceCloseCount n * c ≤ Real.exp E *
      (sourceBoxKsq n *
        sourceOnePointScale (appendixSourceA7 n)
          (sourceInitialLower appendixProfileDelta) (1 / 64) cAnnulus)
  paley_budget :
    Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      1 / sourcePaleyCoefficient n c E

/-- The quantitative source estimates for a literal stopped-annulus atom.
The atom's measurability and profile-disjointness are now theorems, not
fields.  Thus the first remaining field is the positive annular comparison
constant, followed by the actual one- and two-point analytic estimates. -/
structure EuclideanDiskStoppedAtomEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n) where
  cAnnulus : ℝ
  c : ℝ
  E : ℝ
  cAnnulus_pos : 0 < cAnnulus
  c_nonneg : 0 ≤ c
  annulus_lower : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    cAnnulus * successfulProfileWeight n appendixProfileDelta q ≤
      incrementLaw.real (D.atom x q)
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    D.atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64) cAnnulus
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom y)
      (appendixSeparationLevel n x y) E
  close_absorb :
    sourceCloseCount n * c ≤ Real.exp E *
      (sourceBoxKsq n *
        sourceOnePointScale (appendixSourceA7 n)
          (sourceInitialLower appendixProfileDelta) (1 / 64) cAnnulus)
  paley_budget :
    Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      1 / sourcePaleyCoefficient n c E

/-- A source-facing package in which the annular lower estimate has been
reduced to its two primitive ingredients. -/
structure EuclideanDiskPrimitiveEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (L : EuclideanDiskStoppedAtomLowerBounds n D) where
  c : ℝ
  E : ℝ
  c_nonneg : 0 ≤ c
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    D.atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64)
        (L.cExit * L.cTail)
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom y)
      (appendixSeparationLevel n x y) E
  close_absorb :
    sourceCloseCount n * c ≤ Real.exp E *
      (sourceBoxKsq n *
        sourceOnePointScale (appendixSourceA7 n)
          (sourceInitialLower appendixProfileDelta) (1 / 64)
          (L.cExit * L.cTail))
  paley_budget :
    Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      1 / sourcePaleyCoefficient n c E

/-- Primitive random-walk estimates with scale-uniform constants, before
the deterministic Paley--Zygmund asymptotic comparison.  Unlike
`EuclideanDiskPrimitiveEstimates`, this package has no `paley_budget`
field: for the Appendix exponent that inequality follows eventually from
`eventually_sourcePaley_budget`.

The remaining `close_absorb` field is deliberately retained.  Its proof
uses the quantitative lower order of the annular comparison constant and
of `appendixSourceA7`, rather than merely polynomial-versus-stretched-
exponential decay. -/
structure EuclideanDiskUniformPrimitiveEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (L : EuclideanDiskStoppedAtomLowerBounds n D) (c E : ℝ) where
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    D.atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64)
        (L.cExit * L.cTail)
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom y)
      (appendixSeparationLevel n x y) E
  close_absorb :
    sourceCloseCount n * c ≤ Real.exp E *
      (sourceBoxKsq n *
        sourceOnePointScale (appendixSourceA7 n)
          (sourceInitialLower appendixProfileDelta) (1 / 64)
          (L.cExit * L.cTail))

/-- Scale-uniform primitive estimates after replacing the artificial
constant close-shell absorption by the genuine one-point asymptotic.  The
deterministic `exp (-2n)` cost cancels the source-box area; the remaining
`C n^b` loss is absorbed by the final larger Appendix exponent. -/
structure EuclideanDiskUniformPrimitiveCoreEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (L : EuclideanDiskStoppedAtomLowerBounds n D) (c E C b : ℝ) where
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    D.atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64)
        (L.cExit * L.cTail)
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom y)
      (appendixSeparationLevel n x y) E
  onePointScale_lower :
    Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b) ≤
      sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64)
        (L.cExit * L.cTail)

/-- The source-facing version of the scale-uniform primitive core.  The
proved quantitative A.7 theorem and the fixed endpoint factors have been
removed from the assumptions: the only lower-order input is now the
genuine annular exit/tail comparison. -/
structure EuclideanDiskUniformPrimitiveAnnulusEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (L : EuclideanDiskStoppedAtomLowerBounds n D)
    (c E cAnnulusCost : ℝ) where
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    D.atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64)
        (L.cExit * L.cTail)
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasSourceExitWordCertificate
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom y)
      (appendixSeparationLevel n x y) E
  annulusProduct_lower :
    Real.exp (-cAnnulusCost * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      L.cExit * L.cTail

/-- Restore the complete one-point lower order from the sole annular
comparison input. -/
theorem EuclideanDiskUniformPrimitiveAnnulusEstimates.toCoreEstimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    {L : EuclideanDiskStoppedAtomLowerBounds n D}
    {c E cAnnulusCost : ℝ}
    (H : EuclideanDiskUniformPrimitiveAnnulusEstimates
      epsilon n D L c E cAnnulusCost)
    (hn : 1 ≤ n)
    (hA7 : Real.exp (-2 * (n : ℝ) -
      appendixSourceA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
        appendixSourceA7 n) :
    EuclideanDiskUniformPrimitiveCoreEstimates epsilon n D L c E
      (sourceOnePointCost (max 0 cAnnulusCost)) (753 / 1250 : ℝ) where
  local_time_witness := H.local_time_witness
  onePoint_upper := H.onePoint_upper
  twoPoint_source := H.twoPoint_source
  onePointScale_lower := by
    apply sourceOnePointScale_quantitative_lower hn _ hA7
    have hpow : 0 ≤ (n : ℝ) ^ (753 / 1250 : ℝ) := by positivity
    apply (Real.exp_le_exp.mpr ?_).trans H.annulusProduct_lower
    nlinarith [le_max_right 0 cAnnulusCost]

/-- A valid scale-uniform core package forces its one-point comparison
constant to be nonnegative.  Indeed the checked Proposition-A.7 lower bound
and the positive exit/tail factors make the successful-site event have
strictly positive mass, while `onePoint_upper` bounds that mass by `c` times
the same strictly positive scale.  Thus `0 ≤ c` is a consequence, not an
independent source assumption. -/
theorem nonneg_comparison_of_uniformPrimitiveCoreEstimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    {L : EuclideanDiskStoppedAtomLowerBounds n D} {c E C b : ℝ}
    (hn64 : 64 ≤ n)
    (H : EuclideanDiskUniformPrimitiveCoreEstimates epsilon n D L c E C b)
    (hA7 : appendixSourceA7 n ≤
      halfNegBinPathSum (sourceProfiles appendixProfileDelta n)) :
    0 ≤ c := by
  let R := sourceBoxRadius n
  let x : Site := (2 * (R : ℤ), 2 * (R : ℤ))
  have hx : x ∈ sourceSiteBox n := by
    have hR : 0 ≤ (sourceBoxRadius n : ℤ) := by omega
    simp [x, R, sourceSiteBox, appendixSiteBox]
    omega
  let q := sourceOnePointScale (appendixSourceA7 n)
    (sourceInitialLower appendixProfileDelta) (1 / 64)
    (L.cExit * L.cTail)
  have hqpos : 0 < q := by
    dsimp [q]
    unfold sourceOnePointScale
    exact mul_pos L.product_pos
      (mul_pos
        (mul_pos (sourceInitialLower_pos appendixProfileDelta) (by norm_num))
        (appendixSourceA7_pos n))
  have hlower : q ≤ incrementLaw.real
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) := by
    dsimp [q]
    exact annular_firstMoment_lower_of_propositionA7 incrementLaw
      appendixProfileDelta (sourceProfiles appendixProfileDelta n) (D.atom x)
      (appendixSourceA7_pos n).le
      (sourceInitialLower_nonneg appendixProfileDelta) (by norm_num)
      L.product_pos.le
      (fun q hq ↦ sourceInitialLower_le hq)
      (fun q hq ↦ source_terminalMass_lower hn64
        (by norm_num [appendixProfileDelta]) q hq)
      hA7 (D.atom_measurable x hx) (D.atom_disjoint x hx)
      (L.annulus_lower (by omega) x hx)
  have hupper : incrementLaw.real
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
        c * q := by
    simpa [q] using H.onePoint_upper x hx
  nlinarith

/-- Add the now-deterministic Paley budget to a uniform primitive package. -/
def EuclideanDiskUniformPrimitiveEstimates.toPrimitiveEstimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    {L : EuclideanDiskStoppedAtomLowerBounds n D} {c E : ℝ}
    (H : EuclideanDiskUniformPrimitiveEstimates epsilon n D L c E)
    (hc : 0 ≤ c)
    (hpaley : Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      1 / sourcePaleyCoefficient n c E) :
    EuclideanDiskPrimitiveEstimates epsilon n D L where
  c := c
  E := E
  c_nonneg := hc
  local_time_witness := H.local_time_witness
  onePoint_upper := H.onePoint_upper
  twoPoint_source := H.twoPoint_source
  close_absorb := H.close_absorb
  paley_budget := hpaley

/-- The exact atom mass calculation discharges the full annular lower field
from the primitive package. -/
def EuclideanDiskPrimitiveEstimates.toStoppedAtomEstimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    {L : EuclideanDiskStoppedAtomLowerBounds n D}
    (H : EuclideanDiskPrimitiveEstimates epsilon n D L) (hn : 2 ≤ n) :
    EuclideanDiskStoppedAtomEstimates epsilon n D where
  cAnnulus := L.cExit * L.cTail
  c := H.c
  E := H.E
  cAnnulus_pos := L.product_pos
  c_nonneg := H.c_nonneg
  annulus_lower := L.annulus_lower hn
  local_time_witness := H.local_time_witness
  onePoint_upper := H.onePoint_upper
  twoPoint_source := H.twoPoint_source
  close_absorb := H.close_absorb
  paley_budget := H.paley_budget

/-- Source-facing analytic package after finite exit/tail cylinders have
discharged both primitive mass lower bounds. -/
abbrev EuclideanDiskFiniteCylinderEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (C : EuclideanDiskFiniteCylinderData n D) (hn : 2 ≤ n) :=
  EuclideanDiskPrimitiveEstimates epsilon n D (C.toLowerBounds hn)

/-- Finite-cylinder estimates with fixed comparison constants and no
separate Paley-budget field. -/
abbrev EuclideanDiskUniformFiniteCylinderEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (C : EuclideanDiskFiniteCylinderData n D) (hn : 2 ≤ n)
    (c E : ℝ) :=
  EuclideanDiskUniformPrimitiveEstimates epsilon n D
    (C.toLowerBounds hn) c E

/-- Finite-cylinder core estimates with both asymptotic budgets internal to
the eventual consumer. -/
abbrev EuclideanDiskUniformFiniteCylinderCoreEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (C : EuclideanDiskFiniteCylinderData n D) (hn : 2 ≤ n)
    (c E Cq b : ℝ) :=
  EuclideanDiskUniformPrimitiveCoreEstimates epsilon n D
    (C.toLowerBounds hn) c E Cq b

/-- Finite-cylinder source package whose only asymptotic lower field is the
annular exit/tail product. -/
abbrev EuclideanDiskUniformFiniteCylinderAnnulusEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (C : EuclideanDiskFiniteCylinderData n D) (hn : 2 ≤ n)
    (c E cAnnulusCost : ℝ) :=
  EuclideanDiskUniformPrimitiveAnnulusEstimates epsilon n D
    (C.toLowerBounds hn) c E cAnnulusCost

/-- Finite-cylinder source data with no probability lower bound left as a
field.  The two-point field is restricted to the checked canonical-right
exit-word route, so the strongest literal source cut cannot fall back to the
legacy potential-boundary denominator interface.  The last field only bounds
the total length of the two explicit cylinder words; their exact Bernoulli
mass is computed above. -/
structure EuclideanDiskUniformFiniteCylinderLengthEstimates
    (epsilon : ℝ) (n : ℕ) (D : EuclideanDiskStoppedAtomData n)
    (C : EuclideanDiskFiniteCylinderData n D) (hn : 2 ≤ n)
    (c E cAnnulusCost : ℝ) where
  local_time_witness : ∀ x ∈ sourceSiteBox n,
    ∀ q ∈ sourceProfiles appendixProfileDelta n,
    D.atom x q ⊆ {ω | diskThreshold epsilon n ≤
      (localTime (simpleRandomWalk ω) (euclideanExitTime (K n) ω) x : ℝ)}
  onePoint_upper : ∀ x ∈ sourceSiteBox n,
    incrementLaw.real
        (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x) ≤
      c * sourceOnePointScale (appendixSourceA7 n)
        (sourceInitialLower appendixProfileDelta) (1 / 64)
        ((C.toLowerBounds hn).cExit * (C.toLowerBounds hn).cTail)
  twoPoint_source : ∀ x ∈ sourceSiteBox n, ∀ y ∈ sourceSiteBox n,
    appendixSeparationLevel n x y ≤ n + 1 →
    HasCanonicalRightSourceExitWordCertificateAtScale n
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom x)
      (euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom y)
      (appendixSeparationLevel n x y) E
  totalLength_cost :
    Real.log 4 * ((C.exitLength + C.tailLength : ℕ) : ℝ) ≤
      cAnnulusCost * (n : ℝ) ^ (753 / 1250 : ℝ)

/-- All literal finite-cylinder data needed at one sufficiently large disk
scale.  Packaging the stopped atom and its two cylinder witnesses together
avoids asking a source theorem to make arbitrary choices at irrelevant
small scales. -/
structure EuclideanDiskFiniteCylinderLengthPackage
    (n : ℕ) (c E cAnnulusCost : ℝ) where
  hn : 2 ≤ n
  data : EuclideanDiskStoppedAtomData n
  cylinder : EuclideanDiskFiniteCylinderData n data
  estimates : Nonempty (EuclideanDiskUniformFiniteCylinderLengthEstimates
    appendixEpsilon n data cylinder hn c E cAnnulusCost)

/-- The one-point scale associated with a packaged finite-cylinder witness. -/
noncomputable def EuclideanDiskFiniteCylinderLengthPackage.onePointScale
    {n : ℕ} {c E cAnnulusCost : ℝ}
    (P : EuclideanDiskFiniteCylinderLengthPackage n c E cAnnulusCost) : ℝ :=
  sourceOnePointScale (appendixSourceA7 n)
    (sourceInitialLower appendixProfileDelta) (1 / 64)
    (P.cylinder.exitMass * P.cylinder.tailFactor)

/-- A total scale function used only to run the eventual Paley--Zygmund
budget.  Its fallback value is irrelevant whenever the packaged source data
exist. -/
noncomputable def selectedFiniteCylinderOnePointScale
    (c E cAnnulusCost : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if h : Nonempty
        (EuclideanDiskFiniteCylinderLengthPackage n c E cAnnulusCost) then
      (Classical.choice h).onePointScale
    else 0

/-- Exact cylinder masses convert the deterministic total-length budget to
the annular product lower bound used by the Appendix consumer. -/
theorem EuclideanDiskUniformFiniteCylinderLengthEstimates.toAnnulusEstimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    {C : EuclideanDiskFiniteCylinderData n D} {hn : 2 ≤ n}
    {c E cAnnulusCost : ℝ}
    (H : EuclideanDiskUniformFiniteCylinderLengthEstimates
      epsilon n D C hn c E cAnnulusCost) :
    EuclideanDiskUniformFiniteCylinderAnnulusEstimates
      epsilon n D C hn c E cAnnulusCost where
  local_time_witness := H.local_time_witness
  onePoint_upper := H.onePoint_upper
  twoPoint_source := fun x hx y hy hxy ↦ Or.inr
    (hasCanonicalRightSourceExitWordCertificate_of_atScale
      (H.twoPoint_source x hx y hy hxy))
  annulusProduct_lower := by
    change Real.exp (-cAnnulusCost * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      C.exitMass * C.tailFactor
    rw [C.exitMass_mul_tailFactor_eq_exp]
    exact Real.exp_le_exp.mpr (by linarith [H.totalLength_cost])

/-- The structural stopped-annulus construction supplies the two set-level
fields of `EuclideanDiskRemainingEstimates`. -/
def EuclideanDiskStoppedAtomEstimates.toRemainingEstimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    (H : EuclideanDiskStoppedAtomEstimates epsilon n D) :
    EuclideanDiskRemainingEstimates epsilon n D.atom where
  cAnnulus := H.cAnnulus
  c := H.c
  E := H.E
  cAnnulus_pos := H.cAnnulus_pos
  c_nonneg := H.c_nonneg
  atom_measurable := D.atom_measurable
  atom_disjoint := D.atom_disjoint
  annulus_lower := H.annulus_lower
  local_time_witness := H.local_time_witness
  onePoint_upper := H.onePoint_upper
  twoPoint_source := H.twoPoint_source
  close_absorb := H.close_absorb
  paley_budget := H.paley_budget

/-- At every sufficiently large scale, the remaining source inputs produce
the original package with the canonical A.7 factor. -/
noncomputable def EuclideanDiskRemainingEstimates.toSourceEstimates
    {epsilon : ℝ} {n : ℕ}
    {atom : Site → NatPath (n - 2) → Set (ℕ → Direction)}
    (H : EuclideanDiskRemainingEstimates epsilon n atom)
    (hn : 64 ≤ n)
    (hA7 : appendixSourceA7 n ≤
      halfNegBinPathSum (sourceProfiles appendixProfileDelta n)) :
    EuclideanDiskSourceEstimates epsilon appendixProfileDelta n atom where
  A7 := appendixSourceA7 n
  cAnnulus := H.cAnnulus
  c := H.c
  E := H.E
  n_large := hn
  delta_le_one := by norm_num [appendixProfileDelta]
  A7_nonneg := (appendixSourceA7_pos n).le
  cAnnulus_nonneg := H.cAnnulus_pos.le
  c_nonneg := H.c_nonneg
  q_pos := by
    unfold sourceOnePointScale
    exact mul_pos H.cAnnulus_pos
      (mul_pos
        (mul_pos (sourceInitialLower_pos appendixProfileDelta) (by norm_num))
        (appendixSourceA7_pos n))
  A7_lower := hA7
  atom_measurable := H.atom_measurable
  atom_disjoint := H.atom_disjoint
  annulus_lower := H.annulus_lower
  local_time_witness := H.local_time_witness
  onePoint_upper := H.onePoint_upper
  twoPoint_source := H.twoPoint_source
  close_absorb := H.close_absorb
  paley_budget := H.paley_budget

/-- Literal one-scale Appendix-A disk success, with all combinatorial and
second-moment bookkeeping discharged. -/
theorem euclideanDiskGood_probability_lower_of_source_estimates
    {epsilon delta : ℝ} {n : ℕ} (hn : 1 ≤ n)
    {atom : Site → NatPath (n - 2) → Set (ℕ → Direction)}
    (H : EuclideanDiskSourceEstimates epsilon delta n atom) :
    ENNReal.ofReal
        (Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ)))) <
      incrementLaw (euclideanDiskGood epsilon n) := by
  let A : Site → Set (ℕ → Direction) :=
    euclideanSuccessfulSiteEvent delta n atom
  let q := sourceOnePointScale H.A7 (sourceInitialLower delta) (1 / 64) H.cAnnulus
  have hA : ∀ x ∈ sourceSiteBox n, MeasurableSet (A x) := by
    intro x hx
    exact measurableSet_euclideanSuccessfulSiteEvent
      (H.atom_measurable x hx)
  have honePoint : ∀ x ∈ sourceSiteBox n,
      q ≤ incrementLaw.real (A x) ∧
        incrementLaw.real (A x) ≤ H.c * q := by
    intro x hx
    constructor
    · dsimp [q, A]
      exact annular_firstMoment_lower_of_propositionA7 incrementLaw delta
        (sourceProfiles delta n) (atom x)
        H.A7_nonneg (sourceInitialLower_nonneg delta) (by norm_num)
        H.cAnnulus_nonneg
        (fun q hq ↦ sourceInitialLower_le hq)
        (fun q hq ↦ source_terminalMass_lower H.n_large H.delta_le_one q hq)
        H.A7_lower
        (H.atom_measurable x hx) (H.atom_disjoint x hx)
        (H.annulus_lower x hx)
    · exact H.onePoint_upper x hx
  have hcardEq : ((sourceSiteBox n).card : ℝ) = sourceBoxKsq n :=
    card_sourceSiteBox n
  have hpaley :
      1 / sourcePaleyCoefficient n H.c H.E ≤
        incrementLaw.real (someSuccessful (sourceSiteBox n) A) := by
    have hresult := appendixA_success_lower_bound incrementLaw
      (sourceSiteBox n) A (appendixSeparationLevel n) (n + 1)
      hA H.q_pos H.c_nonneg (sourceBoxKsq_pos n)
      (by positivity : (0 : ℝ) ≤ 1)
      (by unfold sourceShellConstant; positivity)
      (by unfold sourceCloseCount; positivity)
      (by simpa [hcardEq])
      (by simpa [hcardEq])
      honePoint
      (fun x hx l hl ↦ source_separationShell_card_le_box hn hx hl)
      (fun x hx y hy hxy ↦
        twoPoint_of_sourceExitWordCertificate
          (H.twoPoint_source x hx y hy hxy))
      (fun x hx ↦ close_neighbor_card_le n x)
      (by simpa using H.close_absorb)
    simpa [sourcePaleyCoefficient] using hresult
  have hsubset : someSuccessful (sourceSiteBox n) A ⊆
      euclideanDiskGood epsilon n := by
    simpa [A, euclideanSomeSuccessful] using
      (euclideanSomeSuccessful_subset_diskGood H.local_time_witness)
  have hreal : Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      incrementLaw.real (euclideanDiskGood epsilon n) := by
    exact H.paley_budget.trans_le (hpaley.trans
      (measureReal_mono hsubset
        (measure_ne_top incrementLaw (euclideanDiskGood epsilon n))))
  exact (ENNReal.ofReal_lt_iff_lt_toReal
    (Real.exp_pos _).le
    (measure_ne_top incrementLaw (euclideanDiskGood epsilon n))).2 hreal

/-- One-scale disk success with the close-pair term retained at its true
size.  This avoids the unnecessarily strong legacy requirement that the
entire unresolved shell be absorbed into a scale-independent constant. -/
theorem euclideanDiskGood_probability_lower_of_uniformPrimitiveCore_estimates
    {epsilon : ℝ} {n : ℕ} {D : EuclideanDiskStoppedAtomData n}
    {L : EuclideanDiskStoppedAtomLowerBounds n D} {c E C b : ℝ}
    (hn1 : 1 ≤ n) (hn2 : 2 ≤ n) (hn64 : 64 ≤ n) (hc : 0 ≤ c)
    (H : EuclideanDiskUniformPrimitiveCoreEstimates epsilon n D L c E C b)
    (hA7 : appendixSourceA7 n ≤
      halfNegBinPathSum (sourceProfiles appendixProfileDelta n))
    (hpaley : Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      1 / sourceUnabsorbedPaleyCoefficient n c E
        (sourceOnePointScale (appendixSourceA7 n)
          (sourceInitialLower appendixProfileDelta) (1 / 64)
          (L.cExit * L.cTail))) :
    ENNReal.ofReal
        (Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ)))) <
      incrementLaw (euclideanDiskGood epsilon n) := by
  let A : Site → Set (ℕ → Direction) :=
    euclideanSuccessfulSiteEvent appendixProfileDelta n D.atom
  let q := sourceOnePointScale (appendixSourceA7 n)
    (sourceInitialLower appendixProfileDelta) (1 / 64)
    (L.cExit * L.cTail)
  have hqpos : 0 < q := by
    dsimp [q]
    unfold sourceOnePointScale
    exact mul_pos L.product_pos
      (mul_pos
        (mul_pos (sourceInitialLower_pos appendixProfileDelta) (by norm_num))
        (appendixSourceA7_pos n))
  have hA : ∀ x ∈ sourceSiteBox n, MeasurableSet (A x) := by
    intro x hx
    exact measurableSet_euclideanSuccessfulSiteEvent
      (D.atom_measurable x hx)
  have honePoint : ∀ x ∈ sourceSiteBox n,
      q ≤ incrementLaw.real (A x) ∧
        incrementLaw.real (A x) ≤ c * q := by
    intro x hx
    constructor
    · dsimp [q, A]
      exact annular_firstMoment_lower_of_propositionA7 incrementLaw
        appendixProfileDelta (sourceProfiles appendixProfileDelta n) (D.atom x)
        (appendixSourceA7_pos n).le
        (sourceInitialLower_nonneg appendixProfileDelta) (by norm_num)
        L.product_pos.le
        (fun q hq ↦ sourceInitialLower_le hq)
        (fun q hq ↦ source_terminalMass_lower hn64
          (by norm_num [appendixProfileDelta]) q hq)
        hA7 (D.atom_measurable x hx) (D.atom_disjoint x hx)
        (L.annulus_lower hn2 x hx)
    · exact H.onePoint_upper x hx
  have hcardEq : ((sourceSiteBox n).card : ℝ) = sourceBoxKsq n :=
    card_sourceSiteBox n
  have hpaleyLower :
      1 / sourceUnabsorbedPaleyCoefficient n c E q ≤
        incrementLaw.real (someSuccessful (sourceSiteBox n) A) := by
    have hresult := appendixA_success_lower_bound_unabsorbed incrementLaw
      (sourceSiteBox n) A (appendixSeparationLevel n) (n + 1)
      hA hqpos hc (sourceBoxKsq_pos n)
      (by positivity : (0 : ℝ) ≤ 1)
      (by unfold sourceShellConstant; positivity)
      (by unfold sourceCloseCount; positivity)
      (by simpa [hcardEq])
      (by simpa [hcardEq])
      honePoint
      (fun x hx l hl ↦ source_separationShell_card_le_box hn1 hx hl)
      (fun x hx y hy hxy ↦
        twoPoint_of_sourceExitWordCertificate
          (H.twoPoint_source x hx y hy hxy))
      (fun x hx ↦ close_neighbor_card_le n x)
    simpa [sourcePaleyCoefficient, sourceUnabsorbedPaleyCoefficient] using hresult
  have hsubset : someSuccessful (sourceSiteBox n) A ⊆
      euclideanDiskGood epsilon n := by
    simpa [A, euclideanSomeSuccessful] using
      (euclideanSomeSuccessful_subset_diskGood H.local_time_witness)
  have hreal : Real.exp (-((n : ℝ) ^ (3 / 5 + epsilon / 3 : ℝ))) <
      incrementLaw.real (euclideanDiskGood epsilon n) := by
    exact hpaley.trans_le (hpaleyLower.trans
      (measureReal_mono hsubset
        (measure_ne_top incrementLaw (euclideanDiskGood epsilon n))))
  exact (ENNReal.ofReal_lt_iff_lt_toReal
    (Real.exp_pos _).le
    (measure_ne_top incrementLaw (euclideanDiskGood epsilon n))).2 hreal

/-- Eventual one-scale source estimates instantiate the published
`EuclideanAppendixDiskEstimate` directly. -/
theorem euclideanAppendixDiskEstimate_of_eventually_source_estimates
    {delta : ℝ}
    (atom : (n : ℕ) → Site → NatPath (n - 2) → Set (ℕ → Direction))
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskSourceEstimates appendixEpsilon delta n (atom n))) :
    EuclideanAppendixDiskEstimate := by
  filter_upwards [hsource, eventually_ge_atTop (1 : ℕ)] with n hnsource hn
  obtain ⟨H⟩ := hnsource
  exact euclideanDiskGood_probability_lower_of_source_estimates hn H

/-- Proposition A.7, its finite low-scale prefix, and the deterministic
large-scale fields are no longer source premises.  Eventual remaining
annular/exit-word estimates therefore give the Euclidean Appendix theorem
directly. -/
theorem euclideanAppendixDiskEstimate_of_eventually_remaining_estimates
    (atom : (n : ℕ) → Site → NatPath (n - 2) → Set (ℕ → Direction))
    (hremaining : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskRemainingEstimates appendixEpsilon n (atom n))) :
    EuclideanAppendixDiskEstimate := by
  apply euclideanAppendixDiskEstimate_of_eventually_source_estimates
    (delta := appendixProfileDelta) atom
  filter_upwards [hremaining, eventually_appendixSourceA7_lower,
    eventually_ge_atTop (64 : ℕ)] with n hnrem hA7 hn
  obtain ⟨H⟩ := hnrem
  exact ⟨H.toSourceEstimates hn hA7⟩

/-- Eventual analytic estimates for the literal stopped-annulus atoms imply
the Euclidean Appendix-A disk estimate.  No A.7 lower bound and no
measurability/disjointness premise remains in this source-facing theorem. -/
theorem euclideanAppendixDiskEstimate_of_eventually_stoppedAtom_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskStoppedAtomEstimates appendixEpsilon n (D n))) :
    EuclideanAppendixDiskEstimate := by
  apply euclideanAppendixDiskEstimate_of_eventually_remaining_estimates
    (fun n ↦ (D n).atom)
  filter_upwards [hsource] with n hn
  obtain ⟨H⟩ := hn
  exact ⟨H.toRemainingEstimates⟩

/-- The source disk estimate from primitive first-exit and fresh-tail lower
bounds.  The exact strong-Markov identity, annular first-moment assembly,
and Proposition A.7 factor are all internal to this implication. -/
theorem euclideanAppendixDiskEstimate_of_eventually_primitive_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (L : (n : ℕ) → EuclideanDiskStoppedAtomLowerBounds n (D n))
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (EuclideanDiskPrimitiveEstimates appendixEpsilon n (D n) (L n))) :
    EuclideanAppendixDiskEstimate := by
  apply euclideanAppendixDiskEstimate_of_eventually_stoppedAtom_estimates D
  filter_upwards [hsource, eventually_ge_atTop (2 : ℕ)] with n hnsource hn
  obtain ⟨H⟩ := hnsource
  exact ⟨H.toStoppedAtomEstimates hn⟩

/-- Uniform primitive comparison constants make the final
Paley--Zygmund inequality automatic.  Thus a source proof using fixed
one- and two-point constants need only establish the local-time witness,
the actual one-point and two-point estimates, and close-pair absorption. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformPrimitive_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (L : (n : ℕ) → EuclideanDiskStoppedAtomLowerBounds n (D n))
    (c E : ℝ) (hc : 0 ≤ c)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskUniformPrimitiveEstimates
        appendixEpsilon n (D n) (L n) c E)) :
    EuclideanAppendixDiskEstimate := by
  apply euclideanAppendixDiskEstimate_of_eventually_primitive_estimates D L
  filter_upwards [hsource, eventually_sourcePaley_budget c E] with n hnsource hpaley
  obtain ⟨H⟩ := hnsource
  exact ⟨H.toPrimitiveEstimates hc hpaley⟩

/-- Scale-uniform primitive core estimates imply the Appendix theorem with
the close-shell geometry and both Paley--Zygmund budgets discharged
internally. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformPrimitiveCore_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (L : (n : ℕ) → EuclideanDiskStoppedAtomLowerBounds n (D n))
    (c E C b : ℝ)
    (hb : b < 3 / 5 + appendixEpsilon / 3)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskUniformPrimitiveCoreEstimates
        appendixEpsilon n (D n) (L n) c E C b)) :
    EuclideanAppendixDiskEstimate := by
  have hc : 0 ≤ c := by
    have hcn : ∀ᶠ n : ℕ in atTop, 0 ≤ c := by
      filter_upwards [hsource, eventually_appendixSourceA7_lower,
        eventually_ge_atTop (64 : ℕ)] with n hnsource hA7 hn64
      obtain ⟨H⟩ := hnsource
      exact nonneg_comparison_of_uniformPrimitiveCoreEstimates hn64 H hA7
    rcases hcn.exists with ⟨n, hn⟩
    exact hn
  let q : ℕ → ℝ := fun n ↦
    sourceOnePointScale (appendixSourceA7 n)
      (sourceInitialLower appendixProfileDelta) (1 / 64)
      ((L n).cExit * (L n).cTail)
  have hq : ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ) - C * (n : ℝ) ^ b) ≤ q n := by
    filter_upwards [hsource] with n hnsource
    obtain ⟨H⟩ := hnsource
    exact H.onePointScale_lower
  have hpaley := eventually_sourceUnabsorbedPaley_budget_of_onePoint_lower
    q c E C b hc hb hq
  filter_upwards [hsource, eventually_appendixSourceA7_lower, hpaley,
    eventually_ge_atTop (64 : ℕ)] with n hnsource hA7 hpaleyN hn64
  obtain ⟨H⟩ := hnsource
  exact euclideanDiskGood_probability_lower_of_uniformPrimitiveCore_estimates
    (by omega) (by omega) hn64 hc H hA7 (by simpa [q] using hpaleyN)

/-- The source-facing primitive consumer.  The quantitative A.7 lower
bound and fixed endpoint factors are internal; only the annular exit/tail
comparison retains an asymptotic lower-bound premise. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformPrimitiveAnnulus_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (L : (n : ℕ) → EuclideanDiskStoppedAtomLowerBounds n (D n))
    (c E cAnnulusCost : ℝ)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskUniformPrimitiveAnnulusEstimates
        appendixEpsilon n (D n) (L n) c E cAnnulusCost)) :
    EuclideanAppendixDiskEstimate := by
  apply
    euclideanAppendixDiskEstimate_of_eventually_uniformPrimitiveCore_estimates
      D L c E (sourceOnePointCost (max 0 cAnnulusCost)) (753 / 1250 : ℝ)
        (by norm_num [appendixEpsilon])
  filter_upwards [hsource, eventually_appendixSourceA7_quantitative_lower,
    eventually_ge_atTop (1 : ℕ)] with n hnsource hA7 hn
  obtain ⟨H⟩ := hnsource
  exact ⟨H.toCoreEstimates hn hA7⟩

/-- Strongest finite-cylinder source consumer.  The allowed-exit mass,
fresh-tail mass, stopped-atom measurability/disjointness, annular first
moment, and Proposition A.7 lower bound are all proved internally.  The
remaining package consists only of the local-time implication, matching
one-point upper bound, two-point exit-word estimate, and asymptotic
second-moment budgets. -/
theorem euclideanAppendixDiskEstimate_of_eventually_finiteCylinder_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (C : (n : ℕ) → EuclideanDiskFiniteCylinderData n (D n))
    (hsource : ∀ᶠ n : ℕ in atTop,
      ∃ hn : 2 ≤ n,
        Nonempty (EuclideanDiskFiniteCylinderEstimates
          appendixEpsilon n (D n) (C n) hn)) :
    EuclideanAppendixDiskEstimate := by
  apply euclideanAppendixDiskEstimate_of_eventually_stoppedAtom_estimates D
  filter_upwards [hsource] with n hnsource
  obtain ⟨hn, H⟩ := hnsource
  obtain ⟨H⟩ := H
  exact ⟨H.toStoppedAtomEstimates hn⟩

/-- Strongest scale-uniform finite-cylinder consumer.  In addition to the
two primitive mass bounds, this version also discharges the final
Paley--Zygmund asymptotic inequality internally. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformFiniteCylinder_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (C : (n : ℕ) → EuclideanDiskFiniteCylinderData n (D n))
    (c E : ℝ) (hc : 0 ≤ c)
    (hsource : ∀ᶠ n : ℕ in atTop,
      ∃ hn : 2 ≤ n,
        Nonempty (EuclideanDiskUniformFiniteCylinderEstimates
          appendixEpsilon n (D n) (C n) hn c E)) :
    EuclideanAppendixDiskEstimate := by
  apply euclideanAppendixDiskEstimate_of_eventually_stoppedAtom_estimates D
  filter_upwards [hsource, eventually_sourcePaley_budget c E] with
      n hnsource hpaley
  obtain ⟨hn, H⟩ := hnsource
  obtain ⟨H⟩ := H
  exact ⟨(H.toPrimitiveEstimates hc hpaley).toStoppedAtomEstimates hn⟩

/-- Strongest current finite-cylinder consumer.  The allowed-exit and
fresh-tail masses, stopped-atom set theory, annular first moment,
Proposition A.7, close-pair geometry, and Paley asymptotics are all proved
inside the implication.  The remaining fields are the pathwise local-time
witness, the matching one-point upper estimate, the two-point exit-word
estimate, and the genuine `exp (-2n-C n^b)` lower order of the explicit
one-point scale. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformFiniteCylinderCore_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (C : (n : ℕ) → EuclideanDiskFiniteCylinderData n (D n))
    (c E Cq b : ℝ)
    (hb : b < 3 / 5 + appendixEpsilon / 3)
    (hsource : ∀ᶠ n : ℕ in atTop,
      ∃ hn : 2 ≤ n,
        Nonempty (EuclideanDiskUniformFiniteCylinderCoreEstimates
          appendixEpsilon n (D n) (C n) hn c E Cq b)) :
    EuclideanAppendixDiskEstimate := by
  have hc : 0 ≤ c := by
    have hcn : ∀ᶠ n : ℕ in atTop, 0 ≤ c := by
      filter_upwards [hsource, eventually_appendixSourceA7_lower,
        eventually_ge_atTop (64 : ℕ)] with n hnsource hA7 hn64
      obtain ⟨hn, H⟩ := hnsource
      obtain ⟨H⟩ := H
      exact nonneg_comparison_of_uniformPrimitiveCoreEstimates hn64 H hA7
    rcases hcn.exists with ⟨n, hn⟩
    exact hn
  let q : ℕ → ℝ := fun n ↦
    sourceOnePointScale (appendixSourceA7 n)
      (sourceInitialLower appendixProfileDelta) (1 / 64)
      ((C n).exitMass * (C n).tailFactor)
  have hq : ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ) - Cq * (n : ℝ) ^ b) ≤ q n := by
    filter_upwards [hsource, eventually_ge_atTop (2 : ℕ)] with n hnsource hn2
    obtain ⟨hn, H⟩ := hnsource
    obtain ⟨H⟩ := H
    simpa only [q, EuclideanDiskFiniteCylinderData.toLowerBounds] using
      H.onePointScale_lower
  have hpaley := eventually_sourceUnabsorbedPaley_budget_of_onePoint_lower
    q c E Cq b hc hb hq
  filter_upwards [hsource, eventually_appendixSourceA7_lower, hpaley,
    eventually_ge_atTop (64 : ℕ)] with n hnsource hA7 hpaleyN hn64
  obtain ⟨hn, H⟩ := hnsource
  obtain ⟨H⟩ := H
  let L := (C n).toLowerBounds hn
  exact euclideanDiskGood_probability_lower_of_uniformPrimitiveCore_estimates
    (by omega) hn hn64 hc H hA7
      (by
        simpa only [q, L, EuclideanDiskFiniteCylinderData.toLowerBounds] using
          hpaleyN)

/-- Strongest finite-cylinder source consumer.  Its lower-order field is
only the genuine annular product `exitMass * tailFactor`; the complete
one-point scale and the second-moment budget are reconstructed internally. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformFiniteCylinderAnnulus_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (C : (n : ℕ) → EuclideanDiskFiniteCylinderData n (D n))
    (c E cAnnulusCost : ℝ)
    (hsource : ∀ᶠ n : ℕ in atTop,
      ∃ hn : 2 ≤ n,
        Nonempty (EuclideanDiskUniformFiniteCylinderAnnulusEstimates
          appendixEpsilon n (D n) (C n) hn c E cAnnulusCost)) :
    EuclideanAppendixDiskEstimate := by
  apply
    euclideanAppendixDiskEstimate_of_eventually_uniformFiniteCylinderCore_estimates
      D C c E (sourceOnePointCost (max 0 cAnnulusCost)) (753 / 1250 : ℝ)
        (by norm_num [appendixEpsilon])
  filter_upwards [hsource, eventually_appendixSourceA7_quantitative_lower,
    eventually_ge_atTop (2 : ℕ)] with n hnsource hA7 hn2
  obtain ⟨hn, H⟩ := hnsource
  obtain ⟨H⟩ := H
  exact ⟨hn, ⟨H.toCoreEstimates (by omega) hA7⟩⟩

/-- Strongest finite-cylinder source consumer: the annular probability
lower bound is reconstructed from the exact mass of the two displayed
cylinders.  The source now supplies only their deterministic total-length
budget, together with the local-time and one-point fields and the
canonical-right exit-word certificate. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_uniformFiniteCylinderLength_estimates
    (D : (n : ℕ) → EuclideanDiskStoppedAtomData n)
    (C : (n : ℕ) → EuclideanDiskFiniteCylinderData n (D n))
    (c E cAnnulusCost : ℝ)
    (hsource : ∀ᶠ n : ℕ in atTop,
      ∃ hn : 2 ≤ n,
        Nonempty (EuclideanDiskUniformFiniteCylinderLengthEstimates
          appendixEpsilon n (D n) (C n) hn c E cAnnulusCost)) :
    EuclideanAppendixDiskEstimate := by
  apply
    euclideanAppendixDiskEstimate_of_eventually_uniformFiniteCylinderAnnulus_estimates
      D C c E cAnnulusCost
  filter_upwards [hsource] with n hnsource
  obtain ⟨hn, H⟩ := hnsource
  obtain ⟨H⟩ := H
  exact ⟨hn, ⟨H.toAnnulusEstimates⟩⟩

/-- Source-faithful version of the strongest finite-cylinder consumer.

Only sufficiently large scales need carry a stopped atom and cylinder
witness.  This theorem selects those witnesses locally inside the eventual
filter, so callers no longer provide meaningless total functions at the
finitely many discarded scales. -/
theorem
    euclideanAppendixDiskEstimate_of_eventually_finiteCylinderLengthPackages
    (c E cAnnulusCost : ℝ)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskFiniteCylinderLengthPackage
        n c E cAnnulusCost)) :
    EuclideanAppendixDiskEstimate := by
  have hcEvent : ∀ᶠ n : ℕ in atTop, 0 ≤ c := by
    filter_upwards [hsource, eventually_appendixSourceA7_quantitative_lower,
      eventually_appendixSourceA7_lower,
      eventually_ge_atTop (64 : ℕ)] with n hnsource hquant hA7 hn64
    let P := Classical.choice hnsource
    obtain ⟨H⟩ := P.estimates
    let L := P.cylinder.toLowerBounds P.hn
    have Hcore : EuclideanDiskUniformPrimitiveCoreEstimates
        appendixEpsilon n P.data L c E
          (sourceOnePointCost (max 0 cAnnulusCost))
          (753 / 1250 : ℝ) :=
      H.toAnnulusEstimates.toCoreEstimates (by omega) hquant
    exact nonneg_comparison_of_uniformPrimitiveCoreEstimates hn64 Hcore hA7
  have hc : 0 ≤ c := (hcEvent.exists).choose_spec
  let q : ℕ → ℝ := selectedFiniteCylinderOnePointScale c E cAnnulusCost
  have hq : ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ) -
          sourceOnePointCost (max 0 cAnnulusCost) *
            (n : ℝ) ^ (753 / 1250 : ℝ)) ≤ q n := by
    filter_upwards [hsource, eventually_appendixSourceA7_quantitative_lower,
      eventually_ge_atTop (1 : ℕ)] with n hnsource hquant hn
    let P := Classical.choice hnsource
    obtain ⟨H⟩ := P.estimates
    let L := P.cylinder.toLowerBounds P.hn
    have Hcore : EuclideanDiskUniformPrimitiveCoreEstimates
        appendixEpsilon n P.data L c E
          (sourceOnePointCost (max 0 cAnnulusCost))
          (753 / 1250 : ℝ) :=
      H.toAnnulusEstimates.toCoreEstimates hn hquant
    simpa only [q, selectedFiniteCylinderOnePointScale, hnsource,
      ↓reduceDIte, EuclideanDiskFiniteCylinderLengthPackage.onePointScale,
      P, L, EuclideanDiskFiniteCylinderData.toLowerBounds] using
        Hcore.onePointScale_lower
  have hpaley := eventually_sourceUnabsorbedPaley_budget_of_onePoint_lower
    q c E (sourceOnePointCost (max 0 cAnnulusCost))
      (753 / 1250 : ℝ) hc (by norm_num [appendixEpsilon]) hq
  filter_upwards [hsource, eventually_appendixSourceA7_quantitative_lower,
    eventually_appendixSourceA7_lower, hpaley,
    eventually_ge_atTop (64 : ℕ)] with
      n hnsource hquant hA7 hpaleyN hn64
  let P := Classical.choice hnsource
  obtain ⟨H⟩ := P.estimates
  let L := P.cylinder.toLowerBounds P.hn
  have Hcore : EuclideanDiskUniformPrimitiveCoreEstimates
      appendixEpsilon n P.data L c E
        (sourceOnePointCost (max 0 cAnnulusCost))
        (753 / 1250 : ℝ) :=
    H.toAnnulusEstimates.toCoreEstimates (by omega) hquant
  have hpaleyP : Real.exp (-((n : ℝ) ^
        (3 / 5 + appendixEpsilon / 3 : ℝ))) <
      1 / sourceUnabsorbedPaleyCoefficient n c E P.onePointScale := by
    simpa only [q, selectedFiniteCylinderOnePointScale, hnsource,
      ↓reduceDIte, P] using hpaleyN
  exact euclideanDiskGood_probability_lower_of_uniformPrimitiveCore_estimates
    (by omega) P.hn hn64 hc Hcore hA7
      (by
        simpa only [EuclideanDiskFiniteCylinderLengthPackage.onePointScale,
          L, EuclideanDiskFiniteCylinderData.toLowerBounds] using hpaleyP)

end Erdos1166.HLOZAppendixADiskSuccess
