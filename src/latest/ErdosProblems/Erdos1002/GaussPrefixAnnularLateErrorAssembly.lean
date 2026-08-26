import ErdosProblems.Erdos1002.GaussPrefixAnnularLateFutureBlock
import ErdosProblems.Erdos1002.GaussPrefixLateAggregateCancellation
import ErdosProblems.Erdos1002.PrefixFreezingAggregate
import ErdosProblems.Erdos1002.GaussFactorialTupleReplacement
import ErdosProblems.Erdos1002.GaussPrefixAnnularBadEventMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Error assembly for the upper retained annular late case

The late argument has four logically separate approximation stages:

1. deletion of the global denominator-bad event;
2. exact-to-digit replacement of future value windows;
3. freezing of the prefix phase and value coordinates;
4. freezing of the Lebesgue-to-Gauss density.

The estimates for those stages live in different modules.  This file keeps
their absolute values inside the complete finite tuple sum and proves that
their sum tends to zero.  It then proves, for every fixed `rho > 0`, that the
complete upper-retained covariance error tends to zero: the number of
retained tagged tuples is polynomial in the annular depth horizon, while the
explicit Gauss mixing rate decays geometrically in the retained midpoint gap.

The final theorem leaves only the factorized prefix-mean times future-mean
sum.  No oscillatory estimate for that remaining term is assumed here.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLateErrorAssemblyPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Deterministic four-stage telescoping -/

/-- Pointwise four-stage telescoping, with every norm taken before any
finite summation. -/
theorem norm_sub_le_four_stage
    (exact good digit frozenPrefix frozenDensity : ℂ) :
    ‖exact - frozenDensity‖ ≤
      ‖exact - good‖ + ‖good - digit‖ +
        ‖digit - frozenPrefix‖ + ‖frozenPrefix - frozenDensity‖ := by
  have hdecomp :
      exact - frozenDensity =
        (exact - good) + (good - digit) +
          (digit - frozenPrefix) + (frozenPrefix - frozenDensity) := by
    ring
  rw [hdecomp]
  calc
    ‖(exact - good) + (good - digit) +
        (digit - frozenPrefix) + (frozenPrefix - frozenDensity)‖ ≤
      ‖(exact - good) + (good - digit) + (digit - frozenPrefix)‖ +
        ‖frozenPrefix - frozenDensity‖ := norm_add_le _ _
    _ ≤
      (‖(exact - good) + (good - digit)‖ +
          ‖digit - frozenPrefix‖) +
        ‖frozenPrefix - frozenDensity‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤
      (‖exact - good‖ + ‖good - digit‖ +
          ‖digit - frozenPrefix‖) +
        ‖frozenPrefix - frozenDensity‖ := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

/-- Aggregate form of the four-stage telescoping inequality.  This is the
quantifier order required in the paper: the norm of each tuple error is
formed before summing over both indices. -/
theorem sum_nested_norm_sub_le_four_stage
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : Finset α) (futures : α → Finset β)
    (exact good digit frozenPrefix frozenDensity : α → β → ℂ) :
    (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖exact p u - frozenDensity p u‖) ≤
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖exact p u - good p u‖) +
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖good p u - digit p u‖) +
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖digit p u - frozenPrefix p u‖) +
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖frozenPrefix p u - frozenDensity p u‖) := by
  calc
    (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖exact p u - frozenDensity p u‖) ≤
      ∑ p ∈ prefixes, ∑ u ∈ futures p,
        (‖exact p u - good p u‖ + ‖good p u - digit p u‖ +
          ‖digit p u - frozenPrefix p u‖ +
          ‖frozenPrefix p u - frozenDensity p u‖) := by
      apply Finset.sum_le_sum
      intro p _hp
      apply Finset.sum_le_sum
      intro u _hu
      exact norm_sub_le_four_stage
        (exact p u) (good p u) (digit p u)
        (frozenPrefix p u) (frozenDensity p u)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

/-- If the four auditable aggregate errors tend to zero separately, then
the complete exact-to-frozen aggregate error tends to zero. -/
theorem tendsto_sum_nested_norm_exact_sub_frozen_zero_of_four_stages
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (exact good digit frozenPrefix frozenDensity :
      ℕ → α → β → ℂ)
    (hbad : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖exact N p u - good N p u‖)
      atTop (nhds 0))
    (hreplacement : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖good N p u - digit N p u‖)
      atTop (nhds 0))
    (hfreezing : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖digit N p u - frozenPrefix N p u‖)
      atTop (nhds 0))
    (hdensity : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖frozenPrefix N p u - frozenDensity N p u‖)
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖exact N p u - frozenDensity N p u‖)
      atTop (nhds 0) := by
  let upper : ℕ → ℝ := fun N ↦
    (∑ p ∈ prefixes N, ∑ u ∈ futures N p,
      ‖exact N p u - good N p u‖) +
    (∑ p ∈ prefixes N, ∑ u ∈ futures N p,
      ‖good N p u - digit N p u‖) +
    (∑ p ∈ prefixes N, ∑ u ∈ futures N p,
      ‖digit N p u - frozenPrefix N p u‖) +
    (∑ p ∈ prefixes N, ∑ u ∈ futures N p,
      ‖frozenPrefix N p u - frozenDensity N p u‖)
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa only [upper, zero_add] using!
      ((hbad.add hreplacement).add hfreezing).add hdensity
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦
        Finset.sum_nonneg fun _u _hu ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦
      sum_nested_norm_sub_le_four_stage
        (prefixes N) (futures N)
        (exact N) (good N) (digit N)
        (frozenPrefix N) (frozenDensity N)
  · exact hupper

/-- A complex nested sum tends to zero whenever the sum of the norms of
its summands tends to zero. -/
theorem tendsto_nested_sum_zero_of_sum_norm
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (z : ℕ → α → β → ℂ)
    (hnorm : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p, ‖z N p u‖)
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦ by
      calc
        ‖∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u‖ ≤
            ∑ p ∈ prefixes N,
              ‖∑ u ∈ futures N p, z N p u‖ :=
          norm_sum_le _ _
        _ ≤ ∑ p ∈ prefixes N, ∑ u ∈ futures N p, ‖z N p u‖ := by
          apply Finset.sum_le_sum
          intro p _hp
          exact norm_sum_le _ _
  · exact hnorm

/-! ## The prefix-freezing envelope as an aggregate-ready limit -/

/-- The exact event decomposition from `PrefixFreezingAggregate` turns
limits for the phase-window mass and the finitely many endpoint-strip
masses into a limit for the integrated freezing envelope. -/
theorem tendsto_integral_oscillatoryPrefixFreezingEnvelope_zero
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (a b : ℕ → Fin r → ℝ)
    (coordinate : ℕ → Ω → Fin r → ℝ)
    (K phaseRadius eta : ℕ → ℝ)
    (hcoordinate : ∀ N i, Measurable fun ω ↦ coordinate N ω i)
    (hphase : Tendsto
      (fun N ↦
        (2 * Real.pi * |K N| * phaseRadius N) *
          mu.real
            (closedWindowTupleEvent
              (fun i ↦ a N i - eta N)
              (fun i ↦ b N i + eta N)
              (coordinate N)))
      atTop (nhds 0))
    (hboundary : ∀ j : Fin r, Tendsto
      (fun N ↦
        mu.real
          (closedBoundaryWindowTupleEvent
            (a N) (b N) (coordinate N) (eta N) j))
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦
        ∫ ω, oscillatoryPrefixFreezingEnvelope
          (a N) (b N) (coordinate N ω)
          (K N) (phaseRadius N) (eta N) ∂mu)
      atTop (nhds 0) := by
  have hboundarySum :
      Tendsto
        (fun N ↦ ∑ j : Fin r,
          mu.real
            (closedBoundaryWindowTupleEvent
              (a N) (b N) (coordinate N) (eta N) j))
        atTop (nhds 0) := by
    simpa using! tendsto_finset_sum Finset.univ
      (fun j _hj ↦ hboundary j)
  have htotal :
      Tendsto
        (fun N ↦
          (2 * Real.pi * |K N| * phaseRadius N) *
              mu.real
                (closedWindowTupleEvent
                  (fun i ↦ a N i - eta N)
                  (fun i ↦ b N i + eta N)
                  (coordinate N)) +
            ∑ j : Fin r,
              mu.real
                (closedBoundaryWindowTupleEvent
                  (a N) (b N) (coordinate N) (eta N) j))
        atTop (nhds 0) := by
    simpa only [zero_add] using! hphase.add hboundarySum
  exact htotal.congr' (Eventually.of_forall fun N ↦ by
    symm
    exact integral_oscillatoryPrefixFreezingEnvelope_eq_eventMasses
      mu (a N) (b N) (coordinate N)
      (K N) (phaseRadius N) (eta N) (hcoordinate N))

/-! ## Ready-made bad-event and exact-to-digit limits -/

/-- Direct paper-facing alias of the denominator-bad moment deletion used
for the first late approximation stage. -/
theorem tendsto_annularLate_denominatorBadApproximationMoment_zero
    (Ds Ls : ℕ → ℕ) (r Cdepth : ℕ)
    {lower upper Delta : ℝ}
    (hr : 0 < r) (hlower : 0 < lower) (hupper : lower < upper)
    (hDsLinear :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ᶠ N : ℕ in atTop,
          (Ds N : ℝ) ≤ D * Real.log (N : ℝ))
    (hCdepth : 0 < Cdepth) (hDelta : 0 < Delta)
    (hLs : Tendsto Ls atTop atTop) :
    Tendsto
      (fun N ↦ ∫ x in
          gaussDenominatorLinearBadEvent Cdepth (Ls N) Delta,
        (gaussApproximationWindowCount
          (Real.log (N : ℝ)) (Ds N) lower upper x : ℝ) ^ r
          ∂uniform01Measure)
      atTop (nhds 0) := by
  exact
    tendsto_gaussApproximationWindowCount_pow_on_denominatorBadEvent
      Ds Ls r Cdepth hr hlower hupper hDsLinear
      hCdepth hDelta hLs

/-- Direct paper-facing alias of the aggregate exact-to-digit replacement
limit.  It can be applied to any fixed-order separated future family. -/
theorem tendsto_annularLate_futureReplacement_zero
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {lower upper R : ℝ} (gap : ℕ)
    (hgap0 : 0 < gap)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hlower : 0 < lower) (hupper : lower < upper)
    (hgap : ∀ L, ∀ t ∈ tuples L, ∀ i j, i < j →
      (t i).1 + gap ≤ (t j).1)
    (hrate : 0 ≤ rate gap) (hrateR : rate gap ≤ R) :
    Tendsto
      (fun L : ℕ ↦
        ∑ t ∈ tuples L,
          gaussMeasure.real
            (gaussApproximationTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1) ∆
              gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)))
      atTop (nhds 0) := by
  exact tendsto_sum_gaussMeasure_real_symmDiff_tupleFamily_zero
    hpsi hr gap hgap0 tuples hlower hupper hgap hrate hrateR

/-! ## Polynomial cardinality of the actual upper retained family -/

/-- The complete tagged upper-retained family has at most one additional
ambient power beyond the tuple dimension.  The additional power absorbs
the fixed finite number of chronological occurrence orders. -/
theorem
    eventually_nestedPairCount_annularUpperRetained_le_ambient_pow_succ
    {rho : ℝ} {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      nestedPairCount
          (Finset.univ :
            Finset (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k))
          (fun e ↦ annularCanonicalLaterUpperMidpointTupleFamily
            rho N k hr e (mode e) (hmode e)) ≤
        annularDepthAmbientSize N ^ (MixedOccurrenceCount k + 1) := by
  let orderCount : ℕ :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
  filter_upwards
    [eventually_gt_atTop 1,
      tendsto_annularDepthAmbientSize_atTop.eventually_ge_atTop orderCount]
      with N hN horder
  have hfamily (e :
      Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
      (annularCanonicalLaterUpperMidpointTupleFamily
        rho N k hr e (mode e) (hmode e)).card ≤
          annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
    apply card_boundedNatTupleFamily_le
    intro t ht j
    have hupper :=
      (mem_laterUpperMidpointNatTupleFamily_iff.mp ht).1
    have hlate := (mem_lateFirstNatTupleFamily_iff.mp hupper).1
    have hcanonical := (mem_separatedNatTupleFamily_iff.mp hlate).1
    exact canonicalAnnularGridTupleFamily_lt_ambient
      hgrid k htime hN e t hcanonical j
  unfold nestedPairCount
  calc
    (∑ e ∈
        (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)),
        (annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e (mode e) (hmode e)).card) ≤
      ∑ _e ∈
        (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)),
        annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
      exact Finset.sum_le_sum fun e _he ↦ hfamily e
    _ = orderCount *
        annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      rfl
    _ ≤ annularDepthAmbientSize N *
        annularDepthAmbientSize N ^ MixedOccurrenceCount k :=
      Nat.mul_le_mul_right
        (annularDepthAmbientSize N ^ MixedOccurrenceCount k) horder
    _ = annularDepthAmbientSize N ^
        (MixedOccurrenceCount k + 1) := by
      rw [pow_succ]
      ac_rfl

/-! ## Fixed-`rho` covariance cancellation -/

/-- Polynomially many upper-retained covariance errors are killed by the
actual half-band gap for every fixed `rho > 0`. -/
theorem tendsto_nested_annularUpperRetained_covariance_zero
    {rho : ℝ} (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (z : ℕ →
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      (Fin (MixedOccurrenceCount k) → ℕ) → ℂ)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ∀ e ∈ (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)),
      ∀ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e (mode e) (hmode e),
        ‖z N e t‖ ≤
          (384 * Real.log 2) *
            (527 / 540 : ℝ) ^ annularUpperRetainedGap rho N) :
    Tendsto
      (fun N ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e),
            z N e t)
      atTop (nhds 0) := by
  let prefixes :
      ℕ → Finset
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) :=
    fun _N ↦ Finset.univ
  let futures :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ annularCanonicalLaterUpperMidpointTupleFamily
      rho N k hr e (mode e) (hmode e)
  apply tendsto_nested_sum_zero_of_pairCount_le_scalePow_gaussMixingRate
    prefixes futures z
    annularDepthAmbientSize (annularUpperRetainedGap rho)
    (tendsto_annularUpperRetainedGap_atTop hrho)
    (MixedOccurrenceCount k + 1) ⌈2 / rho⌉₊
    (C := 384 * Real.log 2) (by positivity)
  · exact Eventually.of_forall fun N ↦
      annularDepthAmbientSize_le_natCeil_two_div_rho_mul_gap_add_one
        hrho N
  · simpa only [prefixes, futures] using!
      eventually_nestedPairCount_annularUpperRetained_le_ambient_pow_succ
        (rho := rho) hgrid k hr htime mode hmode
  · simpa only [prefixes, futures] using! hbound

/-- Consequently the explicit scalar mixing-error term in the aggregate
recombination inequality tends to zero. -/
theorem tendsto_annularUpperRetained_pairCount_mul_mixingError_zero
    {rho : ℝ} (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        (nestedPairCount
          (Finset.univ :
            Finset (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k))
          (fun e ↦ annularCanonicalLaterUpperMidpointTupleFamily
            rho N k hr e (mode e) (hmode e)) : ℝ) *
        ((384 * Real.log 2) *
          (527 / 540 : ℝ) ^ annularUpperRetainedGap rho N))
      atTop (nhds 0) := by
  let gap : ℕ → ℕ := annularUpperRetainedGap rho
  let scale : ℕ → ℕ := annularDepthAmbientSize
  let dimension : ℕ := MixedOccurrenceCount k + 1
  let dilation : ℕ := ⌈2 / rho⌉₊
  let theta : ℝ := 540 / 527
  let gapSucc : ℕ → ℕ := fun N ↦ gap N + 1
  let upper : ℕ → ℝ := fun N ↦
    ((384 * Real.log 2) * (dilation : ℝ) ^ dimension * theta) *
      ((gapSucc N : ℝ) ^ dimension *
        (theta ^ gapSucc N)⁻¹)
  have htheta : 1 < theta := by
    dsimp only [theta]
    norm_num
  have hgap :
      Tendsto gap atTop atTop := by
    exact tendsto_annularUpperRetainedGap_atTop hrho
  have hgapSucc : Tendsto gapSucc atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun N ↦ Nat.le_add_right (gap N) 1) hgap
  have hpoly :
      Tendsto
        (fun N ↦
          (gapSucc N : ℝ) ^ dimension *
            (theta ^ gapSucc N)⁻¹)
        atTop (nhds 0) := by
    have h :=
      (tendsto_natPower_mul_inverse_geometric
        dimension 1 (by omega) htheta).comp hgapSucc
    simpa only [one_mul] using! h
  have hupper : Tendsto upper atTop (nhds 0) := by
    have h := hpoly.const_mul
      ((384 * Real.log 2) * (dilation : ℝ) ^ dimension * theta)
    simpa only [upper, mul_zero] using! h
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards
      [Eventually.of_forall (fun N ↦
          annularDepthAmbientSize_le_natCeil_two_div_rho_mul_gap_add_one
            hrho N),
        eventually_nestedPairCount_annularUpperRetained_le_ambient_pow_succ
          (rho := rho) hgrid k hr htime mode hmode]
      with N hscaleN hcardN
    have hpairReal :
        (nestedPairCount
            (Finset.univ :
              Finset (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k))
            (fun e ↦ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e)) : ℝ) ≤
          (scale N : ℝ) ^ dimension := by
      exact_mod_cast hcardN
    have hscaleReal :
        (scale N : ℝ) ^ dimension ≤
          ((dilation * (gap N + 1) : ℕ) : ℝ) ^ dimension := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hscaleN
    have hrateNonneg :
        0 ≤ (384 * Real.log 2) *
          (527 / 540 : ℝ) ^ gap N := by
      positivity
    have hfactor :
        (527 / 540 : ℝ) ^ gap N =
          theta * (theta ^ gapSucc N)⁻¹ := by
      dsimp only [theta, gapSucc]
      rw [show (527 / 540 : ℝ) = (540 / 527 : ℝ)⁻¹ by
        norm_num, inv_pow, pow_succ, mul_inv_rev]
      field_simp
    calc
      (nestedPairCount
            (Finset.univ :
              Finset (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k))
            (fun e ↦ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e)) : ℝ) *
          ((384 * Real.log 2) *
            (527 / 540 : ℝ) ^ annularUpperRetainedGap rho N) ≤
        (scale N : ℝ) ^ dimension *
          ((384 * Real.log 2) *
            (527 / 540 : ℝ) ^ gap N) := by
        exact mul_le_mul_of_nonneg_right hpairReal hrateNonneg
      _ ≤
        ((dilation * (gap N + 1) : ℕ) : ℝ) ^ dimension *
          ((384 * Real.log 2) *
            (527 / 540 : ℝ) ^ gap N) := by
        exact mul_le_mul_of_nonneg_right hscaleReal hrateNonneg
      _ = upper N := by
        rw [hfactor]
        dsimp only [upper, gapSucc]
        push_cast
        rw [mul_pow]
        ring
  · exact hupper

/-! ## Final late-error reduction with the factorized main left explicit -/

/-- For the actual upper-retained tagged family, four vanishing
approximation stages plus fixed-`rho` mixing show that the exact aggregate
differs by `o(1)` from the explicit factorized prefix-times-future sum.

The five term families are deliberately caller-supplied: downstream code
instantiates them with the literal good-event term, the future digit
replacement, the affine frozen prefix, and the frozen density. -/
theorem
    tendsto_annularUpperRetained_exact_sub_factorized_zero_of_four_stages
    {rho : ℝ} (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (exact good digit frozenPrefix frozenJoint :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        (Fin (MixedOccurrenceCount k) → ℕ) → ℂ)
    (prefixMean futureMean :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        (Fin (MixedOccurrenceCount k) → ℕ) → ℂ)
    (hbad : Tendsto
      (fun N ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e),
            ‖exact N e t - good N e t‖)
      atTop (nhds 0))
    (hreplacement : Tendsto
      (fun N ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e),
            ‖good N e t - digit N e t‖)
      atTop (nhds 0))
    (hfreezing : Tendsto
      (fun N ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e),
            ‖digit N e t - frozenPrefix N e t‖)
      atTop (nhds 0))
    (hdensity : Tendsto
      (fun N ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e),
            ‖frozenPrefix N e t - frozenJoint N e t‖)
      atTop (nhds 0))
    (hmixing : ∀ᶠ N : ℕ in atTop,
      ∀ e ∈ (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)),
      ∀ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e (mode e) (hmode e),
        ‖frozenJoint N e t -
            prefixMean N e t * futureMean N e t‖ ≤
          (384 * Real.log 2) *
            (527 / 540 : ℝ) ^ annularUpperRetainedGap rho N) :
    Tendsto
      (fun N ↦
        (∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
                rho N k hr e (mode e) (hmode e),
              exact N e t) -
          ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
                rho N k hr e (mode e) (hmode e),
              prefixMean N e t * futureMean N e t)
      atTop (nhds 0) := by
  let prefixes :
      ℕ → Finset
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) :=
    fun _N ↦ Finset.univ
  let futures :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ annularCanonicalLaterUpperMidpointTupleFamily
      rho N k hr e (mode e) (hmode e)
  have hnorm :
      Tendsto
        (fun N ↦
          ∑ e ∈ prefixes N, ∑ t ∈ futures N e,
            ‖exact N e t - frozenJoint N e t‖)
        atTop (nhds 0) := by
    apply
      tendsto_sum_nested_norm_exact_sub_frozen_zero_of_four_stages
        prefixes futures exact good digit frozenPrefix frozenJoint
    · simpa only [prefixes, futures] using! hbad
    · simpa only [prefixes, futures] using! hreplacement
    · simpa only [prefixes, futures] using! hfreezing
    · simpa only [prefixes, futures] using! hdensity
  have hexactFrozen :
      Tendsto
        (fun N ↦
          ∑ e ∈ prefixes N, ∑ t ∈ futures N e,
            (exact N e t - frozenJoint N e t))
        atTop (nhds 0) :=
    tendsto_nested_sum_zero_of_sum_norm prefixes futures
      (fun N e t ↦ exact N e t - frozenJoint N e t) hnorm
  have hcovariance :
      Tendsto
        (fun N ↦
          ∑ e ∈ prefixes N, ∑ t ∈ futures N e,
            (frozenJoint N e t -
              prefixMean N e t * futureMean N e t))
        atTop (nhds 0) := by
    apply tendsto_nested_annularUpperRetained_covariance_zero
      hrho hgrid k hr htime mode hmode
    simpa only [prefixes, futures] using! hmixing
  have hsum :
      Tendsto
        (fun N ↦
          (∑ e ∈ prefixes N, ∑ t ∈ futures N e,
              (exact N e t - frozenJoint N e t)) +
            ∑ e ∈ prefixes N, ∑ t ∈ futures N e,
              (frozenJoint N e t -
                prefixMean N e t * futureMean N e t))
        atTop (nhds 0) := by
    simpa only [zero_add] using! hexactFrozen.add hcovariance
  exact hsum.congr' (Eventually.of_forall fun N ↦ by
    simp only [prefixes, futures, Finset.sum_sub_distrib]
    ring)

end

end Erdos1002
