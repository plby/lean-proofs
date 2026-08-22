/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZFiniteProductCoordinateUnion
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaBalance
import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily
import ErdosProblems.Erdos1165.TilingOrientedAllCreationStoppedCoordinate

/-!
# Literal finite-product bound for the oriented Theta screen

This file is the quantitative half of the all-creation Theta construction.
It works on one concrete retained trace and bounds the Boolean screen that
some represented away domino has an exceptional lazy total.  The bound is
derived only from the literal negative-binomial point masses.  In
particular, no path-space probability estimate is an input.
-/

open Filter
open scoped BigOperators

namespace Erdos1165.HLOZSourceOrientedThetaProduct

open ExternalProposition44 FiniteDominoProductLaw
open HLOZAllSixExactCoordinateProductClosure HLOZGapBetaNumerics
open HLOZFiniteProductCoordinateUnion HLOZNegativeBinomialTruncation
open HLOZSourceOrientedThetaBalance
open HLOZShellZeroExternalWindow
open TilingCappedMarginalization TilingSpatialInsertionFiber
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Scale-only arithmetic needed by every concrete oriented Theta fibre.
It is separated from the trace so the eventual proof is constructed once. -/
structure OrientedThetaScaleArithmetic (m : ℕ) : Prop where
  level_pos : 0 < m
  width : (HLOZProposition48Candidates.shellWidth48 m : ℝ) ≤
    (m : ℝ) / 10
  geometric : geometricDeviation m ≤
    m + HLOZProposition48Candidates.shellWidth48 m
  theta : thetaLowDeviation m ≤
    m + HLOZProposition48Candidates.shellWidth48 m
  thick_nonneg : 0 ≤ hlozThickThresholdReal44 m
  low_dom : (HLOZProposition48Candidates.shellWidth48 m : ℝ) +
      thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)

theorem eventually_orientedThetaScaleArithmetic :
    ∀ᶠ m : ℕ in atTop, OrientedThetaScaleArithmetic m := by
  have hpower := ExternalProposition44.eventually_const_mul_nat_rpow_le
    20 kappaOne 1 (by norm_num [kappaOne])
  filter_upwards
    [HLOZSharpWindowProductClosure.eventually_shellWidth48_cast_le_two_rpow,
      hpower, ScreeningInstantiation.eventually_geometricDeviation_le_half,
      eventually_theta_low_arithmetic, eventually_ge_atTop (1 : ℕ)] with
      m hwidth hpowerM hgeometric htheta hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hwidth10 :
      (HLOZProposition48Candidates.shellWidth48 m : ℝ) ≤ (m : ℝ) / 10 := by
    simp only [Real.rpow_one] at hpowerM
    nlinarith
  refine
    { level_pos := by omega
      width := hwidth10
      geometric := ?_
      theta := ?_
      thick_nonneg := htheta.1
      low_dom := htheta.2.1 }
  · have hw0 : (0 : ℝ) ≤ HLOZProposition48Candidates.shellWidth48 m := by
      positivity
    nlinarith
  · have hw0 : (0 : ℝ) ≤ HLOZProposition48Candidates.shellWidth48 m := by
      positivity
    nlinarith [htheta.2.2]

/-- The coordinate-level failure tested by the restricted Theta screen. -/
def thetaCoordinateBad (m w externalLow externalHigh i v : ℕ) : Prop :=
  v ∈ thetaFailureWindow m w i ∧
    ¬(externalLow ≤ i ∧ i < externalHigh)

instance (m w externalLow externalHigh i : ℕ) :
    DecidablePred (thetaCoordinateBad m w externalLow externalHigh i) :=
  Classical.decPred _

/-- The two source costs, selected by the literal retained multiplicity. -/
def thetaCoordinateCost (m i : ℕ) : ℝ :=
  if hlozThickLevel44 m ≤ i then
    Real.exp (-17 * balanceRateScale m)
  else
    Real.exp (-17 * thetaLowRateScale m)

lemma lazy_le_total_upper_of_mem_thetaFailureWindow
    {m w i v : ℕ} (hv : v ∈ thetaFailureWindow m w i) :
    v ≤ m + w := by
  have htotal := add_mem_total_union_of_mem_thetaFailureWindow hv
  rw [Finset.mem_union] at htotal
  rcases htotal with hs | hr
  · simp only [HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow]
      at hs
    omega
  · simp only
      [HLOZShellZeroReplacementWindows.mem_shellZeroReplacementTotalWindow]
      at hr
    omega

lemma card_tilingCoordinatesAt_pos
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : TilingExternalDomino t x r) :
    0 < Fintype.card (TilingCoordinatesAt t x r b) := by
  classical
  obtain ⟨j, _hj, hbase⟩ := Finset.mem_image.mp b.2
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨j, hbase⟩⟩

lemma card_tilingCoordinatesAt_le_retainedCount_succ
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : TilingExternalDomino t x r) :
    Fintype.card (TilingCoordinatesAt t x r b) ≤ i + 1 := by
  classical
  simpa using Fintype.card_le_of_injective
    (fun q : TilingCoordinatesAt t x r b ↦ q.1) Subtype.val_injective

/-- One raw coordinate window has exactly one of the two Proposition 4.5
costs.  The cap and ambient upper hypotheses are the deterministic support
conditions supplied by the concrete all-creation fibre. -/
theorem sum_thetaCoordinateBad_tilingAwayPointMass_le
    {retainedCount cap upper m w externalLow externalHigh : ℕ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (b : TilingAwayDomino t x r D)
    (hm : 0 < m)
    (hwidth : (w : ℝ) ≤ (m : ℝ) / 10)
    (hw : w = HLOZProposition48Candidates.shellWidth48 m)
    (hexternalLow : externalLow = shellZeroExternalLow48 m)
    (hexternalHigh : externalHigh = shellZeroExternalHigh48 m)
    (hgeometric : geometricDeviation m ≤ m + w)
    (htheta : thetaLowDeviation m ≤ m + w)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : (w : ℝ) + thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (hwindowUpper : ∀ v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t x r b.1)), v < upper)
    (hwindowCap : ∀ v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t x r b.1)), v ≤ cap) :
    (∑ v : Fin upper,
        if thetaCoordinateBad m w externalLow externalHigh
            (Fintype.card (TilingCoordinatesAt t x r b.1)) v then
          tilingAwayPointMass (cap := cap) t x r D b v else 0) ≤
      thetaCoordinateCost m
        (Fintype.card (TilingCoordinatesAt t x r b.1)) := by
  classical
  let i := Fintype.card (TilingCoordinatesAt t x r b.1)
  have hi : 0 < i := card_tilingCoordinatesAt_pos t x r b.1
  by_cases himbalance : externalLow ≤ i ∧ i < externalHigh
  · have hfalse : ∀ v : Fin upper,
        ¬thetaCoordinateBad m w externalLow externalHigh i v := by
      intro v hv
      exact hv.2 himbalance
    simp only [i, hfalse, ↓reduceIte, Finset.sum_const_zero]
    unfold thetaCoordinateCost
    split <;> positivity
  · have heq : (∑ v : Fin upper,
        if thetaCoordinateBad m w externalLow externalHigh i v then
          tilingAwayPointMass (cap := cap) t x r D b v else 0) =
        SmallWindow.windowMass i (thetaFailureWindow m w i) := by
      calc
        _ = ∑ v : Fin upper,
            if (v : ℕ) ∈ thetaFailureWindow m w i then
              tilingAwayPointMass (cap := cap) t x r D b v else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          simp only [thetaCoordinateBad, himbalance, not_false_eq_true,
            and_true]
        _ = _ := sum_tilingAwayPointMass_window t x r D b upper
          (thetaFailureWindow m w i) hwindowUpper hwindowCap hi
    rw [heq]
    unfold thetaCoordinateCost
    by_cases hhigh : hlozThickLevel44 m ≤ i
    · rw [if_pos hhigh]
      have houtside : i < externalLow ∨ externalHigh ≤ i := by omega
      rcases houtside with hlower | hupper
      · exact thetaFailureWindowMass_le_high_lower_cost hm hi hwidth
          (by simpa only [hexternalLow] using hlower) hw
          (by simpa only [Nat.cast_add] using hgeometric)
      · exact thetaFailureWindowMass_le_high_upper_cost hm hi hwidth
          (by simpa only [hexternalHigh] using hupper) hw
          (by simpa only [Nat.cast_add] using hgeometric)
    · rw [if_neg hhigh]
      exact thetaFailureWindowMass_le_low_cost hm hi hwidth
        (Nat.lt_of_not_ge hhigh) hthreshold0 hdom
        (by simpa only [Nat.cast_add] using htheta)

/-- Boolean acceptor for the finite union of coordinate Theta failures. -/
def allCreationThetaAccepts
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Bool :=
  decide (∃ b, thetaCoordinateBad m w externalLow externalHigh
    (Fintype.card (TilingCoordinatesAt t (data.start cap)
      (data.retained cap) b.1)) (ell b))

noncomputable def allCreationThetaCoordinateCostSum
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) : ℝ :=
  ∑ b : TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap), thetaCoordinateCost m
    (Fintype.card (TilingCoordinatesAt t (data.start cap)
      (data.retained cap) b.1))

/-- Deterministic arithmetic/support fields for one literal Theta product.
Bundling them keeps the quantitative theorem independent of the eventual
scale proof used by the source application. -/
structure AllCreationThetaProductArithmetic
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) : Prop where
  level_pos : 0 < m
  width : (w : ℝ) ≤ (m : ℝ) / 10
  width_eq : w = HLOZProposition48Candidates.shellWidth48 m
  externalLow_eq : externalLow = shellZeroExternalLow48 m
  externalHigh_eq : externalHigh = shellZeroExternalHigh48 m
  geometric : geometricDeviation m ≤ m + w
  theta : thetaLowDeviation m ≤ m + w
  thick_nonneg : 0 ≤ hlozThickThresholdReal44 m
  low_dom : (w : ℝ) + thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)
  upper_le_cap : ∀ b, data.upper cap b ≤ data.coordinateCap cap + 1
  mean : ∀ b, 2 * Fintype.card (TilingCoordinatesAt t (data.start cap)
    (data.retained cap) b.1) ≤ 15 * data.upper cap b
  window_upper : ∀
    (b : TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap)) v,
    v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t (data.start cap)
        (data.retained cap) b.1)) → v < data.upper cap b
  window_cap : ∀
    (b : TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap)) v,
    v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t (data.start cap)
      (data.retained cap) b.1)) → v ≤ data.coordinateCap cap

def allCreationThetaBad
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (b : TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap)) (v : Fin (data.upper cap b)) : Prop :=
  thetaCoordinateBad m w externalLow externalHigh
    (Fintype.card (TilingCoordinatesAt t (data.start cap)
      (data.retained cap) b.1)) v

instance
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (b : TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap)) (v : Fin (data.upper cap b)) :
    Decidable (allCreationThetaBad data w externalLow externalHigh cap b v) := by
  unfold allCreationThetaBad
  infer_instance

def allCreationThetaCost
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ)
    (b : TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap)) : ℝ :=
  thetaCoordinateCost m (Fintype.card
    (TilingCoordinatesAt t (data.start cap) (data.retained cap) b.1))

lemma allCreationTheta_pointMass_nonneg
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) (b) (v : ℕ) :
    0 ≤ tilingAwayPointMass (cap := data.coordinateCap cap) t
      (data.start cap) (data.retained cap) (data.distinguished cap) b v :=
  tilingAwayExactTotalMass_nonneg t (data.start cap) (data.retained cap)
    (data.distinguished cap) b v

lemma allCreationTheta_coordinate_sum_eq_one
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) (b) :
    (∑ v : Fin (data.upper cap b), coordinateMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t
        (data.start cap) (data.retained cap) (data.distinguished cap))
      (data.upper cap) b v) = 1 := by
  exact sum_coordinateMass_eq_one_of_zero_pos _ _
    (allCreationTheta_pointMass_nonneg data cap) (data.upper_pos cap)
    (fun c ↦ tilingAwayExactTotalMass_zero_pos t (data.start cap)
      (data.retained cap) (data.distinguished cap) c) b

lemma allCreationTheta_denominator
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (w externalLow externalHigh cap : ℕ)
    (arith : AllCreationThetaProductArithmetic data w externalLow
      externalHigh cap) (b) :
    (1 / 2 : ℝ) ≤ ∑ v : Fin (data.upper cap b),
      tilingAwayPointMass (cap := data.coordinateCap cap) t
        (data.start cap) (data.retained cap) (data.distinguished cap) b v := by
  exact half_le_sum_tilingAwayPointMass t (data.start cap)
    (data.retained cap) (data.distinguished cap) b (data.upper cap b)
    (data.upper_pos cap b) (arith.upper_le_cap b)
    (card_tilingCoordinatesAt_pos t (data.start cap)
      (data.retained cap) b.1) (arith.mean b)

lemma allCreationTheta_bad_mass_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (w externalLow externalHigh cap : ℕ)
    (arith : AllCreationThetaProductArithmetic data w externalLow
      externalHigh cap) (b) :
    (∑ v : Fin (data.upper cap b),
      if thetaCoordinateBad m w externalLow externalHigh
          (Fintype.card (TilingCoordinatesAt t (data.start cap)
            (data.retained cap) b.1)) v then
        tilingAwayPointMass (cap := data.coordinateCap cap) t
          (data.start cap) (data.retained cap) (data.distinguished cap) b v
      else 0) ≤ allCreationThetaCost data cap b := by
  classical
  exact sum_thetaCoordinateBad_tilingAwayPointMass_le t
    (data.start cap) (data.retained cap) (data.distinguished cap) b
    arith.level_pos arith.width arith.width_eq arith.externalLow_eq
    arith.externalHigh_eq arith.geometric arith.theta arith.thick_nonneg
    arith.low_dom (arith.window_upper b) (arith.window_cap b)

private theorem allCreationBoolScreenMass_thetaCost_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (arith : AllCreationThetaProductArithmetic data w externalLow
      externalHigh cap) :
    allCreationBoolScreenMass data
        (allCreationThetaAccepts data w externalLow externalHigh) cap ≤
      2 * ∑ b : TilingAwayDomino t (data.start cap) (data.retained cap)
          (data.distinguished cap), allCreationThetaCost data cap b := by
  classical
  let pointMass := tilingAwayPointMass (cap := data.coordinateCap cap) t
    (data.start cap) (data.retained cap) (data.distinguished cap)
  let upper := data.upper cap
  let bad := fun b (v : Fin (upper b)) ↦
    thetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t (data.start cap)
        (data.retained cap) b.1)) v
  let cost := fun b : TilingAwayDomino t (data.start cap)
      (data.retained cap) (data.distinguished cap) ↦ thetaCoordinateCost m
    (Fintype.card (TilingCoordinatesAt t (data.start cap)
      (data.retained cap) b.1))
  have hpoint : ∀ b v, 0 ≤ pointMass b v :=
    allCreationTheta_pointMass_nonneg data cap
  have hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1 := by
    exact allCreationTheta_coordinate_sum_eq_one data cap
  have hden : ∀ b, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper b), pointMass b v := by
    exact allCreationTheta_denominator data w externalLow externalHigh cap arith
  have hbad : ∀ b, (∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0) ≤ cost b := by
    exact allCreationTheta_bad_mass_le data w externalLow externalHigh cap arith
  have haccepts : ∀ ell, allCreationThetaAccepts data w externalLow
      externalHigh cap ell = true ↔ ∃ b, bad b (ell b) := by
    intro ell
    simp [allCreationThetaAccepts, bad, upper]
  have hmain := @screenMass_bool_iff_exists_coordinate_le_two_mul_sum
    (TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap))
    (instFintypeTilingAwayDomino t (data.start cap)
      (data.retained cap) (data.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    pointMass upper bad (fun _ ↦ Classical.decPred _)
    (allCreationThetaAccepts data w externalLow externalHigh cap) haccepts cost
    hpoint hsum hden hbad
  let explicitUniv : Finset
      (TilingAwayDomino t (data.start cap) (data.retained cap)
        (data.distinguished cap)) :=
    @Finset.univ
      (TilingAwayDomino t (data.start cap) (data.retained cap)
        (data.distinguished cap))
      (instFintypeTilingAwayDomino t (data.start cap)
        (data.retained cap) (data.distinguished cap))
  unfold allCreationBoolScreenMass
  calc
    @screenMass
        (TilingAwayDomino t (data.start cap) (data.retained cap)
          (data.distinguished cap))
        (instFintypeTilingAwayDomino t (data.start cap)
          (data.retained cap) (data.distinguished cap))
        (fun a b ↦ Subtype.instDecidableEq a b)
        pointMass upper (fun ell ↦ allCreationThetaAccepts data w externalLow
          externalHigh cap ell = true) (fun _ ↦ instDecidableEqBool _ true) ≤
      2 * ∑ b ∈ explicitUniv, cost b := hmain
    _ = 2 * ∑ b, allCreationThetaCost data cap b := by
      congr 1
      have huniv : explicitUniv =
          (Finset.univ : Finset (TilingAwayDomino t (data.start cap)
            (data.retained cap) (data.distinguished cap))) := by
        ext b
        simp [explicitUniv]
      rw [huniv]
      rfl

/-- Literal finite-product union bound for one all-creation fibre.  The
result still records the exact sum of the high/low coordinate costs; the
Prop. 4.4 support budget is applied at the trace-family layer. -/
theorem allCreationBoolScreenMass_theta_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (arith : AllCreationThetaProductArithmetic data w externalLow
      externalHigh cap) :
    allCreationBoolScreenMass data
        (allCreationThetaAccepts data w externalLow externalHigh) cap ≤
      2 * allCreationThetaCoordinateCostSum data cap := by
  simpa only [allCreationThetaCoordinateCostSum, allCreationThetaCost] using
    allCreationBoolScreenMass_thetaCost_le data w externalLow externalHigh cap
      arith

/-- Coordinates in the Proposition 4.4 (large retained local-time) part of
one exact all-creation trace. -/
def thetaHighCoordinates
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) :
    Finset (TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap)) :=
  Finset.univ.filter fun b ↦ hlozThickLevel44 m ≤
    Fintype.card (TilingCoordinatesAt t (data.start cap)
      (data.retained cap) b.1)

lemma sum_thetaCoordinateCost_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) :
    (∑ b : TilingAwayDomino t (data.start cap) (data.retained cap)
        (data.distinguished cap), thetaCoordinateCost m
          (Fintype.card (TilingCoordinatesAt t (data.start cap)
            (data.retained cap) b.1))) ≤
      ((thetaHighCoordinates data cap).card : ℝ) *
          Real.exp (-17 * balanceRateScale m) +
        (S.card : ℝ) * Real.exp (-17 * thetaLowRateScale m) := by
  classical
  let highCost := Real.exp (-17 * balanceRateScale m)
  let lowCost := Real.exp (-17 * thetaLowRateScale m)
  calc
    (∑ b : TilingAwayDomino t (data.start cap) (data.retained cap)
        (data.distinguished cap), thetaCoordinateCost m
          (Fintype.card (TilingCoordinatesAt t (data.start cap)
            (data.retained cap) b.1))) ≤
        ∑ b : TilingAwayDomino t (data.start cap) (data.retained cap)
          (data.distinguished cap),
          ((if hlozThickLevel44 m ≤ Fintype.card
              (TilingCoordinatesAt t (data.start cap)
                (data.retained cap) b.1) then highCost else 0) + lowCost) := by
      apply Finset.sum_le_sum
      intro b _
      unfold thetaCoordinateCost highCost lowCost
      split
      · exact le_add_of_nonneg_right (Real.exp_pos _).le
      · simp only [zero_add, le_refl]
    _ = ((thetaHighCoordinates data cap).card : ℝ) * highCost +
        (S.card : ℝ) * lowCost := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [show (∑ b : TilingAwayDomino t (data.start cap)
          (data.retained cap) (data.distinguished cap),
          if hlozThickLevel44 m ≤ Fintype.card
              (TilingCoordinatesAt t (data.start cap)
                (data.retained cap) b.1) then highCost else 0) =
          ((thetaHighCoordinates data cap).card : ℝ) * highCost by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, thetaHighCoordinates]]
      · simp only [Finset.sum_const, nsmul_eq_mul]
        have huniv : (Finset.univ : Finset
            (TilingAwayDomino t (data.start cap) (data.retained cap)
              (data.distinguished cap))) =
            @Finset.univ (TilingAwayDomino t (data.start cap)
              (data.retained cap) (data.distinguished cap))
              (instFintypeTilingAwayDomino t (data.start cap)
                (data.retained cap) (data.distinguished cap)) := by
          ext b
          simp only [Finset.mem_univ]
        have hcard : (Finset.univ : Finset
            (TilingAwayDomino t (data.start cap) (data.retained cap)
              (data.distinguished cap))).card = S.card := by
          rw [huniv]
          simpa only [Finset.card_univ] using
            OrientedAllCreationPrefixedStoppedCoordinateSpec.card_away_eq_support
              data cap
        rw [hcard]
    _ = _ := rfl

/-- The concrete all-creation cap schedule discharges every finite
normalization side condition in the Theta product bound. -/
theorem orientedAllCreationConcreteFiber_theta_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData
      t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt)
    (externalLow externalHigh cap : ℕ)
    (hm : 0 < m)
    (hwidth : (HLOZProposition48Candidates.shellWidth48 m : ℝ) ≤
      (m : ℝ) / 10)
    (hgeometric : geometricDeviation m ≤
      m + HLOZProposition48Candidates.shellWidth48 m)
    (htheta : thetaLowDeviation m ≤
      m + HLOZProposition48Candidates.shellWidth48 m)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : (HLOZProposition48Candidates.shellWidth48 m : ℝ) +
        thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (hexternalLow : externalLow = shellZeroExternalLow48 m)
    (hexternalHigh : externalHigh = shellZeroExternalHigh48 m) :
    let data := orientedAllCreationConcreteFiber
      o m k supportAt supportData eta
    allCreationBoolScreenMass data
        (allCreationThetaAccepts data
          (HLOZProposition48Candidates.shellWidth48 m)
          externalLow externalHigh) cap ≤
      2 * (((thetaHighCoordinates data cap).card : ℝ) *
          Real.exp (-17 * balanceRateScale m) +
        (eta.1.2.card : ℝ) * Real.exp (-17 * thetaLowRateScale m)) := by
  let data := orientedAllCreationConcreteFiber
    o m k supportAt supportData eta
  have harith : AllCreationThetaProductArithmetic data
      (HLOZProposition48Candidates.shellWidth48 m)
      externalLow externalHigh cap := by
    refine
      { level_pos := hm
        width := hwidth
        width_eq := rfl
        externalLow_eq := hexternalLow
        externalHigh_eq := hexternalHigh
        geometric := hgeometric
        theta := htheta
        thick_nonneg := hthreshold0
        low_dom := hdom
        upper_le_cap := ?_
        mean := ?_
        window_upper := ?_
        window_cap := ?_ }
    · intro b
      dsimp only [data, orientedAllCreationConcreteFiber]
      omega
    · intro b
      have hcard := card_tilingCoordinatesAt_le_retainedCount_succ t
        (data.start cap) (data.retained cap) b.1
      dsimp only [data, orientedAllCreationConcreteFiber,
        OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
        OrientedAllCreationPrefixedStoppedCoordinateSpec.retained] at hcard ⊢
      omega
    · intro b v hv
      have hv' := lazy_le_total_upper_of_mem_thetaFailureWindow hv
      dsimp only [data, orientedAllCreationConcreteFiber]
      omega
    · intro b v hv
      have hv' := lazy_le_total_upper_of_mem_thetaFailureWindow hv
      dsimp only [data, orientedAllCreationConcreteFiber]
      omega
  have hraw := allCreationBoolScreenMass_theta_le data
    (HLOZProposition48Candidates.shellWidth48 m) externalLow externalHigh cap
    harith
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (sum_thetaCoordinateCost_le data cap) (by norm_num))

/-- Premise-free-at-scale specialization: all external windows and every
moderate-deviation inequality are the canonical source choices. -/
theorem orientedAllCreationConcreteFiber_theta_le_of_scale
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData
      t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt)
    (cap : ℕ) (scale : OrientedThetaScaleArithmetic m) :
    let data := orientedAllCreationConcreteFiber
      o m k supportAt supportData eta
    allCreationBoolScreenMass data
        (allCreationThetaAccepts data
          (HLOZProposition48Candidates.shellWidth48 m)
          (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) cap ≤
      2 * (((thetaHighCoordinates data cap).card : ℝ) *
          Real.exp (-17 * balanceRateScale m) +
        (eta.1.2.card : ℝ) * Real.exp (-17 * thetaLowRateScale m)) := by
  exact orientedAllCreationConcreteFiber_theta_le supportData eta
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) cap
    scale.level_pos scale.width scale.geometric scale.theta
    scale.thick_nonneg scale.low_dom rfl rfl

end

end Erdos1165.HLOZSourceOrientedThetaProduct
