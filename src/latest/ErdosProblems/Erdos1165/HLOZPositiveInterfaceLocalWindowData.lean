/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceAggregateRecovery
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationAggregateSharpTail
import ErdosProblems.Erdos1165.HLOZTruncatedSharpWindowRatio

/-!
# Local sharp-window data on a positive-interface atom

This file derives the coordinatewise positivity and truncated adjacent-window
comparison needed by the positive-interface cofinal product.  The accepted
base window is the honest prefix-correct window from
`HLOZPositiveInterfaceAggregateRecovery`.
-/

open Set
open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfaceLocalWindowData

open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open HLOZAllSixExactCoordinateProductClosure
open HLOZProposition48Candidates
open HLOZTruncatedSharpWindowRatio
open HLOZSharpWindowProductClosure
open FiniteDominoProductLaw
open LazyDecomposition ScreeningInstantiation SmallWindow SpatialInsertionFiber
open TilingAwayNegativeBinomial
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedPrefixedSupportBridge
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Every away coordinate of a nonempty exact positive-interface atom has a
nonempty same-rank accepted total window. -/
theorem positiveInterfaceFixedBoundaryDominoMax_lt
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (positiveInterfaceTerminal eta) b.1 < m := by
  classical
  rcases eta.2 with ⟨s, hs⟩
  let n := creationTimeNat m k s
  obtain ⟨q, hword⟩ :=
    exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
      t o n s eta.1.1.external
        (congrArg OrientedAllCreationTraceCode.external hs.1.2.2)
  let cap₀ := ∑ j, q j
  have hqcap (j : Fin (eta.1.1.external.retainedCount + 1)) :
      q j ≤ cap₀ := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ j)
  let qc : TilingCappedCoordinates eta.1.1.external.retainedCount cap₀ :=
    fun j ↦ ⟨q j, Nat.lt_succ_of_le (hqcap j)⟩
  have hdata := reconstructedCoordinates_mem_exactAtom
    o m k (PositiveInterfaceSupportAt t o m externalThreshold)
      (positiveInterfaceSupportData t o m k externalThreshold)
      eta.1.2 eta.1.1 s hs q hword cap₀ hqcap
  have hcanonical := canonical_mem_supportAtom_of_predicate_accepted
    cap₀ qc hdata.1 hdata.2
  have hstrict := positiveInterfaceCanonical_strictAway
    eta hm qc hcanonical hdata.2 b.1 b.2
  have hnonneg : 0 ≤ tilingDominoTotal t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (qc j : ℕ)) b.1 :=
    Nat.zero_le _
  omega

/-- The honest accepted base window has strictly positive normalized
coordinate mass, uniformly in the cap. -/
theorem positiveInterfaceBaseLocalPos
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    0 < ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
      if (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap))
          ((PositiveInterfaceFiber eta).upper cap) b v else 0 := by
  classical
  let fiber := PositiveInterfaceFiber eta
  let v₀ : Fin (fiber.upper cap b) := ⟨0, fiber.upper_pos cap b⟩
  have hboundary := positiveInterfaceFixedBoundaryDominoMax_lt eta hm cap b
  have hv₀mem : (v₀ : ℕ) ∈ positiveInterfaceBaseWindow eta cap b := by
    unfold positiveInterfaceBaseWindow
    rw [Finset.mem_range]
    exact Nat.sub_pos_of_lt hboundary
  have hv₀raw : 0 < tilingAwayPointMass
      (cap := fiber.coordinateCap cap) t (fiber.start cap)
      (fiber.retained cap) (fiber.distinguished cap) b v₀ := by
    simpa only [v₀, tilingAwayPointMass] using
      tilingAwayExactTotalMass_zero_pos (cap := fiber.coordinateCap cap)
        t (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap) b
  have hdenPos : 0 < ∑ j : Fin (fiber.upper cap b),
      tilingAwayPointMass (cap := fiber.coordinateCap cap) t
        (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap) b j := by
    exact hv₀raw.trans_le (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (fiber.upper cap b) ↦
        tilingAwayPointMass (cap := fiber.coordinateCap cap) t
          (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap) b j)
      (fun j _ ↦ tilingAwayExactTotalMass_nonneg t
        (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap) b j)
      (Finset.mem_univ v₀))
  have hv₀mass : 0 < coordinateMass
      (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
        (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap))
      (fiber.upper cap) b v₀ := by
    simpa only [coordinateMass, v₀.isLt, ↓reduceIte] using
      (div_pos hv₀raw hdenPos)
  apply hv₀mass.trans_le
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun v : Fin (fiber.upper cap b) ↦
      if (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap))
          (fiber.upper cap) b v else 0)
    (fun v _ ↦ by
      split
      · exact coordinateMass_nonneg_of_pointMass_nonneg _ _
          (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap) b' ell) b v
      · exact le_rfl)
    (Finset.mem_univ v₀)
  simpa only [if_pos hv₀mem] using hsingle

/-- Membership in the positive-interface support is exactly the retained
multiplicity lower bound needed to activate the sharp windows. -/
theorem positiveInterfaceCoordinateCount_ge_externalThreshold
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    externalThreshold ≤ Fintype.card (TilingCoordinatesAt t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) b.1) := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2 b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  let n := creationTimeNat m k s
  have hbSupport : b.1.1 ∈ PositiveInterfaceSupportAt t o m
      externalThreshold s n := by
    rw [hs.2]
    exact hbS
  have hcode : fixedOrientedTypedExternalWordCode t o n s =
      eta.1.1.external :=
    congrArg OrientedAllCreationTraceCode.external hs.1.2.2
  unfold PositiveInterfaceSupportAt orientedPositiveInterfaceSupportAt at hbSupport
  rw [hcode] at hbSupport
  rcases (mem_orientedPositiveInterfaceCodeSupport_iff.mp hbSupport) with
    ⟨hb, hthick, _⟩
  change externalThreshold ≤ Fintype.card (TilingCoordinatesAt t
    eta.1.1.external.start eta.1.1.external.retained b.1)
  simpa using hthick

/-- The untruncated active adjacent windows satisfy the checked local-CLT
comparison on every coordinate of a thick positive-interface support. -/
theorem positiveInterfaceWindowRatio
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (harith : SharpWindowArithmeticAt m)
    (hactive : m / 2 ≤ externalThreshold) (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    (∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
      if (v : ℕ) ∈ activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap))
          ((PositiveInterfaceFiber eta).upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
          if (v : ℕ) ∈ activeLowerFailureWindow m
              (Fintype.card (TilingCoordinatesAt t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap) b.1)) then
            coordinateMass
              (tilingAwayPointMass
                (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap)
                ((PositiveInterfaceFiber eta).distinguished cap))
              ((PositiveInterfaceFiber eta).upper cap) b v else 0 := by
  classical
  let fiber := PositiveInterfaceFiber eta
  let i := Fintype.card (TilingCoordinatesAt t (fiber.start cap)
    (fiber.retained cap) b.1)
  have hi : m / 2 ≤ i := hactive.trans
    (positiveInterfaceCoordinateCount_ge_externalThreshold eta cap b)
  have hiFacts := harith.2 i hi
  have hcard : i ≤ eta.1.1.external.retainedCount + 1 := by
    change Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
      eta.1.1.external.retained b.1) ≤ eta.1.1.external.retainedCount + 1
    simpa using Fintype.card_le_of_injective
      (fun q : TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b.1 ↦ q.1) Subtype.val_injective
  have hscaleR : (60 * shellWidth48 m + 30 : ℝ) ≤ i := by
    have hmoderate := hiFacts.2.1
    unfold adjacentWindowRadius at hmoderate
    linarith
  have hscale : 60 * shellWidth48 m + 30 ≤ i := by
    exact_mod_cast hscaleR
  have hupperLt : ∀ v ∈ upperFailureWindow i (shellWidth48 m),
      v < fiber.upper cap b := by
    intro v hv
    rw [upperFailureWindow, Finset.mem_Ico] at hv
    change v < max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + 1
    omega
  have hlowerLt : ∀ v ∈ lowerFailureWindow i (shellWidth48 m),
      v < fiber.upper cap b := by
    intro v hv
    rw [lowerFailureWindow, Finset.mem_Ico] at hv
    change v < max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + 1
    omega
  have hupperCap : ∀ v ∈ upperFailureWindow i (shellWidth48 m),
      v ≤ fiber.coordinateCap cap := by
    intro v hv
    rw [upperFailureWindow, Finset.mem_Ico] at hv
    change v ≤ max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + cap
    omega
  have hlowerCap : ∀ v ∈ lowerFailureWindow i (shellWidth48 m),
      v ≤ fiber.coordinateCap cap := by
    intro v hv
    rw [lowerFailureWindow, Finset.mem_Ico] at hv
    change v ≤ max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + cap
    omega
  change
    (∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ activeUpperFailureWindow m i then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap))
          (fiber.upper cap) b v else 0) ≤
      (4 / 3 : ℝ) * ∑ v : Fin (fiber.upper cap b),
        if (v : ℕ) ∈ activeLowerFailureWindow m i then
          coordinateMass
            (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
              (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap))
            (fiber.upper cap) b v else 0
  rw [activeUpperFailureWindow_eq_of_active hi,
    activeLowerFailureWindow_eq_of_active hi]
  refine (tilingAway_coordinateMass_window_ratio_of_localCLT t
    (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap)
    (fiber.upper cap) b
    (upperFailureWindow i (shellWidth48 m))
    (lowerFailureWindow i (shellWidth48 m)) hupperLt hlowerLt
    hupperCap hlowerCap hiFacts.1 (adjacentWindowRadius_nonneg _)
    (adjacentWindowSeparation_nonneg _) hiFacts.2.1
    (lowerFailureWindow_nonempty harith.1) (by simp)
    (fun _ hv ↦ upperFailureWindow_deviation_le hv)
    (fun _ hv ↦ lowerFailureWindow_deviation_le hv)
    (fun _ hu _ hl ↦ adjacentFailureWindow_deviation_sub_le hu hl)).trans ?_
  apply mul_le_mul_of_nonneg_right hiFacts.2.2
  exact Finset.sum_nonneg fun v _ ↦ by
    split
    · exact coordinateMass_nonneg_of_pointMass_nonneg _ _
        (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t
          (fiber.start cap) (fiber.retained cap)
          (fiber.distinguished cap) b' ell) b v
    · exact le_rfl

/-- Intersecting both adjacent windows with the honest same-rank accepted
window preserves the local `4/3` comparison. -/
theorem positiveInterfaceWindowRatio_inter_base
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (harith : SharpWindowArithmeticAt m)
    (hactive : m / 2 ≤ externalThreshold) (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    (∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
      if (v : ℕ) ∈ activeUpperFailureWindow m
            (Fintype.card (TilingCoordinatesAt t
              ((PositiveInterfaceFiber eta).start cap)
              ((PositiveInterfaceFiber eta).retained cap) b.1)) ∧
          (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap))
          ((PositiveInterfaceFiber eta).upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
          if (v : ℕ) ∈ activeLowerFailureWindow m
                (Fintype.card (TilingCoordinatesAt t
                  ((PositiveInterfaceFiber eta).start cap)
                  ((PositiveInterfaceFiber eta).retained cap) b.1)) ∧
              (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
            coordinateMass
              (tilingAwayPointMass
                (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap)
                ((PositiveInterfaceFiber eta).distinguished cap))
              ((PositiveInterfaceFiber eta).upper cap) b v else 0 := by
  let fiber := PositiveInterfaceFiber eta
  let i := Fintype.card (TilingCoordinatesAt t (fiber.start cap)
    (fiber.retained cap) b.1)
  let cut := m - prefixedTilingFixedBoundaryDominoMax
    eta.1.1.external.initial.1 eta.1.1.external.start
    eta.1.1.external.retained (positiveInterfaceTerminal eta) b.1
  have hratio := positiveInterfaceWindowRatio eta harith hactive cap b
  have htruncated := activeFailureWindow_inter_Iio_ratio m i
    (fiber.upper cap b) cut
    (fun v ↦ coordinateMass
      (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
        (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap))
      (fiber.upper cap) b v)
    (fun v ↦ coordinateMass_nonneg_of_pointMass_nonneg _ _
      (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t
        (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap) b' ell) b v)
    (by norm_num) hratio
  simpa only [positiveInterfaceBaseWindow, Finset.mem_range] using htruncated

/-! ## Cofinal cap coherence of the truncated positive-interface screen -/

/-- Public spelling of the literal truncated positive-interface coordinate
predicate.  This is definitionally the predicate used by
`StaticSupportRecoveryCertificate.truncatedSharpTailData`. -/
noncomputable def positiveInterfaceScreenedPredicate
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((PositiveInterfaceFiber eta).coordinateCap cap)) : Prop :=
  let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
  (PositiveInterfaceFiber eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)
      ((PositiveInterfaceFiber eta).upper cap)
      (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true)
      ((splitTilingCoordinatesEquiv t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap)
        ((PositiveInterfaceFiber eta).distinguished cap) q).2)

private theorem positiveInterfaceCoordinateCap_mono
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    {cap cap' : ℕ} (hcap : cap ≤ cap') :
    (PositiveInterfaceFiber eta).coordinateCap cap ≤
      (PositiveInterfaceFiber eta).coordinateCap cap' := by
  change max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap ≤
    max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap'
  omega

private theorem positiveInterfaceScreenedPredicate_cast
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((PositiveInterfaceFiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((PositiveInterfaceFiber eta).stoppingTime cap)
      ((PositiveInterfaceFiber eta).initial cap) t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
      ((PositiveInterfaceFiber eta).tail cap))
    (hscreen : positiveInterfaceScreenedPredicate eta hm hk threshold
      shell bound cap q) :
    positiveInterfaceScreenedPredicate eta hm hk threshold shell bound cap'
      (castAllCreationCappedCoordinates eta.1.1
        (positiveInterfaceCoordinateCap_mono eta hcap) q) := by
  classical
  let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
  rcases hscreen with ⟨hpred, ell, hell, htotal⟩
  refine ⟨?_, ell, ?_, ?_⟩
  · exact orientedAllCreationStoppedAtomPredicate_cast
      o m k (PositiveInterfaceSupportAt t o m externalThreshold)
      eta.1.2 eta.1.1 (positiveInterfaceCoordinateCap_mono eta hcap)
      q hpred haccepted
  · exact hell
  · intro b
    simp only [OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.distinguished]
      at htotal b ⊢
    calc
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (fun j ↦ (castAllCreationCappedCoordinates eta.1.1
            (positiveInterfaceCoordinateCap_mono eta hcap) q j : ℕ)) b.1 :=
        tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 := by
        simp only [coe_castAllCreationCappedCoordinates]
      _ = tilingAwayTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained
            (supportComplementDistinguished t eta.1.1.external.start
              eta.1.1.external.retained eta.1.2) q).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _).symm
      _ = ell b := htotal b

/-- Literal stopped paths satisfying the positive-interface truncated
screen at one cap. -/
def positiveInterfaceScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((PositiveInterfaceFiber eta).stoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).coordinateCap cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (positiveInterfaceScreenedPredicate eta hm hk threshold shell bound cap))

/-- The genuine screened stopped fibres form an increasing cofinal cap
family. -/
theorem monotone_positiveInterfaceScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) :
    Monotone fun cap ↦ positiveInterfaceScreenedFiber eta hm hk threshold
      shell bound cap := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let q' := castAllCreationCappedCoordinates eta.1.1
    (positiveInterfaceCoordinateCap_mono eta hcap) q.1
  have haccepted' := prefixedStoppingAccepted_castAllCreation
    m k eta.1.1 (positiveInterfaceCoordinateCap_mono eta hcap) q.1 q.2.2
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact positiveInterfaceScreenedPredicate_cast eta hm hk threshold
      shell bound hcap q.1 q.2.2 q.2.1
  · rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((PositiveInterfaceFiber eta).isStoppingTime cap')
      ((PositiveInterfaceFiber eta).initial cap') t
      ((PositiveInterfaceFiber eta).start cap')
      ((PositiveInterfaceFiber eta).retained cap') (fun j ↦ (q' j : ℕ))
      ((PositiveInterfaceFiber eta).tail cap') haccepted']
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((PositiveInterfaceFiber eta).isStoppingTime cap)
      ((PositiveInterfaceFiber eta).initial cap) t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
      ((PositiveInterfaceFiber eta).tail cap) q.2.2] at hq
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail, q',
      coe_castAllCreationCappedCoordinates] using hq

end

end Erdos1165.HLOZPositiveInterfaceLocalWindowData
