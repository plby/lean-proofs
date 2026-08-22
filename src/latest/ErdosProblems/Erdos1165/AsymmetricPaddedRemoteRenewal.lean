/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedBridgeExtraction
import ErdosProblems.Erdos1165.AnnularOffspringRenewal
import ErdosProblems.Erdos1165.AnnularRecursiveWeightedRenewal

/-!
# The remote renewal exposed by the asymmetric padding

Between the retained separation boundary at level `l` and the padded cut at
level `p`, a bridge is an ordinary annular renewal.  Its middle states are on
level `p - 1`, its deleted child returns run from level `p` back to level
`p - 1`, and its escape endpoint lies on level `l`.

This file identifies the literal excursion-count kernel with that finite
renewal and records the small endpoint oscillation of its unmarked remote
continuation.  The latter is the analytic input used when recursively
decorated level-`p` returns are substituted into the retained outer bridge.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedRemoteRenewal

open AnnularBoundaryExcursionKernel AnnularOffspringKernel
open AnnularOffspringKernelRadial AnnularOffspringRenewal
open AnnularProfileClocks AppendixPairMoment
open AnnularRecursiveDecoratedProfileCode AnnularRecursiveProfileRow
open AnnularRecursiveProfileShape AnnularRecursiveWeightedRenewal
open AsymmetricPaddedEndpointHarnack
open MarkedBoundaryVisitKernel PlanarPotential RealDiscFinite
open TerminalProfileBoundarySeparation TerminalSpliceProfileGeometry ThickPoint

noncomputable section

/-- States on the boundary immediately outside the padded cut. -/
abbrev PaddedMiddlePoint (n p : ℕ) (center : Point) :=
  BoundaryFinsetPoint center (scaleRadius n (p - 1))

/-- Entrance states on the padded cut. -/
abbrev PaddedInnerPoint (n p : ℕ) (center : Point) :=
  BoundaryFinsetPoint center (scaleRadius n p)

/-- Retained outer endpoints at the geometric separation level. -/
abbrev PaddedOuterPoint (n l : ℕ) (center : Point) :=
  BoundaryFinsetPoint center (scaleRadius n l)

/-- Initial states of a retained coarse bridge.  Such a bridge begins one
boundary inside its retained level-`l` endpoint and may reach the endpoint
before it ever enters the padded renewal at level `p - 1`. -/
abbrev PaddedNearPoint (n l : ℕ) (center : Point) :=
  BoundaryFinsetPoint center (scaleRadius n (l + 1))

/-- First entrance of a coarse bridge into the padded predecessor boundary,
with the retained endpoint included in the stopping barrier. -/
def paddedPreludeEntryKernelENNReal
    (n l p : ℕ) (center : Point) :
    PaddedNearPoint n l center → PaddedMiddlePoint n p center → ℝ≥0∞ :=
  fun start u ↦ skeletonExitKernel
    (profileInnerBoundary n (p - 1) center ∪ profileInnerBoundary n l center)
    start.1 u.1

/-- Direct exit of a coarse bridge before it enters the padded predecessor
boundary. -/
def paddedPreludeDirectKernelENNReal
    (n l p : ℕ) (center : Point) :
    PaddedNearPoint n l center → PaddedOuterPoint n l center → ℝ≥0∞ :=
  fun start w ↦ skeletonExitKernel
    (profileInnerBoundary n (p - 1) center ∪ profileInnerBoundary n l center)
    start.1 w.1

/-- The original unmarked coarse bridge, before splitting at the padded
predecessor boundary. -/
def paddedNearUnmarkedKernelENNReal
    (n l : ℕ) (center : Point) :
    PaddedNearPoint n l center → PaddedOuterPoint n l center → ℝ≥0∞ :=
  fun start w ↦ skeletonExitKernel
    (profileInnerBoundary n l center) start.1 w.1

/-- The retained first-hit step from the padded predecessor boundary to the
padded inner boundary, before the remote level-`l` exit. -/
def paddedInwardKernelENNReal
    (n l p : ℕ) (center : Point) :
    PaddedMiddlePoint n p center → PaddedInnerPoint n p center → ℝ≥0∞ :=
  fun u z ↦ skeletonExitKernel
    (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
    u.1 z.1

/-- One remote cycle: first enter level `p`, then return to level `p - 1`,
before hitting the retained level-`l` boundary. -/
def paddedCycleKernelENNReal
    (n l p : ℕ) (center : Point) :
    PaddedMiddlePoint n p center → PaddedMiddlePoint n p center → ℝ≥0∞ :=
  annularCycleKernel
    (profileInnerBoundary n l center)
    (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center)
    (fun u : PaddedMiddlePoint n p center ↦ u.1)
    (fun z : PaddedInnerPoint n p center ↦ z.1)

/-- The final remote escape to the retained level-`l` endpoint. -/
def paddedEscapeKernelENNReal
    (n l p : ℕ) (center : Point) :
    PaddedMiddlePoint n p center → PaddedOuterPoint n l center → ℝ≥0∞ :=
  annularEscapeKernel
    (profileInnerBoundary n l center)
    (profileInnerBoundary n p center)
    (fun u ↦ u.1) (fun w ↦ w.1)

/-- The unmarked remote first-exit kernel. -/
def paddedUnmarkedKernelENNReal
    (n l p : ℕ) (center : Point) :
    PaddedMiddlePoint n p center → PaddedOuterPoint n l center → ℝ≥0∞ :=
  annularUnmarkedKernel
    (profileInnerBoundary n l center) (fun u ↦ u.1) (fun w ↦ w.1)

/-- The three padded boundaries are pairwise disjoint and every padded-inner
point must cross the middle boundary before reaching the retained outer
boundary. -/
theorem paddedRemoteRenewal_geometry
    {n l p : ℕ} (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (center : Point) :
    Disjoint (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) ∧
      Disjoint (profileInnerBoundary n p center)
        (profileInnerBoundary n l center) ∧
      Disjoint (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n l center) ∧
      ∀ z : PaddedInnerPoint n p center,
        FirstHitSeparates
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n l center) z.1 := by
  have hinnerMiddle :
      scaleRadius n p + 1 ≤ scaleRadius n (p - 1) :=
    scaleRadius_add_one_le_previous hn (by omega) (by omega)
  have hmiddleOuter :
      scaleRadius n (p - 1) + 1 ≤ scaleRadius n l := by
    have hadjacent :
        scaleRadius n (p - 1) + 1 ≤ scaleRadius n (p - 2) :=
      scaleRadius_add_one_le_previous hn (by omega) (by omega)
    exact hadjacent.trans
      (scaleRadius_antitone_of_le (by omega : l ≤ p - 2) (by omega))
  have hinnerOuter : scaleRadius n p + 1 ≤ scaleRadius n l :=
    hinnerMiddle.trans
      (le_trans (by linarith : scaleRadius n (p - 1) ≤
        scaleRadius n (p - 1) + 1) hmiddleOuter)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact discBoundaries_disjoint_of_separated center hinnerMiddle |>.symm
  · exact discBoundaries_disjoint_of_separated center hinnerOuter
  · exact discBoundaries_disjoint_of_separated center hmiddleOuter
  · intro z
    exact FirstHitSeparates.discBoundaries
      (mem_discBoundaryFinset.mp z.2)
      (scaleRadius_antitone_of_le (by omega : p - 1 ≤ p) hp)
      hmiddleOuter

/-- Splitting an original coarse bridge at its first visit to the padded
predecessor boundary is exact.  The first term covers bridges that exit
directly; every other bridge enters a padded middle state and then follows
the unrestricted remote continuation. -/
theorem paddedPreludeDirect_add_entry_unmarked_eq_nearUnmarked
    {n l p : ℕ} (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (center : Point) (start : PaddedNearPoint n l center)
    (w : PaddedOuterPoint n l center) :
    paddedPreludeDirectKernelENNReal n l p center start w +
        ∑ u : PaddedMiddlePoint n p center,
          paddedPreludeEntryKernelENNReal n l p center start u *
            paddedUnmarkedKernelENNReal n l p center u w =
      paddedNearUnmarkedKernelENNReal n l center start w := by
  obtain ⟨_hMiddleInner, _hInnerOuter, hMiddleOuter, _hseparates⟩ :=
    paddedRemoteRenewal_geometry hn hlp hp center
  let unionPoint :
      PaddedMiddlePoint n p center ⊕ PaddedOuterPoint n l center → Point :=
    Sum.elim (fun u ↦ u.1) (fun e ↦ e.1)
  have hunion : EnumeratesBoundary unionPoint
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) :=
    enumeratesBoundary_sum_union
      (enumeratesBoundary_boundaryFinsetPoint _ _)
      (enumeratesBoundary_boundaryFinsetPoint _ _) hMiddleOuter
  have hfirst := skeletonExitKernel_compose_finite
    (start := start.1) (endpoint := w.1)
    (FirstHitSeparates.of_subset
      (subset_union_right : profileInnerBoundary n l center ⊆
        profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center))
    hunion
  rw [Fintype.sum_sum_type] at hfirst
  have houterSum :
      (∑ e : PaddedOuterPoint n l center,
        skeletonExitKernel
            (profileInnerBoundary n (p - 1) center ∪
              profileInnerBoundary n l center) start.1 e.1 *
          skeletonExitKernel (profileInnerBoundary n l center) e.1 w.1) =
        skeletonExitKernel
          (profileInnerBoundary n (p - 1) center ∪
            profileInnerBoundary n l center) start.1 w.1 := by
    classical
    have hw : w.1 ∈ profileInnerBoundary n l center := by
      simpa only [profileInnerBoundary] using mem_discBoundaryFinset.mp w.2
    rw [Finset.sum_eq_single w]
    · rw [skeletonExitKernel_self hw, mul_one]
    · intro e _ hew
      have hpointNe : w.1 ≠ e.1 := by
        intro heq
        exact hew (Subtype.ext heq.symm)
      have he : e.1 ∈ profileInnerBoundary n l center := by
        simpa only [profileInnerBoundary] using mem_discBoundaryFinset.mp e.2
      rw [skeletonExitKernel_eq_zero_of_boundary_start_ne
          he hpointNe, mul_zero]
    · simp
  change skeletonExitKernel (profileInnerBoundary n l center) start.1 w.1 =
      (∑ u : PaddedMiddlePoint n p center,
        skeletonExitKernel
            (profileInnerBoundary n (p - 1) center ∪
              profileInnerBoundary n l center) start.1 u.1 *
          skeletonExitKernel (profileInnerBoundary n l center) u.1 w.1) +
        ∑ e : PaddedOuterPoint n l center,
          skeletonExitKernel
              (profileInnerBoundary n (p - 1) center ∪
                profileInnerBoundary n l center) start.1 e.1 *
            skeletonExitKernel (profileInnerBoundary n l center) e.1 w.1 at hfirst
  change skeletonExitKernel
          (profileInnerBoundary n (p - 1) center ∪
            profileInnerBoundary n l center) start.1 w.1 +
        ∑ u : PaddedMiddlePoint n p center,
          skeletonExitKernel
              (profileInnerBoundary n (p - 1) center ∪
                profileInnerBoundary n l center) start.1 u.1 *
            skeletonExitKernel (profileInnerBoundary n l center) u.1 w.1 =
      skeletonExitKernel (profileInnerBoundary n l center) start.1 w.1
  rw [← houterSum]
  calc
    _ = (∑ u : PaddedMiddlePoint n p center,
          skeletonExitKernel
              (profileInnerBoundary n (p - 1) center ∪
                profileInnerBoundary n l center) start.1 u.1 *
            skeletonExitKernel (profileInnerBoundary n l center) u.1 w.1) +
        ∑ e : PaddedOuterPoint n l center,
          skeletonExitKernel
              (profileInnerBoundary n (p - 1) center ∪
                profileInnerBoundary n l center) start.1 e.1 *
            skeletonExitKernel (profileInnerBoundary n l center) e.1 w.1 :=
      add_comm _ _
    _ = _ := hfirst.symm

/-- Exact identification of the padded excursion-count bridge with its
finite-state remote renewal. -/
theorem boundaryExcursionExitKernel_eq_paddedRenewal
    {n l p : ℕ} (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (center : Point) (a : ℕ) (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center) :
    boundaryExcursionExitKernel
        (profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) u.1 a w.1 =
      markedOffspringKernelENNReal
        (paddedCycleKernelENNReal n l p center)
        (paddedEscapeKernelENNReal n l p center) a u w := by
  obtain ⟨hMiddleInner, hInnerOuter, hMiddleOuter, hseparates⟩ :=
    paddedRemoteRenewal_geometry hn hlp hp center
  simpa only [paddedCycleKernelENNReal, paddedEscapeKernelENNReal] using
    boundaryExcursionExitKernel_eq_markedOffspringKernelENNReal
    (profileInnerBoundary n l center)
    (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center)
    (fun z : PaddedMiddlePoint n p center ↦ z.1)
    (fun z : PaddedInnerPoint n p center ↦ z.1)
    (fun z : PaddedOuterPoint n l center ↦ z.1)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    hMiddleInner hInnerOuter hMiddleOuter hseparates a u w

@[simp] theorem paddedUnmarkedKernelENNReal_eq
    (n l p : ℕ) (center : Point)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center) :
    paddedUnmarkedKernelENNReal n l p center u w =
      skeletonExitKernel (profileInnerBoundary n l center) u.1 w.1 := by
  rfl

/-- The logarithmic padding makes the unmarked remote continuation nearly
independent of its level-`p - 1` starting point, uniformly in the retained
outer endpoint. -/
theorem paddedUnmarkedKernelENNReal_le_budget
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 1 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point)
    (u v : PaddedMiddlePoint q (pairPrefixScale q l) center)
    (w : PaddedOuterPoint q l center) :
    paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
        center v w ≤
      ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) *
        paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
          center u w := by
  have hweighted := weightedBoundaryExitMass_le_budget hq hl hpadding
    hpadPos hconstant center {w.1} (fun _ ↦ 1)
    (by
      intro exit hexit
      simp only [Finset.mem_singleton] at hexit
      subst exit
      exact mem_discBoundaryFinset.mp w.2)
    (mem_discBoundaryFinset.mp u.2)
    (mem_discBoundaryFinset.mp v.2)
  simpa only [paddedUnmarkedKernelENNReal,
    AnnularOffspringKernel.annularUnmarkedKernel,
    RealRadiusPoissonEndpoint.weightedBoundaryExitMass,
    profileInnerBoundary, Finset.sum_singleton, one_mul] using hweighted

/-- One padded cycle followed by an arbitrary unmarked remote continuation
is a subrow of the same unmarked continuation. -/
theorem paddedLeafCycle_eq_cycleKernel
    {n l p : ℕ} (center : Point)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center) :
    (∑ z : PaddedInnerPoint n p center,
      paddedInwardKernelENNReal n l p center u z *
        ∑ v : PaddedMiddlePoint n p center,
          recursiveProfileGapKernelENNReal n p center .leaf z v *
            paddedUnmarkedKernelENNReal n l p center v w) =
      ∑ v : PaddedMiddlePoint n p center,
        paddedCycleKernelENNReal n l p center u v *
          paddedUnmarkedKernelENNReal n l p center v w := by
  simp only [paddedInwardKernelENNReal, paddedCycleKernelENNReal,
    recursiveProfileGapKernelENNReal, profileOuterBoundary,
    annularCycleKernel]
  calc
    (∑ z : PaddedInnerPoint n p center,
        skeletonExitKernel
            (profileInnerBoundary n p center ∪
              profileInnerBoundary n l center) u.1 z.1 *
          ∑ v : PaddedMiddlePoint n p center,
            skeletonExitKernel (profileInnerBoundary n (p - 1) center)
                z.1 v.1 *
              paddedUnmarkedKernelENNReal n l p center v w) =
        ∑ z : PaddedInnerPoint n p center,
          ∑ v : PaddedMiddlePoint n p center,
            skeletonExitKernel
                (profileInnerBoundary n p center ∪
                  profileInnerBoundary n l center) u.1 z.1 *
              (skeletonExitKernel (profileInnerBoundary n (p - 1) center)
                  z.1 v.1 *
                paddedUnmarkedKernelENNReal n l p center v w) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.mul_sum]
    _ = ∑ v : PaddedMiddlePoint n p center,
          ∑ z : PaddedInnerPoint n p center,
            skeletonExitKernel
                (profileInnerBoundary n p center ∪
                  profileInnerBoundary n l center) u.1 z.1 *
              (skeletonExitKernel (profileInnerBoundary n (p - 1) center)
                  z.1 v.1 *
                paddedUnmarkedKernelENNReal n l p center v w) := by
          rw [Finset.sum_comm]
    _ = ∑ v : PaddedMiddlePoint n p center,
          (∑ z : PaddedInnerPoint n p center,
            skeletonExitKernel
                (profileInnerBoundary n p center ∪
                  profileInnerBoundary n l center) u.1 z.1 *
              skeletonExitKernel (profileInnerBoundary n (p - 1) center)
                z.1 v.1) *
            paddedUnmarkedKernelENNReal n l p center v w := by
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z _
          ac_rfl

theorem paddedCycle_unmarked_le
    {n l p : ℕ} (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (center : Point) (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center) :
    (∑ z : PaddedInnerPoint n p center,
      paddedInwardKernelENNReal n l p center u z *
        ∑ v : PaddedMiddlePoint n p center,
          recursiveProfileGapKernelENNReal n p center .leaf z v *
            paddedUnmarkedKernelENNReal n l p center v w) ≤
      paddedUnmarkedKernelENNReal n l p center u w := by
  obtain ⟨hMiddleInner, hInnerOuter, _hMiddleOuter, hseparates⟩ :=
    paddedRemoteRenewal_geometry hn hlp hp center
  have hrenew := annularKernel_renewal_ennreal
    (profileInnerBoundary n l center)
    (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center)
    (fun v : PaddedMiddlePoint n p center ↦ v.1)
    (fun z : PaddedInnerPoint n p center ↦ z.1)
    (fun e : PaddedOuterPoint n l center ↦ e.1)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    hInnerOuter hseparates u w
  rw [paddedLeafCycle_eq_cycleKernel]
  calc
    (∑ v : PaddedMiddlePoint n p center,
        paddedCycleKernelENNReal n l p center u v *
          paddedUnmarkedKernelENNReal n l p center v w) ≤
        paddedEscapeKernelENNReal n l p center u w +
          ∑ v : PaddedMiddlePoint n p center,
            paddedCycleKernelENNReal n l p center u v *
              paddedUnmarkedKernelENNReal n l p center v w := by
          exact le_add_left le_rfl
    _ = paddedUnmarkedKernelENNReal n l p center u w := by
          simpa only [paddedUnmarkedKernelENNReal,
            paddedEscapeKernelENNReal, paddedCycleKernelENNReal] using
              hrenew.symm

/-- The escape branch together with one unrestricted leaf cycle is exactly
the unmarked remote renewal row. -/
theorem paddedEscape_add_leafCycle_eq_unmarked
    {n l p : ℕ} (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (center : Point) (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center) :
    paddedEscapeKernelENNReal n l p center u w +
        ∑ z : PaddedInnerPoint n p center,
          paddedInwardKernelENNReal n l p center u z *
            ∑ v : PaddedMiddlePoint n p center,
              recursiveProfileGapKernelENNReal n p center .leaf z v *
                paddedUnmarkedKernelENNReal n l p center v w =
      paddedUnmarkedKernelENNReal n l p center u w := by
  obtain ⟨_hMiddleInner, hInnerOuter, _hMiddleOuter, hseparates⟩ :=
    paddedRemoteRenewal_geometry hn hlp hp center
  have hrenew := annularKernel_renewal_ennreal
    (profileInnerBoundary n l center)
    (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center)
    (fun v : PaddedMiddlePoint n p center ↦ v.1)
    (fun z : PaddedInnerPoint n p center ↦ z.1)
    (fun e : PaddedOuterPoint n l center ↦ e.1)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    hInnerOuter hseparates u w
  rw [paddedLeafCycle_eq_cycleKernel]
  simpa only [paddedUnmarkedKernelENNReal,
    paddedEscapeKernelENNReal, paddedCycleKernelENNReal] using hrenew.symm

/-- The direct escape term is one summand of the unmarked remote renewal. -/
theorem paddedEscapeKernelENNReal_le_unmarked
    {n l p : ℕ} (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (center : Point) (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center) :
    paddedEscapeKernelENNReal n l p center u w ≤
      paddedUnmarkedKernelENNReal n l p center u w := by
  obtain ⟨_hMiddleInner, hInnerOuter, _hMiddleOuter, hseparates⟩ :=
    paddedRemoteRenewal_geometry hn hlp hp center
  have hrenew := annularKernel_renewal_ennreal
    (profileInnerBoundary n l center)
    (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center)
    (fun v : PaddedMiddlePoint n p center ↦ v.1)
    (fun z : PaddedInnerPoint n p center ↦ z.1)
    (fun e : PaddedOuterPoint n l center ↦ e.1)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    (enumeratesBoundary_boundaryFinsetPoint _ _)
    hInnerOuter hseparates u w
  calc
    paddedEscapeKernelENNReal n l p center u w ≤
        paddedEscapeKernelENNReal n l p center u w +
          ∑ v : PaddedMiddlePoint n p center,
            paddedCycleKernelENNReal n l p center u v *
              paddedUnmarkedKernelENNReal n l p center v w := by
          exact le_add_right le_rfl
    _ = paddedUnmarkedKernelENNReal n l p center u w := by
          simpa only [paddedUnmarkedKernelENNReal,
            paddedEscapeKernelENNReal, paddedCycleKernelENNReal] using
              hrenew.symm

/-- On the finite padded predecessor boundary, the remote continuation has
a least value; endpoint Harnack compares every other value to it. -/
theorem paddedUnmarkedKernelENNReal_reference
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 1 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (w : PaddedOuterPoint q l center) :
    ∃ reference : ℝ≥0∞,
      (∀ v : PaddedMiddlePoint q (pairPrefixScale q l) center,
        reference ≤ paddedUnmarkedKernelENNReal q l
          (pairPrefixScale q l) center v w) ∧
      (∀ v : PaddedMiddlePoint q (pairPrefixScale q l) center,
        paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center v w ≤
          ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) * reference) := by
  have hboundary :
      (profileInnerBoundary q (pairPrefixScale q l - 1) center).Nonempty := by
    unfold profileInnerBoundary
    exact ProfileAnnularRowRegular.discBoundary_center_nonempty_of_nonneg center
      (AppendixPair.scaleRadius_nonneg _ _)
  obtain ⟨point, hpoint⟩ := hboundary
  let seed : PaddedMiddlePoint q (pairPrefixScale q l) center :=
    ⟨point, mem_discBoundaryFinset.mpr hpoint⟩
  obtain ⟨minimum, _hminimumMem, hminimum⟩ :=
    Finset.exists_min_image Finset.univ
      (fun v : PaddedMiddlePoint q (pairPrefixScale q l) center ↦
        paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center v w)
      ⟨seed, Finset.mem_univ seed⟩
  refine ⟨paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
      center minimum w, ?_, ?_⟩
  · intro v
    exact hminimum v (Finset.mem_univ v)
  · intro v
    exact paddedUnmarkedKernelENNReal_le_budget hq hl hpadding hpadPos
      hconstant center minimum v w

/-- Recursive children at the padded cut can be substituted inside the
remote annular renewal.  All later offspring counts are absorbed into the
unmarked exit kernel, so endpoint distortion is paid exactly once per
top-level child. -/
theorem heterogeneousRecursivePaddedRenewalKernel_le_unmarked
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (loss : ProfileRefinementTree → ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
        center tree z v ≤ loss tree)
    (trees : List ProfileRefinementTree)
    (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
    (w : PaddedOuterPoint q l center) :
    heterogeneousRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        trees u w ≤
      (trees.map loss).prod *
        ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ trees.length *
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center u w := by
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le
      (Nat.add_le_of_le_sub hpadding hl)
  have hlp : l + 1 < pairPrefixScale q l := by omega
  have hpq : pairPrefixScale q l ≤ q := by
    rw [hpref]
    exact Nat.add_le_of_le_sub hpadding hl
  apply heterogeneousRenewalKernel_le_envelope
    (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
    (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
    (fun _ z v ↦ recursiveProfileGapKernelENNReal q
      (pairPrefixScale q l) center .leaf z v)
    (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
    (paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center)
    loss (ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)))
  · intro tree z exit
    obtain ⟨reference, hlower, hupper⟩ :=
      paddedUnmarkedKernelENNReal_reference hq hl hpadding (by omega)
        hconstant center exit
    exact weighted_recursiveProfileGapKernelENNReal_le z
      (fun v ↦ paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
        center v exit)
      reference (loss tree)
      (ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)))
      (hrow tree z) hlower hupper
  · exact paddedEscapeKernelENNReal_le_unmarked (by omega) hlp hpq center
  · intro _tree start exit
    exact paddedCycle_unmarked_le (by omega) hlp hpq center start exit

/-- Constrained profile populations contain at most `3 q²` children, so the
entire remote endpoint distortion is absorbed by the reserved half-unit
exponential budget. -/
theorem heterogeneousRecursivePaddedRenewalKernel_le_expHalf_unmarked
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (loss : ProfileRefinementTree → ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
        center tree z v ≤ loss tree)
    (trees : List ProfileRefinementTree)
    (hpopulation : trees.length ≤ 3 * q ^ 2)
    (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
    (w : PaddedOuterPoint q l center) :
    heterogeneousRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        trees u w ≤
      (trees.map loss).prod * ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center u w := by
  calc
    heterogeneousRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        trees u w ≤
      (trees.map loss).prod *
        ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ trees.length *
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center u w :=
        heterogeneousRecursivePaddedRenewalKernel_le_unmarked
          hq hl hpadding hpadPos hconstant center loss hrow trees u w
    _ ≤ (trees.map loss).prod *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center u w := by
      gcongr
      exact endpointDistortion_pow_le_expHalf (by omega) hpopulation

/-- Recursive children distributed chronologically among several padded
remote segments.  The exact escape-plus-leaf renewal identity is used at
each segment, so there is no loss for the number of weak allocations of the
global child list among those segments. -/
theorem heterogeneousMultiRecursivePaddedRenewalKernel_le_unmarked
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (loss : ProfileRefinementTree → ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
        center tree z v ≤ loss tree)
    (trees : List ProfileRefinementTree)
    (segments : List
      (PaddedMiddlePoint q (pairPrefixScale q l) center ×
        PaddedOuterPoint q l center)) :
    heterogeneousMultiRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments trees ≤
      (trees.map loss).prod *
        ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ trees.length *
          (segments.map fun segment ↦
            paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
              center segment.1 segment.2).prod := by
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le
      (Nat.add_le_of_le_sub hpadding hl)
  have hlp : l + 1 < pairPrefixScale q l := by omega
  have hpq : pairPrefixScale q l ≤ q := by
    rw [hpref]
    exact Nat.add_le_of_le_sub hpadding hl
  apply heterogeneousMultiRenewalKernel_le_envelope
    (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
    (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
    (fun _ z v ↦ recursiveProfileGapKernelENNReal q
      (pairPrefixScale q l) center .leaf z v)
    (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
    (paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center)
    loss (ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)))
  · intro tree z exit
    obtain ⟨reference, hlower, hupper⟩ :=
      paddedUnmarkedKernelENNReal_reference hq hl hpadding (by omega)
        hconstant center exit
    exact weighted_recursiveProfileGapKernelENNReal_le z
      (fun v ↦ paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
        center v exit)
      reference (loss tree)
      (ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)))
      (hrow tree z) hlower hupper
  · exact paddedEscapeKernelENNReal_le_unmarked (by omega) hlp hpq center
  · intro _tree start exit
    exact (paddedEscape_add_leafCycle_eq_unmarked
      (by omega) hlp hpq center start exit).le

/-- The multi-segment padded renewal also fits in the reserved half-unit
exponential budget when the global child population is at most `3 q²`. -/
theorem heterogeneousMultiRecursivePaddedRenewalKernel_le_expHalf_unmarked
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (loss : ProfileRefinementTree → ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
        center tree z v ≤ loss tree)
    (trees : List ProfileRefinementTree)
    (hpopulation : trees.length ≤ 3 * q ^ 2)
    (segments : List
      (PaddedMiddlePoint q (pairPrefixScale q l) center ×
        PaddedOuterPoint q l center)) :
    heterogeneousMultiRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments trees ≤
      (trees.map loss).prod * ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        (segments.map fun segment ↦
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
            center segment.1 segment.2).prod := by
  calc
    heterogeneousMultiRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments trees ≤
      (trees.map loss).prod *
        ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ trees.length *
          (segments.map fun segment ↦
            paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
              center segment.1 segment.2).prod :=
        heterogeneousMultiRecursivePaddedRenewalKernel_le_unmarked
          hq hl hpadding hpadPos hconstant center loss hrow trees segments
    _ ≤ (trees.map loss).prod * ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        (segments.map fun segment ↦
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
            center segment.1 segment.2).prod := by
      gcongr
      exact endpointDistortion_pow_le_expHalf (by omega) hpopulation

/-- Several retained coarse bridges may start before the padded boundary.
The direct-exit/entrance split is exact, and all bridges share the same
chronological recursive child list. -/
theorem heterogeneousPreludeMultiRecursivePaddedRenewalKernel_le_unmarked
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (loss : ProfileRefinementTree → ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
        center tree z v ≤ loss tree)
    (trees : List ProfileRefinementTree)
    (segments : List
      ((PaddedNearPoint q l center ⊕
          PaddedMiddlePoint q (pairPrefixScale q l) center) ×
        PaddedOuterPoint q l center)) :
    heterogeneousPreludeMultiRenewalKernel
        (paddedPreludeEntryKernelENNReal q l (pairPrefixScale q l) center)
        (paddedPreludeDirectKernelENNReal q l (pairPrefixScale q l) center)
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments trees ≤
      (trees.map loss).prod *
        ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ trees.length *
          (segments.map fun segment ↦ match segment.1 with
            | Sum.inl start =>
                paddedNearUnmarkedKernelENNReal q l center start segment.2
            | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                  center u segment.2).prod := by
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le
      (Nat.add_le_of_le_sub hpadding hl)
  have hlp : l + 1 < pairPrefixScale q l := by omega
  have hpq : pairPrefixScale q l ≤ q := by
    rw [hpref]
    exact Nat.add_le_of_le_sub hpadding hl
  convert heterogeneousPreludeMultiRenewalKernel_le_envelope
    (paddedPreludeEntryKernelENNReal q l (pairPrefixScale q l) center)
    (paddedPreludeDirectKernelENNReal q l (pairPrefixScale q l) center)
    (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
    (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
    (fun _ z v ↦ recursiveProfileGapKernelENNReal q
      (pairPrefixScale q l) center .leaf z v)
    (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
    (paddedNearUnmarkedKernelENNReal q l center)
    (paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center)
    loss (ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)))
    ?_ ?_ ?_ ?_ trees segments using 1
  · congr 1
    induction segments with
    | nil => rfl
    | cons segment segments ih =>
        rcases segment with ⟨stage, exit⟩
        cases stage <;>
          simp only [List.map_cons, List.prod_cons, ih]
  · intro tree z exit
    obtain ⟨reference, hlower, hupper⟩ :=
      paddedUnmarkedKernelENNReal_reference hq hl hpadding (by omega)
        hconstant center exit
    exact weighted_recursiveProfileGapKernelENNReal_le z
      (fun v ↦ paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
        center v exit)
      reference (loss tree)
      (ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)))
      (hrow tree z) hlower hupper
  · exact paddedEscapeKernelENNReal_le_unmarked (by omega) hlp hpq center
  · intro _tree start exit
    exact (paddedEscape_add_leafCycle_eq_unmarked
      (by omega) hlp hpq center start exit).le
  · intro start exit
    exact (paddedPreludeDirect_add_entry_unmarked_eq_nearUnmarked
      (by omega) hlp hpq center start exit).le

/-- The preliminary-entrance multi-bridge renewal fits in the same reserved
half-unit endpoint-distortion budget. -/
theorem heterogeneousPreludeMultiRecursivePaddedRenewalKernel_le_expHalf_unmarked
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (center : Point) (loss : ProfileRefinementTree → ℝ≥0∞)
    (hrow : ∀ (tree : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
        center tree z v ≤ loss tree)
    (trees : List ProfileRefinementTree)
    (hpopulation : trees.length ≤ 3 * q ^ 2)
    (segments : List
      ((PaddedNearPoint q l center ⊕
          PaddedMiddlePoint q (pairPrefixScale q l) center) ×
        PaddedOuterPoint q l center)) :
    heterogeneousPreludeMultiRenewalKernel
        (paddedPreludeEntryKernelENNReal q l (pairPrefixScale q l) center)
        (paddedPreludeDirectKernelENNReal q l (pairPrefixScale q l) center)
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments trees ≤
      (trees.map loss).prod * ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        (segments.map fun segment ↦ match segment.1 with
          | Sum.inl start =>
              paddedNearUnmarkedKernelENNReal q l center start segment.2
          | Sum.inr u =>
              paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                center u segment.2).prod := by
  calc
    _ ≤ (trees.map loss).prod *
        ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ trees.length *
          (segments.map fun segment ↦ match segment.1 with
            | Sum.inl start =>
                paddedNearUnmarkedKernelENNReal q l center start segment.2
            | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                  center u segment.2).prod :=
      heterogeneousPreludeMultiRecursivePaddedRenewalKernel_le_unmarked
        hq hl hpadding hpadPos hconstant center loss hrow trees segments
    _ ≤ _ := by
      gcongr
      exact endpointDistortion_pow_le_expHalf (by omega) hpopulation

end

end Erdos1165.AsymmetricPaddedRemoteRenewal
