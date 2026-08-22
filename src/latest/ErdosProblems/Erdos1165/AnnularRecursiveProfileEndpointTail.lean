/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveConstrainedProfileTailUpper

/-!
# Endpoint-retaining recursive profile tails

The recursive Appendix-A.6 estimate integrates the outer endpoint of every
gap.  At the padded asymmetric interface those endpoints must remain visible
until the retained outer prefix has been attached.  This file exposes the
finite endpoint vector and proves that summing it recovers exactly the
already-checked recursive row.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRecursiveProfileEndpointTail

open AnnularOffspringKernelRadial AnnularProfileClocks
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileShape AnnularRecursiveProfileTailUpper
open AnnularLiteralNestedProfileTailUpper
open AnnularRecursiveConstrainedProfileTailUpper
open AppendixFirstMoment AppendixPair AppendixPairMoment
open AsymmetricActualFarPairData PathInsertion ProfileGapChain
open ProfileConditionalTailUpper ProfileListExponent ProfileSmallBall
open ProfileWeightUpper Proposition13Scales ThickPoint

noncomputable section

/-- The mass of one fixed refinement chain with all top-level outer
endpoints retained. -/
def recursiveProfileGapChainEndpointKernel
    (n start : ℕ) (center : Point) (a : ℕ) (rest : List ℕ)
    (entrance : Fin a → ProfileCycleMiddlePoint n start center)
    (endpoint : Fin a → ProfileCycleOuterPoint n start center)
    (chain : GapChain (a :: rest)) : ℝ≥0∞ :=
  ∏ i : Fin a,
    recursiveProfileGapKernelENNReal n start center
      (profileRefinementTrees a rest chain i) (entrance i) (endpoint i)

/-- Sum over every weak-composition genealogy, still retaining the vector of
outer endpoints of the top-level gaps. -/
def recursiveProfileEndpointRow
    (n start : ℕ) (center : Point) (a : ℕ) (rest : List ℕ)
    (entrance : Fin a → ProfileCycleMiddlePoint n start center)
    (endpoint : Fin a → ProfileCycleOuterPoint n start center) : ℝ≥0∞ :=
  ∑ chain : GapChain (a :: rest),
    recursiveProfileGapChainEndpointKernel
      n start center a rest entrance endpoint chain

/-- Finite Tonelli: integrating the retained endpoint vector is exactly the
product of the endpoint-integrated recursive rows. -/
theorem sum_recursiveProfileGapChainEndpointKernel_eq
    (n start : ℕ) (center : Point) (a : ℕ) (rest : List ℕ)
    (entrance : Fin a → ProfileCycleMiddlePoint n start center)
    (chain : GapChain (a :: rest)) :
    (∑ endpoint : Fin a → ProfileCycleOuterPoint n start center,
      recursiveProfileGapChainEndpointKernel
        n start center a rest entrance endpoint chain) =
      ∏ i : Fin a,
        ∑ w, recursiveProfileGapKernelENNReal n start center
          (profileRefinementTrees a rest chain i) (entrance i) w := by
  unfold recursiveProfileGapChainEndpointKernel
  exact (Fintype.prod_sum (fun (i : Fin a)
    (w : ProfileCycleOuterPoint n start center) ↦
      recursiveProfileGapKernelENNReal n start center
        (profileRefinementTrees a rest chain i) (entrance i) w)).symm

/-- Summing the endpoint-retaining row gives the row occurring in
`eventually_recursiveProfileGapChainRows_le`. -/
theorem sum_recursiveProfileEndpointRow_eq
    (n start : ℕ) (center : Point) (a : ℕ) (rest : List ℕ)
    (entrance : Fin a → ProfileCycleMiddlePoint n start center) :
    (∑ endpoint : Fin a → ProfileCycleOuterPoint n start center,
      recursiveProfileEndpointRow
        n start center a rest entrance endpoint) =
      ∑ chain : GapChain (a :: rest),
        ∏ i : Fin a,
          ∑ w, recursiveProfileGapKernelENNReal n start center
            (profileRefinementTrees a rest chain i) (entrance i) w := by
  unfold recursiveProfileEndpointRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro chain _
  exact sum_recursiveProfileGapChainEndpointKernel_eq
    n start center a rest entrance chain

/-- The existing recursive profile-tail estimate with the top-level outer
endpoint vector exposed and then integrated. -/
theorem eventually_sum_recursiveProfileEndpointRow_le :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ) (m : Profile n),
      IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (start : ℕ), 2 ≤ start → start ≤ n →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m start = a :: rest →
      ∀ entrance : Fin a → ProfileCycleMiddlePoint n start center,
        (∑ endpoint : Fin a → ProfileCycleOuterPoint n start center,
          recursiveProfileEndpointRow
            n start center a rest entrance endpoint) ≤
          ENNReal.ofReal (Real.exp 1 *
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
  filter_upwards [eventually_recursiveProfileGapChainRows_le]
      with n hrow
  intro center delta m hm hdelta start hstart hstartn a rest hvalues entrance
  rw [sum_recursiveProfileEndpointRow_eq]
  exact hrow center delta m hm hdelta start hstart hstartn
    a rest hvalues entrance

/-- Endpoint-retaining form of the sharpened half-exponential recursive
row estimate. -/
theorem eventually_sum_recursiveProfileEndpointRow_le_expHalf :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ) (m : Profile n),
      IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (start : ℕ), 2 ≤ start → start ≤ n →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m start = a :: rest →
      ∀ entrance : Fin a → ProfileCycleMiddlePoint n start center,
        (∑ endpoint : Fin a → ProfileCycleOuterPoint n start center,
          recursiveProfileEndpointRow
            n start center a rest entrance endpoint) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
  filter_upwards [eventually_recursiveProfileGapChainRows_le_expHalf]
      with n hrow
  intro center delta m hm hdelta start hstart hstartn a rest hvalues entrance
  rw [sum_recursiveProfileEndpointRow_eq]
  exact hrow center delta m hm hdelta start hstart hstartn
    a rest hvalues entrance

/-- The segment list starts with the profile value at its retained scale. -/
theorem profileSegmentValues_eq_head_cons_tail
    {n start : ℕ} (hstartn : start ≤ n) (m : Profile n) :
    profileSegmentValues m start =
      profileAtScale m start :: (profileSegmentValues m start).tail := by
  have hlength : n + 1 - start = (n - start) + 1 := by omega
  unfold profileSegmentValues
  rw [hlength, List.ofFn_succ]
  simp

/-- Sum the endpoint-retaining recursive rows over every constrained full
profile extending one exact retained prefix.  The endpoint vector has the
fixed population recorded by that prefix. -/
theorem eventually_sum_fixedPrefix_recursiveProfileEndpointRows_le :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ), delta ≤ 1 →
      ∀ (start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n),
      ∀ (pref : Profile start),
      ∀ entrance : Fin (profileAtScale pref start) →
          ProfileCycleMiddlePoint n start center,
        (∑ m ∈ (constrainedProfiles n delta).filter
            (fun m ↦ profilePrefix hstart hstartn m = pref),
          ∑ endpoint : Fin (profileAtScale pref start) →
              ProfileCycleOuterPoint n start center,
            recursiveProfileEndpointRow n start center
              (profileAtScale pref start)
              (profileSegmentValues m start).tail entrance endpoint) ≤
          ENNReal.ofReal (Real.exp 1 *
            constrainedProfileTailWeight n start hstart hstartn
              pref delta) := by
  filter_upwards [eventually_sum_recursiveProfileEndpointRow_le]
      with n hendpoint
  intro center delta hdelta start hstart hstartn pref entrance
  apply sum_fixedPrefix_rows_le_expOne_constrainedProfileTailWeight
    hstart hstartn pref delta
  intro m hm
  have hmConstrained : IsConstrainedProfile delta m :=
    mem_constrainedProfiles.mp (Finset.mem_filter.mp hm).1
  have hprefix : profilePrefix hstart hstartn m = pref :=
    (Finset.mem_filter.mp hm).2
  have hhead : profileAtScale m start = profileAtScale pref start := by
    rw [← hprefix, profileAtScale_profilePrefix hstart hstartn]
  have hvalues : profileSegmentValues m start =
      profileAtScale pref start :: (profileSegmentValues m start).tail := by
    calc
      profileSegmentValues m start =
          profileAtScale m start :: (profileSegmentValues m start).tail :=
        profileSegmentValues_eq_head_cons_tail hstartn m
      _ = profileAtScale pref start ::
          (profileSegmentValues m start).tail := by rw [hhead]
  exact hendpoint center delta m hmConstrained hdelta start hstart hstartn
    (profileAtScale pref start) (profileSegmentValues m start).tail hvalues
      entrance

/-- Sum the endpoint-retaining recursive rows over constrained profile
extensions while reserving half of the exponential budget for the outer
prefix. -/
theorem eventually_sum_fixedPrefix_recursiveProfileEndpointRows_le_expHalf :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ), delta ≤ 1 →
      ∀ (start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n),
      ∀ (pref : Profile start),
      ∀ entrance : Fin (profileAtScale pref start) →
          ProfileCycleMiddlePoint n start center,
        (∑ m ∈ (constrainedProfiles n delta).filter
            (fun m ↦ profilePrefix hstart hstartn m = pref),
          ∑ endpoint : Fin (profileAtScale pref start) →
              ProfileCycleOuterPoint n start center,
            recursiveProfileEndpointRow n start center
              (profileAtScale pref start)
              (profileSegmentValues m start).tail entrance endpoint) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            constrainedProfileTailWeight n start hstart hstartn
              pref delta) := by
  filter_upwards [eventually_sum_recursiveProfileEndpointRow_le_expHalf]
      with n hendpoint
  intro center delta hdelta start hstart hstartn pref entrance
  apply sum_fixedPrefix_rows_le_expHalf_constrainedProfileTailWeight
    hstart hstartn pref delta
  intro m hm
  have hmConstrained : IsConstrainedProfile delta m :=
    mem_constrainedProfiles.mp (Finset.mem_filter.mp hm).1
  have hprefix : profilePrefix hstart hstartn m = pref :=
    (Finset.mem_filter.mp hm).2
  have hhead : profileAtScale m start = profileAtScale pref start := by
    rw [← hprefix, profileAtScale_profilePrefix hstart hstartn]
  have hvalues : profileSegmentValues m start =
      profileAtScale pref start :: (profileSegmentValues m start).tail := by
    calc
      profileSegmentValues m start =
          profileAtScale m start :: (profileSegmentValues m start).tail :=
        profileSegmentValues_eq_head_cons_tail hstartn m
      _ = profileAtScale pref start ::
          (profileSegmentValues m start).tail := by rw [hhead]
  exact hendpoint center delta m hmConstrained hdelta start hstart hstartn
    (profileAtScale pref start) (profileSegmentValues m start).tail hvalues
      entrance

/-- At the selected Proposition 1.3 scales, the endpoint-retaining recursive
tail has exactly the canonical padded radial-tail bound. -/
theorem eventually_sum_paddedPrefix_recursiveProfileEndpointRows_le
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop, ∀ (center x y : Point)
      (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
        pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)),
      ∀ (pref : Profile (pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))),
      ∀ entrance : Fin (profileAtScale pref
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y))) →
          ProfileCycleMiddlePoint (scaleIndex delta blockIndex)
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y)) center,
        (∑ m ∈ (constrainedProfiles (scaleIndex delta blockIndex)
            profileUpperDelta).filter (fun m ↦
              profilePrefix
                ((show 2 ≤ profileUpperTailStart by
                    norm_num [profileUpperTailStart]).trans
                  (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
                (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
                m = pref),
          ∑ endpoint : Fin (profileAtScale pref
                (pairPrefixScale (scaleIndex delta blockIndex)
                  (separationLevel (scaleIndex delta blockIndex) x y))) →
              ProfileCycleOuterPoint (scaleIndex delta blockIndex)
                (pairPrefixScale (scaleIndex delta blockIndex)
                  (separationLevel (scaleIndex delta blockIndex) x y)) center,
            recursiveProfileEndpointRow
              (scaleIndex delta blockIndex)
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y)) center
              (profileAtScale pref
                (pairPrefixScale (scaleIndex delta blockIndex)
                  (separationLevel (scaleIndex delta blockIndex) x y)))
              (profileSegmentValues m
                (pairPrefixScale (scaleIndex delta blockIndex)
                  (separationLevel (scaleIndex delta blockIndex) x y))).tail
              entrance endpoint) ≤
          ENNReal.ofReal
            (ProfileRadialTailCertificate.expOne hcutoff).radialTail := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hrows := hscaleNat.eventually
    eventually_sum_fixedPrefix_recursiveProfileEndpointRows_le
  filter_upwards [hrows] with blockIndex hrow
  intro center x y hcutoff pref entrance
  let certificate : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne hcutoff
  let start := pairPrefixScale (scaleIndex delta blockIndex)
    (separationLevel (scaleIndex delta blockIndex) x y)
  let hstart : 2 ≤ start :=
    (show 2 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans certificate.tailStart
  have hsum := hrow center profileUpperDelta
    (by norm_num [profileUpperDelta]) start hstart
      certificate.start_le_scale pref entrance
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1 *
        constrainedProfileTailWeight (scaleIndex delta blockIndex) start
          hstart certificate.start_le_scale pref profileUpperDelta) := by
      simpa only [certificate, start, hstart] using hsum
    _ ≤ ENNReal.ofReal certificate.radialTail := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [certificate, ProfileRadialTailCertificate.expOne,
        ProfileRadialTailCertificate.of_geometricCutoff] using
          certificate.coefficient_mul_constrainedTail_le pref
    _ = ENNReal.ofReal
        (ProfileRadialTailCertificate.expOne hcutoff).radialTail := by
      rfl

end

end Erdos1165.AnnularRecursiveProfileEndpointTail
