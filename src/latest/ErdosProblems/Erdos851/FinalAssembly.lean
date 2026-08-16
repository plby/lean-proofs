/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.DyadicDensity
import ErdosProblems.Erdos851.EndpointBridge
import ErdosProblems.Erdos851.EulerMass
import ErdosProblems.Erdos851.MomentEstimate
import ErdosProblems.Erdos851.ScaleErrors
import ErdosProblems.Erdos851.SingularAverage

/-!
# Final assembly for Erdős problem 851

This file deliberately isolates the one remaining beta-sieve input.  Its
statement is already specialized to the one- and two-shift interval counts;
everything after that input (the singular average, moment method, roughness
certificate, and lower-density passage) is proved here.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos851

open ShiftSieve

/-- The concrete one- and two-shift estimates supplied by the beta sieve at
one fixed accuracy, depth, and lower Euler-product endpoint.  The abstract
sieve uses the open prime interval `(z,Y)`, so `Y = y+1` aligns it with the
local Euler product over `(z,y]`.

The additive error is the square of the distribution level. -/
def BetaCardinalEstimatesAt (theta : ℝ) (S z : ℕ) : Prop :=
  ∀ᶠ X : ℕ in atTop,
    let J := logIndex X
    let y := roughCutoff S J
    let Y := y + 1
    let D := distributionLevel J
    let V := localEulerProduct oneShiftDensity z y
    (∀ k ∈ powIndices J,
        (1 - theta) * V * X - (D : ℝ) ^ 2 ≤
          ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ)) ∧
      (∀ k ∈ powIndices J,
        ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) ≤
          (1 + theta) * V * X + (D : ℝ) ^ 2) ∧
      (∀ k ∈ powIndices J, ∀ l ∈ powIndices J, k ≠ l →
        ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card : ℝ) ≤
          (1 + theta) *
              localEulerProduct
                (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y * X +
            (D : ℝ) ^ 2)

/-- The sole analytic interface still required by the final assembly.
Increasing the beta depth `S` makes the relative beta-sieve error arbitrarily
small, uniformly in the fixed lower endpoint `z`. -/
def UniformBetaCardinalEstimates : Prop :=
  ∀ theta : ℝ, 0 < theta → theta ≤ 1 →
    ∃ S : ℕ, 0 < S ∧ ∀ z : ℕ, 2 ≤ z →
      BetaCardinalEstimatesAt theta S z

/-- The local moment assembly at fixed parameters.  A beta relative error
`theta`, a Romanoff tail at most `theta`, and the lower mass bound
`1 ≤ theta * J*V` leave a positive support of relative size
`1 - 18*theta` on every sufficiently large dyadic shell. -/
theorem eventually_roughSupport_of_betaCardinalEstimates
    {theta : ℝ} {S z : ℕ}
    (htheta : 0 < theta) (hthetaSmall : theta ≤ 1 / 18)
    (hz : 2 ≤ z) (htail : romanoffTail z ≤ theta)
    (hbeta : BetaCardinalEstimatesAt theta S z)
    (hmass : ∀ᶠ X : ℕ in atTop,
      1 ≤ theta * ((logIndex X : ℝ) *
        localEulerProduct oneShiftDensity z
          (roughCutoff S (logIndex X)))) :
    ∀ᶠ X : ℕ in atTop,
      (1 - 18 * theta) * X ≤
        (((dyadicInterval X).filter fun a ↦
          0 < roughCount z (roughCutoff S (logIndex X) + 1)
            (logIndex X) a).card : ℝ) := by
  have hthetaNonneg : 0 ≤ theta := htheta.le
  have hthetaOne : theta ≤ 1 := hthetaSmall.trans (by norm_num)
  have htailNonneg : 0 ≤ romanoffTail z := romanoffTail_nonneg z
  have hscale : ∀ᶠ X : ℕ in atTop,
      let J := logIndex X
      let D := distributionLevel J
      (J : ℝ) ^ 2 * (D : ℝ) ^ 2 ≤ X := by
    have hJlarge : ∀ᶠ X : ℕ in atTop, 192 ≤ logIndex X :=
      tendsto_logIndex_atTop.eventually (eventually_ge_atTop 192)
    have hXpos : ∀ᶠ X : ℕ in atTop, 0 < X := eventually_gt_atTop 0
    filter_upwards [hJlarge, hXpos] with X hJlargeX hXposX
    dsimp
    have hnat := pow_mul_sq_mul_distributionLevel_sq_le_scale
      (N := 0) (J := logIndex X) (X := X) hJlargeX (by omega)
        (pow_logIndex_le hXposX)
    norm_num at hnat
    exact_mod_cast hnat
  filter_upwards [hbeta, hmass, hscale, eventually_gt_atTop 0,
      tendsto_logIndex_atTop.eventually (eventually_ge_atTop 1)] with
      X hbetaX hmassX hscaleX hXpos hJpos
  let J := logIndex X
  let y := roughCutoff S J
  let Y := y + 1
  let D := distributionLevel J
  let V := localEulerProduct oneShiftDensity z y
  let mu : ℝ := (J : ℝ) * V
  let E1 : ℝ := theta * V * X + (D : ℝ) ^ 2
  let E2 : ℝ := (D : ℝ) ^ 2
  let sigma : ℕ → ℕ → ℝ := fun k l ↦
    (1 + theta) *
      singularFactor (Nat.dist (2 ^ k) (2 ^ l)) z y
  have hmuMass : 1 ≤ theta * mu := by
    simpa only [J, y, V, mu] using hmassX
  have hmuOne : 1 ≤ mu := by
    nlinarith
  have hE2 : 0 ≤ E2 := by positivity
  have honeLower : ∀ k ∈ powIndices J,
      V * X - E1 ≤
        ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) := by
    intro k hk
    have h := hbetaX.1 k hk
    dsimp [E1]
    nlinarith
  have honeUpper : ∀ k ∈ powIndices J,
      ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) ≤
        V * X + E1 := by
    intro k hk
    have h := hbetaX.2.1 k hk
    dsimp [E1]
    nlinarith
  have htwoUpper : ∀ k ∈ powIndices J, ∀ l ∈ powIndices J, k ≠ l →
      ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card : ℝ) ≤
        V ^ 2 * X * sigma k l + E2 := by
    intro k hk l hl hkl
    have hcard := hbetaX.2.2 k hk l hl hkl
    have hpair := pairShift_localEulerProduct_le
      (Nat.dist (2 ^ k) (2 ^ l)) (z := z) (y := y) hz
    have hfactor : 0 ≤ (1 + theta) * (X : ℝ) := by positivity
    have hmain := mul_le_mul_of_nonneg_right hpair hfactor
    dsimp [V, sigma, E2]
    calc
      ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card : ℝ) ≤
          (1 + theta) *
              localEulerProduct
                (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y * X +
            (D : ℝ) ^ 2 := by
        simpa only [J, y, Y, D] using hcard
      _ ≤ (1 + theta) *
              (localEulerProduct oneShiftDensity z y ^ 2 *
                singularFactor (Nat.dist (2 ^ k) (2 ^ l)) z y) * X +
            (D : ℝ) ^ 2 := by
        gcongr
      _ = localEulerProduct oneShiftDensity z y ^ 2 * X *
              ((1 + theta) *
                singularFactor (Nat.dist (2 ^ k) (2 ^ l)) z y) +
            (D : ℝ) ^ 2 := by ring
  have hsingular : offDiagonalSum (powIndices J) sigma ≤
      (1 + 3 * theta) * (J : ℝ) ^ 2 := by
    have hraw := orderedOffDiagonal_singularFactor_le z y J hz
    have hraw' :
        offDiagonalSum (powIndices J)
            (fun k l ↦ singularFactor (Nat.dist (2 ^ k) (2 ^ l)) z y) ≤
          (J : ℝ) ^ 2 * (1 + romanoffTail z) := by
      simpa only [offDiagonalSum, powIndices, Finset.filter_ne] using hraw
    have htailMul : theta * romanoffTail z ≤ theta := by
      calc
        theta * romanoffTail z ≤ theta * theta :=
          mul_le_mul_of_nonneg_left htail hthetaNonneg
        _ ≤ theta := by
          nlinarith [mul_nonneg hthetaNonneg (sub_nonneg.mpr hthetaOne)]
    have hcoef :
        (1 + theta) * (1 + romanoffTail z) ≤ 1 + 3 * theta := by
      nlinarith
    calc
      offDiagonalSum (powIndices J) sigma =
          (1 + theta) * offDiagonalSum (powIndices J)
            (fun k l ↦
              singularFactor (Nat.dist (2 ^ k) (2 ^ l)) z y) := by
        simp only [offDiagonalSum, sigma, Finset.mul_sum]
      _ ≤ (1 + theta) * ((J : ℝ) ^ 2 *
            (1 + romanoffTail z)) := by
        exact mul_le_mul_of_nonneg_left hraw' (by positivity)
      _ ≤ (1 + 3 * theta) * (J : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (J : ℝ)]
  have hJnonneg : (0 : ℝ) ≤ J := by positivity
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  have hXnonneg : (0 : ℝ) ≤ X := by positivity
  have hscaleReal : (J : ℝ) ^ 2 * (D : ℝ) ^ 2 ≤ X := by
    simpa only [J, D] using hscaleX
  have hJD : (J : ℝ) * (D : ℝ) ^ 2 ≤ X := by
    have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
    nlinarith [mul_nonneg (mul_nonneg hJnonneg hJnonneg)
      (sq_nonneg (D : ℝ))]
  have hfirstError : (J : ℝ) * E1 ≤
      (3 * theta) * ((J : ℝ) * V) * X := by
    dsimp [E1, mu] at hmuMass
    dsimp [E1]
    nlinarith [mul_nonneg hXnonneg (sub_nonneg.mpr hmuMass)]
  have hsecondError : (J : ℝ) * E1 + (J : ℝ) ^ 2 * E2 ≤
      (3 * theta) * ((J : ℝ) * V) ^ 2 * X := by
    have hmuNonneg : 0 ≤ mu := (by linarith : (0 : ℝ) ≤ mu)
    have hmuGrow : mu ≤ mu ^ 2 := by nlinarith
    have hrawError : (J : ℝ) * E1 + (J : ℝ) ^ 2 * E2 ≤
        (3 * theta) * mu * X := by
      dsimp [E1, E2, mu] at hmuMass ⊢
      nlinarith [mul_nonneg hXnonneg (sub_nonneg.mpr hmuMass)]
    have hgrow : (3 * theta) * mu * X ≤
        (3 * theta) * mu ^ 2 * X := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmuGrow (by positivity)) hXnonneg
    simpa only [mu] using hrawError.trans hgrow
  have hmoments := roughMoment_bounds_of_cardinal_estimates
    z Y J X sigma hE2 honeLower honeUpper htwoUpper hsingular
      hfirstError hsecondError
  have hsupport := one_sub_six_mul_le_positiveSupport
    (dyadicInterval X) (roughCount z Y J)
    (η := 3 * theta) (μ := mu) (X := X)
    (by positivity) (by nlinarith) (by nlinarith)
    (by nlinarith) (by positivity)
    (by simpa only [mu] using hmoments.1)
    (by simpa only [mu] using hmoments.2)
  dsimp [J, y, Y, mu] at hsupport ⊢
  convert hsupport using 1 <;> ring

/-- Conditional source-faithful theorem.  Once the uniform beta-cardinality
interface is filled, every `epsilon ∈ (0,1)` admits one fixed factor budget
whose representation set has lower density at least `1-epsilon`. -/
theorem erdos_851_of_uniformBetaCardinalEstimates
    (hbeta : UniformBetaCardinalEstimates) :
    ∀ epsilon : ℝ, epsilon ∈ Set.Ioo 0 1 →
      ∃ r : ℕ, 1 - epsilon ≤ (TwoPowAddSet r).lowerDensity := by
  intro epsilon hepsilon
  let theta : ℝ := epsilon / 36
  have htheta : 0 < theta := by dsimp [theta]; linarith [hepsilon.1]
  have hthetaSmall : theta ≤ 1 / 18 := by
    dsimp [theta]
    linarith [hepsilon.2]
  have hthetaOne : theta ≤ 1 := hthetaSmall.trans (by norm_num)
  obtain ⟨S, hS, hbetaS⟩ := hbeta theta htheta hthetaOne
  obtain ⟨C, hC, hmassBound⟩ :=
    exists_eventually_oneShift_roughCutoff_mass_lower_bound
  have hlogTop : Tendsto (fun z : ℕ ↦ Real.log (z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htailEventually : ∀ᶠ z : ℕ in atTop, romanoffTail z ≤ theta := by
    have hnhds : Set.Iic theta ∈ nhds (0 : ℝ) := by
      exact Iic_mem_nhds htheta
    exact (romanoffTail_tendsto_zero.eventually hnhds)
  have hlogEventually : ∀ᶠ z : ℕ in atTop,
      C * Real.log 2 ≤
        theta * (((8 * S : ℕ) : ℝ) * Real.log (z : ℝ)) := by
    have hthreshold := hlogTop.eventually
      (eventually_ge_atTop
        (C * Real.log 2 /
          (theta * (((8 * S : ℕ) : ℝ))))
        )
    filter_upwards [hthreshold] with z hzlog
    have hden : 0 < theta * (((8 * S : ℕ) : ℝ)) := by positivity
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (div_le_iff₀ hden).mp hzlog
  have hzEventually : ∀ᶠ z : ℕ in atTop, 2 ≤ z := eventually_ge_atTop 2
  obtain ⟨z, htail, hlog, hz⟩ :=
    (htailEventually.and (hlogEventually.and hzEventually)).exists
  have hbetaAt := hbetaS z hz
  have hmassJ := hmassBound hS hz
  have hmassJ' : ∀ᶠ J : ℕ in atTop,
      1 ≤ theta * ((J : ℝ) *
        localEulerProduct oneShiftDensity z (roughCutoff S J)) := by
    filter_upwards [hmassJ] with J hJ
    have hden : 0 < C * Real.log 2 := by positivity
    have hbase : 1 ≤ theta *
        ((((8 * S : ℕ) : ℝ) * Real.log (z : ℝ)) /
          (C * Real.log 2)) := by
      have hbase' : 1 ≤
          (theta * (((8 * S : ℕ) : ℝ) * Real.log (z : ℝ))) /
            (C * Real.log 2) :=
        (le_div_iff₀ hden).2 (by simpa using hlog)
      convert hbase' using 1 <;> ring
    exact hbase.trans (mul_le_mul_of_nonneg_left hJ htheta.le)
  have hmassX : ∀ᶠ X : ℕ in atTop,
      1 ≤ theta * ((logIndex X : ℝ) *
        localEulerProduct oneShiftDensity z
          (roughCutoff S (logIndex X))) :=
    tendsto_logIndex_atTop.eventually hmassJ'
  have hsupport := eventually_roughSupport_of_betaCardinalEstimates
    htheta hthetaSmall hz htail hbetaAt hmassX
  let r := (primesUpTo z).card + 32 * S
  refine ⟨r, ?_⟩
  have hJlarge : ∀ᶠ X : ℕ in atTop, 16 * S ≤ logIndex X :=
    tendsto_logIndex_atTop.eventually (eventually_ge_atTop (16 * S))
  have hXpos : ∀ᶠ X : ℕ in atTop, 0 < X := eventually_gt_atTop 0
  have hcertificate : ∀ᶠ X : ℕ in atTop,
      ∀ a, a ∈ dyadicInterval X →
        0 < roughCount z (roughCutoff S (logIndex X) + 1)
          (logIndex X) a → a ∈ TwoPowAddSet r := by
    filter_upwards [hJlarge, hXpos] with X hJX hX a ha hrough
    apply mem_twoPowAddSet_of_roughCount_pos
      (z := z) (Y := roughCutoff S (logIndex X) + 1)
      (J := logIndex X) (L := 32 * S) (X := X) (a := a) ha
      (pow_logIndex_le hX)
      (by
        have hy : 0 < roughCutoff S (logIndex X) := by
          simp only [roughCutoff]
          positivity
        omega)
    · have hsize := two_mul_lt_roughCutoff_logIndex_pow hS hX hJX
      exact hsize.le.trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
    · simpa only [r] using hrough
  have hdensity : 1 - 18 * theta ≤ (TwoPowAddSet r).lowerDensity := by
    have hbad : ∀ᶠ X : ℕ in atTop,
        (exceptionalDyadicCount (TwoPowAddSet r)ᶜ X : ℝ) ≤
          (18 * theta) * X := by
      filter_upwards [hsupport, hcertificate] with X hsupportX hcertificateX
      classical
      let good := (dyadicInterval X).filter fun a ↦
        0 < roughCount z (roughCutoff S (logIndex X) + 1)
          (logIndex X) a
      let bad := (dyadicInterval X).filter fun a ↦ a ∈ (TwoPowAddSet r)ᶜ
      have hdisjoint : Disjoint good bad := by
        rw [Finset.disjoint_left]
        intro a hagood habad
        have hg := Finset.mem_filter.mp hagood
        have hb := Finset.mem_filter.mp habad
        exact hb.2 (hcertificateX a hg.1 hg.2)
      have hunion : good ∪ bad ⊆ dyadicInterval X := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact (Finset.mem_filter.mp ha).1
        · exact (Finset.mem_filter.mp ha).1
      have hcard : good.card + bad.card ≤ X := by
        calc
          good.card + bad.card = (good ∪ bad).card :=
            (Finset.card_union_of_disjoint hdisjoint).symm
          _ ≤ (dyadicInterval X).card := Finset.card_le_card hunion
          _ = X := by simp [dyadicInterval, two_mul]
      have hcard' : (good.card : ℝ) + bad.card ≤ X := by exact_mod_cast hcard
      have hsupportX' : (1 - 18 * theta) * X ≤ (good.card : ℝ) := by
        simpa only [good] using hsupportX
      rw [exceptionalDyadicCount_eq_filter_card]
      change (bad.card : ℝ) ≤ (18 * theta) * X
      nlinarith
    simpa using (one_sub_le_lowerDensity_compl_of_dyadic
      (TwoPowAddSet r)ᶜ (mul_nonneg (by norm_num) htheta.le) hbad)
  have hloss : 18 * theta ≤ epsilon := by
    dsimp [theta]
    linarith [hepsilon.1]
  exact (sub_le_sub_left hloss 1).trans hdensity

end Erdos851
