import ErdosProblems.Erdos228.OddKernelIdentity
import ErdosProblems.Erdos228.KernelNearGeometry
import ErdosProblems.Erdos228.SineIntegralGrid
import ErdosProblems.Erdos228.KernelDistantClaim
import ErdosProblems.Erdos228.ConcreteKernelClaims

/-!
# The concrete odd-kernel certificate

This module closes the analytic interface left by `OddSine.KernelCertificate`.
The first part is a small numerical adapter: once the normalized odd kernel
has its sharp `2 / 3` lower bound on the dangerous set and its `14 / 3`
global upper bound, it packages those inequalities into the exact
`main + error` format consumed by `OddSine`.

The remaining sections prove those normalized bounds from the exact odd
Dirichlet identity, the grid geometry of a suitable interval family, and the
three concrete kernel estimates.
-/

namespace Erdos228.OddKernelCertificate

open scoped BigOperators Interval
open Set

noncomputable section

open Erdos228.OddSine

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## A numerical adapter for the certificate structure -/

/-- The target sine sum after removing its positive `K * sqrt n` scale. -/
def normalizedTarget {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  targetSine F alpha theta / (K * Real.sqrt n)

private def clippedMagnitude (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) : ℝ :=
  min 4 (max (if dangerous then 4 / 3 else 0) a)

private lemma clippedMagnitude_nonneg (dangerous : Prop) [Decidable dangerous]
    {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ clippedMagnitude dangerous a := by
  unfold clippedMagnitude
  apply le_min (by norm_num)
  exact le_max_of_le_right ha

private lemma clippedMagnitude_le_four (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) :
    clippedMagnitude dangerous a ≤ 4 := by
  exact min_le_left _ _

private lemma four_thirds_le_clippedMagnitude {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (hdangerous : dangerous) :
    4 / 3 ≤ clippedMagnitude dangerous a := by
  unfold clippedMagnitude
  rw [if_pos hdangerous]
  apply le_min (by norm_num)
  exact le_max_left _ _

private lemma abs_sub_clippedMagnitude_le {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (ha : 0 ≤ a)
    (haUpper : a ≤ 14 / 3)
    (haLower : dangerous → 2 / 3 ≤ a) :
    |a - clippedMagnitude dangerous a| ≤ 2 / 3 := by
  classical
  unfold clippedMagnitude
  by_cases hdangerous : dangerous
  · rw [if_pos hdangerous]
    have halower := haLower hdangerous
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right]
      · by_cases ha43 : 4 / 3 ≤ a
        · rw [max_eq_right ha43]
          norm_num
        · rw [max_eq_left (le_of_not_ge ha43)]
          rw [abs_of_nonpos]
          · linarith
          · linarith
      · exact max_le (by norm_num) ha4
    · have h4a : 4 ≤ max (4 / 3) a := by
        exact le_max_of_le_right (le_of_not_ge ha4)
      rw [min_eq_left h4a, abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith
  · rw [if_neg hdangerous, max_eq_right ha]
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right ha4]
      norm_num
    · rw [min_eq_left (le_of_not_ge ha4),
        abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith

private def clippedMain {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  let m := clippedMagnitude (IsDangerous F theta)
    |normalizedTarget F alpha theta|
  if 0 ≤ normalizedTarget F alpha theta then m else -m

private def clippedError {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  normalizedTarget F alpha theta - clippedMain F alpha theta

private lemma abs_clippedMain {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    |clippedMain F alpha theta| =
      clippedMagnitude (IsDangerous F theta)
        |normalizedTarget F alpha theta| := by
  classical
  simp only [clippedMain]
  by_cases hv : 0 ≤ normalizedTarget F alpha theta
  · rw [if_pos hv,
      abs_of_nonneg (clippedMagnitude_nonneg _ (abs_nonneg _))]
  · rw [if_neg hv, abs_neg,
      abs_of_nonneg (clippedMagnitude_nonneg _ (abs_nonneg _))]

private lemma abs_clippedError {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    |clippedError F alpha theta| =
      |(|normalizedTarget F alpha theta| -
        clippedMagnitude (IsDangerous F theta)
          |normalizedTarget F alpha theta|)| := by
  classical
  unfold clippedError clippedMain
  by_cases hv : 0 ≤ normalizedTarget F alpha theta
  · rw [if_pos hv, abs_of_nonneg hv]
  · rw [if_neg hv, abs_of_neg (lt_of_not_ge hv)]
    have heq : normalizedTarget F alpha theta +
        clippedMagnitude (IsDangerous F theta)
            (-normalizedTarget F alpha theta) =
          -(-normalizedTarget F alpha theta -
            clippedMagnitude (IsDangerous F theta)
              (-normalizedTarget F alpha theta)) := by ring
    rw [sub_neg_eq_add, heq, abs_neg]

/-- Package the two sharp normalized estimates into the precise
`OddSine.KernelCertificate` interface.  This lemma is only an internal
adapter: the public theorem below proves both estimates from the interval
geometry and has no analytic hypotheses. -/
noncomputable def kernelCertificate_of_normalized_bounds {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (hlower : ∀ theta, IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|)
    (hupper : ∀ theta, |normalizedTarget F alpha theta| ≤ 14 / 3) :
    KernelCertificate F alpha := by
  classical
  refine
    { main := clippedMain F alpha
      error := clippedError F alpha
      decomposition := ?_
      main_lower := ?_
      main_upper := ?_
      error_bound := ?_ }
  · intro theta
    have hscale : K * Real.sqrt n ≠ 0 := by
      apply mul_ne_zero
      · norm_num [K]
      · exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
    rw [show clippedMain F alpha theta + clippedError F alpha theta =
        normalizedTarget F alpha theta by
      simp only [clippedError]
      ring]
    simp only [normalizedTarget]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ hscale).symm
  · intro theta htheta
    rw [abs_clippedMain]
    exact four_thirds_le_clippedMagnitude htheta
  · intro theta
    rw [abs_clippedMain]
    exact clippedMagnitude_le_four _ _
  · intro theta
    rw [abs_clippedError]
    exact abs_sub_clippedMagnitude_le (abs_nonneg _)
      (hupper theta) (hlower theta)

/-! ## Reduction to the first quadrant -/

/-- It is enough to establish the normalized kernel estimates in the first
quadrant.  The upper bound uses the absolute-value reduction for every odd
sine sum.  For the lower bound, the four clauses in `IsDangerous` give the
corresponding odd/reflection/translation identity directly. -/
theorem normalized_bounds_of_firstQuadrant {n : ℕ}
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (hlower : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      IsDangerous F theta → 2 / 3 ≤ |normalizedTarget F alpha theta|)
    (hupper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |normalizedTarget F alpha theta| ≤ 14 / 3) :
    (∀ theta, IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|) ∧
    (∀ theta, |normalizedTarget F alpha theta| ≤ 14 / 3) := by
  constructor
  · intro theta htheta
    obtain ⟨I, hI, hmem | hmem | hmem | hmem⟩ := htheta
    · exact hlower theta
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
        ⟨I, hI, Or.inl hmem⟩
    · have hqmem : -theta ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (-theta) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (-theta) hqmem hqdanger
      simpa only [normalizedTarget, targetSine,
        oddSineSum_neg, abs_div, abs_neg] using hq
    · have hqmem : Real.pi - theta ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (Real.pi - theta) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (Real.pi - theta) hqmem hqdanger
      simpa only [normalizedTarget, targetSine,
        oddSineSum_pi_sub, abs_div] using hq
    · have hqmem : theta - Real.pi ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (theta - Real.pi) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (theta - Real.pi) hqmem hqdanger
      have heq : theta = (theta - Real.pi) + Real.pi := by ring
      rw [heq]
      simpa only [normalizedTarget, targetSine,
        oddSineSum_add_pi, abs_div, abs_neg] using hq
  · intro theta
    obtain ⟨theta', htheta', heq⟩ :=
      exists_firstQuadrant_abs_oddSineSum_eq n (fourierTarget F alpha) theta
    have hq := hupper theta' htheta'
    simp only [normalizedTarget, targetSine, abs_div] at hq ⊢
    rw [heq]
    exact hq

/-! ## Finite near/distant assembly -/

/-- A nondegenerate suitable interval has strictly ordered integer grid
indices.  This is the exact endpoint form consumed by the grid
sine-integral lemma. -/
theorem exists_gridIndices_lt {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (I : (↑F.base : Type)) :
    ∃ a b : ℤ, a < b ∧
      I.1.1 = (a : ℝ) * Real.pi / n ∧
      I.1.2 = (b : ℝ) * Real.pi / n := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I.1 I.property
  refine ⟨a, b, ?_, ha, hb⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscalePos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hscaled : (a : ℝ) * (Real.pi / (n : ℝ)) <
      (b : ℝ) * (Real.pi / (n : ℝ)) := by
    simpa only [mul_div_assoc, ha, hb] using
      F.nondegenerate I.1 I.property
  have habR : (a : ℝ) < b := by
    nlinarith [hscalePos]
  exact_mod_cast habR

/-- The principal integral on the interval containing the evaluation point
is the main lobe from BBMST Lemma 5.8(a). -/
theorem principalIntegral_self_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (I : (↑F.base : Type)) (htheta : InInterval I.1 theta) :
    Erdos228.KernelDistantClaim.principalIntegral n I.1 theta ∈
      Icc ((4 : ℝ) / 3) 4 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_gridIndices_lt hn F I
  have hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have htheta' : theta ∈ Icc ((a : ℝ) * Real.pi / n)
      ((b : ℝ) * Real.pi / n) := by
    change theta ∈ Icc I.1.1 I.1.2 at htheta
    simpa only [← ha, ← hb] using htheta
  have hmain := Erdos228.SineIntegralGrid.principal_grid_interval_inside
    n hn a b hab hshort htheta'
  simpa only [Erdos228.KernelDistantClaim.principalIntegral, ha, hb] using hmain

/-- Every near interval not containing the evaluation point is an exterior
interval in BBMST Lemma 5.8(b), hence contributes at most `2`. -/
theorem abs_principalIntegral_le_two_of_near_of_not_mem {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (I : (↑F.base : Type))
    (hnear : I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta)
    (hout : ¬InInterval I.1 theta) :
    |Erdos228.KernelDistantClaim.principalIntegral n I.1 theta| ≤ 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_gridIndices_lt hn F I
  have hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have hnearGap : Erdos228.KernelNearGeometry.Near n theta I.1 := by
    simpa only [Erdos228.KernelNearGeometry.nearBaseIntervals,
      Finset.mem_filter, Finset.mem_univ, true_and] using hnear
  rw [InInterval, mem_Icc] at hout
  have hside :
      (theta ≤ (a : ℝ) * Real.pi / n ∧
        (a : ℝ) * Real.pi / n - theta ≤ Real.pi / n) ∨
      ((b : ℝ) * Real.pi / n ≤ theta ∧
        theta - (b : ℝ) * Real.pi / n ≤ Real.pi / n) := by
    rcases not_and_or.mp hout with hleft | hright
    · left
      have htheta : theta ≤ I.1.1 := (lt_of_not_ge hleft).le
      have hgap := hnearGap
      rw [Erdos228.KernelNearGeometry.Near,
        Erdos228.KernelNearGeometry.intervalGap_eq_left
          (F.ordered I.1 I.property) htheta] at hgap
      rw [← ha]
      exact ⟨htheta, hgap.le⟩
    · right
      have htheta : I.1.2 ≤ theta := (lt_of_not_ge hright).le
      have hgap := hnearGap
      rw [Erdos228.KernelNearGeometry.Near,
        Erdos228.KernelNearGeometry.intervalGap_eq_right
          (F.ordered I.1 I.property) htheta] at hgap
      rw [← hb]
      exact ⟨htheta, hgap.le⟩
  have hoff := Erdos228.SineIntegralGrid.principal_grid_interval_outside_near
    n hn a b hab hshort hside
  simpa only [Erdos228.KernelDistantClaim.principalIntegral, ha, hb] using hoff

/-- Abstract assembly of the kernel bookkeeping after Claims 1--3 have been
summed.  The hypotheses are the concrete conclusions proved below:

* `principal` is the `sin(2n u) / u` integral on one grid interval;
* its near part contains one self interval (bounded between `4/3` and `4`)
  or at most two outside intervals (each bounded by `2`);
* `error` is the reflected kernel, denominator-replacement error, and all
  distant principal intervals, whose aggregate is at most `2/3`.

Keeping this finite step separate makes the use of separation and the sign
colouring completely explicit. -/
theorem firstQuadrant_normalized_bounds_of_decomposition {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha)
    (principal : (↑F.base : Type) → ℝ → ℝ) (error : ℝ → ℝ)
    (hdecomposition : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      normalizedTarget F alpha theta =
        (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * principal I theta) + error theta)
    (herror : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |error theta| ≤ 2 / 3)
    (hself_lower : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I : (↑F.base : Type), InInterval I.1 theta →
        4 / 3 ≤ |principal I theta|)
    (hself_upper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I : (↑F.base : Type), InInterval I.1 theta →
        |principal I theta| ≤ 4)
    (hoff_upper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
        ¬InInterval I.1 theta → |principal I theta| ≤ 2) :
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2), IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|) ∧
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |normalizedTarget F alpha theta| ≤ 14 / 3) := by
  classical
  have halpha_abs (I : (↑F.base : Type)) : |alpha I| = 1 := by
    rcases halpha I with hI | hI <;> simp [hI]
  constructor
  · intro theta htheta hdangerous
    obtain ⟨I, hthetaI, _hunique⟩ :=
      Erdos228.KernelNearGeometry.existsUnique_baseSubtype_of_dangerous_firstQuadrant
        hn F htheta hdangerous
    have hnear := Erdos228.KernelNearGeometry.sum_nearBaseIntervals_eq_of_mem hn F
      I.property hthetaI (fun J ↦ alpha J * principal J theta)
    have hmainLower : 4 / 3 ≤ |alpha I * principal I theta| := by
      rw [abs_mul, halpha_abs, one_mul]
      exact hself_lower theta htheta I hthetaI
    have hreverse : |alpha I * principal I theta| ≤
        |normalizedTarget F alpha theta| + |error theta| := by
      rw [hdecomposition theta htheta, hnear]
      calc
        |alpha I * principal I theta| =
            |(alpha I * principal I theta + error theta) - error theta| := by
              ring_nf
        _ ≤ _ := abs_sub _ _
    linarith [herror theta htheta]
  · intro theta htheta
    have hmainUpper :
        |∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * principal I theta| ≤ 4 := by
      by_cases hin : Erdos228.KernelNearGeometry.InBaseUnion F theta
      · obtain ⟨I, hI, hthetaI⟩ := hin
        rw [Erdos228.KernelNearGeometry.sum_nearBaseIntervals_eq_of_mem hn F hI hthetaI]
        rw [abs_mul, halpha_abs, one_mul]
        exact hself_upper theta htheta ⟨I, hI⟩ hthetaI
      · have htwo :=
          Erdos228.KernelNearGeometry.abs_sum_nearBaseIntervals_le_two_mul_of_not_inBaseUnion
            hn F hin (show (0 : ℝ) ≤ 2 by norm_num)
            (fun I ↦ alpha I * principal I theta) (by
              intro I hI
              rw [abs_mul, halpha_abs, one_mul]
              exact hoff_upper theta htheta I hI
                (fun hmem ↦ hin ⟨I.1, I.property, hmem⟩))
        norm_num at htwo ⊢
        exact htwo
    rw [hdecomposition theta htheta]
    calc
      |(∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I theta) + error theta| ≤
          |∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I theta| + |error theta| := abs_add_le _ _
      _ ≤ 4 + 2 / 3 := add_le_add hmainUpper (herror theta htheta)
      _ = 14 / 3 := by norm_num

/-! ## Concrete Claims 1--3 and the certificate -/

/-- The aggregate of the three terms discarded when only the strict-near
principal kernels are retained. -/
def concreteError {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  normalizedTarget F alpha theta -
    ∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
      alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta

theorem concrete_decomposition {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    normalizedTarget F alpha theta =
      (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
        alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta) +
        concreteError F alpha theta := by
  simp only [concreteError]
  ring

/-- The signed aggregate of Claims 1--3 is at most `2 / 3`.  The equality
before the estimate is the exact odd Dirichlet-kernel identity, not an
asymptotic approximation. -/
theorem abs_concreteError_le_two_thirds {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |concreteError F alpha theta| ≤ 2 / 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have htarget :=
    Erdos228.OddKernelIdentity.targetSine_div_eq_sum_quotientIntegral_of_theta_mem_Icc
      hnpos F alpha htheta
  rw [concreteError]
  change normalizedTarget F alpha theta =
      ∑ I : (↑F.base : Type), alpha I *
        Erdos228.ConcreteKernelClaims.quotientIntegral n I.1 theta at htarget
  rw [htarget]
  exact Erdos228.ConcreteKernelClaims.signed_kernel_residual_le_two_thirds
    hn F alpha halpha htheta

/-- The two normalized bounds in the first quadrant, with the exact
principal kernel as the near contribution. -/
theorem concrete_firstQuadrant_normalized_bounds {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) :
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2), IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|) ∧
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |normalizedTarget F alpha theta| ≤ 14 / 3) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply firstQuadrant_normalized_bounds_of_decomposition hnpos F alpha halpha
    (fun I theta ↦ Erdos228.KernelDistantClaim.principalIntegral n I.1 theta)
    (concreteError F alpha)
  · exact fun theta _ ↦ concrete_decomposition F alpha theta
  · exact fun _ htheta ↦ abs_concreteError_le_two_thirds hn F alpha halpha htheta
  · intro theta _ I htheta
    have hmain := principalIntegral_self_mem hnpos F I htheta
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.1
  · intro theta _ I htheta
    have hmain := principalIntegral_self_mem hnpos F I htheta
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.2
  · intro theta _ I hnear hout
    exact abs_principalIntegral_le_two_of_near_of_not_mem hnpos F I hnear hout

/-- The unconditional concrete odd-kernel certificate used by the final
Erdős 228 assembly. -/
noncomputable def kernelCertificate {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) :
    KernelCertificate F alpha := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hfirst := concrete_firstQuadrant_normalized_bounds hn F alpha halpha
  have hglobal := normalized_bounds_of_firstQuadrant F alpha hfirst.1 hfirst.2
  exact kernelCertificate_of_normalized_bounds hnpos F alpha hglobal.1 hglobal.2

end

end Erdos228.OddKernelCertificate
