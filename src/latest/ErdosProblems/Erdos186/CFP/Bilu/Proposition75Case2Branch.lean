/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2Construction
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Branches

/-!
# Constructing the Case 2 branch of Bilu Proposition 7.5

This file packages the presentation-free Proposition 7.4/8.3 geometric
witness into the common `Case2Branch` interface.  The only remaining input
is the explicit numerical comparison appearing in that branch.
-/

namespace Erdos186.CFP.Bilu.Proposition75Case2Branch

open MeasureTheory Set Module
open scoped ENNReal Pointwise RealInnerProductSpace
open BadlyApproximable PolarSeparation Proposition75Data
open Proposition75Case1 Proposition75Case2 Case2Coordinates
open Proposition75Case2Construction Proposition75Branches

noncomputable section

/-- The error-coordinate box in Bilu's distortion body. -/
def distortionErrorBox (r : ℕ) : Set (EuclideanSpace ℝ (Fin r)) :=
  {e | ∀ i, e i ∈ Set.Icc (-1 : ℝ) 1}

theorem isCompact_distortionErrorBox (r : ℕ) :
    IsCompact (distortionErrorBox r) := by
  unfold distortionErrorBox
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hset :
        {e : EuclideanSpace ℝ (Fin r) |
          ∀ i, e i ∈ Set.Icc (-1 : ℝ) 1} =
          ⋂ i, (fun e : EuclideanSpace ℝ (Fin r) ↦ e i) ⁻¹'
            Set.Icc (-1 : ℝ) 1 := by
        ext e
        simp
    rw [hset]
    exact isClosed_iInter fun i ↦
      isClosed_Icc.preimage (by fun_prop)
  · rw [Metric.isBounded_iff_subset_closedBall
      (0 : EuclideanSpace ℝ (Fin r))]
    refine ⟨Real.sqrt r, ?_⟩
    intro e he
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
    calc
      ∑ i, e i ^ 2 ≤ ∑ _i : Fin r, (1 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (e i)) zero_le_one).2
            (abs_le.mpr (he i))
      _ = (r : ℝ) := by simp

/-- Reconstruct a distortion-body point from its head and its bounded
error coordinates. -/
def distortionParametrization {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r)) :
    Ambient m r :=
  WithLp.toLp 2
    (p.1, WithLp.toLp 2 fun i ↦ ⟪p.1, a i⟫ - p.2 i)

theorem continuous_distortionParametrization {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Continuous (distortionParametrization a) := by
  unfold distortionParametrization
  apply (WithLp.prod_continuous_toLp 2 _ _).comp
  apply Continuous.prodMk continuous_fst
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

/-- Compactness of the source body implies compactness of Bilu's full
distortion body. -/
theorem isCompact_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : IsCompact B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    IsCompact (distortionBody B a) := by
  have hparam : distortionBody B a =
      distortionParametrization a ''
        (((2 : ℝ) • B) ×ˢ distortionErrorBox r) := by
    ext z
    constructor
    · intro hz
      let e : EuclideanSpace ℝ (Fin r) :=
        WithLp.toLp 2 fun i ↦ ⟪head z, a i⟫ - tail z i
      refine ⟨(head z, e), ⟨hz.1, ?_⟩, ?_⟩
      · intro i
        change -1 ≤ ⟪head z, a i⟫ - tail z i ∧
          ⟪head z, a i⟫ - tail z i ≤ 1
        exact (abs_le.mp (hz.2 i))
      · apply (WithLp.linearEquiv 2 ℝ
          (EuclideanSpace ℝ (Fin m) ×
            EuclideanSpace ℝ (Fin r))).injective
        apply Prod.ext
        · rfl
        · ext i
          simp [distortionParametrization, e]
    · rintro ⟨p, hp, rfl⟩
      refine ⟨hp.1, ?_⟩
      intro i
      simpa only [distortionParametrization, head, tail,
        WithLp.ofLp_toLp, sub_sub_cancel] using
        (abs_le.mpr (hp.2 i))
  rw [hparam]
  exact ((hB.smul (2 : ℝ)).prod (isCompact_distortionErrorBox r)).image
    (continuous_distortionParametrization a)

/-- The coordinate distortion body is compact under the corresponding
source-body hypothesis. -/
theorem isCompact_coordinateDistortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : IsCompact B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    IsCompact (coordinateDistortionBody B a) := by
  exact (ambientEquiv m r).symm.toHomeomorph.isCompact_preimage.mpr
    (isCompact_distortionBody hB a)

/-- The badly-approximable output and the Proposition 7.4 section geometry
produce the complete small-covolume branch of Proposition 7.5. -/
theorem case2Branch_of_badlyApproximable {m r d k : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (hrank : finrank ℝ D.C0 = d)
    (hdim : d + k + 1 = m + r)
    {X C rho : ℝ}
    (ha : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X C
      (fun i ↦ WithLp.ofLp (a i)))
    (hC : 0 < C)
    (hcovol : ZLattice.covolume D.latticePoints
      μHE[finrank ℝ D.C0] < X)
    (hrho : 0 < rho)
    (hinball : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
        coordinateDistortionBody B a)
    (hcompact : IsCompact (coordinateDistortionBody B a))
    {constant scale : ENNReal}
    (hconstants :
      (2 * ENNReal.ofReal C)⁻¹ *
          (((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
            ((2 : ENNReal) ^ (m + r)) *
            (((d.factorial : ENNReal) *
                ENNReal.ofReal (rho ^ k))⁻¹ *
              ((d + k).factorial : ENNReal))) *
          ENNReal.ofReal (Real.sqrt (m + r)) ≤
        constant * scale) :
    Case2Branch D constant scale := by
  obtain ⟨ell, Xw, hell0, hellBound, hnorm, hl, hXC, hXrho,
      hXgauge⟩ :=
    exists_case2Witness hbalanced hmeasurable hconvex D hrank hdim ha hC
      hcovol hrho hinball hcompact
  refine ⟨d, k, Xw, ENNReal.ofReal (Real.sqrt (m + r)), ?_, ?_⟩
  · rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hnorm
  · simpa only [hXC, hXrho] using hconstants

/-- Source-shaped Case 2 constructor.  Proposition 8.3's unit-cube output
and the head inball give the required ambient inball with Bilu's radius
`1 / (m + 1)` via Proposition 8.4. -/
theorem case2Branch_of_unitCubeIoc {m r d k : ℕ} (hm : 0 < m)
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (haCube : ∀ i, WithLp.ofLp (a i) ∈
      Section8Synthesis.unitCubeIoc m)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
      (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (D : GeometricData B a)
    (hrank : finrank ℝ D.C0 = d)
    (hdim : d + k + 1 = m + r)
    {X C : ℝ}
    (ha : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X C
      (fun i ↦ WithLp.ofLp (a i)))
    (hC : 0 < C)
    (hcovol : ZLattice.covolume D.latticePoints
      μHE[finrank ℝ D.C0] < X)
    (hcompact : IsCompact B)
    {constant scale : ENNReal}
    (hconstants :
      (2 * ENNReal.ofReal C)⁻¹ *
          (((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
            ((2 : ENNReal) ^ (m + r)) *
            (((d.factorial : ENNReal) *
                ENNReal.ofReal ((((m : ℝ) + 1)⁻¹) ^ k))⁻¹ *
              ((d + k).factorial : ENNReal))) *
          ENNReal.ofReal (Real.sqrt (m + r)) ≤
        constant * scale) :
    Case2Branch D constant scale := by
  let W : Case1Witness D (((m : ℝ) + 1)⁻¹) :=
    case1WitnessOfUnitCubeIoc hm D hmeasurable hconvex hhead haCube
  exact case2Branch_of_badlyApproximable hbalanced hmeasurable hconvex D
    hrank hdim ha hC hcovol W.rho_pos W.ambient_inball
      (isCompact_coordinateDistortionBody hcompact a) hconstants

end

end Erdos186.CFP.Bilu.Proposition75Case2Branch

#print axioms Erdos186.CFP.Bilu.Proposition75Case2Branch.case2Branch_of_badlyApproximable
#print axioms Erdos186.CFP.Bilu.Proposition75Case2Branch.case2Branch_of_unitCubeIoc
