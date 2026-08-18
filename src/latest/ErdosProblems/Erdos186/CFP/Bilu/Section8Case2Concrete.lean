/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.PolarSeparation
import ErdosProblems.Erdos186.CFP.Bilu.ProjectionCovolume
import ErdosProblems.Erdos186.CFP.Bilu.Section8GeometrySynthesis

/-!
# The concrete geometric bookkeeping in Bilu Section 8.3, Case 2

This file removes the last two abstract inequalities from
`Section8GeometrySynthesis.combine_case2_with_projection_and_cone`.
Equation (8.7) is obtained from the strict polar-separation inequality,
and equation (8.10) is obtained from the proved projection determinant
estimate.  Thus the final theorem below has only the geometric objects
which occur in Bilu's construction as inputs, rather than hypotheses
named `(8.7)`--`(8.10)`.
-/

namespace Erdos186.CFP.Bilu.Section8Case2Concrete

open MeasureTheory Set Module Submodule
open scoped ENNReal RealInnerProductSpace
open PolarSeparation ProjectionCovolume ProjectionVolumeCoarse
open VolumeSections Section8GeometrySynthesis

/-- The strict real polar-separation estimate implies the `ENNReal`
cross-multiplied form of equation (8.7). -/
theorem equation87_of_strict_polar_separation
    {C gauge innerAbs : ℝ} (hC : 0 < C) (hgauge0 : 0 ≤ gauge)
    (hgauge : 2 * gauge ≤ 1) (hinner : C < innerAbs) :
    2 * ENNReal.ofReal C * ENNReal.ofReal gauge ≤
      ENNReal.ofReal innerAbs := by
  have hreal : 2 * C * gauge ≤ innerAbs :=
    (two_mul_mul_lt_of_gauge_le_half hC hgauge hinner).le
  calc
    2 * ENNReal.ofReal C * ENNReal.ofReal gauge =
        ENNReal.ofReal (2 * C * gauge) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * C)]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ ENNReal.ofReal innerAbs := ENNReal.ofReal_le_ofReal hreal

/-- The projection determinant theorem, with its product of Euclidean
norms split into the two factors used in Bilu's cancellation. -/
theorem equation810_of_projection
    {n : ℕ} {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (u l : EuclideanSpace ℝ (Fin n))
    (hcodim : Module.finrank ℝ W + 1 =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Submodule.orthogonal W) (hu0 : u ≠ 0)
    (hlL : l ∈ Submodule.orthogonal L) (hl0 : l ≠ 0)
    (T : Set L) :
    ENNReal.ofReal |⟪u, l⟫| * volume T ≤
      ENNReal.ofReal ‖u‖ * ENNReal.ofReal ‖l‖ *
        μHE[Module.finrank ℝ L] (projectionRestrict W L '' T) := by
  have h := projection_volume_crossmultiplied
    u l hcodim huW hu0 hlL hl0 T
  rw [ENNReal.ofReal_mul (norm_nonneg u)] at h
  simpa only [mul_assoc] using h

/-- All four estimates in Bilu Section 8.3, Case 2, combined from their
proved geometric sources.

The equality `hsection` is the coordinate identification between the
orthogonal projection in Lemma 6.9 and the first member of the explicit
cone flag.  In Bilu's application it is supplied by the chosen orthogonal
coordinates; no volume inequality is assumed here. -/
theorem combine_case2_of_polar_projection_and_cone
    {n d k : ℕ} {rho gaugeW C : ℝ}
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (u l : EuclideanSpace ℝ (Fin n))
    (T : Set L)
    {Omega : Set (Base (d + k) × ℝ)}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    {V volumeFactor : ℝ≥0∞}
    (hC : 0 < C) (hgaugeW : 0 < gaugeW)
    (hgaugeHalf : 2 * gaugeW ≤ 1)
    (hinner : C < |⟪u, l⟫|)
    (hcodim : Module.finrank ℝ W + 1 =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Submodule.orthogonal W) (hu0 : u ≠ 0)
    (hlL : l ∈ Submodule.orthogonal L) (hl0 : l ≠ 0)
    (hOmega : MeasurableSet Omega)
    (hhalf : MeasurableSet (halfBaseProjection Omega))
    (hconv : Convex ℝ Omega)
    (hsegment : ∀ t ∈ Set.Icc (-(‖u‖ / gaugeW)) (‖u‖ / gaugeW),
      ((0 : Base (d + k)), t) ∈ Omega)
    (hOmegaVolume : (volume.prod volume) Omega ≤ volumeFactor * V)
    (hchain : CoordinateConeChain d k rho S)
    (hfinal : S k = baseProjection Omega)
    (hsection :
      μHE[Module.finrank ℝ L] (projectionRestrict W L '' T) =
        intrinsicVolume d (S 0)) :
    2 * ENNReal.ofReal C * volume T ≤
      ((‖(2 : ℝ)⁻¹‖₊ : ℝ≥0∞) ^ (d + k))⁻¹ * volumeFactor *
        (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k))⁻¹ *
          ((d + k).factorial : ℝ≥0∞)) *
        ENNReal.ofReal ‖l‖ * V := by
  have h87 : 2 * ENNReal.ofReal C * ENNReal.ofReal gaugeW ≤
      ENNReal.ofReal |⟪u, l⟫| :=
    equation87_of_strict_polar_separation hC hgaugeW.le hgaugeHalf hinner
  have h810 : ENNReal.ofReal |⟪u, l⟫| * volume T ≤
      ENNReal.ofReal ‖u‖ * ENNReal.ofReal ‖l‖ *
        intrinsicVolume d (S 0) := by
    simpa only [hsection] using
      equation810_of_projection u l hcodim huW hu0 hlL hl0 T
  simpa only [mul_assoc] using
    (combine_case2_with_projection_and_cone
      (norm_nonneg u) hgaugeW hOmega hhalf hconv hsegment hOmegaVolume
      hchain hfinal h87 h810)

end Erdos186.CFP.Bilu.Section8Case2Concrete

#print axioms Erdos186.CFP.Bilu.Section8Case2Concrete.equation87_of_strict_polar_separation
#print axioms Erdos186.CFP.Bilu.Section8Case2Concrete.equation810_of_projection
#print axioms Erdos186.CFP.Bilu.Section8Case2Concrete.combine_case2_of_polar_projection_and_cone
