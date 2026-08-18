/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.CoordinateFlag
import ErdosProblems.Erdos186.CFP.Bilu.Section8Case2
import ErdosProblems.Erdos186.CFP.Bilu.Section8Case2Concrete

/-!
# Bilu Section 8.3, Case 2 with the canonical Euclidean flag

This removes the abstract cone-chain input from the concrete Case 2
calculation.  The section is the pullback along the canonical first `d`
coordinates in `ℝ^(d+k)`, and its volume estimate follows from the actual
isometric cone construction.
-/

namespace Erdos186.CFP.Bilu.Section8Case2Canonical

open MeasureTheory Set Module Submodule
open scoped ENNReal RealInnerProductSpace
open PolarSeparation ProjectionCovolume ProjectionVolumeCoarse
open VolumeSections Section8Case2 Section8GeometrySynthesis
open Section8Case2Concrete

/-- Isometric image bookkeeping for the section in equation (8.10).
If an isometric coordinate map sends the projected section exactly onto
the image of the canonical prefix pullback, their intrinsic volumes agree.
No volume comparison is assumed. -/
theorem projection_section_volume_eq_canonical_pullback
    {n d k : ℕ} {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (q : W →ₗᵢ[ℝ] Base (d + k)) (T : Set L) (B : Set (Base (d + k)))
    (hrank : finrank ℝ L = d)
    (himage :
      q '' (projectionRestrict W L '' T) =
        canonicalCoordinateFlagF d k 0 (Nat.zero_le k) ''
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B)) :
    μHE[finrank ℝ L] (projectionRestrict W L '' T) =
      intrinsicVolume d
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) := by
  rw [hrank]
  simp only [intrinsicVolume]
  calc
    μHE[d] (projectionRestrict W L '' T) =
        μHE[d] (q '' (projectionRestrict W L '' T)) := by
      symm
      exact q.isometry.euclideanHausdorffMeasure_image _
    _ = μHE[d]
        (canonicalCoordinateFlagF d k 0 (Nat.zero_le k) ''
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B)) := by
      rw [himage]
    _ = μHE[d]
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) := by
      exact (canonicalCoordinateFlagF d k 0
        (Nat.zero_le k)).isometry.euclideanHausdorffMeasure_image _

/-- Monotone form of the preceding coordinate bookkeeping.  This is the
form actually needed in Case 2: the projected lattice section is contained
in the corresponding section of the projected ambient body. -/
theorem projection_section_volume_le_canonical_pullback
    {n d k : ℕ} {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (q : W →ₗᵢ[ℝ] Base (d + k)) (T : Set L) (B : Set (Base (d + k)))
    (hrank : finrank ℝ L = d)
    (himage :
      q '' (projectionRestrict W L '' T) ⊆
        canonicalCoordinateFlagF d k 0 (Nat.zero_le k) ''
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B)) :
    μHE[finrank ℝ L] (projectionRestrict W L '' T) ≤
      intrinsicVolume d
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) := by
  rw [hrank]
  simp only [intrinsicVolume]
  calc
    μHE[d] (projectionRestrict W L '' T) =
        μHE[d] (q '' (projectionRestrict W L '' T)) := by
      symm
      exact q.isometry.euclideanHausdorffMeasure_image _
    _ ≤ μHE[d]
        (canonicalCoordinateFlagF d k 0 (Nat.zero_le k) ''
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B)) :=
      measure_mono himage
    _ = μHE[d]
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) := by
      exact (canonicalCoordinateFlagF d k 0
        (Nat.zero_le k)).isometry.euclideanHausdorffMeasure_image _

/-- Solve a nonzero finite `ENNReal` cross-multiplied section estimate. -/
theorem section_le_of_factor_mul_le
    {factor sectionVolume ambient bound : ENNReal}
    (hfactor0 : factor ≠ 0) (hfactortop : factor ≠ ∞)
    (h : factor * sectionVolume ≤ bound * ambient) :
    sectionVolume ≤ factor⁻¹ * bound * ambient := by
  calc
    sectionVolume = factor⁻¹ * (factor * sectionVolume) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hfactor0 hfactortop, one_mul]
    _ ≤ factor⁻¹ * (bound * ambient) := by gcongr
    _ = factor⁻¹ * bound * ambient := by rw [mul_assoc]

/-- All four estimates in Bilu Section 8.3, Case 2, with equation (8.9)
supplied by the canonical isometric coordinate flag rather than by an
assumed cone chain.

The sole coordinate-bookkeeping equality `hsection` says that the
orthogonal-projection section from equation (8.10) is the pullback of the
projected body along the canonical first `d` coordinates. -/
theorem combine_case2_of_polar_projection_and_canonical_flag
    {n d k : ℕ} {rho gaugeW C : ℝ}
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (u l : EuclideanSpace ℝ (Fin n)) (T : Set L)
    {Omega : Set (Base (d + k) × ℝ)} {V volumeFactor : ENNReal}
    (hrho : 0 < rho) (hC : 0 < C) (hgaugeW : 0 < gaugeW)
    (hgaugeHalf : 2 * gaugeW ≤ 1)
    (hinner : C < |⟪u, l⟫|)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (hlL : l ∈ Lᗮ) (hl0 : l ≠ 0)
    (hOmega : MeasurableSet Omega)
    (hhalf : MeasurableSet (halfBaseProjection Omega))
    (hbase : MeasurableSet (baseProjection Omega))
    (hconv : Convex ℝ Omega)
    (hbaseConv : Convex ℝ (baseProjection Omega))
    (hbaseBall : Metric.closedBall (0 : Base (d + k)) rho ⊆
      baseProjection Omega)
    (hsegment : ∀ t ∈ Set.Icc (-(‖u‖ / gaugeW)) (‖u‖ / gaugeW),
      ((0 : Base (d + k)), t) ∈ Omega)
    (hOmegaVolume : (volume.prod volume) Omega ≤ volumeFactor * V)
    (hsection :
      μHE[finrank ℝ L] (projectionRestrict W L '' T) ≤
        intrinsicVolume d
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹'
            baseProjection Omega)) :
    2 * ENNReal.ofReal C * volume T ≤
      ((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ * volumeFactor *
        (((d.factorial : ENNReal) * ENNReal.ofReal (rho ^ k))⁻¹ *
          ((d + k).factorial : ENNReal)) *
        ENNReal.ofReal ‖l‖ * V := by
  let c82 : ENNReal :=
    ((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ * volumeFactor
  let factor : ENNReal :=
    (d.factorial : ENNReal) * ENNReal.ofReal (rho ^ k)
  let c83 : ENNReal := factor⁻¹ * ((d + k).factorial : ENNReal)
  let sectionVolume : ENNReal :=
    intrinsicVolume d
      ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹'
        baseProjection Omega)
  have h87 : 2 * ENNReal.ofReal C * ENNReal.ofReal gaugeW ≤
      ENNReal.ofReal |⟪u, l⟫| :=
    equation87_of_strict_polar_separation hC hgaugeW.le hgaugeHalf hinner
  have h810projection :=
    equation810_of_projection u l hcodim huW hu0 hlL hl0 T
  have h810 : ENNReal.ofReal |⟪u, l⟫| * volume T ≤
      ENNReal.ofReal ‖u‖ * ENNReal.ofReal ‖l‖ * sectionVolume := by
    calc
      ENNReal.ofReal |⟪u, l⟫| * volume T ≤
          ENNReal.ofReal ‖u‖ * ENNReal.ofReal ‖l‖ *
            μHE[finrank ℝ L] (projectionRestrict W L '' T) := h810projection
      _ ≤ ENNReal.ofReal ‖u‖ * ENNReal.ofReal ‖l‖ * sectionVolume := by
        dsimp only [sectionVolume]
        gcongr
  have h88 : ENNReal.ofReal ‖u‖ *
      intrinsicVolume (d + k) (baseProjection Omega) ≤
        c82 * ENNReal.ofReal gaugeW * V := by
    have hproj := equation88_of_half_projection
      (norm_nonneg u) hgaugeW hOmega hhalf hconv hsegment hOmegaVolume
    rw [show intrinsicVolume (d + k) (baseProjection Omega) =
        volume (baseProjection Omega) by
      simp only [intrinsicVolume]
      have hm :
          (Measure.euclideanHausdorffMeasure (d + k) :
              Measure (Base (d + k))) = volume := by
        simpa using
          (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
            (V := Base (d + k)))
      rw [hm]]
    exact hproj
  have hcross := origin_centered_coordinate_section_bound
    hrho hbase hbaseConv hbaseBall
  have hfactor0 : factor ≠ 0 := by
    dsimp only [factor]
    apply mul_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero d
    · intro hzero
      rw [ENNReal.ofReal_eq_zero] at hzero
      exact (not_le.mpr (pow_pos hrho k)) hzero
  have hfactortop : factor ≠ ∞ := by
    dsimp only [factor]
    finiteness
  have h89 : sectionVolume ≤ c83 *
      intrinsicVolume (d + k) (baseProjection Omega) := by
    exact section_le_of_factor_mul_le hfactor0 hfactortop hcross
  have hgauge0 : ENNReal.ofReal gaugeW ≠ 0 := by
    intro hzero
    rw [ENNReal.ofReal_eq_zero] at hzero
    exact (not_le.mpr hgaugeW) hzero
  have hresult := combine_equations_8_7_to_8_10_ennreal
    hgauge0 ENNReal.ofReal_ne_top h87 h88 h89 h810
  simpa only [c82, c83, factor, sectionVolume, mul_assoc] using hresult

/-- Coordinate-image form of
`combine_case2_of_polar_projection_and_canonical_flag`.  The equality of
section volumes is now derived from an actual isometric map and an equality
of sets, which is the form produced by choosing orthonormal coordinates on
the projected subspace. -/
theorem combine_case2_of_isometric_section_identification
    {n d k : ℕ} {rho gaugeW C : ℝ}
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (u l : EuclideanSpace ℝ (Fin n)) (T : Set L)
    (q : W →ₗᵢ[ℝ] Base (d + k))
    {Omega : Set (Base (d + k) × ℝ)} {V volumeFactor : ENNReal}
    (hrho : 0 < rho) (hC : 0 < C) (hgaugeW : 0 < gaugeW)
    (hgaugeHalf : 2 * gaugeW ≤ 1)
    (hinner : C < |⟪u, l⟫|)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (hrank : finrank ℝ L = d)
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (hlL : l ∈ Lᗮ) (hl0 : l ≠ 0)
    (hOmega : MeasurableSet Omega)
    (hhalf : MeasurableSet (halfBaseProjection Omega))
    (hbase : MeasurableSet (baseProjection Omega))
    (hconv : Convex ℝ Omega)
    (hbaseConv : Convex ℝ (baseProjection Omega))
    (hbaseBall : Metric.closedBall (0 : Base (d + k)) rho ⊆
      baseProjection Omega)
    (hsegment : ∀ t ∈ Set.Icc (-(‖u‖ / gaugeW)) (‖u‖ / gaugeW),
      ((0 : Base (d + k)), t) ∈ Omega)
    (hOmegaVolume : (volume.prod volume) Omega ≤ volumeFactor * V)
    (hsectionImage :
      q '' (projectionRestrict W L '' T) ⊆
        canonicalCoordinateFlagF d k 0 (Nat.zero_le k) ''
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹'
            baseProjection Omega)) :
    2 * ENNReal.ofReal C * volume T ≤
      ((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ * volumeFactor *
        (((d.factorial : ENNReal) * ENNReal.ofReal (rho ^ k))⁻¹ *
          ((d + k).factorial : ENNReal)) *
        ENNReal.ofReal ‖l‖ * V := by
  apply combine_case2_of_polar_projection_and_canonical_flag
    u l T hrho hC hgaugeW hgaugeHalf hinner hcodim huW hu0 hlL hl0
    hOmega hhalf hbase hconv hbaseConv hbaseBall hsegment hOmegaVolume
  exact projection_section_volume_le_canonical_pullback
    q T (baseProjection Omega) hrank hsectionImage

end Erdos186.CFP.Bilu.Section8Case2Canonical

#print axioms Erdos186.CFP.Bilu.Section8Case2Canonical.section_le_of_factor_mul_le
#print axioms Erdos186.CFP.Bilu.Section8Case2Canonical.projection_section_volume_eq_canonical_pullback
#print axioms Erdos186.CFP.Bilu.Section8Case2Canonical.projection_section_volume_le_canonical_pullback
#print axioms Erdos186.CFP.Bilu.Section8Case2Canonical.combine_case2_of_polar_projection_and_canonical_flag
#print axioms Erdos186.CFP.Bilu.Section8Case2Canonical.combine_case2_of_isometric_section_identification
