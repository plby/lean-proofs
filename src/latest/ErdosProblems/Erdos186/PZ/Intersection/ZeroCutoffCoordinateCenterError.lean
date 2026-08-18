/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceHalfCoreZeroCutoffPostCFP
import ErdosProblems.Erdos186.PZ.Intersection.SourceAnisotropicCoreBounds

/-!
# Coordinatewise center error at zero coefficient cutoff
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Exact coordinate bound for either orientation of a translated subset of
the source coefficient box. -/
theorem orientedTranslate_width_sub_one_bound
    {ambient r : ℕ} (P : GAP ambient r)
    {X : Finset (LatticePoint r)} {a : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (ha : a ∈ (gapCoefficientBox P).carrier)
    (orientation : Orientation) :
    ∀ y ∈ orientedTranslate orientation a X, ∀ i,
      |(y i : ℝ)| ≤ ((P.widths i - 1 : ℕ) : ℝ) := by
  intro y hy i
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hdiff := Reduction.GAP.sub_mem_differenceCoefficientGAP_of_mem
    P (hX hx) ha
  have hbound := abs_coordinate_le_width_sub_one_of_mem_difference
    P (x - a) hdiff i
  have hboundReal : (|(x - a) i| : ℝ) ≤
      ((P.widths i - 1 : ℕ) : ℝ) := by exact_mod_cast hbound
  cases orientation with
  | forward =>
      simpa only [orientedDeviation, Pi.sub_apply, Int.cast_abs,
        Int.cast_sub] using hboundReal
  | reverse =>
      simpa only [orientedDeviation, Pi.sub_apply, Int.cast_abs,
        Int.cast_sub, abs_sub_comm] using hboundReal

/-- Coordinate-local form of the canonical rounding-core center estimate. -/
theorem canonicalRoundingCore_center_error_at
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (q : LatticePoint d → ℝ) {width : ℝ} (hwidth : 0 ≤ width)
    (hq : ∀ x ∈ A, 0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (i : Fin d) (hbound : ∀ x ∈ A, |(x i : ℝ)| ≤ width) :
    |zonotopeCenter A q i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W) q) i| ≤
      ((((loss + s : ℕ) : ℝ) * ((1 : ℝ) / 2 * width)) +
        (s : ℝ) * width) := by
  have hcoreLocal : |zonotopeCenter A q i -
      zonotopeCenter (canonicalRoundingCore W) q i| ≤
      ((A \ canonicalRoundingCore W).card : ℝ) *
        ((1 : ℝ) / 2 * width) := by
    change |(∑ x ∈ A, q x * (x i : ℝ)) -
        ∑ x ∈ canonicalRoundingCore W, q x * (x i : ℝ)| ≤ _
    rw [← Finset.sum_sdiff_eq_sub (canonicalRoundingCore_subset_input W)]
    calc
      |∑ x ∈ A \ canonicalRoundingCore W, q x * (x i : ℝ)| ≤
          ∑ x ∈ A \ canonicalRoundingCore W, |q x * (x i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ A \ canonicalRoundingCore W,
          ((1 : ℝ) / 2 * width) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxA := (Finset.mem_sdiff.mp hx).1
        rw [abs_mul, abs_of_nonneg (hq x hxA).1]
        exact mul_le_mul (hq x hxA).2 (hbound x hxA)
          (abs_nonneg _) (by positivity)
      _ = ((A \ canonicalRoundingCore W).card : ℝ) *
          ((1 : ℝ) / 2 * width) := by simp
  have hcard : ((A \ canonicalRoundingCore W).card : ℝ) ≤
      (loss + s : ℕ) := by
    exact_mod_cast card_sdiff_canonicalRoundingCore_le W
  have hcore' : |zonotopeCenter A q i -
      zonotopeCenter (canonicalRoundingCore W) q i| ≤
      ((loss + s : ℕ) : ℝ) * ((1 : ℝ) / 2 * width) :=
    hcoreLocal.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have htranslate : |(W.translatePoint i : ℝ)| ≤ (s : ℝ) * width := by
    obtain ⟨T, hT, hsum⟩ :=
      GAP.mem_subsetSums_iff.mp (translatePoint_mem_subsetSums_reserved W)
    have hcardT : T.card ≤ s :=
      (Finset.card_le_card hT).trans W.reserved_small
    have hsumBound : |∑ x ∈ T, (x i : ℝ)| ≤ (T.card : ℝ) * width := by
      calc
        |∑ x ∈ T, (x i : ℝ)| ≤ ∑ x ∈ T, |(x i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x ∈ T, width := by
          apply Finset.sum_le_sum
          intro x hx
          exact hbound x (W.reserved_subset (hT hx))
        _ = (T.card : ℝ) * width := by simp
    have hcoord : (W.translatePoint i : ℝ) = ∑ x ∈ T, (x i : ℝ) := by
      have hi : W.translatePoint i = ∑ x ∈ T, x i := by
        simpa using congrFun hsum.symm i
      exact_mod_cast hi
    rw [hcoord]
    exact hsumBound.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardT) hwidth)
  change |zonotopeCenter A q i -
      ((W.translatePoint i : ℝ) +
        zonotopeCenter (canonicalRoundingCore W) q i)| ≤ _
  calc
    |zonotopeCenter A q i -
        ((W.translatePoint i : ℝ) +
          zonotopeCenter (canonicalRoundingCore W) q i)| =
        |(zonotopeCenter A q i -
          zonotopeCenter (canonicalRoundingCore W) q i) -
            (W.translatePoint i : ℝ)| := by
          congr 1
          ring
    _ ≤ |zonotopeCenter A q i -
          zonotopeCenter (canonicalRoundingCore W) q i| +
        |(W.translatePoint i : ℝ)| := abs_sub _ _
    _ ≤ (((loss + s : ℕ) : ℝ) * ((1 : ℝ) / 2 * width)) +
        (s : ℝ) * width := add_le_add hcore' htranslate

namespace HighCoefficientSideSelectionData

variable {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}

/-- Exact forward CFP center-error budget in coordinate `i` at cutoff zero. -/
def forwardZeroCoordinateCenterError
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma)
    (i : Fin (selector.chosen A hA).dimension) : ℝ :=
  (((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ) * (1 / 2 : ℝ) +
      E.side₁.reserveBound) *
    ((selector.chosen A hA).progression.widths i - 1 : ℕ)

/-- Exact reverse CFP center-error budget in coordinate `i` at cutoff zero. -/
def reverseZeroCoordinateCenterError
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma)
    (i : Fin (selector.chosen A hA).dimension) : ℝ :=
  (((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ) * (1 / 2 : ℝ) +
      E.side₂.reserveBound) *
    ((selector.chosen A hA).progression.widths i - 1 : ℕ)

theorem commonCenter_forward_zero_coordinate_error
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma)
    (hmu : 0 < mu)
    (i : Fin (selector.chosen A hA).dimension) :
    |E.commonCenter i -
        (realVector E.forwardWitness.translatePoint +
          zonotopeCenter E.forwardRoundingCore
            (D.scaledForwardCoefficient
              (highCoefficientZonotopeScale D))) i| ≤
      E.forwardZeroCoordinateCenterError i := by
  let S := selector.chosen A hA
  let scale := highCoefficientZonotopeScale D
  let W := E.forwardWitness
  let T := orientedTranslate .forward D.a D.A₁
  have hinput : orientedTranslate .forward D.a (D.largeA₁ 0) = T := by
    simp only [ConvexPoolsData.largeA₁_zero, T]
  have hscale : 0 ≤ scale := D.highCoefficientZonotopeScale_nonneg hmu
  have hhalf : scale * (mu * S.identifiedCore.card)⁻¹ = (1 : ℝ) / 2 :=
    D.highCoefficientZonotopeScale_mul_cap hmu
  have hq : ∀ y ∈ T,
      0 ≤ D.scaledForwardCoefficient scale y ∧
        D.scaledForwardCoefficient scale y ≤ (1 : ℝ) / 2 := by
    intro y hy
    have hb := D.forwardCoefficient_bounds hy
    exact ⟨mul_nonneg hscale hb.1,
      (mul_le_mul_of_nonneg_left hb.2 hscale).trans hhalf.le⟩
  have hbound : ∀ y ∈ T, ∀ j,
      |(y j : ℝ)| ≤ ((S.progression.widths j - 1 : ℕ) : ℝ) := by
    exact orientedTranslate_width_sub_one_bound S.progression
      ((D.A₁_subset_erase.trans (Finset.erase_subset _ _)).trans
        S.identifiedCore_subset_coefficientBox)
      (S.identifiedCore_subset_coefficientBox D.a_mem) .forward
  have hwidth : 0 ≤ ((S.progression.widths i - 1 : ℕ) : ℝ) := by positivity
  have hround := canonicalRoundingCore_center_error_at W
    (D.scaledForwardCoefficient scale) hwidth
    (by simpa only [W, hinput] using hq) i
    (by simpa only [W, hinput] using fun y hy ↦ hbound y hy i)
  have hcenterInputAt :
      zonotopeCenter (orientedTranslate .forward D.a (D.largeA₁ 0))
          (D.scaledForwardCoefficient scale) i =
        zonotopeCenter T (D.scaledForwardCoefficient scale) i :=
    congrFun (congrArg
      (fun U ↦ zonotopeCenter U (D.scaledForwardCoefficient scale)) hinput) i
  calc
    |E.commonCenter i -
        (realVector E.forwardWitness.translatePoint +
          zonotopeCenter E.forwardRoundingCore
            (D.scaledForwardCoefficient
              (highCoefficientZonotopeScale D))) i| =
      |zonotopeCenter (orientedTranslate .forward D.a (D.largeA₁ 0))
          (D.scaledForwardCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale)) i| := by
      simp only [commonCenter, S, scale, W]
      rw [hcenterInputAt]
    _ ≤ (((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ) *
          ((1 : ℝ) / 2 *
            (((S.progression.widths i - 1 : ℕ) : ℝ)))) +
        (E.side₁.reserveBound : ℝ) *
          (((S.progression.widths i - 1 : ℕ) : ℝ)) := hround
    _ = E.forwardZeroCoordinateCenterError i := by
      simp only [forwardZeroCoordinateCenterError, S, Nat.cast_add]
      ring

theorem commonCenter_reverse_zero_coordinate_error
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma)
    (hmu : 0 < mu)
    (i : Fin (selector.chosen A hA).dimension) :
    |E.commonCenter i -
        (realVector E.reverseWitness.translatePoint +
          zonotopeCenter E.reverseRoundingCore
            (D.scaledReverseCoefficient
              (highCoefficientZonotopeScale D))) i| ≤
      E.reverseZeroCoordinateCenterError i := by
  let S := selector.chosen A hA
  let scale := highCoefficientZonotopeScale D
  let W := E.reverseWitness
  let T := orientedTranslate .reverse D.a D.A₂
  have hinput : orientedTranslate .reverse D.a (D.largeA₂ 0) = T := by
    simp only [ConvexPoolsData.largeA₂_zero, T]
  have hscale : 0 ≤ scale := D.highCoefficientZonotopeScale_nonneg hmu
  have hhalf : scale * (mu * S.identifiedCore.card)⁻¹ = (1 : ℝ) / 2 :=
    D.highCoefficientZonotopeScale_mul_cap hmu
  have hq : ∀ y ∈ T,
      0 ≤ D.scaledReverseCoefficient scale y ∧
        D.scaledReverseCoefficient scale y ≤ (1 : ℝ) / 2 := by
    intro y hy
    have hb := D.reverseCoefficient_bounds hy
    exact ⟨mul_nonneg hscale hb.1,
      (mul_le_mul_of_nonneg_left hb.2 hscale).trans hhalf.le⟩
  have hbound : ∀ y ∈ T, ∀ j,
      |(y j : ℝ)| ≤ ((S.progression.widths j - 1 : ℕ) : ℝ) := by
    exact orientedTranslate_width_sub_one_bound S.progression
      ((D.A₂_subset_erase.trans (Finset.erase_subset _ _)).trans
        S.identifiedCore_subset_coefficientBox)
      (S.identifiedCore_subset_coefficientBox D.a_mem) .reverse
  have hwidth : 0 ≤ ((S.progression.widths i - 1 : ℕ) : ℝ) := by positivity
  have hround := canonicalRoundingCore_center_error_at W
    (D.scaledReverseCoefficient scale) hwidth
    (by simpa only [W, hinput] using hq) i
    (by simpa only [W, hinput] using fun y hy ↦ hbound y hy i)
  have hcenterInputAt :
      zonotopeCenter (orientedTranslate .reverse D.a (D.largeA₂ 0))
          (D.scaledReverseCoefficient scale) i =
        zonotopeCenter T (D.scaledReverseCoefficient scale) i :=
    congrFun (congrArg
      (fun U ↦ zonotopeCenter U (D.scaledReverseCoefficient scale)) hinput) i
  calc
    |E.commonCenter i -
        (realVector E.reverseWitness.translatePoint +
          zonotopeCenter E.reverseRoundingCore
            (D.scaledReverseCoefficient
              (highCoefficientZonotopeScale D))) i| =
      |zonotopeCenter (orientedTranslate .reverse D.a (D.largeA₂ 0))
          (D.scaledReverseCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledReverseCoefficient scale)) i| := by
      simp only [commonCenter, S, scale, W]
      rw [D.zonotopeCenter_scaledForward_eq_scaledReverse scale,
        hcenterInputAt]
    _ ≤ (((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ) *
          ((1 : ℝ) / 2 *
            (((S.progression.widths i - 1 : ℕ) : ℝ)))) +
        (E.side₂.reserveBound : ℝ) *
          (((S.progression.widths i - 1 : ℕ) : ℝ)) := hround
    _ = E.reverseZeroCoordinateCenterError i := by
      simp only [reverseZeroCoordinateCenterError, S, Nat.cast_add]
      ring

end HighCoefficientSideSelectionData

end

end Erdos186.PZ.Intersection
