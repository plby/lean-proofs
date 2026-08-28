import Wikipedia.SmoothSixDPoincare.CenteredSheetCorrection
import Wikipedia.SmoothSixDPoincare.WhitneyModelGeometry

/-!
# Simultaneous nonlinear correction on the two Whitney model sheets

Each centered correction uses only its own transverse sheet coordinates.
It therefore vanishes on the other sheet's center projection. Their sum
fixes the whole disk, gives both exact sheet restrictions, and preserves
the entire zero-section derivative when the sheet derivatives match.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

open SheetCorrection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def lowerSheetCoordinates : Space →L[ℝ] Sheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Plane × Plane))).prod
      ((ContinuousLinearMap.fst ℝ Plane Plane).comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Plane × Plane)))

def upperSheetCoordinates : Space →L[ℝ] Sheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Plane × Plane))).prod
      ((ContinuousLinearMap.snd ℝ Plane Plane).comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Plane × Plane)))

theorem lowerSheetCoordinates_apply (p : Space) : lowerSheetCoordinates p = (p.1.1, p.2.1) := rfl
theorem upperSheetCoordinates_apply (p : Space) : upperSheetCoordinates p = (p.1.1, p.2.2) := rfl

def correctedSheetMap (G : Space → F) (Rlo Rhi : Sheet → F) (h : ℝ) (p : Space) : F :=
  G p + centeredCorrection Rlo (G ∘ firstSheet) (lowerSheetCoordinates p) +
    centeredCorrection Rhi (G ∘ secondSheet h) (upperSheetCoordinates p)

omit [NormedSpace ℝ F] in
theorem correctedSheetMap_zero (G : Space → F) (Rlo Rhi : Sheet → F) (h : ℝ) (p : ℝ × ℝ) :
    correctedSheetMap G Rlo Rhi h (p, 0) = G (p, 0) := by
  change G (p, 0) + centeredCorrection Rlo (G ∘ firstSheet) (p.1, 0) +
    centeredCorrection Rhi (G ∘ secondSheet h) (p.1, 0) = G (p, 0)
  rw [centeredCorrection_zero, centeredCorrection_zero, add_zero, add_zero]

omit [NormedSpace ℝ F] in
/-- The lower restriction is exactly the original lower sheet map, not just its derivative. -/
theorem correctedSheetMap_lower {G : Space → F} {Rlo Rhi : Sheet → F} {h : ℝ} (q : Sheet)
    (hcenter : Rlo (q.1, 0) = G (firstSheet (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (firstSheet q) = Rlo q := by
  have hlo : lowerSheetCoordinates (firstSheet q) = q := rfl
  have hhi : upperSheetCoordinates (firstSheet q) = (q.1, 0) := rfl
  rw [correctedSheetMap, hlo, hhi, centeredCorrection_zero, add_zero,
    centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

omit [NormedSpace ℝ F] in
/-- The upper restriction is exact simultaneously with the lower one. -/
theorem correctedSheetMap_upper {G : Space → F} {Rlo Rhi : Sheet → F} {h : ℝ} (q : Sheet)
    (hcenter : Rhi (q.1, 0) = G (secondSheet h (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (secondSheet h q) = Rhi q := by
  have hlo : lowerSheetCoordinates (secondSheet h q) = (q.1, 0) := rfl
  have hhi : upperSheetCoordinates (secondSheet h q) = q := rfl
  rw [correctedSheetMap, hlo, hhi, centeredCorrection_zero, add_zero,
    centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

def correctionDomain (U : Set Space) (Dlo Dhi : Set Sheet) : Set Space :=
  U ∩ (lowerSheetCoordinates ⁻¹' (Dlo ∩ centerProjection ⁻¹' Dlo) ∩
    upperSheetCoordinates ⁻¹' (Dhi ∩ centerProjection ⁻¹' Dhi))

theorem isOpen_correctionDomain {U : Set Space} {Dlo Dhi : Set Sheet}
    (hU : IsOpen U) (hDlo : IsOpen Dlo) (hDhi : IsOpen Dhi) :
    IsOpen (correctionDomain U Dlo Dhi) :=
  hU.inter (((hDlo.inter (hDlo.preimage centerProjection.continuous)).preimage
    lowerSheetCoordinates.continuous).inter
      ((hDhi.inter (hDhi.preimage centerProjection.continuous)).preimage
        upperSheetCoordinates.continuous))

theorem contDiffOn_correctedSheetMap {G : Space → F} {Rlo Rhi : Sheet → F} {h : ℝ}
    {U : Set Space} {Dlo Dhi : Set Sheet}
    (hG : ContDiffOn ℝ ∞ G U) (hRlo : ContDiffOn ℝ ∞ Rlo Dlo)
    (hGlo : ContDiffOn ℝ ∞ (G ∘ firstSheet) Dlo)
    (hRhi : ContDiffOn ℝ ∞ Rhi Dhi)
    (hGhi : ContDiffOn ℝ ∞ (G ∘ secondSheet h) Dhi) :
    ContDiffOn ℝ ∞ (correctedSheetMap G Rlo Rhi h) (correctionDomain U Dlo Dhi) :=
  ((hG.mono inter_subset_left).add
    ((contDiffOn_centeredCorrection hRlo hGlo).comp lowerSheetCoordinates.contDiff.contDiffOn
      (fun _ hp => hp.2.1))).add
        ((contDiffOn_centeredCorrection hRhi hGhi).comp upperSheetCoordinates.contDiff.contDiffOn
          (fun _ hp => hp.2.2))

/-- The simultaneous nonlinear correction preserves the actual whole zero-section derivative. -/
theorem hasFDerivAt_correctedSheetMap_zero {G : Space → F} {Rlo Rhi : Sheet → F} {h : ℝ}
    {p : ℝ × ℝ} {L : Space →L[ℝ] F} {Llo Lhi : Sheet →L[ℝ] F}
    (hG : HasFDerivAt G L (p, 0))
    (hRlo : HasFDerivAt Rlo Llo (p.1, 0))
    (hGlo : HasFDerivAt (G ∘ firstSheet) Llo (p.1, 0))
    (hRhi : HasFDerivAt Rhi Lhi (p.1, 0))
    (hGhi : HasFDerivAt (G ∘ secondSheet h) Lhi (p.1, 0)) :
    HasFDerivAt (correctedSheetMap G Rlo Rhi h) L (p, 0) := by
  have hlo : HasFDerivAt
      (centeredCorrection Rlo (G ∘ firstSheet) ∘ lowerSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (hasFDerivAt_centeredCorrection_zero hRlo hGlo).comp (p, (0 : Plane × Plane))
        lowerSheetCoordinates.hasFDerivAt
  have hhi : HasFDerivAt
      (centeredCorrection Rhi (G ∘ secondSheet h) ∘ upperSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (hasFDerivAt_centeredCorrection_zero hRhi hGhi).comp (p, (0 : Plane × Plane))
        upperSheetCoordinates.hasFDerivAt
  convert (hG.add hlo).add hhi using 1 <;> first | rfl | simp only [add_zero]

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
