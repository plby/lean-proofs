import Wikipedia.HopfProblem.DegreeCollapseGeneralRoundedHandleCorner
import Wikipedia.HopfProblem.DegreeCollapseGeneralHeightCylinder
import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm

/-!
# Regularity on the actual sphere–transverse–height collar

The rounded defining function ignores the sphere factor. Its native manifold
differential is surjective at every zero, because the projection to the
transverse and height coordinates has a concrete linear right inverse.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenRoundedHandleCorner

open NoExoticSixSphere GLOrthonormalization Stiefel GeneralRoundedHandleCorner

abbrev Collar := (Sphere 3 × Vector 4) × ℝ

abbrev collarModel := ((𝓡 3).prod (𝓡 4)).prod 𝓘(ℝ, ℝ)

def collarProjection (p : Collar) : Vector 4 × ℝ := (p.1.2, p.2)

theorem contMDiff_collarProjection :
    ContMDiff collarModel 𝓘(ℝ, Vector 4 × ℝ) ∞ collarProjection :=
  (contMDiff_snd.comp contMDiff_fst).prodMk_space contMDiff_snd

theorem mfderiv_collarProjection_apply (p : Collar) (v : (Vector 3 × Vector 4) × ℝ) :
    mfderiv collarModel 𝓘(ℝ, Vector 4 × ℝ) collarProjection p v = (v.1.2, v.2) := by
  have hv : HasMFDerivAt collarModel (𝓡 4) (fun q : Collar ↦ q.1.2) p
      ((ContinuousLinearMap.snd ℝ (Vector 3) (Vector 4)).comp
        (ContinuousLinearMap.fst ℝ (Vector 3 × Vector 4) ℝ)) :=
    (hasMFDerivAt_snd p.1).comp p (hasMFDerivAt_fst p)
  have ht : HasMFDerivAt collarModel 𝓘(ℝ, ℝ) (fun q : Collar ↦ q.2) p
      (ContinuousLinearMap.snd ℝ (Vector 3 × Vector 4) ℝ) := hasMFDerivAt_snd p
  change mfderiv collarModel 𝓘(ℝ, Vector 4 × ℝ) (fun q : Collar ↦ (q.1.2, q.2)) p v = _
  rw [(hasMFDerivAt_prodMk_space hv ht).mfderiv]
  rfl

theorem surjective_mfderiv_collarProjection (p : Collar) :
    Surjective (mfderiv collarModel 𝓘(ℝ, Vector 4 × ℝ) collarProjection p) := by
  intro v
  exact ⟨((0, v.1), v.2), mfderiv_collarProjection_apply p _⟩

def collarLevel (χ : ContDiffBump (0 : ℝ)) (r : ℝ) : Collar → ℝ :=
  level χ r ∘ collarProjection

theorem contMDiff_collarLevel (χ : ContDiffBump (0 : ℝ)) (r : ℝ) :
    ContMDiff collarModel 𝓘(ℝ, ℝ) ∞ (collarLevel χ r) :=
  (contDiff_level χ r).contMDiff.comp contMDiff_collarProjection

theorem regular_collarLevel_zero (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)
    {p : Collar} (hp : collarLevel χ r p = 0) :
    Surjective (mfderiv collarModel 𝓘(ℝ, ℝ) (collarLevel χ r) p) := by
  rw [collarLevel, mfderiv_comp p
    ((contDiff_level χ r).contMDiff.mdifferentiableAt (by simp))
    (contMDiff_collarProjection.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact (regular_zero χ hr hp).comp (surjective_mfderiv_collarProjection p)

def collarSuperlevelAtlas (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r) :
    SuperlevelAtlas (K := Vector 7) collarModel (collarLevel χ r) :=
  Classical.choice (nonempty_superlevelAtlas (contMDiff_collarLevel χ r)
    (fun _ hp ↦ regular_collarLevel_zero χ hr hp) 7 (by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]))

end Wikipedia.HopfProblem.DegreeCollapse.SevenRoundedHandleCorner
