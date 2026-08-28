import Wikipedia.NoExoticSixSphere.RoundedHandleCorner
import Wikipedia.NoExoticSixSphere.SmoothManifoldHeightCylinder
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

namespace NoExoticSixSphere.RoundedHandleCorner

open GLOrthonormalization Stiefel

abbrev Collar (d : ℕ := 3) := (Sphere 3 × Vector d) × ℝ

abbrev collarModel (d : ℕ := 3) := ((𝓡 3).prod (𝓡 d)).prod 𝓘(ℝ, ℝ)

variable {d : ℕ}

def collarProjection (p : Collar d) : Vector d × ℝ := (p.1.2, p.2)

theorem contMDiff_collarProjection :
    ContMDiff (collarModel d) 𝓘(ℝ, Vector d × ℝ) ∞ (collarProjection (d := d)) :=
  (contMDiff_snd.comp contMDiff_fst).prodMk_space contMDiff_snd

theorem mfderiv_collarProjection_apply (p : Collar d) (v : (Vector 3 × Vector d) × ℝ) :
    mfderiv (collarModel d) 𝓘(ℝ, Vector d × ℝ) collarProjection p v = (v.1.2, v.2) := by
  have hv : HasMFDerivAt (collarModel d) (𝓡 d) (fun q : Collar d ↦ q.1.2) p
      ((ContinuousLinearMap.snd ℝ (Vector 3) (Vector d)).comp
        (ContinuousLinearMap.fst ℝ (Vector 3 × Vector d) ℝ)) :=
    (hasMFDerivAt_snd p.1).comp p (hasMFDerivAt_fst p)
  have ht : HasMFDerivAt (collarModel d) 𝓘(ℝ, ℝ) (fun q : Collar d ↦ q.2) p
      (ContinuousLinearMap.snd ℝ (Vector 3 × Vector d) ℝ) := hasMFDerivAt_snd p
  change mfderiv (collarModel d) 𝓘(ℝ, Vector d × ℝ) (fun q : Collar d ↦ (q.1.2, q.2)) p v = _
  rw [(hasMFDerivAt_prodMk_space hv ht).mfderiv]
  rfl

theorem surjective_mfderiv_collarProjection (p : Collar d) :
    Surjective (mfderiv (collarModel d) 𝓘(ℝ, Vector d × ℝ) collarProjection p) := by
  intro v
  exact ⟨((0, v.1), v.2), mfderiv_collarProjection_apply p _⟩

def collarLevel (χ : ContDiffBump (0 : ℝ)) (r : ℝ) : Collar d → ℝ :=
  level χ r ∘ collarProjection

theorem contMDiff_collarLevel (χ : ContDiffBump (0 : ℝ)) (r : ℝ) :
    ContMDiff (collarModel d) 𝓘(ℝ, ℝ) ∞ (collarLevel (d := d) χ r) :=
  (contDiff_level χ r).contMDiff.comp contMDiff_collarProjection

theorem regular_collarLevel_zero (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)
    {p : Collar d} (hp : collarLevel χ r p = 0) :
    Surjective (mfderiv (collarModel d) 𝓘(ℝ, ℝ) (collarLevel χ r) p) := by
  rw [collarLevel, mfderiv_comp p
    ((contDiff_level χ r).contMDiff.mdifferentiableAt (by simp))
    (contMDiff_collarProjection.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact (regular_zero χ hr hp).comp (surjective_mfderiv_collarProjection p)

def collarSuperlevelAtlasOfDimension (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : 3 + d = k) :
    SuperlevelAtlas (K := Vector k) (collarModel d) (collarLevel (d := d) χ r) :=
  Classical.choice (nonempty_superlevelAtlas (contMDiff_collarLevel (d := d) χ r)
    (fun _ hp ↦ regular_collarLevel_zero χ hr hp) k (by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
      omega))

def collarSuperlevelAtlas (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r) :
    SuperlevelAtlas (K := Vector 6) (collarModel 3) (collarLevel (d := 3) χ r) :=
  collarSuperlevelAtlasOfDimension χ hr 6 rfl

end NoExoticSixSphere.RoundedHandleCorner
