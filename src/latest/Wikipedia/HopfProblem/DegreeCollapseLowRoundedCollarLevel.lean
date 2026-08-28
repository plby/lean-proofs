import Wikipedia.HopfProblem.DegreeCollapseGeneralRoundedHandleCorner
import Wikipedia.HopfProblem.DegreeCollapseLowHeightCylinder
import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm

/-!

# The regular defining function in native low-dimensional collar coordinates

The sphere and transverse dimensions are independent. Projection to the
transverse and height variables has a concrete right inverse, so the actual
native derivative of the rounded level is surjective at every zero. Its
boundary atlas uses dimension seven only after the dimension equality.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowRoundedHandleCorner

open NoExoticSixSphere GLOrthonormalization Stiefel GeneralRoundedHandleCorner

abbrev Collar (d q : ℕ) := (NoExoticSixSphere.Sphere d × Vector q) × ℝ

abbrev collarModel (d q : ℕ) := ((𝓡 d).prod (𝓡 q)).prod 𝓘(ℝ, ℝ)

variable {d q : ℕ}

def collarProjection (p : Collar d q) : Vector q × ℝ := (p.1.2, p.2)

theorem contMDiff_collarProjection :
    ContMDiff (collarModel d q) 𝓘(ℝ, Vector q × ℝ) ∞
      (collarProjection (d := d) (q := q)) :=
  (contMDiff_snd.comp contMDiff_fst).prodMk_space contMDiff_snd

theorem mfderiv_collarProjection_apply (p : Collar d q) (v : (Vector d × Vector q) × ℝ) :
    mfderiv (collarModel d q) 𝓘(ℝ, Vector q × ℝ) collarProjection p v =
      (v.1.2, v.2) := by
  have hv : HasMFDerivAt (collarModel d q) (𝓡 q) (fun z : Collar d q ↦ z.1.2) p
      ((ContinuousLinearMap.snd ℝ (Vector d) (Vector q)).comp
        (ContinuousLinearMap.fst ℝ (Vector d × Vector q) ℝ)) :=
    (hasMFDerivAt_snd p.1).comp p (hasMFDerivAt_fst p)
  have ht : HasMFDerivAt (collarModel d q) 𝓘(ℝ, ℝ) (fun z : Collar d q ↦ z.2) p
      (ContinuousLinearMap.snd ℝ (Vector d × Vector q) ℝ) := hasMFDerivAt_snd p
  change mfderiv (collarModel d q) 𝓘(ℝ, Vector q × ℝ)
    (fun z : Collar d q ↦ (z.1.2, z.2)) p v = _
  rw [(hasMFDerivAt_prodMk_space hv ht).mfderiv]
  rfl

theorem surjective_mfderiv_collarProjection (p : Collar d q) :
    Surjective (mfderiv (collarModel d q) 𝓘(ℝ, Vector q × ℝ) collarProjection p) := by
  intro v
  exact ⟨((0, v.1), v.2), mfderiv_collarProjection_apply p _⟩

def collarLevel (χ : ContDiffBump (0 : ℝ)) (r : ℝ) : Collar d q → ℝ :=
  level χ r ∘ collarProjection

theorem contMDiff_collarLevel (χ : ContDiffBump (0 : ℝ)) (r : ℝ) :
    ContMDiff (collarModel d q) 𝓘(ℝ, ℝ) ∞ (collarLevel (d := d) (q := q) χ r) :=
  (contDiff_level (d := q) χ r).contMDiff.comp
    (contMDiff_collarProjection (d := d) (q := q))

theorem regular_collarLevel_zero (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)
    {p : Collar d q} (hp : collarLevel χ r p = 0) :
    Surjective (mfderiv (collarModel d q) 𝓘(ℝ, ℝ) (collarLevel χ r) p) := by
  rw [collarLevel, mfderiv_comp p
    ((contDiff_level χ r).contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_collarProjection (d := d) (q := q)).mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv]
  exact (regular_zero χ hr hp).comp (surjective_mfderiv_collarProjection p)

def collarSuperlevelAtlas (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)
    (hdim : d + q = 7) :
    SuperlevelAtlas (K := Vector 7) (collarModel d q)
      (collarLevel (d := d) (q := q) χ r) :=
  Classical.choice (nonempty_superlevelAtlas (contMDiff_collarLevel (d := d) (q := q) χ r)
    (fun _ hp ↦ regular_collarLevel_zero χ hr hp) 7 (by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
      omega))

end Wikipedia.HopfProblem.DegreeCollapse.LowRoundedHandleCorner
