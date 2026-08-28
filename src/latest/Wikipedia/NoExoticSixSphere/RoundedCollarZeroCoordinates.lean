import Wikipedia.NoExoticSixSphere.RoundedCornerZeroCoordinates
import Wikipedia.NoExoticSixSphere.RoundedCollarLevel

/-! # Explicit sphere-product coordinates on the actual rounded collar zero set -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RoundedHandleCorner

open GLOrthonormalization SmoothCornerRounding

abbrev BoundaryParameters := Sphere 3 × (Sphere 2 × ℝ)

abbrev boundaryParameterModel := (𝓡 3).prod ((𝓡 2).prod 𝓘(ℝ, ℝ))

variable (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)

def collarZeroPoint (r : ℝ) (p : BoundaryParameters) : Collar :=
  ((p.1, (zeroPoint χ r p.2).1), (zeroPoint χ r p.2).2)

theorem collarLevel_collarZeroPoint (r : ℝ) (p : BoundaryParameters) :
    collarLevel χ r (collarZeroPoint χ r p) = 0 := level_zeroPoint χ r p.2

def collarZeroInverse (r : ℝ) (b : Sphere 2) (p : Collar) : BoundaryParameters :=
  (p.1.1, zeroInverse r b (collarProjection p))

include hr in
theorem collarZeroInverse_collarZeroPoint (b : Sphere 2) (p : BoundaryParameters) :
    collarZeroInverse r b (collarZeroPoint χ r p) = p :=
  Prod.ext rfl (zeroInverse_zeroPoint χ hr b p.2)

include hr in
theorem collarZeroPoint_collarZeroInverse (b : Sphere 2) {p : Collar}
    (hp : collarLevel χ r p = 0) : collarZeroPoint χ r (collarZeroInverse r b p) = p := by
  have he := zeroPoint_zeroInverse χ hr b hp
  exact Prod.ext (Prod.ext rfl (congrArg (fun q : Vector 3 × ℝ ↦ q.1) he))
    (congrArg (fun q : Vector 3 × ℝ ↦ q.2) he)

include hr in
theorem contMDiff_collarZeroPoint :
    ContMDiff boundaryParameterModel collarModel ∞ (collarZeroPoint χ r) := by
  have hz := (contMDiff_zeroPoint χ hr).comp
    (show ContMDiff boundaryParameterModel ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (Prod.snd : BoundaryParameters → Sphere 2 × ℝ) from contMDiff_snd)
  exact (contMDiff_fst.prodMk (contDiff_fst.contMDiff.comp hz)).prodMk
    (contDiff_snd.contMDiff.comp hz)

theorem contMDiffAt_collarZeroInverse (b : Sphere 2) {p : Collar} (hp : p.1.2 ≠ 0) :
    ContMDiffAt collarModel boundaryParameterModel ∞ (collarZeroInverse r b) p :=
  (contMDiff_fst.comp contMDiff_fst).contMDiffAt.prodMk
    ((contMDiffAt_zeroInverse b hp).comp p contMDiff_collarProjection.contMDiffAt)

def collarZeroEquiv (b : Sphere 2) : BoundaryParameters ≃ {p : Collar // collarLevel χ r p = 0}
    where
  toFun p := ⟨collarZeroPoint χ r p, collarLevel_collarZeroPoint χ r p⟩
  invFun p := collarZeroInverse r b p.val
  left_inv := collarZeroInverse_collarZeroPoint χ hr b
  right_inv p := Subtype.ext (collarZeroPoint_collarZeroInverse χ hr b p.property)

def collarZeroDiffeomorph (b : Sphere 2)
    (R : RegularLevelAtlas (K := Vector 6) collarModel (collarLevel (d := 3) χ r)) :
    letI := R.chartedSpace;
    BoundaryParameters ≃ₘ⟮boundaryParameterModel, 𝓡 6⟯
      {p : Collar // collarLevel χ r p = 0} := by
  let := R.chartedSpace
  refine
    { toEquiv := collarZeroEquiv χ hr b
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (R.contMDiff_iff_ambient _).mpr (contMDiff_collarZeroPoint χ hr)
  · intro p
    exact (contMDiffAt_collarZeroInverse b
      (transverse_ne_zero_of_level_zero χ hr p.property)).comp p
        R.contMDiff_subtype_val.contMDiffAt

theorem collarZeroDiffeomorph_ambient (b : Sphere 2)
    (R : RegularLevelAtlas (K := Vector 6) collarModel (collarLevel (d := 3) χ r))
    (p : BoundaryParameters) : letI := R.chartedSpace;
    (collarZeroDiffeomorph χ hr b R p).val = collarZeroPoint χ r p := rfl

end NoExoticSixSphere.RoundedHandleCorner
