import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonDifferential
import Wikipedia.HomotopyGroupsOfSpheres.RealCurveCalculus

/-!
# Linear coordinate velocities for reversible vertex variations

The derivative of the actual exponential-coordinate map is a continuous
linear map from reversible vertex fields to the chosen polygon chart. This
construction requires no globally continuous choice of congruence frames.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

abbrev ReversibleModel (v : VertexSpace.Space N m) := (j : Fin m) → ReversibleDirection (v j)

local instance reversibleModelSelfChart (v : VertexSpace.Space N m) :
    LocalLogarithm.NormedChartedSpace (ReversibleModel v) (ReversibleModel v) := chartedSpaceSelf _

local instance coordinateModelSelfChart :
    LocalLogarithm.NormedChartedSpace (Model N m) (Model N m) := chartedSpaceSelf _

local instance coordinateMatrixSelfChart :
    LocalLogarithm.NormedChartedSpace (Matrix N N ℂ) (Matrix N N ℂ) := chartedSpaceSelf _

def variationPoint (v : VertexSpace.Space N m) (W : ReversibleModel v) : VertexSpace.Space N m :=
  vertexVariation v W 1

theorem variationPoint_smul (v : VertexSpace.Space N m) (W : ReversibleModel v) (s : ℝ) :
    variationPoint v (s • W) = vertexVariation v W s := by
  funext j
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (v j).val.val.val * NormedSpace.exp (1 • (s • (W j).val.val)) =
    (v j).val.val.val * NormedSpace.exp (s • (W j).val.val)
  rw [one_smul]

theorem variationPoint_zero (v : VertexSpace.Space N m) : variationPoint v 0 = v := by
  simpa only [zero_smul] using (variationPoint_smul v (0 : ReversibleModel v) 0).trans
    (vertexVariation_zero v 0)

theorem contMDiff_variationPoint (v : VertexSpace.Space N m) :
    ContMDiff 𝓘(ℝ, ReversibleModel v) 𝓘(ℝ, Model N m) ∞ (variationPoint v) := by
  apply VertexSpace.contMDiff_iff_coordinatewise.mpr
  intro j
  apply Smoothness.contMDiff_iff_matrix.mpr
  let L : ReversibleModel v →ₗ[ℝ] Matrix N N ℂ := {
    toFun W := (W j).val.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hL : ContDiff ℝ ∞ L := finiteLinearMap_contDiff L
  have h : ContDiff ℝ ∞ (fun W : ReversibleModel v ↦
      (v j).val.val.val * NormedSpace.exp (L W)) :=
    contDiff_const.mul (ComplexMatrixLocalLogarithm.contDiff_exp.comp hL)
  change ContMDiff 𝓘(ℝ, ReversibleModel v) 𝓘(ℝ, Matrix N N ℂ) ∞
    (fun W : ReversibleModel v ↦ (v j).val.val.val * NormedSpace.exp (1 • (W j).val.val))
  simpa only [one_smul] using! h.contMDiff

def variationCoordinates (v : VertexSpace.Space N m) (W : ReversibleModel v) : Model N m :=
  atVertices v (variationPoint v W)

theorem variationCoordinates_zero (v : VertexSpace.Space N m) : variationCoordinates v 0 = 0 := by
  rw [variationCoordinates, variationPoint_zero, atVertices_self]

theorem contDiffAt_variationCoordinates (v : VertexSpace.Space N m) :
    ContDiffAt ℝ ∞ (variationCoordinates v) 0 := by
  have hmem : variationPoint v 0 ∈ (atVertices v).source := by
    rw [variationPoint_zero]
    exact mem_atVertices_source v
  have h := (contMDiffAt_iff_target_of_mem_source
    (I := 𝓘(ℝ, ReversibleModel v)) (I' := 𝓘(ℝ, Model N m)) (f := variationPoint v)
    (x := 0) (y := v) hmem).mp (contMDiff_variationPoint v).contMDiffAt
  simpa only [] using! h.2.contDiffAt

def coordinateVelocity (v : VertexSpace.Space N m) : ReversibleModel v →L[ℝ] Model N m :=
  fderiv ℝ (variationCoordinates v) 0

theorem hasDerivAt_vertexVariation_coordinates (v : VertexSpace.Space N m)
    (W : ReversibleModel v) :
    HasDerivAt (fun s ↦ atVertices v (vertexVariation v W s)) (coordinateVelocity v W) 0 := by
  have hf : HasFDerivAt (variationCoordinates v) (coordinateVelocity v) ((0 : ℝ) • W) := by
    rw [zero_smul]
    exact ((contDiffAt_variationCoordinates v).differentiableAt (by simp)).hasFDerivAt
  have h := hf.comp_hasDerivAt 0 (real_hasDerivAt_smul (E := ReversibleModel v) W 0)
  simpa only [Function.comp_def, variationCoordinates, variationPoint_smul] using! h

theorem contDiffAt_vertexVariation_coordinates (v : VertexSpace.Space N m)
    (W : ReversibleModel v) :
    ContDiffAt ℝ ∞ (fun s ↦ atVertices v (vertexVariation v W s)) 0 := by
  have hf : ContDiffAt ℝ ∞ (variationCoordinates v) ((0 : ℝ) • W) := by
    rw [zero_smul]
    exact contDiffAt_variationCoordinates v
  have h := hf.comp 0 ((contDiff_id.smul contDiff_const).contDiffAt :
    ContDiffAt ℝ ∞ (fun s : ℝ ↦ s • W) 0)
  change ContDiffAt ℝ ∞ (fun s : ℝ ↦ variationCoordinates v (s • W)) 0 at h
  simpa only [variationCoordinates, variationPoint_smul] using! h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
