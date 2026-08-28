import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCriticalGenerator
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryNegativeVariation

/-! # Sampling the original constrained endpoint variation at polygon vertices -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace RealSymmetricMixing

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

local instance sampledDirectionSelfChart :
    LocalLogarithm.NormedChartedSpace (DirectionSpace N) (DirectionSpace N) := chartedSpaceSelf _

local instance sampledMatrixSelfChart :
    LocalLogarithm.NormedChartedSpace (Matrix N N ℂ) (Matrix N N ℂ) := chartedSpaceSelf _

theorem contMDiff_sandwich_fixed (A : DirectionSpace N) :
    ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, DirectionSpace N) ∞ (sandwich A) := by
  apply Smoothness.contMDiff_iff_matrix.mpr
  let U := (exponential ((1 / 2 : ℝ) • A)).val.val.val
  let T : Matrix N N ℂ →ₗ[ℝ] Matrix N N ℂ := {
    toFun B := U * B * U.transpose
    map_add' B C := by simp only [mul_add, add_mul]
    map_smul' c B := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply] }
  have hT : ContMDiff 𝓘(ℝ, Matrix N N ℂ) 𝓘(ℝ, Matrix N N ℂ) ∞ T := by
    simpa only [] using! (finiteLinearMap_contDiff T).contMDiff
  change ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, Matrix N N ℂ) ∞
    (fun B : SpecialSpace N ↦ U * LocalLogarithm.matrix B * U.transpose)
  exact hT.comp (Smoothness.contMDiff_matrix (N := N))

theorem contMDiff_exponential_scaled (c : ℝ) :
    ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, DirectionSpace N) ∞
      (fun C : DirectionSpace N ↦ exponential (c • C)) := by
  apply Smoothness.contMDiff_iff_matrix.mpr
  have hs : ContDiff ℝ ∞ (fun C : DirectionSpace N ↦ c • C) :=
    finiteLinearMap_contDiff (c • (LinearMap.id : DirectionSpace N →ₗ[ℝ] DirectionSpace N))
  have h := (LocalLogarithm.contDiff_exponential_matrix (N := N)).comp
    hs
  simpa only [] using! h.contMDiff

theorem contMDiff_endpointVariation_direction (A : DirectionSpace N) (t : ℝ) :
    ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, DirectionSpace N) ∞
      (fun C : DirectionSpace N ↦ endpointVariation A C 1 t) := by
  have h := (contMDiff_sandwich_fixed (t • A)).comp
    (contMDiff_exponential_scaled (N := N) (Real.sin (Real.pi * t)))
  simpa only [Function.comp_def, endpointVariation, one_mul] using h

theorem contDiff_endpointVariation_matrix_frobenius (A C : DirectionSpace N) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ (endpointVariation A C z.1 z.2).val.val.val) := by
  have he := ComplexMatrixLocalLogarithm.contDiff_exp (N := N)
  have hh : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) * z.2) :=
    contDiff_const.mul contDiff_snd
  have hp : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 * Real.sin (Real.pi * z.2)) :=
    contDiff_fst.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd))
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦
      NormedSpace.exp (((1 / 2 : ℝ) * z.2) • ImaginarySymmetricMatrices.imaginary A.val)) :=
    he.comp (hh.smul contDiff_const)
  have hC : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦
      NormedSpace.exp ((z.1 * Real.sin (Real.pi * z.2)) •
        ImaginarySymmetricMatrices.imaginary C.val)) := he.comp (hp.smul contDiff_const)
  convert! (hF.mul hC).mul hF using 1
  funext z
  rw [endpointVariation, sandwich_matrix,
    (exponential ((1 / 2 : ℝ) • (z.2 • A))).val.property]
  change NormedSpace.exp (ImaginarySymmetricMatrices.imaginary ((1 / 2 : ℝ) • (z.2 • A.val))) *
      NormedSpace.exp (ImaginarySymmetricMatrices.imaginary ((z.1 * Real.sin (Real.pi * z.2)) •
        C.val)) *
      NormedSpace.exp (ImaginarySymmetricMatrices.imaginary ((1 / 2 : ℝ) • (z.2 • A.val))) = _
  simp only [map_smul, smul_smul]

def sampledVariation (A C : DirectionSpace N) (τ : Fin (m + 2) → ℝ) (s : ℝ) :
    VertexSpace.Space N m := fun j ↦ endpointVariation A C s (τ j.castSucc.succ)

def sampledVariationPoint (A : DirectionSpace N) (τ : Fin (m + 2) → ℝ)
    (C : DirectionSpace N) : VertexSpace.Space N m := sampledVariation A C τ 1

theorem sampledVariationPoint_smul (A C : DirectionSpace N) (τ : Fin (m + 2) → ℝ) (s : ℝ) :
    sampledVariationPoint A τ (s • C) = sampledVariation A C τ s := by
  funext j
  change endpointVariation A (s • C) 1 (τ j.castSucc.succ) =
    endpointVariation A C s (τ j.castSucc.succ)
  rw [endpointVariation, endpointVariation, one_mul, smul_smul, mul_comm]

theorem contMDiff_sampledVariationPoint (A : DirectionSpace N) (τ : Fin (m + 2) → ℝ) :
    ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, Model N m) ∞ (sampledVariationPoint A τ) := by
  apply VertexSpace.contMDiff_iff_coordinatewise.mpr
  intro j
  exact contMDiff_endpointVariation_direction A (τ j.castSucc.succ)

theorem contMDiff_sampledVariation (A C : DirectionSpace N) (τ : Fin (m + 2) → ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model N m) ∞ (sampledVariation A C τ) := by
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, DirectionSpace N) ∞ (fun s : ℝ ↦ s • C) := by
    simpa only [] using! (contDiff_id.smul contDiff_const :
      ContDiff ℝ ∞ (fun s : ℝ ↦ s • C)).contMDiff
  have h := (contMDiff_sampledVariationPoint A τ).comp hline
  simpa only [Function.comp_def, sampledVariationPoint_smul] using! h

theorem sampledVariation_matches (A C : DirectionSpace N) (b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hend : exponential A = b) (s : ℝ) (j : Fin (m + 2)) :
    endpointVariation A C s (τ j) = vertices specialIdentity b (sampledVariation A C τ s) j := by
  induction j using Fin.cases with
  | zero => rw [hzero, endpointVariation_at_zero, vertices_zero]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change endpointVariation A C s (τ (Fin.last (m + 1))) =
        vertices specialIdentity b (sampledVariation A C τ s) (Fin.last (m + 1))
      rw [hone, endpointVariation_at_one, hend, vertices_last]
    | cast j => rw [vertices_interior]; rfl

theorem sampledVariation_zero (A C : DirectionSpace N) (b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (v : VertexSpace.Space N m)
    (hmatch : ∀ j, exponentialCurve A (τ j) = vertices specialIdentity b v j) :
    sampledVariation A C τ 0 = v := by
  funext j
  change endpointVariation A C 0 (τ j.castSucc.succ) = v j
  rw [endpointVariation_base, hmatch, vertices_interior]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
