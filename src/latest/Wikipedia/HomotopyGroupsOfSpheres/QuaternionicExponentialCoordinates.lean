import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponential
import Wikipedia.NoExoticSixSphere.CayleyDifferential
import Wikipedia.NoExoticSixSphere.LocalInverse

/-! # Local invertibility of the symplectic exponential in the actual Cayley coordinates -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform CayleyAtlas

variable {n : ℕ}

def inCoordinates (K : SkewSpace n) : SkewSpace n :=
  skewProjection n (fraction (exp K).val.val.val)

theorem inCoordinates_zero : inCoordinates (0 : SkewSpace n) = 0 := by
  rw [inCoordinates, exp_zero]
  change skewProjection n (fraction (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) = 0
  rw [fraction_one, map_zero]

theorem hasFDerivAt_exp_operator_zero :
    HasFDerivAt (fun K : SkewSpace n => (exp K).val.val.val) (skewInclusion n) 0 := by
  let L := skewInclusion n
  have he : HasFDerivAt
      (NormedSpace.exp : (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) → _)
      (1 : (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →L[ℝ]
        (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) (L 0) := by
    simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ)
      (𝔸 := Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
  convert! he.comp (0 : SkewSpace n) L.hasFDerivAt using 1

theorem hasFDerivAt_fraction_exp_zero :
    HasFDerivAt (fun K : SkewSpace n => fraction (exp K).val.val.val)
      ((-(1 / 2) : ℝ) • skewInclusion n) 0 := by
  have hf : HasFDerivAt (fraction (n := 4 * n + 4))
      ((-(1 / 2) : ℝ) • (1 : (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →L[ℝ]
        (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))))
      (exp (0 : SkewSpace n)).val.val.val := by
    rw [exp_zero]
    exact hasFDerivAt_fraction_one
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp] using!
    (HasFDerivAt.comp (f := fun K : SkewSpace n => (exp K).val.val.val)
      (g := fraction (n := 4 * n + 4)) (0 : SkewSpace n) hf
      (hasFDerivAt_exp_operator_zero (n := n)))

theorem hasFDerivAt_inCoordinates_zero :
    HasFDerivAt (inCoordinates (n := n))
      (realScalarOperator (SkewSpace n) (-(1 / 2))) 0 := by
  have hg : HasFDerivAt (skewProjection n) (skewProjection n)
      (fraction (exp (0 : SkewSpace n)).val.val.val) :=
    hasFDerivAt_finiteSubmoduleProjection (skewSubmodule n) _
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := SkewSpace n)
    (F := Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (G := SkewSpace n)
    (f := fun K : SkewSpace n => fraction (exp K).val.val.val)
    (f' := (-(1 / 2) : ℝ) • skewInclusion n) (g := skewProjection n) (g' := skewProjection n)
    (0 : SkewSpace n) hg (hasFDerivAt_fraction_exp_zero (n := n))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro K
  change (-(1 / 2) : ℝ) • K = skewProjection n ((-(1 / 2) : ℝ) • K.val)
  rw [map_smul, skewProjection_coe]

def coordinateDomain (n : ℕ) : Set (SkewSpace n) := exp ⁻¹' cayleyDomain n

theorem isOpen_coordinateDomain (n : ℕ) : IsOpen (coordinateDomain n) :=
  (isOpen_cayleyDomain n).preimage contMDiff_exp.continuous

theorem zero_mem_coordinateDomain (n : ℕ) : 0 ∈ coordinateDomain n := by
  change exp (0 : SkewSpace n) ∈ cayleyDomain n
  rw [exp_zero]
  exact one_mem_cayleyDomain n

theorem contDiffOn_inCoordinates :
    ContDiffOn ℝ ∞ (inCoordinates (n := n)) (coordinateDomain n) := by
  intro K hK
  have hf : ContDiffAt ℝ ∞ (fun K : SkewSpace n => fraction (exp K).val.val.val) K :=
    ContDiffAt.comp (f := fun K : SkewSpace n => (exp K).val.val.val)
      (g := fraction (n := 4 * n + 4)) K
      (contDiffAt_fraction _ hK) contDiff_exp_operator.contDiffAt
  exact (contDiff_skewProjection.contDiffAt.comp K hf).contDiffWithinAt

theorem inCoordinates_eq_chart (K : SkewSpace n) (hK : K ∈ coordinateDomain n) :
    inCoordinates K = cayleyChart n (exp K) := by
  change skewProjection n (fraction (exp K).val.val.val) = cayleyCoordinates n (exp K)
  rw [cayleyCoordinates_of_mem n _ hK]
  exact skewProjection_fraction (exp K) hK

theorem inCoordinates_fderiv_isInvertible :
    (fderiv ℝ (inCoordinates (n := n)) 0).IsInvertible := by
  rw [realFDeriv_eq_of_hasFDerivAt (E := SkewSpace n) (F := SkewSpace n)
    (hasFDerivAt_inCoordinates_zero (n := n))]
  exact realScalarOperator_isInvertible (SkewSpace n) (-(1 / 2)) (by norm_num)

theorem exists_coordinatePartialDiffeomorph :
    ∃ d : PartialDiffeomorph 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, SkewSpace n)
        (SkewSpace n) (SkewSpace n) ∞,
      0 ∈ d.source ∧ d.source ⊆ coordinateDomain n ∧ (d : _ → _) = inCoordinates :=
  NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn (isOpen_coordinateDomain n)
    (zero_mem_coordinateDomain n) contDiffOn_inCoordinates inCoordinates_fderiv_isInvertible

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential
