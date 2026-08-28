import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureTransitions
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureExponential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponentialCoordinates

/-!
# Local invertibility of exponential curves in complex-structure Cayley coordinates

The coordinate differential at zero is the actual scalar operator `-1/2`.
The inverse-function theorem therefore applies within the anticommuting skew
model. No extension of the ambient group deformation is assumed.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.LocalExponential

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform Exponential

variable {n : ℕ}

def operatorExponential (J : Space n) (K : AntiSkewSpace J) :
    Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) :=
  (exp (antiSkewToSkew J K)).val.val.val

theorem operatorExponential_zero (J : Space n) : operatorExponential J 0 = 1 := by
  unfold operatorExponential
  rw [map_zero, exp_zero]
  rfl

theorem contDiff_operatorExponential (J : Space n) : ContDiff ℝ ∞ (operatorExponential J) :=
  contDiff_exp_operator.comp
    (finiteLinearMap_contDiff (E := AntiSkewSpace J) (F := SkewSpace n) (antiSkewToSkew J))

def inCoordinates (J : Space n) (K : AntiSkewSpace J) : AntiSkewSpace J :=
  Cayley.projection J (fraction (operatorExponential J K))

theorem inCoordinates_zero (J : Space n) : inCoordinates J 0 = 0 := by
  rw [inCoordinates, operatorExponential_zero, fraction_one, map_zero]

theorem hasFDerivAt_operatorExponential_zero (J : Space n) :
    HasFDerivAt (operatorExponential J) (Cayley.inclusion J) 0 := by
  let L := Cayley.inclusion J
  have he : HasFDerivAt
      (NormedSpace.exp : (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) → _)
      (1 : (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →L[ℝ]
        (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) (L 0) := by
    simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ)
      (𝔸 := Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
  convert! he.comp (0 : AntiSkewSpace J) L.hasFDerivAt using 1

theorem hasFDerivAt_fraction_operatorExponential_zero (J : Space n) :
    HasFDerivAt (fun K : AntiSkewSpace J ↦ fraction (operatorExponential J K))
      ((-(1 / 2) : ℝ) • Cayley.inclusion J) 0 := by
  have hf : HasFDerivAt (fraction (n := 4 * n + 4))
      ((-(1 / 2) : ℝ) • (1 : (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →L[ℝ]
        (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))) (operatorExponential J 0) := by
    rw [operatorExponential_zero]
    exact hasFDerivAt_fraction_one
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp] using!
    (HasFDerivAt.comp (f := operatorExponential J) (g := fraction (n := 4 * n + 4))
      (0 : AntiSkewSpace J) hf (hasFDerivAt_operatorExponential_zero J))

theorem hasFDerivAt_inCoordinates_zero (J : Space n) :
    HasFDerivAt (inCoordinates J) (realScalarOperator (AntiSkewSpace J) (-(1 / 2))) 0 := by
  have hg : HasFDerivAt (Cayley.projection J) (Cayley.projection J)
      (fraction (operatorExponential J 0)) :=
    hasFDerivAt_finiteSubmoduleProjection (antiSkewSubmodule J) _
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := AntiSkewSpace J)
    (F := Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (G := AntiSkewSpace J)
    (f := fun K : AntiSkewSpace J ↦ fraction (operatorExponential J K))
    (f' := (-(1 / 2) : ℝ) • Cayley.inclusion J)
    (g := Cayley.projection J) (g' := Cayley.projection J) (0 : AntiSkewSpace J)
    hg (hasFDerivAt_fraction_operatorExponential_zero J)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro K
  change (-(1 / 2) : ℝ) • K = Cayley.projection J ((-(1 / 2) : ℝ) • K.val)
  rw [map_smul, Cayley.projection_coe]

def coordinateDomain (J : Space n) : Set (AntiSkewSpace J) :=
  {K | exp (antiSkewToSkew J K) ∈ cayleyDomain n}

theorem isOpen_coordinateDomain (J : Space n) : IsOpen (coordinateDomain J) :=
  (isOpen_cayleyDomain n).preimage
    (contMDiff_exp.continuous.comp (continuous_antiSkewToSkew J))

theorem zero_mem_coordinateDomain (J : Space n) : 0 ∈ coordinateDomain J := by
  change exp (antiSkewToSkew J (0 : AntiSkewSpace J)) ∈ cayleyDomain n
  rw [map_zero, exp_zero]
  exact one_mem_cayleyDomain n

theorem contDiffOn_inCoordinates (J : Space n) :
    ContDiffOn ℝ ∞ (inCoordinates J) (coordinateDomain J) := by
  intro K hK
  have hden : (1 + operatorExponential J K).IsInvertible := hK
  have hf : ContDiffAt ℝ ∞ (fun K : AntiSkewSpace J ↦ fraction (operatorExponential J K)) K :=
    ContDiffAt.comp (f := operatorExponential J) (g := fraction (n := 4 * n + 4)) K
      (contDiffAt_fraction _ hden) (contDiff_operatorExponential J).contDiffAt
  exact ((Cayley.contDiff_projection J).contDiffAt.comp K hf).contDiffWithinAt

theorem relative_step (J : Space n) (K : AntiSkewSpace J) :
    Cayley.relative J (exponentialStep J K) = exp (antiSkewToSkew J K) := by
  rw [Cayley.relative, exponentialStep_toSymplectic, inv_mul_cancel_left]

theorem step_mem_domain (J : Space n) (K : AntiSkewSpace J) (h : K ∈ coordinateDomain J) :
    exponentialStep J K ∈ Cayley.domain J := by
  change Cayley.relative J (exponentialStep J K) ∈ cayleyDomain n
  rw [relative_step]
  exact h

theorem inCoordinates_eq_chart (J : Space n) (K : AntiSkewSpace J)
    (h : K ∈ coordinateDomain J) :
    inCoordinates J K = Cayley.chart J (exponentialStep J K) := by
  change Cayley.projection J (fraction (operatorExponential J K)) =
    Cayley.coordinates J (exponentialStep J K)
  rw [Cayley.coordinates_of_mem J _ (step_mem_domain J K h)]
  have hp := Cayley.projection_fraction J (exponentialStep J K) (step_mem_domain J K h)
  rw [relative_step] at hp
  exact hp

theorem inCoordinates_fderiv_isInvertible (J : Space n) :
    (fderiv ℝ (inCoordinates J) 0).IsInvertible := by
  rw [realFDeriv_eq_of_hasFDerivAt (E := AntiSkewSpace J) (F := AntiSkewSpace J)
    (hasFDerivAt_inCoordinates_zero J)]
  exact realScalarOperator_isInvertible (AntiSkewSpace J) (-(1 / 2)) (by norm_num)

theorem exists_coordinatePartialDiffeomorph (J : Space n) :
    ∃ d : PartialDiffeomorph 𝓘(ℝ, AntiSkewSpace J) 𝓘(ℝ, AntiSkewSpace J)
        (AntiSkewSpace J) (AntiSkewSpace J) ∞,
      0 ∈ d.source ∧ d.source ⊆ coordinateDomain J ∧ (d : _ → _) = inCoordinates J :=
  NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    (isOpen_coordinateDomain J) (zero_mem_coordinateDomain J)
    (contDiffOn_inCoordinates J) (inCoordinates_fderiv_isInvertible J)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.LocalExponential
