import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonStationarity
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexTangent

/-!
# The actual manifold differential of symplectic polygon energy

The product Cayley coordinate derivative of an exponential vertex variation
is `-W/2`. Combining this with the proved first variation identifies the
manifold differential with the Hilbert--Schmidt pairing against the velocity
jumps. Thus its zero set is exactly the zero-jump locus.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace

open NoExoticSixSphere.GLOrthonormalization

variable {n m : ℕ}

theorem atVertices_self (v : Space n m) : atVertices v v = 0 := by
  funext i
  rw [atVertices_apply, CayleyAtlas.atOperator_apply]
  change cayleyChart n ((v i)⁻¹ * v i) = 0
  rw [inv_mul_cancel]
  exact cayleyChart_one n

theorem atVertices_symm_zero (v : Space n m) : (atVertices v).symm 0 = v := by
  have h := (atVertices v).left_inv (mem_atVertices_source v)
  rwa [atVertices_self] at h

theorem contMDiff_atVertices_symm (v : Space n m) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞ (atVertices v).symm := by
  apply contMDiff_iff_operator_family.mpr
  intro i
  exact (contDiff_symm_operator_eval v i).contMDiff

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt VertexSpace

variable {n m : ℕ}

noncomputable def localEnergy (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (K : Model n m) : ℝ := energy a b τ ((atVertices v).symm K)

theorem contDiffAt_localEnergy (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m) : ContDiffAt ℝ ∞ (localEnergy a b τ v) 0 := by
  have he := (contMDiffOn_energy a b τ).contMDiffAt ((isOpen_admissible a b m).mem_nhds hv)
  have hs := (contMDiff_atVertices_symm v).contMDiffAt (x := (0 : Model n m))
  have he' : ContMDiffAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞ (energy a b τ)
      ((atVertices v).symm 0) := by simpa only [atVertices_symm_zero] using he
  exact (he'.comp 0 hs).contDiffAt

theorem mfderiv_energy_eq_localEnergy (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = fderiv ℝ (localEnergy a b τ v) 0 := by
  have hc := (contMDiffOn_energy a b τ).contMDiffAt
    ((isOpen_admissible a b m).mem_nhds hv)
  have hd : HasMFDerivAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v
      (fderiv ℝ (localEnergy a b τ v) 0) := by
    refine ⟨hc.continuousAt, ?_⟩
    change HasFDerivWithinAt (localEnergy a b τ v) (fderiv ℝ (localEnergy a b τ v) 0)
      (range id) (atVertices v v)
    rw [range_id, atVertices_self, hasFDerivWithinAt_univ]
    exact ((contDiffAt_localEnergy a b τ v hv).differentiableAt (by simp)).hasFDerivAt
  exact hd.mfderiv

theorem localEnergy_derivative_pairing (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m) (W : Model n m) :
    fderiv ℝ (localEnergy a b τ v) 0 ((-(1 / 2) : ℝ) • W) =
      2 * ∑ j : Fin m, innerForm (velocityJump a b τ v j).val
        (W j).val := by
  have hf := ((contDiffAt_localEnergy a b τ v hv).differentiableAt (by simp)).hasFDerivAt
  have hq := hasDerivAt_vertexVariation_coordinates v W
  have hqzero : atVertices v (vertexVariation v W 0) = 0 := by
    rw [vertexVariation_zero, atVertices_self]
  have hf' : HasFDerivAt (localEnergy a b τ v) (fderiv ℝ (localEnergy a b τ v) 0)
      (atVertices v (vertexVariation v W 0)) := by rwa [hqzero]
  have hc := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Model n m) (E := ℝ)
    (0 : ℝ) hf' hq
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), vertexVariation v W s ∈ (atVertices v).source := by
    have hcont : Tendsto (vertexVariation v W) (𝓝 0) (𝓝 v) := by
      have hc := (contMDiff_vertexVariation v W).continuous.continuousAt (x := (0 : ℝ))
      change Tendsto (vertexVariation v W) (𝓝 0) (𝓝 (vertexVariation v W 0)) at hc
      simpa only [vertexVariation_zero] using hc
    exact hcont.eventually ((atVertices v).open_source.mem_nhds (mem_atVertices_source v))
  have heq : (fun s ↦ energy a b τ (vertexVariation v W s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ localEnergy a b τ v (atVertices v (vertexVariation v W s))) := by
    filter_upwards [hmem] with s hs
    exact congrArg (energy a b τ) ((atVertices v).left_inv hs).symm
  exact (hc.congr_of_eventuallyEq heq).unique (hasDerivAt_energy_vertexVariation a b τ v hv W)

theorem mfderiv_energy_apply (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m) (W : Model n m) :
    (mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v W : ℝ) =
      (-4 : ℝ) * ∑ j : Fin m, innerForm (velocityJump a b τ v j).val
        (W j).val := by
  rw [mfderiv_energy_eq_localEnergy a b τ v hv]
  change fderiv ℝ (localEnergy a b τ v) 0 W = _
  have h := localEnergy_derivative_pairing a b τ v hv W
  rw [map_smul, smul_eq_mul] at h
  linarith only [h]

theorem mfderiv_energy_eq_zero_iff (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0 ↔ velocityJump a b τ v = 0 := by
  constructor
  · intro h
    exact velocityJump_eq_zero_of_stationary a b τ v hv
      (isStationary_of_mfderiv_eq_zero a b τ v hv h)
  · intro h
    apply ContinuousLinearMap.ext
    intro W
    have he := mfderiv_energy_apply a b τ v hv (W : Model n m)
    have hz : (-4 : ℝ) * ∑ j : Fin m,
        innerForm (velocityJump a b τ v j).val
          ((W : Model n m) j).val = 0 := by simp [h, innerForm]
    exact he.trans hz

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
