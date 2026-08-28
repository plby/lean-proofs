import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonTangent
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonDifferential

/-!
# Restricted criticality forces all symmetric unitary polygon jumps to vanish

The actual reversible vertex variation stays inside the constrained space.
Its energy derivative is the orthogonal first variation. Applying this to
the velocity jumps gives a sum of squared norms, with no ambient criticality
assumption.
-/

noncomputable section

@[instance_reducible] private def differentialOrthogonalModelNormedSpace (d m : ℕ) :
    NormedSpace ℝ (NoExoticSixSphere.OrthogonalVertexSpace.Model d m) := inferInstance

open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace ComplexMatrixRealRepresentation NoExoticSixSphere.HilbertSchmidt

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

local instance differentialOrthogonalModelSpace :
    NormedSpace ℝ (NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) :=
  differentialOrthogonalModelNormedSpace _ _

local instance differentialModelSelfChart :
    LocalLogarithm.NormedChartedSpace (Model N m) (Model N m) := chartedSpaceSelf _

def localEnergy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (K : Model N m) : ℝ :=
  energy a b τ ((atVertices v).symm K)

theorem contDiffAt_localEnergy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) :
    ContDiffAt ℝ ∞ (localEnergy a b τ v) 0 := by
  have ht : (0 : Model N m) ∈ (atVertices v).target := by
    rw [← atVertices_self v]
    exact (atVertices v).map_source (mem_atVertices_source v)
  have hv' : (atVertices v).symm 0 ∈ admissible a b m := by
    rwa [atVertices_symm_zero]
  exact (contDiffOn_localEnergy a b τ v).contDiffAt
    (((atVertices v).symm.continuousAt ht).preimage_mem_nhds
      ((isOpen_admissible a b m).mem_nhds hv'))

theorem mfderiv_energy_eq_localEnergy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) :
    mfderiv 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) (energy a b τ) v =
      fderiv ℝ (localEnergy a b τ v) 0 := by
  have hc := (contMDiffOn_energy a b τ).contMDiffAt
    ((isOpen_admissible a b m).mem_nhds hv)
  have hd : HasMFDerivAt 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) (energy a b τ) v
      (fderiv ℝ (localEnergy a b τ v) 0) := by
    refine ⟨hc.continuousAt, ?_⟩
    change HasFDerivWithinAt (localEnergy a b τ v) (fderiv ℝ (localEnergy a b τ v) 0)
      (range id) (atVertices v v)
    rw [range_id, atVertices_self, hasFDerivWithinAt_univ]
    exact ((contDiffAt_localEnergy a b τ v hv).differentiableAt (by simp)).hasFDerivAt
  exact hd.mfderiv

theorem hasDerivAt_energy_vertexVariation (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (W : (j : Fin m) → ReversibleDirection (v j)) :
    HasDerivAt (fun s ↦ energy a b τ (vertexVariation v W s))
      (2 * ∑ j : Fin m, innerForm (action (velocityJump a b τ v j).val)
        (action (W j).val.val)) 0 := by
  have h := NoExoticSixSphere.OrthogonalPolygon.hasDerivAt_energy_vertexVariation
    (specialOrthogonal a) (specialOrthogonal b) τ (forget v) (admissible_forget a b hv)
    (fun j ↦ ComplexSkewMatrices.toOrthogonalSkew (W j).val)
  simp_rw [velocityJump_forget a b τ hv, ← forget_vertexVariation] at h
  exact h

def IsStationary (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) : Prop :=
  ∀ γ : ℝ → VertexSpace.Space N m, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model N m) ∞ γ → γ 0 = v →
    HasDerivAt (fun s ↦ energy a b τ (γ s)) 0 0

theorem isStationary_of_mfderiv_eq_zero (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hzero : mfderiv 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    IsStationary a b τ v := by
  intro γ hγ hγzero
  have hE : MDifferentiableAt 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) (energy a b τ) v :=
    ((contMDiffOn_energy a b τ).contMDiffAt
      ((isOpen_admissible a b m).mem_nhds hv)).mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) (energy a b τ) v 0 :=
    hE.hasMFDerivAt.congr_mfderiv hzero
  rw [← hγzero] at hd
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s ↦ energy a b τ (γ s)) 0 (0 : ℝ →L[ℝ] ℝ) := by
    simpa only [ContinuousLinearMap.zero_comp] using!
      hd.comp 0 (((hγ.mdifferentiable (by simp)) 0).hasMFDerivAt)
  have hf : HasFDerivAt (fun s ↦ energy a b τ (γ s)) (0 : ℝ →L[ℝ] ℝ) 0 := hc.hasFDerivAt
  simpa only [zero_apply] using hf.hasDerivAt

theorem velocityJump_eq_zero_of_stationary (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) : velocityJump a b τ v = 0 := by
  let W := jumpDirection a b τ v hv
  let Z := fun j : Fin m ↦ ComplexSkewMatrices.toOrthogonalSkew (velocityJump a b τ v j)
  have hd := hasDerivAt_energy_vertexVariation a b τ v hv W
  have hz := hstat (vertexVariation v W) (contMDiff_vertexVariation v W) (vertexVariation_zero v W)
  have he : 2 * ∑ j : Fin m, squareNorm (Z j).val = 0 := hd.unique hz
  have hsum : ∑ j : Fin m, squareNorm (Z j).val = 0 := by linarith only [he]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) ↦ squareNorm_nonneg (Z j).val)).mp hsum
  funext j
  change velocityJump a b τ v j = 0
  apply ComplexSkewMatrices.toOrthogonalSkew_injective
  rw [map_zero]
  apply Subtype.ext
  exact (squareNorm_eq_zero_iff _).mp (hterm j (Finset.mem_univ j))

theorem velocityJump_eq_zero_of_critical (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) : velocityJump a b τ v = 0 :=
  velocityJump_eq_zero_of_stationary a b τ v hv
    (isStationary_of_mfderiv_eq_zero a b τ v hv
      ((mfderiv_energy_eq_localEnergy a b τ v hv).trans hcrit))

theorem critical_forget (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) :
    mfderiv 𝓘(ℝ, NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) 𝓘(ℝ, ℝ)
      (NoExoticSixSphere.OrthogonalPolygon.energy (specialOrthogonal a) (specialOrthogonal b) τ)
        (forget v) = 0 := by
  apply (NoExoticSixSphere.OrthogonalPolygon.mfderiv_energy_eq_zero_iff
    (specialOrthogonal a) (specialOrthogonal b) τ (forget v) (admissible_forget a b hv)).mpr
  funext j
  rw [velocityJump_forget a b τ hv]
  have hz := congrFun (velocityJump_eq_zero_of_critical a b τ v hv hcrit) j
  change velocityJump a b τ v j = 0 at hz
  rw [hz, map_zero]
  rfl

theorem critical_of_forget (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv
      𝓘(ℝ, NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) 𝓘(ℝ, ℝ)
      (NoExoticSixSphere.OrthogonalPolygon.energy (specialOrthogonal a) (specialOrthogonal b) τ)
        (forget v) = 0) : fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
  have hEsmooth := (NoExoticSixSphere.OrthogonalPolygon.contMDiffOn_energy
      (specialOrthogonal a) (specialOrthogonal b) τ).contMDiffAt
    ((NoExoticSixSphere.OrthogonalPolygon.isOpen_admissible
      (specialOrthogonal a) (specialOrthogonal b) m).mem_nhds (admissible_forget a b hv))
  have hE := hEsmooth.mdifferentiableAt (by simp)
  have hD := hE.hasMFDerivAt.congr_mfderiv hcrit
  have hFsmooth := (contMDiff_forget (N := N) (m := m)).contMDiffAt (x := v)
  have hF := hFsmooth.mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) (energy a b τ) v 0 := by
    simpa only [ContinuousLinearMap.zero_comp] using! hD.comp v hF.hasMFDerivAt
  rw [← mfderiv_energy_eq_localEnergy a b τ v hv]
  exact hd.mfderiv

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
