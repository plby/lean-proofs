import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexVariation
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonStationarity

/-!
# First variation and stationarity of actual symplectic polygons

Compatibility of the local logarithms puts every body velocity in the
quaternionic skew space. Thus the velocity jump itself is an allowed
symplectic variation, and stationarity forces every jump to vanish.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open VertexSpace

variable {n m : ℕ}

def edgeVelocity (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) : SkewSpace n :=
  (1 / (τ i.succ - τ i.castSucc)) • generator a b v i

def velocityJump (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : Model n m :=
  fun j => edgeVelocity a b τ v j.castSucc - edgeVelocity a b τ v j.succ

theorem edgeVelocity_forget (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    NoExoticSixSphere.OrthogonalPolygon.edgeVelocity a.val b.val τ (forget v) i =
      toOrthogonalSkew n (edgeVelocity a b τ v i) := by
  unfold NoExoticSixSphere.OrthogonalPolygon.edgeVelocity edgeVelocity
  rw [generator_forget a b hv i, map_smul]

theorem velocityJump_forget (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) (j : Fin m) :
    NoExoticSixSphere.OrthogonalPolygon.velocityJump a.val b.val τ (forget v) j =
      toOrthogonalSkew n (velocityJump a b τ v j) := by
  unfold NoExoticSixSphere.OrthogonalPolygon.velocityJump velocityJump
  rw [edgeVelocity_forget a b τ hv, edgeVelocity_forget a b τ hv]
  rfl

theorem hasDerivAt_energy_vertexVariation (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m) (W : Model n m) :
    HasDerivAt (fun s => energy a b τ (vertexVariation v W s))
      (2 * ∑ j : Fin m, innerForm (velocityJump a b τ v j).val (W j).val) 0 := by
  have h := NoExoticSixSphere.OrthogonalPolygon.hasDerivAt_energy_vertexVariation
    a.val b.val τ (forget v) (admissible_forget a b hv) (fun j => toOrthogonalSkew n (W j))
  simpa only [energy, forget_vertexVariation, velocityJump_forget a b τ hv,
    toOrthogonalSkew, LinearMap.coe_mk, AddHom.coe_mk] using h

def IsStationary (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : Prop :=
  ∀ γ : ℝ → Space n m, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ γ → γ 0 = v →
    HasDerivAt (fun s => energy a b τ (γ s)) 0 0

theorem isStationary_of_mfderiv_eq_zero (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hzero : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    IsStationary a b τ v := by
  intro γ hγ hγzero
  have hE : MDifferentiableAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v :=
    ((contMDiffOn_energy a b τ).contMDiffAt
      ((isOpen_admissible a b m).mem_nhds hv)).mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v 0 :=
    hE.hasMFDerivAt.congr_mfderiv hzero
  rw [← hγzero] at hd
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s => energy a b τ (γ s)) 0 (0 : ℝ →L[ℝ] ℝ) := by
    simpa only [ContinuousLinearMap.zero_comp] using!
      hd.comp 0 (((hγ.mdifferentiable (by simp)) 0).hasMFDerivAt)
  have hf : HasFDerivAt (fun s => energy a b τ (γ s)) (0 : ℝ →L[ℝ] ℝ) 0 := hc.hasFDerivAt
  simpa only [zero_apply] using hf.hasDerivAt

theorem velocityJump_eq_zero_of_stationary (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) : velocityJump a b τ v = 0 := by
  let W := velocityJump a b τ v
  have hd := hasDerivAt_energy_vertexVariation a b τ v hv W
  have hz := hstat (vertexVariation v W) (contMDiff_vertexVariation v W) (vertexVariation_zero v W)
  have he : 2 * ∑ j : Fin m, squareNorm (W j).val = 0 := hd.unique hz
  have hsum : ∑ j : Fin m, squareNorm (W j).val = 0 := by linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => squareNorm_nonneg (W j).val)).mp hsum
  funext j
  apply Subtype.ext
  exact (squareNorm_eq_zero_iff _).mp (hterm j (Finset.mem_univ j))

theorem adjacent_edgeVelocity_eq_of_stationary (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) (j : Fin m) :
    edgeVelocity a b τ v j.castSucc = edgeVelocity a b τ v j.succ := by
  have h := congrFun (velocityJump_eq_zero_of_stationary a b τ v hv hstat) j
  exact sub_eq_zero.mp h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
