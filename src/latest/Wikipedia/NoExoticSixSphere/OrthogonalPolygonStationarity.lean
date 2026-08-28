import Wikipedia.NoExoticSixSphere.OrthogonalVertexVariation
import Wikipedia.NoExoticSixSphere.HilbertSchmidtSummation

/-!
# Stationary polygons have no velocity jumps

Stationarity means zero derivative of the actual energy along every smooth
curve in the actual finite vertex manifold. Varying each vertex in the
direction of the incoming minus outgoing body velocity gives the sum of
their squared Hilbert--Schmidt norms. Positivity therefore forces all jumps
to vanish.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalVertexSpace HilbertSchmidt

variable {n m : ℕ}

noncomputable def edgeVelocity (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) : SkewOperators n :=
  (1 / (τ i.succ - τ i.castSucc)) • generator a b v i

noncomputable def velocityJump (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : Model n m :=
  fun j ↦ edgeVelocity a b τ v j.castSucc - edgeVelocity a b τ v j.succ

theorem sum_variation_edges (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (W : Model n m) :
    (∑ i : Fin (m + 1),
      2 * (innerForm (generator a b v i : Vector n →L[ℝ] Vector n)
        (vertexField W i.succ : Vector n →L[ℝ] Vector n) -
        innerForm (generator a b v i : Vector n →L[ℝ] Vector n)
          (vertexField W i.castSucc : Vector n →L[ℝ] Vector n)) /
        (τ i.succ - τ i.castSucc)) =
      2 * ∑ j : Fin m, innerForm (velocityJump a b τ v j : Vector n →L[ℝ] Vector n)
        (W j : Vector n →L[ℝ] Vector n) := by
  calc
    _ = 2 * ∑ i : Fin (m + 1),
        (innerForm (edgeVelocity a b τ v i : Vector n →L[ℝ] Vector n)
          (vertexField W i.succ : Vector n →L[ℝ] Vector n) -
          innerForm (edgeVelocity a b τ v i : Vector n →L[ℝ] Vector n)
            (vertexField W i.castSucc : Vector n →L[ℝ] Vector n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change 2 * (_ - _) / _ =
        2 * (innerForm ((1 / (τ i.succ - τ i.castSucc)) •
          (generator a b v i : Vector n →L[ℝ] Vector n)) _ -
        innerForm ((1 / (τ i.succ - τ i.castSucc)) •
          (generator a b v i : Vector n →L[ℝ] Vector n)) _)
      rw [innerForm_smul_left, innerForm_smul_left]
      ring
    _ = _ := by
      congr 1
      have h := sum_pairing_difference
        (fun i ↦ (edgeVelocity a b τ v i : Vector n →L[ℝ] Vector n))
        (fun i ↦ (vertexField W i : Vector n →L[ℝ] Vector n))
        (by rw [vertexField_zero]; rfl) (by rw [vertexField_last]; rfl)
      simpa only [vertexField_interior, velocityJump, Submodule.coe_sub] using! h

theorem hasDerivAt_energy_vertexVariation (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m) (W : Model n m) :
    HasDerivAt (fun r ↦ energy a b τ (vertexVariation v W r))
      (2 * ∑ j : Fin m, innerForm (velocityJump a b τ v j : Vector n →L[ℝ] Vector n)
        (W j : Vector n →L[ℝ] Vector n)) 0 := by
  rw [← sum_variation_edges]
  exact hasDerivAt_energy_vertexVariation_edges a b τ v hv W

def IsStationary (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : Prop :=
  ∀ γ : ℝ → Space n m, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ γ → γ 0 = v →
    HasDerivAt (fun r ↦ energy a b τ (γ r)) 0 0

/-- A zero manifold differential gives stationarity along every actual smooth curve. -/
theorem isStationary_of_mfderiv_eq_zero (a b : OrthogonalOperators n)
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
      (fun r ↦ energy a b τ (γ r)) 0 (0 : ℝ →L[ℝ] ℝ) := by
    simpa only [ContinuousLinearMap.zero_comp] using!
      hd.comp 0 (((hγ.mdifferentiable (by simp)) 0).hasMFDerivAt)
  have hf : HasFDerivAt (fun r ↦ energy a b τ (γ r)) (0 : ℝ →L[ℝ] ℝ) 0 :=
    hc.hasFDerivAt
  simpa only [zero_apply] using hf.hasDerivAt

theorem velocityJump_eq_zero_of_stationary (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) : velocityJump a b τ v = 0 := by
  let W := velocityJump a b τ v
  have hd := hasDerivAt_energy_vertexVariation a b τ v hv W
  have hz := hstat (vertexVariation v W) (contMDiff_vertexVariation v W) (vertexVariation_zero v W)
  have he : 2 * ∑ j : Fin m, squareNorm (W j : Vector n →L[ℝ] Vector n) = 0 := hd.unique hz
  have hsum : ∑ j : Fin m, squareNorm (W j : Vector n →L[ℝ] Vector n) = 0 := by linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) ↦
      squareNorm_nonneg (W j : Vector n →L[ℝ] Vector n))).mp hsum
  funext j
  apply Subtype.ext
  exact (squareNorm_eq_zero_iff _).mp (hterm j (Finset.mem_univ j))

theorem adjacent_edgeVelocity_eq_of_stationary (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) (j : Fin m) :
    edgeVelocity a b τ v j.castSucc = edgeVelocity a b τ v j.succ := by
  have h := congrFun (velocityJump_eq_zero_of_stationary a b τ v hv hstat) j
  exact sub_eq_zero.mp h

end NoExoticSixSphere.OrthogonalPolygon
