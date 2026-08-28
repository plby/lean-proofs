import Wikipedia.HopfProblem.OrbitPairSpherePolygonFirstVariation

/-!
# Critical sphere polygons satisfy the actual tangent balance equations

A vanishing manifold differential implies stationarity along every smooth
vertex curve. Applying this to the actual variation in the balance field
gives the negative sum of the squared balance norms. Thus every balance
vanishes. This derives, rather than assumes, the critical point equations.
Their interpretation as a single sampled great circle is a later step.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace

variable {n m : ℕ}

def IsStationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : Prop :=
  ∀ γ : ℝ → Space n m, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ γ → γ 0 = v →
    HasDerivAt (fun r => energy a b τ (γ r)) 0 0

theorem isStationary_of_mfderiv_eq_zero (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hzero : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    IsStationary a b τ v := by
  intro γ hγ hγzero
  have hE : MDifferentiableAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v :=
    ((contMDiffOn_energy (costDomain n) a b τ).contMDiffAt
      ((isOpen_admissible (costDomain n) a b m).mem_nhds hv)).mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v 0 :=
    hE.hasMFDerivAt.congr_mfderiv hzero
  rw [← hγzero] at hd
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun r => energy a b τ (γ r)) 0 (0 : ℝ →L[ℝ] ℝ) := by
    simpa only [ContinuousLinearMap.zero_comp] using!
      hd.comp 0 (((hγ.mdifferentiable (by simp)) 0).hasMFDerivAt)
  have hf : HasFDerivAt (fun r => energy a b τ (γ r)) (0 : ℝ →L[ℝ] ℝ) 0 :=
    hc.hasFDerivAt
  simpa only [zero_apply] using hf.hasDerivAt

theorem balance_eq_zero_of_stationary (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) : balance a b τ v = 0 := by
  let W := balanceField a b τ v
  have hd := hasDerivAt_energy_variation a b τ v hv W
  have hz := hstat (variation v W) (contMDiff_variation v W) (variation_zero v W)
  have he : -2 * ∑ j : Fin m, ‖balance a b τ v j‖ ^ 2 = 0 := by
    simpa only [W, balanceField, real_inner_self_eq_norm_sq] using hd.unique hz
  have hsum : ∑ j : Fin m, ‖balance a b τ v j‖ ^ 2 = 0 := by linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => sq_nonneg ‖balance a b τ v j‖)).mp hsum
  funext j
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hterm j (Finset.mem_univ j)))

theorem incoming_eq_neg_outgoing_of_stationary (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (j : Fin m) :
    incomingLog a b τ v j.castSucc = -outgoingLog a b τ v j.succ := by
  apply eq_neg_iff_add_eq_zero.mpr
  exact congrFun (balance_eq_zero_of_stationary a b τ v hv hstat) j

theorem balance_eq_zero_of_mfderiv_eq_zero (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hzero : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    balance a b τ v = 0 :=
  balance_eq_zero_of_stationary a b τ v hv (isStationary_of_mfderiv_eq_zero a b τ v hv hzero)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
