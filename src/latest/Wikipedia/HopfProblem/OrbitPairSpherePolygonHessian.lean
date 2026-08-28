import Wikipedia.HopfProblem.OrbitPairSpherePolygonIndex
import Wikipedia.HopfProblem.OrbitPairSphereVertexCoordinates
import Wikipedia.NoExoticSixSphere.SecondDerivativeAtCritical

/-!
# The actual local Hessian of sphere polygon energy

Energy is expressed in a translation of the existing native vertex chart,
on its actual open admissible domain. A vanishing manifold differential
gives a vanishing coordinate differential by the chain rule. The second
derivative along normalized vertex variations is therefore exactly the
coordinate Hessian evaluated on their actual chart tangents. Consequently
the sampled negative family is a negative definite linear Hessian subspace.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ}

def localEnergy (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (K : Model n m) : ℝ := energy a b τ (fromCoordinates v K)

def localAdmissible (a b : Sphere n) (v : Space n m) : Set (Model n m) :=
  coordinateDomain v ∩ (fromCoordinates v) ⁻¹' admissible (costDomain n) a b m

theorem isOpen_localAdmissible (a b : Sphere n) (v : Space n m) :
    IsOpen (localAdmissible a b v) := by
  apply isOpen_iff_mem_nhds.mpr
  intro K hK
  have hs := (contMDiffOn_fromCoordinates v).contMDiffAt
    ((isOpen_coordinateDomain v).mem_nhds hK.1)
  exact inter_mem ((isOpen_coordinateDomain v).mem_nhds hK.1)
    (hs.continuousAt.preimage_mem_nhds ((isOpen_admissible (costDomain n) a b m).mem_nhds hK.2))

theorem zero_mem_localAdmissible (a b : Sphere n) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m) : (0 : Model n m) ∈ localAdmissible a b v := by
  refine ⟨zero_mem_coordinateDomain v, ?_⟩
  change fromCoordinates v 0 ∈ admissible (costDomain n) a b m
  rwa [fromCoordinates_zero]

theorem localEnergy_zero (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    localEnergy a b τ v 0 = energy a b τ v := by rw [localEnergy, fromCoordinates_zero]

theorem contDiffOn_localEnergy (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    ContDiffOn ℝ ∞ (localEnergy a b τ v) (localAdmissible a b v) := by
  intro K hK
  have he := (contMDiffOn_energy (costDomain n) a b τ).contMDiffAt
    ((isOpen_admissible (costDomain n) a b m).mem_nhds hK.2)
  have hs := (contMDiffOn_fromCoordinates v).contMDiffAt
    ((isOpen_coordinateDomain v).mem_nhds hK.1)
  exact (ContMDiffAt.comp (g := energy a b τ) (f := fromCoordinates v)
    K he hs).contDiffAt.contDiffWithinAt

theorem contDiffAt_localEnergy (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) :
    ContDiffAt ℝ ∞ (localEnergy a b τ v) 0 :=
  (contDiffOn_localEnergy a b τ v).contDiffAt
    ((isOpen_localAdmissible a b v).mem_nhds (zero_mem_localAdmissible a b v hv))

theorem localEnergy_critical (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
  have hE : MDifferentiableAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v :=
    ((contMDiffOn_energy (costDomain n) a b τ).contMDiffAt
      ((isOpen_admissible (costDomain n) a b m).mem_nhds hv)).mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) (fromCoordinates v 0) 0 := by
    rw [fromCoordinates_zero]
    exact hE.hasMFDerivAt.congr_mfderiv hcrit
  have hs : MDifferentiableAt 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m)
      (fromCoordinates v) (0 : Model n m) :=
    ((contMDiffOn_fromCoordinates v).contMDiffAt
      ((isOpen_coordinateDomain v).mem_nhds (zero_mem_coordinateDomain v))).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hc : HasMFDerivAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (localEnergy a b τ v) 0
      (0 : Model n m →L[ℝ] ℝ) := by
    simpa only [ContinuousLinearMap.zero_comp] using! hd.comp 0 hs.hasMFDerivAt
  have hf : HasFDerivAt (localEnergy a b τ v) (0 : Model n m →L[ℝ] ℝ) (0 : Model n m) :=
    hc.hasFDerivAt
  exact hf.fderiv

def localHessian (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : Model n m →L[ℝ] Model n m →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (localEnergy a b τ v)) 0

theorem secondDerivative_eq_localHessian (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) (W : Field v) :
    deriv (deriv (fun s => energy a b τ (normalVariation v W s))) 0 =
      localHessian a b τ v (normalChartTangent v W) (normalChartTangent v W) := by
  let γ : ℝ → Model n m := fun s => coordinates v (normalVariation v W s)
  have hγzero : γ 0 = 0 := by simp only [γ, normalVariation_zero, coordinates_self]
  have hf : ContDiffAt ℝ 2 (localEnergy a b τ v) (γ 0) := by
    rw [hγzero]
    exact (contDiffAt_localEnergy a b τ v hv).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγ : ContDiffAt ℝ 2 γ 0 :=
    (contDiffAt_normalVariation_centeredCoordinates v W).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : fderiv ℝ (localEnergy a b τ v) (γ 0) = 0 := by
    rw [hγzero]
    exact localEnergy_critical a b τ v hv hcrit
  have hsecond := SecondDerivativeAtCritical.deriv_deriv_comp hf hγ hc
  have heq : (fun s => energy a b τ (normalVariation v W s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => localEnergy a b τ v (γ s)) := by
    filter_upwards [eventually_normalVariation_source v W] with s hs
    exact congrArg (energy a b τ) (fromCoordinates_coordinates v (normalVariation v W s) hs).symm
  rw [heq.deriv.deriv_eq, hsecond, hγzero]
  exact congrArg₂ (fun X Y => localHessian a b τ v X Y)
    (hasDerivAt_normalVariation_centeredCoordinates v W).deriv
    (hasDerivAt_normalVariation_centeredCoordinates v W).deriv

theorem exists_negative_hessianFamily_of_critical (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : b.val = -a.val) (habove : Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (L : (Fin d → ℝ) →ₗ[ℝ] Model n m), d + 2 = 2 * n ∧
      Function.Injective L ∧ ∀ c, c ≠ 0 → localHessian a b τ v (L c) (L c) < 0 := by
  obtain ⟨d, R, hd, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin d → ℝ) →ₗ[ℝ] Model n m := (normalChartTangent v).toLinearMap.comp R
  refine ⟨d, L, hd, (normalChartTangent_injective v).comp hR, fun c hc => ?_⟩
  have h := hneg c hc
  rwa [secondDerivative_eq_localHessian a b τ v hv hcrit (R c)] at h

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
