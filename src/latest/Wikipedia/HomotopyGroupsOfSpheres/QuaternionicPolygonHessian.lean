import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonDifferential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonCriticalIndex
import Wikipedia.HomotopyGroupsOfSpheres.RealHessianCalculus

/-!
# The actual Hessian and its negative symplectic subspace

At a critical polygon, the second variation equals the second Fréchet
derivative in its product Cayley chart. The symplectic negative variations
therefore give an injective linear subspace of the actual Hessian.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {n m : ℕ}

theorem contDiffAt_vertexVariation_coordinates (v : Space n m) (W : Model n m) :
    ContDiffAt ℝ ∞ (fun s => atVertices v (vertexVariation v W s)) 0 := by
  have hmem : vertexVariation v W 0 ∈ (atVertices v).source := by
    rw [vertexVariation_zero]
    exact mem_atVertices_source v
  have h := (contMDiffAt_iff_target_of_mem_source
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model n m)) (f := vertexVariation v W) (x := 0)
    (y := v) hmem).mp (contMDiff_vertexVariation v W).contMDiffAt
  exact h.2.contDiffAt

def localHessian (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : RealHessianForm (Model n m) :=
  realHessian (E := Model n m) (localEnergy a b τ v) 0

theorem secondDerivative_eq_localHessian (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) (W : Model n m) :
    deriv (deriv (fun s => energy a b τ (vertexVariation v W s))) 0 =
      localHessian a b τ v ((-(1 / 2) : ℝ) • W) ((-(1 / 2) : ℝ) • W) := by
  let γ : ℝ → Model n m := fun s => atVertices v (vertexVariation v W s)
  have hγzero : γ 0 = 0 := by simp only [γ, vertexVariation_zero, atVertices_self]
  have hf : ContDiffAt ℝ 2 (localEnergy a b τ v) (γ 0) := by
    rw [hγzero]
    exact (contDiffAt_localEnergy a b τ v hv).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγ : ContDiffAt ℝ 2 γ 0 :=
    (contDiffAt_vertexVariation_coordinates v W).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : fderiv ℝ (localEnergy a b τ v) (γ 0) = 0 := by
    rw [hγzero, ← mfderiv_energy_eq_localEnergy a b τ v hv]
    exact hcrit
  have hsecond := NoExoticSixSphere.SecondDerivativeAtCritical.deriv_deriv_comp
    (E := Model n m) hf hγ hc
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), vertexVariation v W s ∈ (atVertices v).source := by
    have hcont : Tendsto (vertexVariation v W) (𝓝 0) (𝓝 v) := by
      have hh := (contMDiff_vertexVariation v W).continuous.continuousAt (x := (0 : ℝ))
      change Tendsto (vertexVariation v W) (𝓝 0) (𝓝 (vertexVariation v W 0)) at hh
      simpa only [vertexVariation_zero] using hh
    exact hcont.eventually ((atVertices v).open_source.mem_nhds (mem_atVertices_source v))
  have heq : (fun s => energy a b τ (vertexVariation v W s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => localEnergy a b τ v (γ s)) := by
    filter_upwards [hmem] with s hs
    exact congrArg (energy a b τ) ((atVertices v).left_inv hs).symm
  rw [heq.deriv.deriv_eq, hsecond, hγzero]
  have ht := real_deriv_eq_of_hasDerivAt (E := Model n m)
    (hasDerivAt_vertexVariation_coordinates v W)
  exact congrArg₂ (fun X Y => localHessian a b τ v X Y) ht ht

/-- The actual Hessian has an `n`-dimensional negative subspace in `Sp(n+1)`. -/
theorem exists_negative_hessianFamily_of_critical (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] Model n m, Function.Injective L ∧
      ∀ c, c ≠ 0 → localHessian a b τ v (L c) (L c) < 0 := by
  obtain ⟨R, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin n → ℝ) →ₗ[ℝ] Model n m :=
    (realScalarOperator (Model n m) (-(1 / 2))).toLinearMap.comp R
  have hL : Function.Injective L := by
    intro c e he
    apply hR
    change (-(1 / 2) : ℝ) • R c = (-(1 / 2) : ℝ) • R e at he
    exact (smul_right_injective (M := Model n m) (by norm_num : (-(1 / 2) : ℝ) ≠ 0)) he
  refine ⟨L, hL, fun (c : Fin n → ℝ) (hc : c ≠ 0) => ?_⟩
  have h := hneg c hc
  rwa [secondDerivative_eq_localHessian a b τ v hv.1 hcrit (R c)] at h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
