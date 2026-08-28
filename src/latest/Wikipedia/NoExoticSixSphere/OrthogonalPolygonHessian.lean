import Wikipedia.NoExoticSixSphere.OrthogonalPolygonDifferential
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonIndex
import Wikipedia.NoExoticSixSphere.SecondDerivativeAtCritical

/-!
# The actual local Hessian and its negative subspace

The second variation of polygon energy at a critical point is identified with
the second Fréchet derivative in the product Cayley chart. The previously
constructed negative variations therefore give an injective linear subspace
on which this actual Hessian is negative definite.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {n m : ℕ}

theorem contDiffAt_chart_exp_zero :
    ContDiffAt ℝ ∞ (fun K : SkewOperators n ↦ CayleyTransform.chart (exp K)) 0 := by
  have hi : ContDiffAt ℝ ∞ (inCoordinates (n := n)) 0 :=
    contDiffOn_inCoordinates.contDiffAt ((isOpen_coordinateDomain n).mem_nhds
      (zero_mem_coordinateDomain n))
  apply hi.congr_of_eventuallyEq
  filter_upwards [(isOpen_coordinateDomain n).mem_nhds (zero_mem_coordinateDomain n)] with K hK
  exact (inCoordinates_eq_chart K hK).symm

theorem contDiffAt_vertexVariation_coordinates (v : Space n m) (W : Model n m) :
    ContDiffAt ℝ ∞ (fun s ↦ atVertices v (vertexVariation v W s)) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  have hs : ContDiffAt ℝ ∞ (fun s : ℝ ↦ s • W i) 0 := contDiffAt_id.smul contDiffAt_const
  have hc : ContDiffAt ℝ ∞ (fun K : SkewOperators n ↦ CayleyTransform.chart (exp K))
      ((0 : ℝ) • W i) := by simpa only [zero_smul] using contDiffAt_chart_exp_zero (n := n)
  simpa only [coordinates_vertexVariation, Function.comp_def] using hc.comp 0 hs

noncomputable def localHessian (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : Model n m →L[ℝ] Model n m →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (localEnergy a b τ v)) 0

theorem secondDerivative_eq_localHessian (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) (W : Model n m) :
    deriv (deriv (fun s ↦ energy a b τ (vertexVariation v W s))) 0 =
      localHessian a b τ v ((-(1 / 2) : ℝ) • W) ((-(1 / 2) : ℝ) • W) := by
  let γ : ℝ → Model n m := fun s ↦ atVertices v (vertexVariation v W s)
  have hγzero : γ 0 = 0 := by simp only [γ, vertexVariation_zero, atVertices_self]
  have hf : ContDiffAt ℝ 2 (localEnergy a b τ v) (γ 0) := by
    rw [hγzero]
    exact (contDiffAt_localEnergy a b τ v hv).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγ : ContDiffAt ℝ 2 γ 0 :=
    (contDiffAt_vertexVariation_coordinates v W).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : fderiv ℝ (localEnergy a b τ v) (γ 0) = 0 := by
    rw [hγzero, ← mfderiv_energy_eq_localEnergy a b τ v hv]
    exact hcrit
  have hsecond := SecondDerivativeAtCritical.deriv_deriv_comp hf hγ hc
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), vertexVariation v W s ∈ (atVertices v).source := by
    have hcont : Tendsto (vertexVariation v W) (𝓝 0) (𝓝 v) := by
      have hh := (contMDiff_vertexVariation v W).continuous.continuousAt (x := (0 : ℝ))
      change Tendsto (vertexVariation v W) (𝓝 0) (𝓝 (vertexVariation v W 0)) at hh
      simpa only [vertexVariation_zero] using hh
    exact hcont.eventually ((atVertices v).open_source.mem_nhds (mem_atVertices_source v))
  have heq : (fun s ↦ energy a b τ (vertexVariation v W s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ localEnergy a b τ v (γ s)) := by
    filter_upwards [hmem] with s hs
    exact congrArg (energy a b τ) ((atVertices v).left_inv hs).symm
  rw [heq.deriv.deriv_eq, hsecond, hγzero]
  exact congrArg₂ (fun X Y ↦ localHessian a b τ v X Y)
    (hasDerivAt_vertexVariation_coordinates v W).deriv
    (hasDerivAt_vertexVariation_coordinates v W).deriv

/-- A nonminimal antipodal critical polygon has an actual negative Hessian
subspace of dimension `n - 2` in its finite-dimensional coordinate model. -/
theorem exists_negative_hessianFamily_of_critical (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (L : (Fin d → ℝ) →ₗ[ℝ] Model n m), d + 2 = n ∧
      Function.Injective L ∧ ∀ c, c ≠ 0 → localHessian a b τ v (L c) (L c) < 0 := by
  obtain ⟨d, R, hd, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin d → ℝ) →ₗ[ℝ] Model n m := (-(1 / 2) : ℝ) • R
  have hL : Function.Injective L := by
    intro c e he
    apply hR
    exact (smul_right_injective (M := Model n m) (by norm_num : (-(1 / 2) : ℝ) ≠ 0)) he
  refine ⟨d, L, hd, hL, fun c hc ↦ ?_⟩
  have h := hneg c hc
  rwa [secondDerivative_eq_localHessian a b τ v hv.1 hcrit (R c)] at h

end NoExoticSixSphere.OrthogonalPolygon
