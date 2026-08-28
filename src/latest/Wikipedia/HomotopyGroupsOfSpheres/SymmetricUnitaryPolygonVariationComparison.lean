import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySampledVariation
import Wikipedia.NoExoticSixSphere.SecondDerivativeComparison
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Sampling preserves negative second variations of constrained energy

Near the base parameter, the sampled vertices remain admissible and the
short polygon has no more energy than the original smooth variation. At
the common exponential base path the energies agree, so their second
derivatives have the same order.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology
open Set Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace RealSymmetricMixing ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

theorem secondDerivative_sampled_le (b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible specialIdentity b m)
    (A C : DirectionSpace N) (hend : exponential A = b)
    (hmatch : ∀ j, exponentialCurve A (τ j) = vertices specialIdentity b v j)
    (hcontact : energy specialIdentity b τ v =
      QuaternionicSymmetricMatrices.energy (exponentialCurve A)) :
    deriv (deriv (fun s ↦ energy specialIdentity b τ (sampledVariation A C τ s))) 0 ≤
      deriv (deriv (fun s ↦ QuaternionicSymmetricMatrices.energy
        (fun t ↦ endpointVariation A C s t))) 0 := by
  let V := sampledVariation A C τ
  let F : ℝ → ℝ := fun s ↦ energy specialIdentity b τ (V s)
  let G : ℝ → ℝ := fun s ↦ QuaternionicSymmetricMatrices.energy
    (fun t ↦ endpointVariation A C s t)
  have hV : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model N m) ∞ V := contMDiff_sampledVariation A C τ
  have hVzero : V 0 = v := sampledVariation_zero A C b τ v hmatch
  have hVadmissible : ∀ᶠ s in 𝓝 (0 : ℝ), V s ∈ admissible specialIdentity b m := by
    have hc := hV.continuous.continuousAt (x := (0 : ℝ))
    change Tendsto V (𝓝 0) (𝓝 (V 0)) at hc
    rw [hVzero] at hc
    exact hc.eventually ((isOpen_admissible specialIdentity b m).mem_nhds hv)
  have hF : ContDiffAt ℝ ∞ F 0 := by
    have he := (contMDiffOn_energy specialIdentity b τ).contMDiffAt
      ((isOpen_admissible specialIdentity b m).mem_nhds
        (show V 0 ∈ admissible specialIdentity b m by simpa only [hVzero] using hv))
    simpa only [] using! (he.comp 0 hV.contMDiffAt).contDiffAt
  have hMatrix : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦
      (endpointVariation A C z.1 z.2).val.val.val) :=
    contDiff_endpointVariation_matrix_frobenius A C
  let O : ℝ × ℝ → NoExoticSixSphere.GLOrthonormalization.OrthogonalOperators
      (2 * Fintype.card N) := fun z ↦ specialOrthogonal (endpointVariation A C z.1 z.2)
  have hO : ContDiff ℝ ∞ (NoExoticSixSphere.OrthogonalMaurerCartan.operator O) :=
    (contDiff_action (N := N)).comp hMatrix
  have hG (s : ℝ) : DifferentiableAt ℝ G s :=
    (NoExoticSixSphere.OrthogonalFirstVariation.hasDerivAt_energy hO s 0 1).differentiableAt
  have hGtwo : DifferentiableAt ℝ (deriv G) 0 :=
    (hasDerivAt_deriv_energy_endpointVariation A C).differentiableAt
  have hFtwo : DifferentiableAt ℝ (deriv F) 0 :=
    (hF.derivWithin (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  apply NoExoticSixSphere.SecondDerivativeComparison.le_of_touching
    (((hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ ht ↦ ht.differentiableAt one_ne_zero))
    (Filter.Eventually.of_forall hG) hF.continuousAt (hG 0).continuousAt
    hFtwo.hasDerivAt hGtwo.hasDerivAt
  · change energy specialIdentity b τ (V 0) =
      QuaternionicSymmetricMatrices.energy (fun t ↦ endpointVariation A C 0 t)
    simp only [hVzero, endpointVariation_base]
    exact hcontact
  · filter_upwards [hVadmissible] with s hs
    have hslice : ContDiff ℝ ∞ (fun t ↦ (endpointVariation A C s t).val.val.val) :=
      hMatrix.comp (f := fun t : ℝ ↦ (s, t)) (contDiff_const.prodMk contDiff_id)
    have h := energy_le_of_matching_vertices specialIdentity b τ hτ hs hslice
      (sampledVariation_matches A C b τ hzero hone hend s)
    simpa only [hzero, hone, F, G, V, QuaternionicSymmetricMatrices.energy] using! h

theorem exponential_polygon_energy_contact (b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible specialIdentity b m)
    (A : DirectionSpace N)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1,
      path specialIdentity b τ hτ v hv t = exponentialCurve A t) :
    energy specialIdentity b τ v = QuaternionicSymmetricMatrices.energy (exponentialCurve A) := by
  rw [← path_energy_eq specialIdentity b τ hτ v hv, hzero, hone]
  apply NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
  intro t ht
  exact congrArg (fun B : SpecialSpace N ↦ action B.val.val.val) (hpath t ht)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
