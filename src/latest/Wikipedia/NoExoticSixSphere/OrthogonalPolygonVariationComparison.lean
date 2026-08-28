import Wikipedia.NoExoticSixSphere.OrthogonalShortPolygons
import Wikipedia.NoExoticSixSphere.OrthogonalVertexVariation
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonEnergy
import Wikipedia.NoExoticSixSphere.OrthogonalExponentialVariation
import Wikipedia.NoExoticSixSphere.SecondDerivativeComparison
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Comparing second variations with a short polygon replacement

Sample an actual smooth endpoint-zero variation field at the interior
vertices. Near the base parameter the resulting polygon remains short and
has no more energy than the smooth variation. When their base energies
agree, the polygon's actual second energy derivative is no greater.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalVertexSpace

variable {n m : ℕ}

def sampledField (τ : Fin (m + 2) → ℝ) (W : ℝ → SkewOperators n) : Model n m :=
  fun j ↦ W (τ j.castSucc.succ)

theorem sampledVariation_matches (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (γ : ℝ → OrthogonalOperators n) (W : ℝ → SkewOperators n)
    (hmatch : ∀ j, γ (τ j) = vertices a b v j)
    (hl : W (τ 0) = 0) (hu : W (τ (Fin.last (m + 1))) = 0)
    (s : ℝ) (j : Fin (m + 2)) :
    OrthogonalExponentialVariation.family γ W (s, τ j) =
      vertices a b (vertexVariation v (sampledField τ W) s) j := by
  induction j using Fin.cases with
  | zero =>
    rw [OrthogonalExponentialVariation.family_of_field_zero γ W hl, hmatch,
      vertices_zero, vertices_zero]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change OrthogonalExponentialVariation.family γ W (s, τ (Fin.last (m + 1))) =
        vertices a b (vertexVariation v (sampledField τ W) s) (Fin.last (m + 1))
      rw [OrthogonalExponentialVariation.family_of_field_zero γ W hu, hmatch,
        vertices_last, vertices_last]
    | cast j =>
      rw [vertices_interior]
      simp only [OrthogonalExponentialVariation.family, hmatch, vertices_interior,
        vertexVariation, sampledField]

theorem secondDerivative_le_of_energy_contact (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ shortDomain a b m)
    {γ : ℝ → OrthogonalOperators n} {W : ℝ → SkewOperators n}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (hW : ContDiff ℝ ∞ W)
    (hmatch : ∀ j, γ (τ j) = vertices a b v j)
    (hl : W (τ 0) = 0) (hu : W (τ (Fin.last (m + 1))) = 0)
    (hcontact : energy a b τ v = OrthogonalPathEnergy.energy
      (fun t ↦ (γ t).1.1) (τ 0) (τ (Fin.last (m + 1)))) :
    deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (sampledField τ W) s))) 0 ≤
      deriv (deriv (fun s ↦ OrthogonalPathEnergy.energy
        (fun t ↦ (OrthogonalExponentialVariation.family γ W (s, t)).1.1)
          (τ 0) (τ (Fin.last (m + 1))))) 0 := by
  let V := vertexVariation v (sampledField τ W)
  let A := OrthogonalExponentialVariation.family γ W
  let F : ℝ → ℝ := fun s ↦ energy a b τ (V s)
  let G : ℝ → ℝ := fun s ↦ OrthogonalPathEnergy.energy
    (fun t ↦ (A (s, t)).1.1) (τ 0) (τ (Fin.last (m + 1)))
  have hV : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ V := contMDiff_vertexVariation v _
  have hVzero : V 0 = v := vertexVariation_zero v _
  have hVshort : ∀ᶠ s in 𝓝 (0 : ℝ), V s ∈ shortDomain a b m := by
    have hc := hV.continuous.continuousAt (x := (0 : ℝ))
    change Tendsto V (𝓝 0) (𝓝 (V 0)) at hc
    rw [hVzero] at hc
    exact hc.eventually (shortDomain_mem_nhds a b hv)
  have hF : ContDiffAt ℝ ∞ F 0 := by
    have he := (contMDiffOn_energy a b τ).contMDiffAt
      ((isOpen_admissible a b m).mem_nhds
        (show V 0 ∈ admissible a b m by simpa only [hVzero] using hv.1))
    exact (he.comp 0 hV.contMDiffAt).contDiffAt
  have hA : ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator A) :=
    OrthogonalExponentialVariation.contDiff_family_operator hγ hW
  have hG (s : ℝ) : DifferentiableAt ℝ G s :=
    (OrthogonalFirstVariation.hasDerivAt_energy hA s _ _).differentiableAt
  have hAl (s : ℝ) : A (s, τ 0) = A (0, τ 0) := by
    dsimp only [A]
    rw [OrthogonalExponentialVariation.family_of_field_zero γ W hl,
      OrthogonalExponentialVariation.family_zero]
  have hAu (s : ℝ) : A (s, τ (Fin.last (m + 1))) = A (0, τ (Fin.last (m + 1))) := by
    dsimp only [A]
    rw [OrthogonalExponentialVariation.family_of_field_zero γ W hu,
      OrthogonalExponentialVariation.family_zero]
  have hGtwo : DifferentiableAt ℝ (deriv G) 0 :=
    (OrthogonalFirstVariation.hasDerivAt_deriv_energy hA _ _ hAl hAu 0).differentiableAt
  have hFtwo : DifferentiableAt ℝ (deriv F) 0 :=
    (hF.derivWithin (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  apply SecondDerivativeComparison.le_of_touching
    (((hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ ht ↦ ht.differentiableAt one_ne_zero))
    (Filter.Eventually.of_forall hG) hF.continuousAt (hG 0).continuousAt
    hFtwo.hasDerivAt hGtwo.hasDerivAt
  · simpa only [F, G, V, A, vertexVariation_zero,
      OrthogonalExponentialVariation.family_zero] using hcontact
  · filter_upwards [hVshort] with s hs
    have hslice : ContDiff ℝ ∞ (fun t ↦ (A (s, t)).1.1) :=
      hA.comp (contDiff_const.prodMk contDiff_id)
    exact energy_le_of_matching_vertices a b τ hτ hs.1 hslice
      (sampledVariation_matches a b τ v γ W hmatch hl hu s)
      (fun i ↦ (hs.2 i).le)

end NoExoticSixSphere.OrthogonalPolygon
