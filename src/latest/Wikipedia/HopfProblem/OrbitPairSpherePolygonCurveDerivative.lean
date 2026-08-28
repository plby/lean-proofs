import Wikipedia.HopfProblem.OrbitPairSphereNormalVertexVariation
import Wikipedia.HopfProblem.OrbitPairSpherePolygonFirstVariation

/-!
# The actual polygon-energy derivative along any smooth vertex curve

The first variation depends only on the actual tangent velocities at the
current vertices. This version applies at any parameter, rather than only
to the initial point of an exponential variation. It also gives the
initial derivative of the normalized variations used for descent.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereAngle SpherePairedGeodesic

variable {n m : ℕ}

theorem hasDerivAt_vertices_curve (a b : Sphere n) {γ : ℝ → Space n m} (s : ℝ)
    (W : Field (γ s))
    (hW : ∀ j : Fin m, HasDerivAt (fun r => (γ r j).val) (W j : Vector (n + 1)) s)
    (i : Fin (m + 2)) :
    HasDerivAt (fun r => (vertices a b (γ r) i).val) (vertexField (γ s) W i) s := by
  induction i using Fin.cases with
  | zero => simpa only [vertices_zero, vertexField_zero] using hasDerivAt_const s a.val
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [Fin.succ_last, vertices_last, vertexField_last] using
        hasDerivAt_const s b.val
    | cast j => simpa only [vertices_interior, vertexField_interior] using hW j

theorem hasDerivAt_energy_curve (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {γ : ℝ → Space n m} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ γ)
    (s : ℝ) (hs : γ s ∈ admissible (costDomain n) a b m) (W : Field (γ s))
    (hW : ∀ j : Fin m, HasDerivAt (fun r => (γ r j).val) (W j : Vector (n + 1)) s) :
    HasDerivAt (fun r => energy a b τ (γ r))
      (-2 * ∑ j : Fin m, inner ℝ (W j : Vector (n + 1)) (balance a b τ (γ s) j)) s := by
  rw [← sum_variation_edges a b τ (γ s) W]
  apply HasDerivAt.fun_sum
  intro i _
  have hleft : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun r => vertices a b (γ r) i.castSucc) := (contMDiff_vertices a b i.castSucc).comp hγ
  have hright : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun r => vertices a b (γ r) i.succ) := (contMDiff_vertices a b i.succ).comp hγ
  have hd := SphereAngle.hasDerivAt_sphereCost hleft.contMDiffAt hright.contMDiffAt
    (hasDerivAt_vertices_curve a b s W hW i.castSucc)
    (hasDerivAt_vertices_curve a b s W hW i.succ) (hs i)
  exact hd.div_const (τ i.succ - τ i.castSucc)

theorem hasDerivAt_energy_normalVariation (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) (W : Field v) :
    HasDerivAt (fun s => energy a b τ (normalVariation v W s))
      (-2 * ∑ j : Fin m, inner ℝ (W j : Vector (n + 1)) (balance a b τ v j)) 0 := by
  have h := hasDerivAt_energy_curve a b τ (contMDiff_normalVariation v W) (0 : ℝ)
  rw [normalVariation_zero] at h
  exact h hv W (hasDerivAt_normalVariation_eval v W)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
