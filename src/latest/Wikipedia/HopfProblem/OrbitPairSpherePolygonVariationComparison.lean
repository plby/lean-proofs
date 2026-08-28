import Wikipedia.HopfProblem.OrbitPairSphereNormalVertexVariation
import Wikipedia.NoExoticSixSphere.SecondDerivativeComparison

/-!
# Sampling normalized path variations and comparing actual second derivatives

A tangent path field samples to actual tangent vectors at the interior
vertices. Its normalized sphere variation agrees exactly with the normalized
vertex variation at every sample, including both fixed endpoints. The polygon
energy is therefore no greater than the integral path energy for every
parameter. At energy contact, their actual second derivatives are ordered.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace

variable {n m : ℕ}

def sampledField (v : Space n m) (τ : Fin (m + 2) → ℝ) (W : ℝ → Vector (n + 1))
    (hW : ∀ j : Fin m, inner ℝ (v j).val (W (τ j.castSucc.succ)) = 0) : Field v :=
  fun j => ⟨W (τ j.castSucc.succ), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hW j)⟩

theorem sampledField_apply (v : Space n m) (τ : Fin (m + 2) → ℝ)
    (W : ℝ → Vector (n + 1))
    (hW : ∀ j : Fin m, inner ℝ (v j).val (W (τ j.castSucc.succ)) = 0) (j : Fin m) :
    (sampledField v τ W hW j : Vector (n + 1)) = W (τ j.castSucc.succ) := rfl

theorem sample_orthogonality (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m)
    {γ W : ℝ → Vector (n + 1)}
    (hmatch : ∀ j : Fin (m + 2), γ (τ j) = (vertices a b v j).val)
    (horth : ∀ t, inner ℝ (γ t) (W t) = 0) (j : Fin m) :
    inner ℝ (v j).val (W (τ j.castSucc.succ)) = 0 := by
  have he : γ (τ j.castSucc.succ) = (v j).val := by rw [hmatch, vertices_interior]
  rw [← he]
  exact horth _

theorem sampledVariation_matches (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m)
    {γ W : ℝ → Vector (n + 1)} (hunit : ∀ t, ‖γ t‖ = 1)
    (hmatch : ∀ j : Fin (m + 2), γ (τ j) = (vertices a b v j).val)
    (horth : ∀ t, inner ℝ (γ t) (W t) = 0)
    (hl : W (τ 0) = 0) (hu : W (τ (Fin.last (m + 1))) = 0)
    (s : ℝ) (j : Fin (m + 2)) :
    SphereNormalVariation.family γ W (s, τ j) =
      (vertices a b (normalVariation v
        (sampledField v τ W (sample_orthogonality a b τ v hmatch horth)) s) j).val := by
  induction j using Fin.cases with
  | zero =>
    rw [SphereNormalVariation.family_of_field_zero hunit hl, hmatch, vertices_zero, vertices_zero]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change SphereNormalVariation.family γ W (s, τ (Fin.last (m + 1))) =
        (vertices a b (normalVariation v
          (sampledField v τ W (sample_orthogonality a b τ v hmatch horth)) s)
          (Fin.last (m + 1))).val
      rw [SphereNormalVariation.family_of_field_zero hunit hu, hmatch, vertices_last, vertices_last]
    | cast j =>
      rw [vertices_interior, normalVariation_val]
      simp only [SphereNormalVariation.family, hmatch, vertices_interior, sampledField_apply]

theorem secondDerivative_le_of_energy_contact (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    {γ W : ℝ → Vector (n + 1)} (hγ : ContDiff ℝ ∞ γ) (hW : ContDiff ℝ ∞ W)
    (hunit : ∀ t, ‖γ t‖ = 1) (horth : ∀ t, inner ℝ (γ t) (W t) = 0)
    (hmatch : ∀ j : Fin (m + 2), γ (τ j) = (vertices a b v j).val)
    (hl : W (τ 0) = 0) (hu : W (τ (Fin.last (m + 1))) = 0)
    (hcontact : energy a b τ v = SpherePathEnergy.energy γ (τ 0) (τ (Fin.last (m + 1)))) :
    deriv (deriv (fun s => energy a b τ (normalVariation v
      (sampledField v τ W (sample_orthogonality a b τ v hmatch horth)) s))) 0 ≤
      deriv (deriv (fun s => SpherePathEnergy.energy
        (fun t => SphereNormalVariation.family γ W (s, t))
          (τ 0) (τ (Fin.last (m + 1))))) 0 := by
  let V := normalVariation v (sampledField v τ W (sample_orthogonality a b τ v hmatch horth))
  let A := SphereNormalVariation.family γ W
  let F : ℝ → ℝ := fun s => energy a b τ (V s)
  let G : ℝ → ℝ := fun s => SpherePathEnergy.energy
    (fun t => A (s, t)) (τ 0) (τ (Fin.last (m + 1)))
  have hV : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ V := contMDiff_normalVariation v _
  have hVzero : V 0 = v := normalVariation_zero v _
  have hF : ContDiffAt ℝ ∞ F 0 := by
    have he := (contMDiffOn_energy (costDomain n) a b τ).contMDiffAt
      ((isOpen_admissible (costDomain n) a b m).mem_nhds
        (show V 0 ∈ admissible (costDomain n) a b m by rwa [hVzero]))
    exact (ContMDiffAt.comp (g := energy a b τ) (f := V) 0 he hV.contMDiffAt).contDiffAt
  have hA : ContDiff ℝ ∞ A := SphereNormalVariation.contDiff_family hγ hW hunit horth
  have hG (s : ℝ) : DifferentiableAt ℝ G s :=
    (SpherePathEnergy.hasDerivAt_energy hA s _ _).differentiableAt
  have hGtwo : DifferentiableAt ℝ (deriv G) 0 :=
    (SpherePathEnergy.hasDerivAt_deriv_energy hA 0 _ _).differentiableAt
  have hFtwo : DifferentiableAt ℝ (deriv F) 0 :=
    (hF.derivWithin (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  apply SecondDerivativeComparison.le_of_touching
    (((hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ ht => ht.differentiableAt one_ne_zero))
    (Filter.Eventually.of_forall hG) hF.continuousAt (hG 0).continuousAt
    hFtwo.hasDerivAt hGtwo.hasDerivAt
  · simpa only [F, G, V, A, normalVariation_zero, SphereNormalVariation.family_zero hunit]
      using hcontact
  · apply Filter.Eventually.of_forall
    intro s
    have hslice : ContDiff ℝ ∞ (fun t => A (s, t)) :=
      hA.comp (contDiff_const.prodMk contDiff_id)
    exact energy_le_of_matching_vertices a b τ hτ (V s) hslice
      (fun t => SphereNormalVariation.norm_family hunit horth (s, t))
      (sampledVariation_matches a b τ v hunit hmatch horth hl hu s)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
