import Wikipedia.SmoothSixDPoincare.HomotopySphereAnnularExtension
import Wikipedia.SmoothSixDPoincare.BigonBallHomeomorph

/-!
# Extend a complete cornered boundary neighborhood in the homotopy six-sphere

Transport to the actual Euclidean disk, use the annular extension, and
transport back. The global map is continuous and agrees with the original
map on an open neighborhood of the entire bigon frontier. Its exterior is
constant off a compact set. No smoothness of the transport is used.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {M : Type*} [TopologicalSpace M]

/-- Extend the actual locally continuous boundary map, preserving a full open neighborhood. -/
theorem exists_bigon_neighborhood_extension_of_circle_nullhomotopies
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {h : ℝ} (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hf : ContinuousOn f W) (hfrontW : frontier (bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M), ∃ c : M, ∃ K : Set (ℝ × ℝ),
      IsCompact K ∧ (∀ x ∉ K, F x = c) ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ frontier (bigon h) ⊆ U ∧ U ⊆ W ∧ EqOn F f U := by
  obtain ⟨φ, _, _, hφfront⟩ := exists_bigon_disk_homeomorph hh
  let W' : Set (Hemisphere.Ambient 2) := φ.symm ⁻¹' W
  let g : Hemisphere.Ambient 2 → M := f ∘ φ.symm
  have hW' : IsOpen W' := hW.preimage φ.symm.continuous
  have hg : ContinuousOn g W' := hf.comp φ.symm.continuous.continuousOn (fun _ hx => hx)
  have hSW : sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W' := by
    intro y hy
    have hy' : y ∈ φ '' frontier (bigon h) := by rw [hφfront]; exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    change φ.symm (φ x) ∈ W
    rw [φ.symm_apply_apply]
    exact hfrontW hx
  obtain ⟨G, c, K', hK', hconst, U', hU', hSU', hU'W', heq⟩ :=
    exists_circle_neighborhood_extension_of_circle_nullhomotopies hnull hW' hg hSW
  let F : C(ℝ × ℝ, M) := G.comp ⟨φ, φ.continuous⟩
  let K := φ.symm '' K'
  let U := φ ⁻¹' U'
  refine ⟨F, c, K, hK'.image φ.symm.continuous, ?_, U, hU'.preimage φ.continuous, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : φ x ∉ K' := fun hmem => hx ⟨φ x, hmem, φ.symm_apply_apply x⟩
    exact hconst (φ x) hx'
  · intro x hx
    apply hSU'
    rw [← hφfront]
    exact mem_image_of_mem φ hx
  · intro x hx
    have hx' : φ.symm (φ x) ∈ W := hU'W' hx
    rwa [φ.symm_apply_apply] at hx'
  · intro x hx
    change G (φ x) = f x
    rw [heq hx]
    change f (φ.symm (φ x)) = f x
    rw [φ.symm_apply_apply]

/-- The original homotopy equivalence supplies the required circle contractions. -/
theorem exists_bigon_neighborhood_extension_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    {h : ℝ} (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hf : ContinuousOn f W) (hfrontW : frontier (bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M), ∃ c : M, ∃ K : Set (ℝ × ℝ),
      IsCompact K ∧ (∀ x ∉ K, F x = c) ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ frontier (bigon h) ⊆ U ∧ U ⊆ W ∧ EqOn F f U :=
  exists_bigon_neighborhood_extension_of_circle_nullhomotopies
    (fun f => sphereMap_nullhomotopic_of_homotopySixSphere e (by norm_num : 1 < 6) f)
    hh hW hf hfrontW

end Wikipedia.SmoothSixDPoincare
