import Wikipedia.HopfProblem.DegreeCollapseCanonicalFourFamily
import Wikipedia.HopfProblem.DegreeCollapseSpherePassageFrames

/-!
# The original embedded three-sphere parametrizations differ by an integral unit

The embeddings identify their source spheres with the exact common image.
Their transition is therefore a genuine sphere homeomorphism, whose third
homology map is multiplication by one or minus one. This controls an old
basin parametrization after new critical charts or windows are chosen.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "S₃" => Hemisphere.Sphere 3

theorem same_image_three_sphere_maps_unit {Y : Type} [TopologicalSpace Y]
    (α β : C(S₃, Y)) (hα : IsEmbedding α) (hβ : IsEmbedding β) (hrange : range β = range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      singularHomologyMap β 3 = k • singularHomologyMap α 3 := by
  let e : S₃ ≃ₜ S₃ := hβ.toHomeomorph.trans
    ((Homeomorph.setCongr hrange).trans hα.toHomeomorph.symm)
  have heq : α.comp (e : C(S₃, S₃)) = β := by
    apply ContinuousMap.ext
    intro x
    have hh := congrArg Subtype.val
      (hα.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hβ.toHomeomorph x)))
    exact hh
  have hbij : Bijective (singularHomologyMap (e : C(S₃, S₃)) 3) :=
    (homeomorphHomologyEquiv e 3).bijective
  obtain ⟨k, hk, hu⟩ := sphere_map_unit_of_homology_bijective 2 (Homeomorph.refl S₃)
    (e : C(S₃, S₃)) hbij
  rcases hk with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul] at hu ⊢
    rw [← heq, singularHomologyMap_comp, hu]
    change (singularHomologyMap α 3).comp (singularHomologyMap (ContinuousMap.id S₃) 3) = _
    rw [singularHomologyMap_id, LinearMap.comp_id]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_zsmul] at hu ⊢
    rw [← heq, singularHomologyMap_comp, hu, LinearMap.comp_neg]
    change -((singularHomologyMap α 3).comp (singularHomologyMap (ContinuousMap.id S₃) 3)) = _
    rw [singularHomologyMap_id, LinearMap.comp_id]

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [T2Space M] [CompactSpace M] in
theorem same_image_three_section_classes_unit {a : ℝ}
    (α β : C(S₃, {y : M // f y = a})) (hα : IsEmbedding α) (hβ : IsEmbedding β)
    (hrange : range β = range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ threeSectionClass β = k • threeSectionClass α := by
  obtain ⟨k, hk, hm⟩ := same_image_three_sphere_maps_unit α β hα hβ hrange
  have heval : (k • singularHomologyMap α 3) (unitSphereTopClass 2) =
      k • singularHomologyMap α 3 (unitSphereTopClass 2) :=
    map_zsmul (LinearMap.evalAddMonoidHom (unitSphereTopClass 2)) k (singularHomologyMap α 3)
  refine ⟨k, hk, ?_⟩
  simp only [threeSectionClass, singularHomologyMap_comp, LinearMap.comp_apply,
    hm, heval, map_zsmul]

omit [T2Space M] [CompactSpace M] in
theorem nativeFourBasinFamily_replace_zero
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n : ℕ} (q : criticalPoints E f) (p : Fin n → criticalPoints E f)
    (αq βq : C(S₃, {y : M // f y = a})) (α : Fin n → C(S₃, {y : M // f y = a}))
    (hfamily : IsNativeFourBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j))) (hrange : range βq = range αq) :
    let _ := RegularLevel.chartedSpace hf ha
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ βq → IsClosedEmbedding βq →
    (∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) βq x)) →
    IsNativeFourBasinFamily S hf ha (Fin.cases q p) (Fin.cases βq (fun j => α j)) := by
  let _ := RegularLevel.chartedSpace hf ha
  dsimp only
  intro hβs hβe hβi
  have hr (j : Fin (n + 1)) : range (Fin.cases βq (fun j => α j) j) =
      range (Fin.cases αq (fun j => α j) j) := by
    cases j using Fin.cases with
    | zero => exact hrange
    | succ j => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hβs
    | succ j => exact hfamily.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβe
    | succ j => exact hfamily.2.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβi
    | succ j => exact hfamily.2.2.1 j.succ
  · intro j k hjk
    rw [hr j, hr k]
    exact hfamily.2.2.2.1 hjk
  · intro j y
    rw [hr j]
    exact hfamily.2.2.2.2 j y

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
