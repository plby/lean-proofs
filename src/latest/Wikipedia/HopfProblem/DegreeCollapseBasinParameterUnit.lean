import Wikipedia.HopfProblem.DegreeCollapseCommonCutSignedSlide

/-!
# Two embedded parametrizations of the same sphere image differ by a unit

The embeddings identify their source spheres with the exact common image.
Their transition is therefore a genuine sphere homeomorphism, whose second
homology map is multiplication by one or minus one. This controls an old
basin parametrization after new critical charts or windows are chosen.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "S₂" => Hemisphere.Sphere 2

theorem same_image_sphere_maps_unit {Y : Type} [TopologicalSpace Y]
    (α β : C(S₂, Y)) (hα : IsEmbedding α) (hβ : IsEmbedding β) (hrange : range β = range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      singularHomologyMap β 2 = k • singularHomologyMap α 2 := by
  let e : S₂ ≃ₜ S₂ := hβ.toHomeomorph.trans
    ((Homeomorph.setCongr hrange).trans hα.toHomeomorph.symm)
  have heq : α.comp (e : C(S₂, S₂)) = β := by
    apply ContinuousMap.ext
    intro x
    have hh := congrArg Subtype.val
      (hα.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hβ.toHomeomorph x)))
    exact hh
  have hbij : Bijective (singularHomologyMap (e : C(S₂, S₂)) 2) :=
    (homeomorphHomologyEquiv e 2).bijective
  obtain ⟨k, hk, hu⟩ := two_sphere_map_unit_of_homology_bijective (Homeomorph.refl S₂)
    (e : C(S₂, S₂)) hbij
  rcases hk with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul] at hu ⊢
    rw [← heq, singularHomologyMap_comp, hu]
    change (singularHomologyMap α 2).comp (singularHomologyMap (ContinuousMap.id S₂) 2) = _
    rw [singularHomologyMap_id, LinearMap.comp_id]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_zsmul] at hu ⊢
    rw [← heq, singularHomologyMap_comp, hu, LinearMap.comp_neg]
    change -((singularHomologyMap α 2).comp (singularHomologyMap (ContinuousMap.id S₂) 2)) = _
    rw [singularHomologyMap_id, LinearMap.comp_id]

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem same_image_section_classes_unit {a : ℝ}
    (α β : C(S₂, {y : M // f y = a})) (hα : IsEmbedding α) (hβ : IsEmbedding β)
    (hrange : range β = range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ middleSectionClass β = k • middleSectionClass α := by
  obtain ⟨k, hk, hm⟩ := same_image_sphere_maps_unit α β hα hβ hrange
  have heval : (k • singularHomologyMap α 2) (unitSphereTopClass 1) =
      k • singularHomologyMap α 2 (unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (unitSphereTopClass 1)) k (singularHomologyMap α 2)
  refine ⟨k, hk, ?_⟩
  simp only [middleSectionClass, singularHomologyMap_comp, LinearMap.comp_apply, hm, heval, map_zsmul]

theorem nativeMiddleBasinFamily_replace_zero
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n : ℕ} (q : criticalPoints E f) (p : Fin n → criticalPoints E f)
    (αq βq : C(S₂, {y : M // f y = a})) (α : Fin n → C(S₂, {y : M // f y = a}))
    (hfamily : IsNativeMiddleBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j))) (hrange : range βq = range αq) :
    let _ := RegularLevel.chartedSpace hf ha
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ βq → IsClosedEmbedding βq →
    (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) βq x)) →
    IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases βq (fun j => α j)) := by
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
