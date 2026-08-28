import Wikipedia.HopfProblem.DegreeCollapseGeometricFourMatrix

/-!
# Transport the actual three/four geometric matrix across a regular band

Literal sublevel inclusion gives the homology equivalence. The same complete
flow transports all sphere parameters and their entire backward-basin images.
Its actual orbit homotopies identify the three-classes. Transport the original
basis by this inclusion to retain every matrix entry exactly.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.three_section_class_of_flow_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (β : C(Hemisphere.Sphere 3, {y : M // f y = b}))
    (α : C(Hemisphere.Sphere 3, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val) :
    singularHomologyMap (sublevelMap f hab.le) 3 (threeSectionClass α) =
      threeSectionClass β := by
  have hm := homotopic_homologyMap (S.level_transport_homotopic_in_sublevel hf hab ha β α horbit) 3
  have hmaps : (sublevelMap f hab.le).comp ((levelSublevelMap f le_rfl).comp α) =
      (levelSublevelMap f hab.le).comp α := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [threeSectionClass, ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps, ← hm]
  rfl

def regularCutThreeHomologyEquiv
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ criticalPoints E f) :
    SingularHomology {y : M // f y ≤ a} 3 ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ b} 3 :=
  LinearEquiv.ofBijective (singularHomologyMap (sublevelMap f hab) 3)
    (regular_sublevel_inclusion_bijective hf hab hband 3)

theorem AdaptedSurgeryWindows.exists_lower_cut_geometric_four_matrix
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hba : b < a) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (hband : ∀ y, f y ∈ Icc b a → y ∉ criticalPoints E f)
    (za : {y : M // f y = a})
    {r n : ℕ} (p : Fin n → criticalPoints E f) (hp : ∀ j, a < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (γ : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = a}))
    (hγ : IsNativeFourBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalFourMatrix B γ).mulVec) :
    ∃ β : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = b}),
      IsNativeFourBasinFamily S hf hb p (fun j => β j) ∧
      (∀ j x, ∃ t : ℝ, S.flow t (γ j x).val = (β j x).val) ∧
      (∀ j, regularCutThreeHomologyEquiv hf hba.le hband (threeSectionClass (β j)) =
        threeSectionClass (γ j)) ∧
      let B' := B.trans (regularCutThreeHomologyEquiv hf hba.le hband).symm
      canonicalFourMatrix B' β = canonicalFourMatrix B γ ∧
      Surjective (canonicalFourMatrix B' β).mulVec := by
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨β₀, hβ, horbit⟩ := S.exists_regular_band_four_basin_family hf hba ha hb
    (fun y hy h => hband y h hy) za p hp (fun j => γ j) hγ
  let β : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = b}) :=
    fun j => ⟨β₀ j, (hβ.1 j).continuous⟩
  have hclass (j : Fin n) :
      regularCutThreeHomologyEquiv hf hba.le hband (threeSectionClass (β j)) =
        threeSectionClass (γ j) :=
    S.three_section_class_of_flow_transport hf hba hb (γ j) (β j) (horbit j)
  let B' := B.trans (regularCutThreeHomologyEquiv hf hba.le hband).symm
  have hmatrix : canonicalFourMatrix B' β = canonicalFourMatrix B γ := by
    funext i j
    change B.symm (regularCutThreeHomologyEquiv hf hba.le hband (threeSectionClass (β j))) i =
      B.symm (threeSectionClass (γ j)) i
    rw [hclass j]
  refine ⟨β, hβ, horbit, hclass, hmatrix, ?_⟩
  rw [hmatrix]
  exact hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
