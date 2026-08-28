import Wikipedia.HopfProblem.DegreeCollapsePrimitiveFunctionalUnit

/-!
# Move the full geometric matrix to a lower native regular cut

Use the same actual complete flow. Literal sublevel inclusion is an
isomorphism across the regular band, and its orbit homotopies identify
every original sphere class. The transported basis gives exactly the same
matrix, rather than an independently chosen presentation.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

def regularCutHomologyEquiv
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ criticalPoints E f) :
    SingularHomology {y : M // f y ≤ a} 2 ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ b} 2 :=
  LinearEquiv.ofBijective (singularHomologyMap (sublevelMap f hab) 2)
    (regular_sublevel_inclusion_bijective hf hab hband 2)

theorem AdaptedSurgeryWindows.exists_lower_cut_geometric_matrix
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hba : b < a) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (hband : ∀ y, f y ∈ Icc b a → y ∉ criticalPoints E f)
    (za : {y : M // f y = a})
    {r n : ℕ} (p : Fin n → criticalPoints E f) (hp : ∀ j, a < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin n → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ β : Fin n → C(S₂, {y : M // f y = b}),
      IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
      (∀ j x, ∃ t : ℝ, S.flow t (γ j x).val = (β j x).val) ∧
      (∀ j, regularCutHomologyEquiv hf hba.le hband (middleSectionClass (β j)) =
        middleSectionClass (γ j)) ∧
      let B' := B.trans (regularCutHomologyEquiv hf hba.le hband).symm
      canonicalMiddleMatrix B' β = canonicalMiddleMatrix B γ ∧
      Surjective (canonicalMiddleMatrix B' β).mulVec := by
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨β₀, hβ, horbit⟩ := S.exists_regular_band_middle_basin_family hf hba ha hb
    (fun y hy h => hband y h hy) za p hp (fun j => γ j) hγ
  let β : Fin n → C(S₂, {y : M // f y = b}) := fun j => ⟨β₀ j, (hβ.1 j).continuous⟩
  have hclass (j : Fin n) : regularCutHomologyEquiv hf hba.le hband (middleSectionClass (β j)) =
      middleSectionClass (γ j) :=
    S.section_class_of_flow_transport hf hba hb (γ j) (β j) (horbit j)
  let B' := B.trans (regularCutHomologyEquiv hf hba.le hband).symm
  have hmatrix : canonicalMiddleMatrix B' β = canonicalMiddleMatrix B γ := by
    funext i j
    simp only [canonicalMiddleMatrix, classCoordinateMatrix]
    change B.symm (regularCutHomologyEquiv hf hba.le hband (middleSectionClass (β j))) i =
      B.symm (middleSectionClass (γ j)) i
    rw [hclass j]
  refine ⟨β, hβ, horbit, hclass, hmatrix, ?_⟩
  rw [hmatrix]
  exact hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
