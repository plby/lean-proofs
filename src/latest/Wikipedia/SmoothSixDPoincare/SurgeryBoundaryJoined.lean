import Wikipedia.SmoothSixDPoincare.ImageComplementJoined
import Wikipedia.SmoothSixDPoincare.SurgeryComplementHomeomorph
import Wikipedia.SmoothSixDPoincare.SurgeryBeltAvoidance

/-!
# Construct paths between arbitrary points of the actual surgery boundary

Move each endpoint into the belt complement using the checked belt-avoidance
homotopy. The actual complement homeomorphism transfers fixed-endpoint path
avoidance from the old boundary. Concatenate these three genuine paths.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

variable {N F R X Y G H : Type*}
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X]

theorem newBoundary_joined (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] (hn : 0 < n)
    (d : SurgeryBoundaryPair N F R X Y)
    (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 1 + n < Module.finrank ℝ G)
    (hjoin : ∀ x y : X, Joined x y) : ∀ x y : Y, Joined x y := by
  intro y₀ y₁
  have hnormal : 1 < Module.finrank ℝ N := by
    rw [show Module.finrank ℝ N = n + 1 from Fact.out]
    omega
  let x : Hemisphere.Sphere 1 := Classical.choice
    (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
  obtain ⟨g₀, havoid₀, ⟨H₀⟩⟩ :=
    d.exists_belt_avoiding_circle hnormal (ContinuousMap.const _ y₀)
  obtain ⟨g₁, havoid₁, ⟨H₁⟩⟩ :=
    d.exists_belt_avoiding_circle hnormal (ContinuousMap.const _ y₁)
  let z₀ : d.NewComplement := ⟨g₀ x, havoid₀ x⟩
  let z₁ : d.NewComplement := ⟨g₁ x, havoid₁ x⟩
  let e := d.complementHomeomorph
  have hold : Joined (e.symm z₀) (e.symm z₁) :=
    ImageComplement.joined_of_ambient_joined d.attachingSphere hattach
      (by simpa only [finrank_euclideanSpace_fin] using hdim)
      (e.symm z₀) (e.symm z₁) (hjoin _ _)
  have hmiddle : Joined z₀ z₁ := by
    simpa only [Homeomorph.apply_symm_apply] using hold.map e.continuous
  exact (show Joined y₀ (z₀ : Y) from ⟨H₀.evalAt x⟩).trans
    ((hmiddle.map continuous_subtype_val).trans
      (show Joined (z₁ : Y) y₁ from ⟨(H₁.evalAt x).symm⟩))

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
