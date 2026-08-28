import Wikipedia.SmoothSixDPoincare.MorseCollapseLocalSum
import Wikipedia.SmoothSixDPoincare.SeparatedPointConnecting
import Wikipedia.SmoothSixDPoincare.SpherePointConnecting

/-!
# The original collapse local classes are actual one-point sphere classes

The reduction from the many-point cover is exact in the original local
boundary coordinates. Stereographic contractibility then proves that each
such one-point map is injective and an isomorphism in higher degrees.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (m : ℕ)
  (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
  [Fintype (d.beltIntersectionPoints m g)]

open Classical in
theorem collapseLocalClass_singlePoint (k : ℕ)
    (a : SingularHomology (Hemisphere.Sphere m) (k + 1)) (i : d.beltIntersectionPoints m g) :
    d.collapseLocalClass m g D k a i =
      LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) k a :=
  D.sphereConnecting_component k a i

open Classical in
theorem collapseLocalClass_injective (k : ℕ) (i : d.beltIntersectionPoints m g) :
    Function.Injective (fun a => d.collapseLocalClass m g D k a i) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro a b hab
  change d.collapseLocalClass m g D k a i = d.collapseLocalClass m g D k b i at hab
  rw [d.collapseLocalClass_singlePoint m g D k a i,
    d.collapseLocalClass_singlePoint m g D k b i] at hab
  exact SpherePoint.connecting_injective i.val (D.data i) k hab

open Classical in
def collapseLocalClassEquiv (k : ℕ) (i : d.beltIntersectionPoints m g) :
    SingularHomology (Hemisphere.Sphere m) (k + 2) ≃ₗ[ℤ]
      SingularHomology (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (k + 1) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact SpherePoint.connectingHomologyEquiv i.val (D.data i) k

open Classical in
theorem collapseLocalClassEquiv_apply (k : ℕ) (i : d.beltIntersectionPoints m g)
    (a : SingularHomology (Hemisphere.Sphere m) (k + 2)) :
    d.collapseLocalClassEquiv m g D k i a = d.collapseLocalClass m g D (k + 1) a i := by
  rw [d.collapseLocalClass_singlePoint]
  rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
