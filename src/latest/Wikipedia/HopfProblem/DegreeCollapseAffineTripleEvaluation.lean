import Wikipedia.NoExoticSixSphere.AffineParameterEvaluation
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Independent affine variations at three distinct sphere points

Three distinct points on the unit sphere are affinely independent. Lifting
them to vectors with last coordinate one gives a linearly independent
family. A linear left inverse then interpolates arbitrary three values.
This proves surjectivity for the actual affine parameter family.
-/

noncomputable section

open Function Set
open scoped BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.AffineTripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization AffinePerturbation

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem linearIndependent_lift {x : ι → E} (hx : AffineIndependent ℝ x) :
    LinearIndependent ℝ (fun i ↦ (x i, (1 : ℝ))) := by
  apply linearIndependent_iff'.mpr
  intro s w hw i hi
  have hE : ∑ j ∈ s, w j • x j = 0 := by
    simpa only [map_sum, map_smul, map_zero, LinearMap.fst_apply] using
      congrArg (LinearMap.fst ℝ E ℝ) hw
  have hR : ∑ j ∈ s, w j = 0 := by
    simpa only [map_sum, map_smul, map_zero, LinearMap.snd_apply, smul_eq_mul, mul_one] using
      congrArg (LinearMap.snd ℝ E ℝ) hw
  exact hx.eq_zero_of_sum_eq_zero hR hE i hi

theorem exists_linear_interpolation {V : Type*} [AddCommGroup V] [Module ℝ V]
    {x : ι → V} (hx : LinearIndependent ℝ x) (v : ι → F) :
    ∃ L : V →ₗ[ℝ] F, ∀ i, L (x i) = v i := by
  let C : (ι →₀ ℝ) →ₗ[ℝ] V := Finsupp.linearCombination ℝ x
  have hC : Injective C := hx
  obtain ⟨A, hA⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  let L : V →ₗ[ℝ] F := (Finsupp.linearCombination ℝ v).comp A
  refine ⟨L, fun i ↦ ?_⟩
  have hi := LinearMap.congr_fun hA (Finsupp.single i 1)
  have hAi : A (x i) = Finsupp.single i 1 := by simpa [C] using hi
  change Finsupp.linearCombination ℝ v (A (x i)) = v i
  rw [hAi]
  simp

theorem exists_affine_interpolation [FiniteDimensional ℝ E]
    {x : ι → E} (hx : AffineIndependent ℝ x) (v : ι → F) :
    ∃ p : Parameters E F, ∀ i, evaluation (x i) p = v i := by
  have hx' : LinearIndependent ℝ (fun i ↦ (x i, (1 : ℝ))) := linearIndependent_lift hx
  obtain ⟨L, hL⟩ := exists_linear_interpolation (V := E × ℝ) (F := F)
    (x := fun i ↦ (x i, (1 : ℝ))) hx' v
  let T : E × ℝ →L[ℝ] F := L.toContinuousLinearMap
  let A : E →L[ℝ] F := T.comp (ContinuousLinearMap.inl ℝ E ℝ)
  refine ⟨(A, T (0, 1)), fun i ↦ ?_⟩
  change T (x i, 0) + T (0, 1) = v i
  rw [← map_add]
  change L (x i + 0, 0 + 1) = v i
  simpa only [add_zero, zero_add] using hL i

def tripleEvaluation (x y z : E) : Parameters E F →L[ℝ] F × F × F :=
  (evaluation x).prod ((evaluation y).prod (evaluation z))

theorem affineIndependent_sphere_triple (x y z : Sphere 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    AffineIndependent ℝ ![(x : Vector 4), (y : Vector 4), (z : Vector 4)] := by
  have hs : EuclideanGeometry.Cospherical (Metric.sphere (0 : Vector 4) 1) :=
    ⟨0, 1, fun _ hp ↦ hp⟩
  exact hs.affineIndependent_of_mem_of_ne x.property y.property z.property
    (fun h ↦ hxy (Subtype.ext h)) (fun h ↦ hxz (Subtype.ext h))
    (fun h ↦ hyz (Subtype.ext h))

theorem surjective_tripleEvaluation (x y z : Sphere 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Surjective (tripleEvaluation (F := F) (x : Vector 4) (y : Vector 4) (z : Vector 4)) := by
  rintro ⟨a, b, c⟩
  obtain ⟨p, hp⟩ := exists_affine_interpolation
    (affineIndependent_sphere_triple x y z hxy hxz hyz) ![a, b, c]
  exact ⟨p, Prod.ext (hp 0) (Prod.ext (hp 1) (hp 2))⟩

theorem surjective_smul_tripleEvaluation (x y z : Sphere 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {a : ℝ} (ha : a ≠ 0) :
    Surjective (a • tripleEvaluation (F := F) (x : Vector 4) (y : Vector 4) (z : Vector 4)) := by
  intro v
  obtain ⟨p, hp⟩ := surjective_tripleEvaluation x y z hxy hxz hyz (a⁻¹ • v)
  refine ⟨p, ?_⟩
  change a • tripleEvaluation (x : Vector 4) (y : Vector 4) (z : Vector 4) p = v
  rw [hp, smul_inv_smul₀ ha]

end Wikipedia.HopfProblem.DegreeCollapse.AffineTripleParameters
