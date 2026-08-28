import Wikipedia.HopfProblem.DegreeCollapseReflectionFrameTwist
import Wikipedia.HopfProblem.DegreeCollapseCubeSphereGenerator
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth stable-trivial frame twists with every even evaluation multiplier

The reflection product has polynomial operator coordinates on the unit sphere.
Third Hurewicz and actual manifold smoothing provide smooth self-maps of S3
with every integral homology multiplier. Pulling back the reflection product
therefore realizes every even multiplier, with an actual contraction after
one stabilization. No surgery or bordism existence is inferred here.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectionFrameTwist

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.OrthogonalPaths NoExoticSixSphere.OrthogonalStabilization
open NoExoticSixSphere.SmoothCube
open SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

/-- Polynomial extension of the unit-normal reflection operator. -/
def reflectionPolynomial (n : ℕ) (w : Vector n) : Vector n →L[ℝ] Vector n :=
  ContinuousLinearMap.id ℝ _ - (2 : ℝ) • (innerSL ℝ w).smulRight w

theorem contDiff_reflectionPolynomial (n : ℕ) :
    ContDiff ℝ ∞ (reflectionPolynomial n) := by
  unfold reflectionPolynomial
  exact contDiff_const.sub
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Vector n ↦ (2 : ℝ))).smul
      ((innerSL ℝ).contDiff.smulRight contDiff_id))

theorem reflectionPolynomial_unit {n : ℕ} (w : UnitSphere (Vector n)) :
    reflectionPolynomial n w.val = (reflection w.val).1.1 := by
  apply ContinuousLinearMap.ext
  intro x
  change x - (2 : ℝ) • (inner ℝ w.val x • w.val) =
    hyperplaneReflectionOperator w.val x
  rw [hyperplaneReflectionOperator_apply, ClosedHemisphere.unit_norm]
  simp only [one_pow, inv_one, mul_one, smul_smul]

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem contMDiff_twist_operator (v : UnitSphere (Vector 4)) :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞
      (fun x : Sphere 3 ↦ (twist v x).1.1) := by
  have h : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞
      (fun x : Sphere 3 ↦ reflectionPolynomial 4 x.val) :=
    (contDiff_reflectionPolynomial 4).contMDiff.comp contMDiff_coe_sphere
  have heq : (fun x : Sphere 3 ↦ (twist v x).1.1) =
      fun x : Sphere 3 ↦ (reflectionPolynomial 4 x.val).comp (reflection v.val).1.1 := by
    funext x
    rw [reflectionPolynomial_unit]
    rfl
  rw [heq]
  exact h.clm_comp contMDiff_const

/-- Every integral multiplier is realized by an actual smooth self-map of S3. -/
theorem exists_smooth_homology_multiplier (k : ℤ) :
    ∃ f : C(Sphere 3, Sphere 3), ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
      ∀ a : SingularHomology (Sphere 3) 3, singularHomologyMap f 3 a = k • a := by
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let : Subsingleton (π_ 2 (Sphere 3) (spherePole 3)) :=
    subsingleton_sphereHomotopyGroup (by decide) (spherePole 3)
  let g := (integralClassRepresentative (spherePole 3) (k • integralCubeSphereClass)).val
  obtain ⟨f, hf, H⟩ := exists_smooth_map_homotopic (I := 𝓡 3) (J := 𝓡 3) g
  have hclass : singularHomologyMap f 3 integralCubeSphereClass =
      k • integralCubeSphereClass := by
    rw [← homotopic_homologyMap H 3]
    exact integralSphereClass_representative (spherePole 3) (k • integralCubeSphereClass)
  refine ⟨f, hf, ?_⟩
  intro a
  obtain ⟨j, rfl⟩ := CubeSphereGenerator.generates a
  rw [map_zsmul, hclass]
  exact smul_comm j k integralCubeSphereClass

/-- All even evaluation multipliers occur among smooth, stably contracted families. -/
theorem exists_smooth_even_twist (v : UnitSphere (Vector 4))
    (z : UnitSphere (Vector 5)) (k : ℤ) :
    ∃ a : C(Sphere 3, OrthogonalOperators 4),
      ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞ (fun x ↦ (a x).1.1) ∧
      (stabilizeMap z a).Homotopic (ContinuousMap.const _ (identity 5)) ∧
      ∀ c : SingularHomology (Sphere 3) 3,
        singularHomologyMap (column v a) 3 c = (2 * k) • c := by
  obtain ⟨f, hf, hmult⟩ := exists_smooth_homology_multiplier k
  refine ⟨(twist v).comp f, (contMDiff_twist_operator v).comp hf,
    stabilized_twist_nullhomotopic z v f, ?_⟩
  intro c
  have heq : column v ((twist v).comp f) = (column v (twist v)).comp f := rfl
  rw [heq, singularHomologyMap_comp, LinearMap.comp_apply, twist_column_homology, hmult]
  rw [two_mul, add_zsmul]

end Wikipedia.HopfProblem.DegreeCollapse.ReflectionFrameTwist
