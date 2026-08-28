import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureModels

/-!
# The component sphere models agree with the original boundary maps

The exterior sphere slices slide to the original endpoint slices without
meeting any intrinsic singularity. The half-radius linking spheres expand
inside their original charts. These are homotopies in the actual regular
parameter space, hence give equality of the induced integral homology maps.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

theorem regularSphereInclusion_cap (b : Bool) (s : Sphere 3) :
    (P.regularSphereInclusion (.inl b) s).val = (if b then 1 else 0, s) := by
  cases b <;> rfl

theorem regularSphereInclusion_link_eq (q : singularParameters (n := 6) g) :
    P.regularSphereInclusion (.inr q) = (P.ball q).regularLink := rfl

def capSphereBoundaryHomotopy (b : Bool) :
    (P.regularModelSphere (.inl b)).Homotopy (P.regularSphereInclusion (.inl b)) where
  toFun p := ⟨(if b then 2 - (p.1 : ℝ) else (p.1 : ℝ) - 1, p.2), by
    intro hs
    have ht := P.singular_time_interior hs
    cases b
    · change (p.1 : ℝ) - 1 ∈ Ioo (0 : ℝ) 1 at ht
      linarith [ht.1, p.1.property.2]
    · change 2 - (p.1 : ℝ) ∈ Ioo (0 : ℝ) 1 at ht
      linarith [ht.2, p.1.property.2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    cases b
    · exact ((continuous_subtype_val.comp continuous_fst).sub continuous_const).prodMk
        continuous_snd
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd
  map_zero_left s := by
    apply Subtype.ext
    rw [P.regularModelSphere_cap]
    cases b <;> norm_num [SphereCylinder.capBaseTime]
  map_one_left s := by
    apply Subtype.ext
    rw [P.regularSphereInclusion_cap]
    cases b <;> norm_num

def modelSphereBoundaryHomotopy (i : BoundaryIndex g) :
    (P.regularModelSphere i).Homotopy (P.regularSphereInclusion i) := by
  rcases i with b | q
  · exact P.capSphereBoundaryHomotopy b
  · rw [P.regularModelSphere_link_eq, P.regularSphereInclusion_link_eq]
    exact (P.ball q).smallLinkHomotopy

theorem regularModelSphere_homologyMap (i : BoundaryIndex g) (n : ℕ) :
    singularHomologyMap (P.regularModelSphere i) n =
      singularHomologyMap (P.regularSphereInclusion i) n :=
  homotopy_homologyMap (P.modelSphereBoundaryHomotopy i) n

end NoExoticSixSphere.SphereFamily.ParityBallSystem
