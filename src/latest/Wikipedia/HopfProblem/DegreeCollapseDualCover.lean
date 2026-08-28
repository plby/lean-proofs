import Wikipedia.SmoothSixDPoincare.FramedFaceNormalCoordinates
import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology

/-!
# The actual complement-and-tube homology detector of a framed sphere

The core complement and the original full face-chart target cover the
ambient manifold. On their intersection, the actual inverse chart's
normal coordinate is nonzero. Normalization followed by the genuine
Mayer--Vietoris connecting map gives a homology detector. No global
duality theorem or prescribed intersection functional is assumed.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.DualCover

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

theorem cover : (oldPatch A : Set X) ∪ A.chart.target = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ range (coreMap A)
  · obtain ⟨u, rfl⟩ := hx
    exact Or.inr (core_mem_chart_target A u)
  · exact Or.inl hx

theorem normal_ne_zero (x : ↥((oldPatch A : Set X) ∩ A.chart.target)) :
    normalProjection A x.val ≠ 0 := by
  intro hz
  apply x.property.1
  refine ⟨(A.chart.symm x.val).1, ?_⟩
  calc
    coreMap A (A.chart.symm x.val).1 = A.chart ((A.chart.symm x.val).1, (0 : F)) :=
      (A.point _ ⟨0, by simp⟩).symm
    _ = A.chart (A.chart.symm x.val) := congrArg A.chart (Prod.ext rfl hz.symm)
    _ = x.val := A.chart.right_inv x.property.2

def overlapNormal : C(↥((oldPatch A : Set X) ∩ A.chart.target), PuncturedRadial.Space F) where
  toFun x := ⟨normalProjection A x.val, normal_ne_zero A x⟩
  continuous_toFun := ((contMDiffOn_normalProjection A).continuousOn.comp_continuous
    continuous_subtype_val (fun x => x.property.2)).subtype_mk _

def overlapDirection : C(↥((oldPatch A : Set X) ∩ A.chart.target), sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp (overlapNormal A)

def detector (k : ℕ) : SingularHomology X (k + 1) →ₗ[ℤ]
    SingularHomology (sphere (0 : F) 1) k := by
  let D := connectingHomomorphism (oldPatch A) A.chart.target (oldPatch A).isOpen
    A.chart.open_target (cover A) k
  let P := singularHomologyMap (overlapDirection A) k
  exact P.comp D

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
