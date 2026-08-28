import Wikipedia.HopfProblem.DegreeCollapseDualLocalSum
import Wikipedia.SmoothSixDPoincare.SphereOutwardClass
import Wikipedia.SmoothSixDPoincare.OutwardLocalBoundaryHomology

/-!
# The genuine dual detector acts by the actual signed normal count

All local source classes are expressed using one constructed global outward
isomorphism. The native local-degree theorem then gives the fixed normal
Jacobian sign at each original crossing. Summing identifies the detector
with multiplication by the actual integer count, with no supplied degree
formula and no unspecified local orientation choices.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.DualCover

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle SphereNormalCoordinates
open SingularMayerVietoris SphereHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "P₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₃" => sphere (0 : P₄) 1

local instance : Fact (Module.finrank ℝ P₄ = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (j : (ℝ × F) ≃L[ℝ] P₄) (B : P₃ ≃L[ℝ] F) (g : C(S₃, X))

def normalSign (q : S₃) : SignType :=
  SignType.sign (normalJacobian j q (mfderiv (𝓡 3) 𝓘(ℝ, F) (normalProjection A ∘ g) q))

def normalCount (hfin : (crossings A g).Finite) : ℤ :=
  ∑ q ∈ hfin.toFinset, (normalSign A j g q : ℤ)

open Classical in
theorem normalCount_smul [Fintype (crossings A g)] (hfin : (crossings A g).Finite)
    {T : Type*} [AddCommGroup T] (a : T) :
    (∑ i : crossings A g, (normalSign A j g i.val : ℤ) • a) = normalCount A j g hfin • a := by
  have hcount : (∑ i : crossings A g, (normalSign A j g i.val : ℤ)) =
      normalCount A j g hfin :=
    (Finset.sum_subtype hfin.toFinset (fun _ => hfin.mem_toFinset)
      (fun x => (normalSign A j g x : ℤ))).symm
  exact Finset.sum_smul.symm.trans (congrArg (fun z : ℤ => z • a) hcount)

variable [FiniteDimensional ℝ F] [Fact (Module.finrank ℝ F = 2 + 1)]

theorem localContribution_signed
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (D : Neighborhoods A g) (i : crossings A g) (k : ℕ)
    (a : SingularHomology S₃ (k + 2)) :
    singularHomologyMap (D.data i).innerBoundary.normalizedMap (k + 1)
      (LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) (k + 1) a) =
      (normalSign A j g i.val : ℤ) •
        singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) (SpherePoint.outwardClass 1 j B k a) := by
  rw [SpherePoint.pointConnecting_eq_outward 1 j B i.val (D.data i) k a]
  have hs := normal_smooth_at A g hg i.val i.property
  have hA := normal_isInvertible_at A g hg ht i.val i.property
  have hc0 := NativeParametrization.centered_zero (D := P₃) i.val
  have h := SphereNormalCoordinates.localBoundary_homology_outward 1
    (NativeParametrization.centered i.val) j B (NativeParametrization.zero_mem_centered_source i.val)
    (normalProjection A ∘ g) (hc0.symm ▸ hs.mdifferentiableAt (by simp))
    (hc0.symm ▸ hA) (D.linear i) (D.derivative_eq i) (D.data i).innerBoundary k
    (SpherePoint.outwardClass 1 j B k a)
  rw [hc0] at h
  exact h

open Classical in
theorem detector_signed_count
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (hfin : (crossings A g).Finite) (k : ℕ) (a : SingularHomology S₃ (k + 2)) :
    detector A (k + 1) (singularHomologyMap g (k + 2) a) =
      normalCount A j g hfin •
        singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) (SpherePoint.outwardClass 1 j B k a) := by
  letI := hfin.fintype
  obtain ⟨D⟩ := nonempty_neighborhoods A g hfin hg ht
  apply (detector_sum A g D (k + 1) a).trans
  apply Eq.trans (Finset.sum_congr rfl (fun i _ => localContribution_signed A j B g hg ht D i k a))
  exact normalCount_smul A j g hfin _

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
