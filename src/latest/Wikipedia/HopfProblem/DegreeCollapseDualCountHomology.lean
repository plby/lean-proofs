import Wikipedia.HopfProblem.DegreeCollapseDualNormalCount
import Wikipedia.SmoothSixDPoincare.SphereCountMarking

/-!
# Homological control of the actual framed-core normal count

Mark the genuine overlap detector by the constructed integral sphere
isomorphism. Its value on a sphere is the actual signed normal count times
one fixed source marking. A unit detector value forces a unit geometric
count. The count is invariant under actual sphere homotopies whenever the
two endpoint maps are transverse with finite crossing sets.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.DualCover

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "P₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₃" => sphere (0 : P₄) 1

local instance : Fact (Module.finrank ℝ P₄ = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ F = 2 + 1)]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (j : (ℝ × F) ≃L[ℝ] P₄) (B : P₃ ≃L[ℝ] F)

def markedDetector : SingularHomology X 3 →ₗ[ℤ] ℤ :=
  (SpherePoint.overlapCountMark 1 B).toLinearMap.comp (detector A 2)

theorem markedDetector_sphere_count (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (hfin : (crossings A g).Finite) (a : SingularHomology S₃ 3) :
    markedDetector A B (singularHomologyMap g 3 a) =
      normalCount A j g hfin * SpherePoint.sourceCountMark 1 j B a := by
  have h := congrArg (SpherePoint.overlapCountMark 1 B)
    (detector_signed_count A j B g hg ht hfin 1 a)
  rw [map_zsmul, SpherePoint.overlapCountMark_linear] at h
  exact h

theorem normalCount_eq_marked (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (hfin : (crossings A g).Finite) :
    normalCount A j g hfin = markedDetector A B
      (singularHomologyMap g 3 ((SpherePoint.sourceCountMark 1 j B).symm 1)) := by
  have h := markedDetector_sphere_count A j B g hg ht hfin
    ((SpherePoint.sourceCountMark 1 j B).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at h
  exact h.symm

theorem normalCount_unit_of_detector_image (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (hfin : (crossings A g).Finite) (a : SingularHomology S₃ 3)
    (ha : markedDetector A B (singularHomologyMap g 3 a) = 1) :
    (normalCount A j g hfin).natAbs = 1 := by
  have h := markedDetector_sphere_count A j B g hg ht hfin a
  rw [ha] at h
  exact Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one _ h.symm)

theorem normalCount_zero_of_detector_image (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (hfin : (crossings A g).Finite) (a : SingularHomology S₃ 3) (ha : a ≠ 0)
    (hz : markedDetector A B (singularHomologyMap g 3 a) = 0) :
    normalCount A j g hfin = 0 := by
  have h := markedDetector_sphere_count A j B g hg ht hfin a
  rw [hz] at h
  have hn : SpherePoint.sourceCountMark 1 j B a ≠ 0 := by
    intro he
    exact ha ((SpherePoint.sourceCountMark 1 j B).injective
      (he.trans (map_zero _).symm))
  exact (mul_eq_zero.mp h.symm).resolve_right hn

include B in
theorem normalCount_eq_of_homotopic (g g' : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g) (hg' : ContMDiff (𝓡 3) J ∞ g')
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (ht' : ∀ x u, coreMap A u = g' x → Surjective
      ((mfderiv (𝓡 3) J g' x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (hfin : (crossings A g).Finite) (hfin' : (crossings A g').Finite)
    (hh : g.Homotopic g') : normalCount A j g hfin = normalCount A j g' hfin' := by
  rw [normalCount_eq_marked A j B g hg ht hfin,
    normalCount_eq_marked A j B g' hg' ht' hfin', homotopic_homologyMap hh 3]

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
