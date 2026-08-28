import Wikipedia.HopfProblem.DegreeCollapseCubeSphereGenerator
import Wikipedia.HopfProblem.DegreeCollapseDualCountHomology
import Wikipedia.HopfProblem.DegreeCollapseFramedNormalSigns
import Wikipedia.HopfProblem.DegreeCollapseFramedCountComparison
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections

/-!
# Reduction of the genuine marked detector to the actual intersection count

The source cubical class has unit value under every integral marking.
Thus its fixed marking factor becomes one modulo two. Every transverse
normal sign likewise reduces to one. The original source crossing set
is in bijection with the actual ordered intersection pairs, since the
fixed framed core is injective. No unit detector class is required.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedNormal

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SmoothCube
open Wikipedia.SmoothSixDPoincare FramedSurgery
open SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

theorem unit_int_cast_modTwo (z : ℤ) (hz : IsUnit z) : (z : ZMod 2) = 1 := by
  rcases Int.isUnit_iff.mp hz with rfl | rfl <;> norm_num <;> decide

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [T2Space M] [IsManifold (𝓡 6) ∞ M]
  (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (j : (ℝ × Vector 3) ≃L[ℝ] Vector 4) (g : C(Sphere 3, M))

def pairsCrossingsEquiv : MapIntersections.pairs g (coreMap (E := Vector 4) A) ≃
    DualCover.crossings (E := Vector 4) A g where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property.symm⟩⟩
  invFun x := ⟨(x.val, Function.invFun (coreMap (E := Vector 4) A) (g x.val)),
    (Function.invFun_eq x.property).symm⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, Function.invFun (coreMap (E := Vector 4) A) (g p.val.1)) = p.val
    refine Prod.ext rfl ?_
    apply FramedCore.injective_core A
    exact (Function.invFun_eq ⟨p.val.2, p.property.symm⟩).trans p.property
  right_inv _ := Subtype.ext rfl

theorem pairs_ncard_eq_crossings :
    (MapIntersections.pairs g (coreMap (E := Vector 4) A)).ncard =
      (DualCover.crossings (E := Vector 4) A g).ncard :=
  Nat.card_congr (pairsCrossingsEquiv A g)

theorem normalCount_modTwo (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (ht : ∀ x u, coreMap (E := Vector 4) A u = g x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u)))
    (hfin : (DualCover.crossings (E := Vector 4) A g).Finite) :
    (DualCover.normalCount (E := Vector 4) A j g hfin : ZMod 2) =
      MapIntersections.parity g (coreMap (E := Vector 4) A) := by
  classical
  have hs (x : Sphere 3) (hx : x ∈ hfin.toFinset) :
      ((DualCover.normalSign (E := Vector 4) A j g x : ℤ) : ZMod 2) = 1 := by
    rcases normalSign_unit A j g hg ht x (hfin.mem_toFinset.mp hx) with hp | hn
    · rw [hp]
      norm_num
    · rw [hn]
      norm_num
      decide
  unfold DualCover.normalCount MapIntersections.parity
  rw [Int.cast_sum, pairs_ncard_eq_crossings A g]
  rw [Finset.sum_congr rfl hs, Set.ncard_eq_toFinset_card _ hfin]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

include j in
theorem markedDetector_modTwo_transverse (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (ht : ∀ x u, coreMap (E := Vector 4) A u = g x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u)))
    (hfin : (DualCover.crossings (E := Vector 4) A g).Finite) :
    (DualCover.markedDetector (E := Vector 4) A (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (integralSphereClass g) : ZMod 2) = MapIntersections.parity g (coreMap (E := Vector 4) A) := by
  have h := DualCover.markedDetector_sphere_count (E := Vector 4) A j
    (ContinuousLinearEquiv.refl ℝ (Vector 3)) g hg ht hfin integralCubeSphereClass
  change DualCover.markedDetector (E := Vector 4) A (ContinuousLinearEquiv.refl ℝ (Vector 3))
    (integralSphereClass g) = _ at h
  rw [h, Int.cast_mul]
  have hu := CubeSphereGenerator.marking_unit
    (SpherePoint.sourceCountMark 1 j (ContinuousLinearEquiv.refl ℝ (Vector 3)))
  rw [unit_int_cast_modTwo _ hu, mul_one]
  exact normalCount_modTwo A j g hg ht hfin

end Wikipedia.HopfProblem.DegreeCollapse.FramedNormal
