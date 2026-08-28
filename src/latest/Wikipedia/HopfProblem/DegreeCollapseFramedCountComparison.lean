import Wikipedia.HopfProblem.DegreeCollapseFramedNormalSigns
import Wikipedia.HopfProblem.DegreeCollapseMutualSheetSignEquivalence
import Wikipedia.HopfProblem.DegreeCollapseMutualSheetFinite
import Wikipedia.HopfProblem.DegreeCollapseFiniteSignComparison

/-!
# The homological normal count and the intrinsic Whitney count agree in absolute value

For any two actual crossings construct the native bigon. Both the fixed
normal sign and the intrinsic ordered intersection sign are equivalent
to its actual corner condition. Thus they recognize exactly the same
opposite pairs on the original finite crossing set. The algebraic sign
comparison gives equality of the absolute integer sums, without choosing
independent local orientations or assuming a global sign formula.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedNormal

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare WhitneyPairModel FramedSurgery
open OrbitPair.DeterminantSignCover

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [T2Space M] [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (oS : Orientation (tangentBundleCore (𝓡 3) (Sphere 3)))
  (oM : Orientation (tangentBundleCore (𝓡 6) M))
  (j : (ℝ × Vector 3) ≃L[ℝ] Vector 4)
  (K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6)
  (g : C(Sphere 3, M))

theorem normal_opposite_iff_intrinsic
    (hgood : MutualSheets.Good (D := Vector 3) (E := Vector 6) (coreMap (E := Vector 4) A) g)
    (x₀ x₁ : Sphere 3) (hx₀ : x₀ ∈ DualCover.crossings (E := Vector 4) A g)
    (hx₁ : x₁ ∈ DualCover.crossings (E := Vector 4) A g) :
    (DualCover.normalSign (E := Vector 4) A j g x₀ *
      DualCover.normalSign (E := Vector 4) A j g x₁ = -1) ↔
      (MutualSheets.pointSign oS oS oM K g (coreMap (E := Vector 4) A) x₀ *
        MutualSheets.pointSign oS oS oM K g (coreMap (E := Vector 4) A) x₁ = -1) := by
  by_cases he : x₀ = x₁
  · subst x₁
    have hs : ∀ s : SignType, s * s ≠ -1 := by decide
    constructor <;> intro h <;> exact (hs _ h).elim
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  obtain ⟨u₀, hu₀⟩ := hx₀
  obtain ⟨u₁, hu₁⟩ := hx₁
  have hpartner₀ : Function.invFun (coreMap (E := Vector 4) A) (g x₀) = u₀ := by
    apply FramedCore.injective_core A
    exact (Function.invFun_eq ⟨u₀, hu₀⟩).trans hu₀.symm
  have hpartner₁ : Function.invFun (coreMap (E := Vector 4) A) (g x₁) = u₁ := by
    apply FramedCore.injective_core A
    exact (Function.invFun_eq ⟨u₁, hu₁⟩).trans hu₁.symm
  have hpoint := MutualSheets.pointSign_opposite_iff oS oS oM K g (coreMap (E := Vector 4) A) x₀ x₁
  rw [hpartner₀, hpartner₁] at hpoint
  obtain ⟨v, hv⟩ := exists_ne (0 : Vector 3)
  obtain ⟨B⟩ := MutualSheets.nonempty_bigonData (by simp) (by simp)
    hg (contMDiff_coreMap (E := Vector 4) A) hinj (FramedCore.injective_core A)
    hi (FramedCore.injective_core_derivative A) ht hu₀ hu₁ he
    (PathConnectedSpace.somePath x₀ x₁) (PathConnectedSpace.somePath u₀ u₁) hv hv hv hv
  have hxB₀ : g x₀ = B.lowerNormal.chart (StripCoordinates.center 0) :=
    (congrArg g B.left_zero).symm.trans
      ((B.lower.center 0 (by simp)).symm.trans (B.lowerNormal.center 0))
  have hxB₁ : g x₁ = B.lowerNormal.chart (StripCoordinates.center 1) :=
    (congrArg g B.left_one).symm.trans
      ((B.lower.center 1 (by simp)).symm.trans (B.lowerNormal.center 1))
  have hnormal := opposite_normalSigns_iff_corners A j g hg hinj hi ht
    B.tube B.lowerNormal B.upperNormal x₀ x₁ hxB₀ hxB₁
  let J : Sheet ≃L[ℝ] Vector 3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Sheet, Plane, Module.finrank_prod])
  have hswap (x u : Sphere 3) (hc : coreMap (E := Vector 4) A u = g x) :
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u).coprod
        (mfderiv (𝓡 3) (𝓡 6) g x)) := by
    let Dg : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) g x
    let Da : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u
    exact TransverseCoordinates.surjective_coprod_swap Dg Da (ht x u hc)
  have hends : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) (B.rightArc t)).coprod
        (mfderiv (𝓡 3) (𝓡 6) g (B.leftArc t))) := by
    intro t htI
    change Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) (B.rightArc t) : Vector 3 →L[ℝ] Vector 6).coprod
        (mfderiv (𝓡 3) (𝓡 6) g (B.leftArc t) : Vector 3 →L[ℝ] Vector 6))
    rcases htI with rfl | rfl
    · rw [B.left_zero, B.right_zero]
      exact hswap x₀ u₀ hu₀
    · rw [B.left_one, B.right_one]
      exact hswap x₁ u₁ hu₁
  have hintrinsic : (B.tube.sheetPairDet B.lowerNormal B.upperNormal 0 *
      B.tube.sheetPairDet B.lowerNormal B.upperNormal 1 < 0) ↔
      MutualSheets.intersectionSign oS oS oM K g (coreMap (E := Vector 4) A) x₀ u₀ ≠
        MutualSheets.intersectionSign oS oS oM K g (coreMap (E := Vector 4) A) x₁ u₁ := by
    constructor
    · intro hc
      have h := MutualSheets.opposite_corners_imply_opposite_signs oS oS oM J K
        B.tube B.lowerNormal B.upperNormal hg (contMDiff_coreMap (E := Vector 4) A)
        hi (FramedCore.injective_core_derivative A) hends hc
      simpa only [B.left_zero, B.left_one, B.right_zero, B.right_one] using h
    · intro hc
      apply MutualSheets.opposite_signs_imply_opposite_corner_determinants oS oS oM J K
        B.tube B.lowerNormal B.upperNormal hg (contMDiff_coreMap (E := Vector 4) A)
        hi (FramedCore.injective_core_derivative A) hends
      simpa only [B.left_zero, B.left_one, B.right_zero, B.right_one] using hc
  exact hnormal.trans (hintrinsic.trans hpoint.symm)

theorem count_natAbs_eq
    (hgood : MutualSheets.Good (D := Vector 3) (E := Vector 6) (coreMap (E := Vector 4) A) g)
    (hfin : (DualCover.crossings (E := Vector 4) A g).Finite) :
    (DualCover.normalCount (E := Vector 4) A j g hfin).natAbs =
      (MutualSheets.signedCount oS oS oM K g (coreMap (E := Vector 4) A) hfin).natAbs := by
  apply SignComparison.natAbs_sum_eq_of_opposite_iff hfin.toFinset
    (DualCover.normalSign (E := Vector 4) A j g)
    (MutualSheets.pointSign oS oS oM K g (coreMap (E := Vector 4) A))
  · intro x hx
    exact normalSign_unit A j g hgood.1 hgood.2.2.2 x (hfin.mem_toFinset.mp hx)
  · intro x _
    exact MutualSheets.pointSign_unit oS oS oM K g (coreMap (E := Vector 4) A) x
  · intro x hx y hy
    exact normal_opposite_iff_intrinsic A oS oM j K g hgood x y
      (hfin.mem_toFinset.mp hx) (hfin.mem_toFinset.mp hy)

end Wikipedia.HopfProblem.DegreeCollapse.FramedNormal
