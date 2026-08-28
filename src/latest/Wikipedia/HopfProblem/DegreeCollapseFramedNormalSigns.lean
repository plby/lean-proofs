import Wikipedia.HopfProblem.DegreeCollapseFramedNormalCorners
import Wikipedia.SmoothSixDPoincare.SphereSheetIntersectionSigns

/-!
# Actual normal intersection signs are the Whitney corner signs

The fixed inverse-face normal coordinates and the source sphere's outward
orientation determine the signed count used by the homology detector.
The original retained strip chart compares these normal Jacobians with
the actual corner determinants, including the fixed change of normal
model. No sign correspondence is an input hypothesis.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedNormal

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare WhitneyPairModel FramedSurgery SphereNormalCoordinates

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [T2Space M] [IsManifold (𝓡 6) ∞ M]
  (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (j : (ℝ × Vector 3) ≃L[ℝ] Vector 4) (g : C(Sphere 3, M))

theorem normalSign_opposite_iff (x y : Sphere 3) :
    DualCover.normalSign (E := Vector 4) A j g x * DualCover.normalSign (E := Vector 4) A j g y = -1 ↔
      normalJacobian j x (mfderiv (𝓡 3) (𝓡 3) (normalProjection (E := Vector 4) A ∘ g) x) *
        normalJacobian j y (mfderiv (𝓡 3) (𝓡 3) (normalProjection (E := Vector 4) A ∘ g) y) < 0 := by
  unfold DualCover.normalSign
  rw [← sign_mul, sign_eq_neg_one_iff]

theorem normalSign_unit (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (ht : ∀ x u, coreMap (E := Vector 4) A u = g x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u)))
    (x : Sphere 3) (hx : x ∈ DualCover.crossings (E := Vector 4) A g) :
    DualCover.normalSign (E := Vector 4) A j g x = 1 ∨ DualCover.normalSign (E := Vector 4) A j g x = -1 := by
  have hA := DualCover.normal_isInvertible_at (E := Vector 4) A g hg ht x hx
  have hn : DualCover.normalSign (E := Vector 4) A j g x ≠ 0 :=
    sign_ne_zero.mpr (normalJacobian_ne_zero j x _ hA)
  rcases SignType.trichotomy (DualCover.normalSign (E := Vector 4) A j g x) with h | h | h
  · exact Or.inr h
  · exact (hn h).elim
  · exact Or.inl h

theorem normal_model_data (i : Sheet ≃L[ℝ] Vector 3)
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (ht : ∀ x u, coreMap (E := Vector 4) A u = g x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u)))
    (x : Sphere 3) (hx : x ∈ DualCover.crossings (E := Vector 4) A g) :
    ContMDiffAt (𝓡 6) 𝓘(ℝ, Sheet) ∞ (sheetNormal A i) (g x) ∧
      (mfderiv (𝓡 3) 𝓘(ℝ, Sheet) (sheetNormal A i ∘ g) x).IsInvertible ∧
      normalJacobian ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) i).trans j)
        x (mfderiv (𝓡 3) 𝓘(ℝ, Sheet) (sheetNormal A i ∘ g) x) =
        normalJacobian j x (mfderiv (𝓡 3) (𝓡 3) (normalProjection (E := Vector 4) A ∘ g) x) := by
  obtain ⟨u, hu⟩ := hx
  have hxO : g x ∈ A.chart.target := hu ▸ core_mem_chart_target (E := Vector 4) A u
  have hq := (smooth_sheetNormal A i).contMDiffAt (A.chart.open_target.mem_nhds hxO)
  have hn := DualCover.normal_smooth_at (E := Vector 4) A g hg x ⟨u, hu⟩
  have hA := DualCover.normal_isInvertible_at (E := Vector 4) A g hg ht x ⟨u, hu⟩
  have hi : ContMDiff (𝓡 3) 𝓘(ℝ, Sheet) ∞ i.symm := i.symm.contDiff.contMDiff
  have hdi : mfderiv (𝓡 3) 𝓘(ℝ, Sheet) i.symm (normalProjection (E := Vector 4) A (g x)) =
      i.symm.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact i.symm.toContinuousLinearMap.fderiv
  have hBA : (mfderiv (𝓡 3) 𝓘(ℝ, Sheet) (sheetNormal A i ∘ g) x : Vector 3 →L[ℝ] Sheet) =
      i.symm.toContinuousLinearMap.comp (mfderiv (𝓡 3) (𝓡 3) (normalProjection (E := Vector 4) A ∘ g) x) := by
    change mfderiv (𝓡 3) 𝓘(ℝ, Sheet) (i.symm ∘ (normalProjection (E := Vector 4) A ∘ g)) x = _
    have hc := mfderiv_comp x (hi.mdifferentiableAt (by simp)) (hn.mdifferentiableAt (by simp))
    refine hc.trans ?_
    change (mfderiv (𝓡 3) 𝓘(ℝ, Sheet) i.symm (normalProjection (E := Vector 4) A (g x)) :
      Vector 3 →L[ℝ] Sheet).comp
        (mfderiv (𝓡 3) (𝓡 3) (normalProjection (E := Vector 4) A ∘ g) x :
          Vector 3 →L[ℝ] Vector 3) = _
    rw [hdi]
    rfl
  refine ⟨hq, ?_, ?_⟩
  · rw [hBA]
    exact (show i.symm.toContinuousLinearMap.IsInvertible from ⟨i.symm, rfl⟩).comp hA
  · rw [hBA]
    exact normalJacobian_change_normal_model j i x _ hA

theorem opposite_normalSigns_iff_corners
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) (hinj : Injective g)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x))
    (ht : ∀ x u, coreMap (E := Vector 4) A u = g x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (coreMap (E := Vector 4) A) u)))
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := Vector 6) (range g) (range (coreMap (E := Vector 4) A)) a b k l h)
    (d : StripNormalData Plane (Vector 3) (E := Vector 6) (range g) k)
    (e : StripNormalData Plane (Vector 3) (E := Vector 6) (range (coreMap (E := Vector 4) A)) l)
    (x₀ x₁ : Sphere 3)
    (hx₀ : g x₀ = d.chart (StripCoordinates.center 0))
    (hx₁ : g x₁ = d.chart (StripCoordinates.center 1)) :
    (DualCover.normalSign (E := Vector 4) A j g x₀ * DualCover.normalSign (E := Vector 4) A j g x₁ = -1) ↔
      tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0 := by
  let i : Sheet ≃L[ℝ] Vector 3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Sheet, Plane, Module.finrank_prod])
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) i).trans j
  have hcross (t : ℝ) (ht' : t = 0 ∨ t = 1) (x : Sphere 3)
      (hx : g x = d.chart (StripCoordinates.center t)) : x ∈ DualCover.crossings (E := Vector 4) A g := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht' with rfl | rfl <;> simp
    change g x ∈ range (coreMap (E := Vector 4) A)
    rw [hx, tube.corner_sheet_charts_coincide d e ht']
    exact (e.sheet _ (e.line htI)).mpr rfl
  obtain ⟨hq₀, hi₀, hJ₀⟩ := normal_model_data A j g i hg ht x₀ (hcross 0 (Or.inl rfl) x₀ hx₀)
  obtain ⟨hq₁, hi₁, hJ₁⟩ := normal_model_data A j g i hg ht x₁ (hcross 1 (Or.inr rfl) x₁ hx₁)
  have hs := SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet (V := Vector 4)
    d.chart g hg hinj hi d.sheet d.line (by simp [Module.finrank_prod])
    (sheetNormal A i) j' x₀ x₁ hx₀ hx₁ hq₀ hq₁ hi₀ hi₁
  rw [hJ₀, hJ₁] at hs
  exact (normalSign_opposite_iff A j g x₀ x₁).trans
    (hs.trans (corners_iff_sheetNormal A i tube d e).symm)

end Wikipedia.HopfProblem.DegreeCollapse.FramedNormal
