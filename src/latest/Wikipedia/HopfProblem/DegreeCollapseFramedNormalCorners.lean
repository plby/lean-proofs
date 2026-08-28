import Wikipedia.HopfProblem.DegreeCollapseMutualNormalCorners
import Wikipedia.HopfProblem.DegreeCollapseFramedCoreImmersion
import Wikipedia.HopfProblem.DegreeCollapseDualNormalCount

/-!
# The original framed face supplies the Whitney normal detector

The inverse face chart provides one normal map along the entire fixed
core. In a fixed three-dimensional sheet model it is smooth, vanishes on
that core, and is submersive. Thus the generic normal-corner comparison
applies to every constructed bigon against this actual framed sphere.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedNormal

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare WhitneyPairModel FramedSurgery

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [T2Space M] [IsManifold (𝓡 6) ∞ M]
  (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (i : Sheet ≃L[ℝ] Vector 3)

def sheetNormal : M → Sheet := i.symm ∘ normalProjection (E := Vector 4) A

theorem smooth_sheetNormal :
    ContMDiffOn (𝓡 6) 𝓘(ℝ, Sheet) ∞ (sheetNormal A i) A.chart.target :=
  i.symm.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_normalProjection (E := Vector 4) A)

theorem sheetNormal_derivative (x : M) (hx : x ∈ A.chart.target) :
    mfderiv (𝓡 6) 𝓘(ℝ, Sheet) (sheetNormal A i) x =
      i.symm.toContinuousLinearMap.comp (mfderiv (𝓡 6) (𝓡 3) (normalProjection (E := Vector 4) A) x) := by
  have hn := (contMDiffOn_normalProjection (E := Vector 4) A).contMDiffAt (A.chart.open_target.mem_nhds hx)
  have hi : ContMDiff (𝓡 3) 𝓘(ℝ, Sheet) ∞ i.symm := i.symm.contDiff.contMDiff
  have hdi : mfderiv (𝓡 3) 𝓘(ℝ, Sheet) i.symm (normalProjection (E := Vector 4) A x) =
      i.symm.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact i.symm.toContinuousLinearMap.fderiv
  rw [sheetNormal, mfderiv_comp x (hi.mdifferentiableAt (by simp))
    (hn.mdifferentiableAt (by simp)), hdi]
  rfl

theorem sheetNormal_submersive (x : M) (hx : x ∈ A.chart.target) :
    Surjective (mfderiv (𝓡 6) 𝓘(ℝ, Sheet) (sheetNormal A i) x) := by
  rw [sheetNormal_derivative A i x hx]
  exact i.symm.surjective.comp (surjective_normalProjection_derivative (E := Vector 4) A x hx)

theorem corners_iff_sheetNormal
    {S : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := Vector 6) S (range (coreMap (E := Vector 4) A)) a b k l h)
    (d : StripNormalData Plane (Vector 3) (E := Vector 6) S k)
    (e : StripNormalData Plane (Vector 3) (E := Vector 6) (range (coreMap (E := Vector 4) A)) l) :
    (tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : Sheet => sheetNormal A i (d.chart (w, 0))) (0, 0)).det *
        (fderiv ℝ (fun w : Sheet => sheetNormal A i (d.chart (w, 0))) (1, 0)).det < 0 := by
  have hcenter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      e.chart (StripCoordinates.center t) ∈ range (coreMap (E := Vector 4) A) :=
    (e.sheet _ (e.line ht)).mpr rfl
  have hcenterO (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      e.chart (StripCoordinates.center t) ∈ A.chart.target := by
    obtain ⟨u, hu⟩ := hcenter t ht
    exact hu ▸ core_mem_chart_target (E := Vector 4) A u
  apply MutualSheets.corners_iff_normal_determinants tube d e (sheetNormal A i)
    A.chart.open_target (smooth_sheetNormal A i)
  · rintro z ⟨⟨u, rfl⟩, _⟩
    change i.symm (normalProjection (E := Vector 4) A (coreMap (E := Vector 4) A u)) = 0
    rw [normalProjection_core, map_zero]
  · exact hcenterO
  · exact fun t ht => sheetNormal_submersive A i _ (hcenterO t ht)

end Wikipedia.HopfProblem.DegreeCollapse.FramedNormal
