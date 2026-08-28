import Wikipedia.HopfProblem.DegreeCollapseStandardBeltCircle
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# A point of the original belt outside a lower-dimensional smooth image

The positive Morse coordinates are projected onto a hemisphere's disk
coordinates. Those coordinates cover an actual open ball on the belt.
A lower-dimensional smooth image cannot cover that ball. This selects a
belt point directly, without assuming ambient density restricts to the belt.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

def euclideanTail (n : ℕ) : Hemisphere.Ambient (n + 1) →L[ℝ] Hemisphere.Ambient n :=
  ( { toFun := fun x => WithLp.toLp 2 (fun i : Fin n => x i.succ)
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro a x; ext i; rfl } :
    Hemisphere.Ambient (n + 1) →ₗ[ℝ] Hemisphere.Ambient n).toContinuousLinearMap

theorem euclideanTail_hemisphere {n : ℕ} (b : Bool) (x : Hemisphere.Ball n) :
    euclideanTail n (Hemisphere.point b x).val = x.val := by
  ext i
  rfl

variable {E M D H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace H] {I : ModelWithCorners ℝ D H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [LindelofSpace Y]
  {f : M → ℝ} {p : M}

theorem exists_belt_point_avoiding_smooth_image (d : MorseSurgeryData E f p)
    (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (g : Y → M) (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hdim : Module.finrank ℝ D < n) :
    ∃ v : sphere (0 : d.chart.PositiveCoordinates) 1,
      (d.surgery.beltSphere v).val ∉ range g := by
  let b := (stdOrthonormalBasis ℝ d.chart.PositiveCoordinates).reindex
    (finCongr (Fact.out : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1))
  let L : d.chart.PositiveCoordinates ≃ₗᵢ[ℝ] Hemisphere.Ambient (n + 1) := b.repr
  let P : M → Hemisphere.Ambient n := fun x =>
    euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart x).2)
  let U : Set Y := g ⁻¹' d.chart.splitChart.source
  have hU : IsOpen U := d.chart.splitChart.open_source.preimage hg.continuous
  have hPg : ContMDiffOn I 𝓘(ℝ, Hemisphere.Ambient n) ∞ (P ∘ g) U := by
    have hc : ContMDiffOn I
        𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
        (d.chart.splitChart ∘ g) U :=
      d.chart.splitChart.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
    let A : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates →L[ℝ] Hemisphere.Ambient n :=
      (euclideanTail n).comp ((d.radius⁻¹ • L.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (ContinuousLinearMap.snd ℝ d.chart.NegativeCoordinates d.chart.PositiveCoordinates))
    have hQ : ContDiff ℝ ∞ (fun z : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates =>
        euclideanTail n (d.radius⁻¹ • L z.2)) := A.contDiff
    exact hQ.contMDiff.comp_contMDiffOn hc
  have hdense := GeneralPosition.dense_compl_manifold_image hU hPg
    (show Module.finrank ℝ D < Module.finrank ℝ (Hemisphere.Ambient n) by
      simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hdim)
  obtain ⟨x, hxavoid, hxnorm⟩ := hdense.exists_dist_lt 0 (show (0 : ℝ) < 1 by norm_num)
  have hx : ‖x‖ < 1 := by simpa only [dist_zero_left] using hxnorm
  let xB : Hemisphere.Ball n := ⟨x, mem_closedBall_zero_iff.mpr hx.le⟩
  let w := Hemisphere.point true xB
  let v : sphere (0 : d.chart.PositiveCoordinates) 1 :=
    ⟨L.symm w.val, by
      rw [mem_sphere_zero_iff_norm, L.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp w.property⟩
  have hcoord : d.chart.splitChart (d.surgery.beltSphere v).val = (0, d.radius • v.val) := by
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)
  have hproject : P (d.surgery.beltSphere v).val = x := by
    change euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart (d.surgery.beltSphere v).val).2) = x
    rw [hcoord]
    change euclideanTail n (d.radius⁻¹ • L (d.radius • (L.symm w.val))) = x
    rw [L.map_smul, L.apply_symm_apply, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
    exact euclideanTail_hemisphere true xB
  refine ⟨v, ?_⟩
  rintro ⟨y, hy⟩
  apply hxavoid
  refine ⟨y, ?_, ?_⟩
  · change g y ∈ d.chart.splitChart.source
    rw [hy]
    exact d.belt_mem_normalDomain v
  · change P (g y) = x
    rw [hy]
    exact hproject

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
