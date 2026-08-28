import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairChart
import Wikipedia.NoExoticSixSphere.CleanTransverseSphereResolution
import Wikipedia.NoExoticSixSphere.ConvexProductChartContraction
import Wikipedia.NoExoticSixSphere.SphereResolutionChartContainment

/-!
# Resolving the actual embedded reference pair inside a retained chart

A globally clean sheet chart exists at its unique center fibers. The actual
glued sphere is a self-transverse immersion with unordered double-point
parity one. If the enclosing chart has convex source, the entire resolution
has an explicit contraction through that same original manifold chart.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hball : closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Φ.source)

theorem exists_clean_chart :
    ∃ b : ℝ, 0 < b ∧ ∃ Γ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
      (Vector 3 × Vector 3) M ∞,
      closedBall (0 : Vector 3) b ×ˢ closedBall (0 : Vector 3) b ⊆ Γ.source ∧
      Γ.target ⊆ Φ.target ∧
      (∀ v, (v, 0) ∈ Γ.source → Γ (v, 0) = chartLeft Φ hball (sourceChart v)) ∧
      (∀ v, (0, v) ∈ Γ.source → Γ (0, v) = chartRight Φ hball (sourceChart v)) ∧
      (∀ q ∈ Γ.source,
        (∀ x, chartLeft Φ hball x = Γ q ↔ q.2 = 0 ∧ x = sourceChart q.1) ∧
        (∀ x, chartRight Φ hball x = Γ q ↔ q.1 = 0 ∧ x = sourceChart q.2)) := by
  have hz : chartLeft Φ hball (sourceChart 0) = chartRight Φ hball (sourceChart 0) :=
    (chartLeft_center Φ hball).trans (chartRight_center Φ hball).symm
  exact exists_globally_clean_sphere_sheetChart (chartLeft Φ hball) (chartRight Φ hball)
    (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball) hz
    (fun _ h ↦ injective_chartLeft Φ hball h)
    (fun _ h ↦ injective_chartRight Φ hball h)
    (chart_pairTransverse Φ hball _ _ hz) Φ.open_target
    (range_chartLeft Φ hball ⟨sourceChart 0, rfl⟩)

variable (Γ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Γ.source)
  (hleft : ∀ v, (v, 0) ∈ Γ.source → Γ (v, 0) = chartLeft Φ hball (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Γ.source → Γ (0, v) = chartRight Φ hball (sourceChart v))
  (hclean : ∀ q ∈ Γ.source,
    (∀ x, chartLeft Φ hball x = Γ q ↔ q.2 = 0 ∧ x = sourceChart q.1) ∧
    (∀ x, chartRight Φ hball x = Γ q ↔ q.1 = 0 ∧ x = sourceChart q.2))

def resolution : C(Sphere 3, M) :=
  gluedSphereMap Γ (chartLeft Φ hball) (chartRight Φ hball) hε ⟨ha.1.le, ha.2⟩
    hprod hleft hright (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)

theorem contMDiff_resolution :
    ContMDiff (𝓡 3) (𝓡 6) ∞ (resolution Φ hball Γ hε ha hprod hleft hright) :=
  contMDiff_gluedSphere Γ (chartLeft Φ hball) (chartRight Φ hball) hε ⟨ha.1.le, ha.2⟩
    hprod hleft hright (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)

theorem injective_mfderiv_resolution (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (resolution Φ hball Γ hε ha hprod hleft hright) x) :=
  injective_mfderiv_gluedSphere Γ (chartLeft Φ hball) (chartRight Φ hball) hε hprod ha
    hleft hright (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
    (injective_mfderiv_chartLeft Φ hball) (injective_mfderiv_chartRight Φ hball) x

include hclean in
theorem selfTransverse_resolution :
    NativeSphereSelfTransverse (resolution Φ hball Γ hε ha hprod hleft hright) :=
  selfTransverse_gluedSphere Γ (chartLeft Φ hball) (chartRight Φ hball) hε ha hprod
    hleft hright hclean (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
    (chartLeft_selfTransverse Φ hball) (chartRight_selfTransverse Φ hball)
    (chart_pairTransverse Φ hball)

include hclean in
theorem unorderedParity_resolution :
    SphereSelfIntersections.unorderedParity (resolution Φ hball Γ hε ha hprod hleft hright) =
      1 := by
  have hfinF := SphereSelfIntersections.finite_pairs (contMDiff_chart_left Φ hball)
    ((nativeSphereSelfTransverse_iff _).mp (chartLeft_selfTransverse Φ hball))
    (injective_mfderiv_chartLeft Φ hball)
  have hfinG := SphereSelfIntersections.finite_pairs (contMDiff_chart_right Φ hball)
    ((nativeSphereSelfTransverse_iff _).mp (chartRight_selfTransverse Φ hball))
    (injective_mfderiv_chartRight Φ hball)
  have hfinFG := MapIntersections.finite_pairs_of_nativeTransverse
    (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball) (chart_pairTransverse Φ hball)
  have h := gluedSphere_unorderedParity (chartLeft Φ hball) (chartRight Φ hball) Γ hε ha.1
    hprod hclean hfinF hfinG hfinFG
  rw [SphereSelfIntersections.unorderedParity_zero_of_injective _ (injective_chartLeft Φ hball),
    SphereSelfIntersections.unorderedParity_zero_of_injective _ (injective_chartRight Φ hball),
    chart_intersectionParity_zero Φ hball, zero_add, zero_add, zero_add] at h
  exact h

theorem resolution_mem_chartTarget (hΓ : Γ.target ⊆ Φ.target) (x : Sphere 3) :
    resolution Φ hball Γ hε ha hprod hleft hright x ∈ Φ.target :=
  gluedSphere_mem_of_ranges Γ (chartLeft Φ hball) (chartRight Φ hball) hε hprod hΓ
    (fun y ↦ range_chartLeft Φ hball ⟨y, rfl⟩)
    (fun y ↦ range_chartRight Φ hball ⟨y, rfl⟩) x

def resolutionContraction (hc : Convex ℝ Φ.source) (hΓ : Γ.target ⊆ Φ.target) :
    (resolution Φ hball Γ hε ha hprod hleft hright).Homotopy
      (ContinuousMap.const _ (Φ 0)) :=
  ProductChartCoordinates.contraction Φ hc (hball (mem_closedBall_self (by norm_num)))
    (resolution Φ hball Γ hε ha hprod hleft hright)
    (resolution_mem_chartTarget Φ hball Γ hε ha hprod hleft hright hΓ)

def leftContraction (hc : Convex ℝ Φ.source) :
    (chartLeft Φ hball).Homotopy (ContinuousMap.const _ (Φ 0)) :=
  ProductChartCoordinates.contraction Φ hc (hball (mem_closedBall_self (by norm_num)))
    (chartLeft Φ hball) (fun x ↦ range_chartLeft Φ hball ⟨x, rfl⟩)

def rightContraction (hc : Convex ℝ Φ.source) :
    (chartRight Φ hball).Homotopy (ContinuousMap.const _ (Φ 0)) :=
  ProductChartCoordinates.contraction Φ hc (hball (mem_closedBall_self (by norm_num)))
    (chartRight Φ hball) (fun x ↦ range_chartRight Φ hball ⟨x, rfl⟩)

end NoExoticSixSphere.DoubleCrossingSpherePair
