import Wikipedia.NoExoticSixSphere.WhitneySphereChart

/-!
# An actual contraction of the chart-contained Whitney sphere

Scalar contraction stays in the same product of closed balls. Composing
with the retained chart gives a whole-sphere homotopy to its center in the
original manifold, not merely a contraction of the coordinate formula.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.WhitneySphere

open GLOrthonormalization

theorem contracted_map_mem_product (t : unitInterval) (x : Sphere 3) :
    (1 - (t : ℝ)) • map x ∈
      closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 := by
  have hball (u : Vector 3) (hu : u ∈ closedBall (0 : Vector 3) 1) :
      (1 - (t : ℝ)) • u ∈ closedBall (0 : Vector 3) 1 := by
    have ht : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    have hu' : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
    calc
      (1 - (t : ℝ)) * ‖u‖ ≤ (1 - (t : ℝ)) * 1 := mul_le_mul_of_nonneg_left hu' ht
      _ ≤ 1 := by linarith [t.property.1]
  exact ⟨hball _ (map_mem_product x).1, hball _ (map_mem_product x).2⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hprod : closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 ⊆ Φ.source)

def contraction : (chartContinuousMap Φ hprod).Homotopy (ContinuousMap.const _ (Φ 0)) where
  toFun p := Φ ((1 - (p.1 : ℝ)) • map p.2)
  continuous_toFun := by
    apply Φ.toOpenPartialHomeomorph.continuousOn.comp_continuous
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (contMDiff_map.continuous.comp continuous_snd)
    · exact fun p ↦ hprod (contracted_map_mem_product p.1 p.2)
  map_zero_left x := by
    change Φ ((1 - (0 : ℝ)) • map x) = Φ (map x)
    rw [sub_zero, one_smul]
  map_one_left x := by
    change Φ ((1 - (1 : ℝ)) • map x) = Φ 0
    rw [sub_self, zero_smul]

end NoExoticSixSphere.WhitneySphere
