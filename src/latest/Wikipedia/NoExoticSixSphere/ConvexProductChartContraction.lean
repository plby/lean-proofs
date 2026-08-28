import Wikipedia.NoExoticSixSphere.SphereSumCapCoordinates

/-!
# Actual contractions through a convex retained product chart

The inverse chart supplies the coordinate map, and scalar contraction stays
inside its proved convex source. Every sphere map contained in its target
therefore has an explicit homotopy to the original chart center.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ProductChartCoordinates

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hc : Convex ℝ Φ.source) (h0 : (0 : Vector 3 × Vector 3) ∈ Φ.source)

include hc h0 in
theorem contracted_coordinate_mem_source (t : unitInterval) {z : Vector 3 × Vector 3}
    (hz : z ∈ Φ.source) : (1 - (t : ℝ)) • z ∈ Φ.source :=
  hc.smul_mem_of_zero_mem h0 hz ⟨sub_nonneg.mpr t.property.2,
    sub_le_self 1 t.property.1⟩

def contraction (f : C(Sphere 3, M)) (hf : ∀ x, f x ∈ Φ.target) :
    f.Homotopy (ContinuousMap.const _ (Φ 0)) where
  toFun p := Φ ((1 - (p.1 : ℝ)) • Φ.symm (f p.2))
  continuous_toFun := by
    have hi : Continuous (fun p : unitInterval × Sphere 3 ↦ Φ.symm (f p.2)) :=
      Φ.symm.toOpenPartialHomeomorph.continuousOn.comp_continuous
        (f.continuous.comp continuous_snd) (fun p ↦ hf p.2)
    exact Φ.toOpenPartialHomeomorph.continuousOn.comp_continuous
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul hi)
      (fun p ↦ contracted_coordinate_mem_source Φ hc h0 p.1 (Φ.map_target (hf p.2)))
  map_zero_left x := by
    change Φ ((1 - (0 : ℝ)) • Φ.symm (f x)) = f x
    rw [sub_zero, one_smul]
    exact Φ.right_inv (hf x)
  map_one_left x := by
    change Φ ((1 - (1 : ℝ)) • Φ.symm (f x)) = Φ 0
    rw [sub_self, zero_smul]

end NoExoticSixSphere.ProductChartCoordinates
