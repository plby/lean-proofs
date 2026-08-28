import Wikipedia.NoExoticSixSphere.SpherePinchMap

/-!
# Each one-sided geometric pinch collapses a hemisphere

The northern collapse is homotopic to the identity by the actual normalized
straight segment. Its inner product with the original point is nonnegative,
so that segment never vanishes. The southern collapse is its precomposition
with the antipodal map. These are maps on the original unit sphere.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereFold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def northCollapse (v : UnitSphere E) : C(UnitSphere E, UnitSphere E) :=
  pinch v (ContinuousMap.id _) (ContinuousMap.const _ (antipode v)) rfl

def southCollapse (v : UnitSphere E) : C(UnitSphere E, UnitSphere E) :=
  pinch v (ContinuousMap.const _ (antipode v)) (ContinuousMap.id _) rfl

theorem northCollapse_north (v x : UnitSphere E) (hx : 0 ≤ height v x) :
    northCollapse v x = fold v x := pinch_north _ _ _ _ x hx

theorem northCollapse_south (v x : UnitSphere E) (hx : height v x ≤ 0) :
    northCollapse v x = antipode v := pinch_south _ _ _ _ x hx

theorem southCollapse_north (v x : UnitSphere E) (hx : 0 ≤ height v x) :
    southCollapse v x = antipode v := pinch_north _ _ _ _ x hx

theorem southCollapse_south (v x : UnitSphere E) (hx : height v x ≤ 0) :
    southCollapse v x = fold v x := pinch_south _ _ _ _ x hx

theorem inner_northCollapse_nonneg (v x : UnitSphere E) :
    0 ≤ inner ℝ (x : E) (northCollapse v x : E) := by
  by_cases hx : 0 ≤ height v x
  · rw [northCollapse_north v x hx, fold_val, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm,
      ← real_inner_comm (x : E) (v : E)]
    change 0 ≤ 2 * height v x * 1 ^ 2 - height v x
    linarith
  · rw [northCollapse_south v x (le_of_not_ge hx)]
    change 0 ≤ inner ℝ (x : E) (-(v : E))
    rw [inner_neg_right, real_inner_comm]
    exact neg_nonneg.mpr (le_of_not_ge hx)

theorem nonnegative_inner_segment_ne_zero (x y : UnitSphere E)
    (hxy : 0 ≤ inner ℝ (x : E) (y : E)) (t : unitInterval) :
    (1 - (t : ℝ)) • (x : E) + (t : ℝ) • (y : E) ≠ 0 := by
  by_cases ht : (t : ℝ) = 1
  · simpa only [ht, sub_self, zero_smul, one_smul, zero_add]
      using ne_zero_of_mem_unit_sphere y
  · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    intro hz
    have he := congrArg (fun z : E ↦ inner ℝ (x : E) z) hz
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, inner_zero_right] at he
    nlinarith [mul_nonneg t.property.1 hxy]

def northCollapseHomotopy (v : UnitSphere E) :
    (ContinuousMap.id (UnitSphere E)).Homotopy (northCollapse v) where
  toFun p := ⟨NormedSpace.normalize
    ((1 - (p.1 : ℝ)) • (p.2 : E) + (p.1 : ℝ) • (northCollapse v p.2 : E)), by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize
      (nonnegative_inner_segment_ne_zero p.2 (northCollapse v p.2)
        (inner_northCollapse_nonneg v p.2) p.1)⟩
  continuous_toFun := by
    have ht : Continuous (fun p : unitInterval × UnitSphere E ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : unitInterval × UnitSphere E ↦ (p.2 : E)) :=
      continuous_subtype_val.comp continuous_snd
    have hy : Continuous (fun p : unitInterval × UnitSphere E ↦
        (northCollapse v p.2 : E)) :=
      continuous_subtype_val.comp ((northCollapse v).continuous.comp continuous_snd)
    have hB : Continuous (fun p : unitInterval × UnitSphere E ↦
        (1 - (p.1 : ℝ)) • (p.2 : E) + (p.1 : ℝ) • (northCollapse v p.2 : E)) :=
      ((continuous_const.sub ht).smul hx).add (ht.smul hy)
    exact ((hB.norm.inv₀ (fun p ↦ norm_ne_zero_iff.mpr
      (nonnegative_inner_segment_ne_zero p.2 (northCollapse v p.2)
        (inner_northCollapse_nonneg v p.2) p.1))).smul hB).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change NormedSpace.normalize
      ((1 - (0 : ℝ)) • (x : E) + (0 : ℝ) • (northCollapse v x : E)) = (x : E)
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using
      NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x)
  map_one_left x := by
    apply Subtype.ext
    change NormedSpace.normalize
      ((1 - (1 : ℝ)) • (x : E) + (1 : ℝ) • (northCollapse v x : E)) = _
    simpa only [sub_self, zero_smul, one_smul, zero_add] using
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (ClosedHemisphere.unit_norm (northCollapse v x))

theorem southCollapse_eq_north_antipode (v x : UnitSphere E) :
    southCollapse v x = northCollapse v (antipode x) := by
  by_cases hx : 0 ≤ height v x
  · rw [southCollapse_north v x hx,
      northCollapse_south v (antipode x) (by rw [height_antipode]; exact neg_nonpos.mpr hx)]
  · have hn : 0 ≤ height v (antipode x) := by
      rw [height_antipode]
      exact neg_nonneg.mpr (le_of_not_ge hx)
    rw [southCollapse_south v x (le_of_not_ge hx), northCollapse_north v (antipode x) hn,
      fold_antipode]

end NoExoticSixSphere.SphereFold
