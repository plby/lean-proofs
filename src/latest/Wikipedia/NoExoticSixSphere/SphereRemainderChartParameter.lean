import Wikipedia.NoExoticSixSphere.SphereRemainderBasepoint

/-!
# The remainder's actual target-chart parameter and its contraction

The inverse retained chart gives a continuous map into the specified closed
product of balls. Linear contraction within that convex product supplies
a genuine parameter homotopy. These are coordinates of the constructed
manifold-valued remainder, not an assumed chart lift or nullhomotopy.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

abbrev RemainderParameters (ε : ℝ) :=
  ↥(closedBall (0 : Vector 3) (ε * 4) ×ˢ closedBall (0 : Vector 3) (ε * 4))

def remainderParameterZero (ε : ℝ) (hε : 0 < ε) : RemainderParameters ε :=
  ⟨0, mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩

def contractRemainderParameter (ε : ℝ) (hε : 0 < ε) (t : unitInterval)
    (p : RemainderParameters ε) : RemainderParameters ε := by
  refine ⟨(1 - t.val) • p.val, ?_⟩
  have hc : Convex ℝ (closedBall (0 : Vector 3) (ε * 4) ×ˢ
      closedBall (0 : Vector 3) (ε * 4)) :=
    (convex_closedBall (0 : Vector 3) (ε * 4)).prod (convex_closedBall _ _)
  have h := hc p.property (remainderParameterZero ε hε).property
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring : 1 - t.val + t.val = 1)
  simpa only [remainderParameterZero, smul_zero, add_zero] using h

theorem continuous_contractRemainderParameter (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun q : unitInterval × RemainderParameters ε ↦
      contractRemainderParameter ε hε q.1 q.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def remainderParameterContraction (ε : ℝ) (hε : 0 < ε)
    (q : C(Sphere 3, RemainderParameters ε)) :
    q.Homotopy (ContinuousMap.const _ (remainderParameterZero ε hε)) where
  toFun p := contractRemainderParameter ε hε p.1 (q p.2)
  continuous_toFun := (continuous_contractRemainderParameter ε hε).comp
    (continuous_fst.prodMk (q.continuous.comp continuous_snd))
  map_zero_left x := by
    apply Subtype.ext
    change (1 - (0 : unitInterval).val) • (q x).val = (q x).val
    simp
  map_one_left x := by
    apply Subtype.ext
    change (1 - (1 : unitInterval).val) • (q x).val = 0
    simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M)) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)

def remainderChartMap : C(Sphere 3, Vector 3 × Vector 3) where
  toFun x := Φ.symm (remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x)
  continuous_toFun := Φ.toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
    (remainderBasepoint Φ F G hε ha hprod hleft hright hF hG).continuous
    (remainderBasepoint_mem_target Φ F G hε ha hprod hleft hright hF hG)

theorem remainderChartMap_mem_product (x : Sphere 3) :
    remainderChartMap Φ F G hε ha hprod hleft hright hF hG x ∈
      closedBall (0 : Vector 3) (ε * 4) ×ˢ closedBall (0 : Vector 3) (ε * 4) := by
  obtain ⟨z, hz, he⟩ :=
    remainderBasepoint_mem_chartProduct_image Φ F G hε ha hprod hleft hright hF hG x
  change Φ.symm (remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x) ∈ _
  have hcoord : Φ.symm (remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x) = z :=
    (congrArg Φ.symm he).symm.trans (Φ.left_inv (hprod hz))
  exact hcoord.symm ▸ hz

def remainderChartParameter : C(Sphere 3, RemainderParameters ε) :=
  ⟨fun x ↦ ⟨remainderChartMap Φ F G hε ha hprod hleft hright hF hG x,
    remainderChartMap_mem_product Φ F G hε ha hprod hleft hright hF hG x⟩,
    (remainderChartMap Φ F G hε ha hprod hleft hright hF hG).continuous.subtype_mk _⟩

theorem remainderChartParameter_apply (x : Sphere 3) :
    (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG x).val =
      Φ.symm (remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x) := rfl

theorem chart_remainderChartParameter (x : Sphere 3) :
    Φ (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG x).val =
      remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x :=
  Φ.right_inv (remainderBasepoint_mem_target Φ F G hε ha hprod hleft hright hF hG x)

def remainderChartContraction :
    (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG).Homotopy
      (ContinuousMap.const _ (remainderParameterZero ε hε)) :=
  remainderParameterContraction ε hε
    (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG)

end NoExoticSixSphere.SphereSumNeck
