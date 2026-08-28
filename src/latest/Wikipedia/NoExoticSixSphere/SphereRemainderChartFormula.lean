import Wikipedia.NoExoticSixSphere.SphereRemainderChartParameter

/-!
# Exact target-chart formulas for the remainder's three pieces

The two folded cap coordinates are determined solely by the source
homeomorphisms and reference chart. The middle coordinate is the actual
scaled capped-neck model. These identities retain the inverse-chart domains
and show explicitly where the original target data cancels from the parameter.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction

theorem sourceCoordinate_of_removed {ε : ℝ} {x : Sphere 3} (hx : x ∈ removedSourceDisk ε) :
    sourceChart (sourceChart.symm x) = x ∧ sourceChart.symm x ∈ ball (0 : Vector 3) (ε * 4) := by
  obtain ⟨v, hv, he⟩ := hx
  have hs : v ∈ sourceChart.source := by rw [sourceChart_source]; trivial
  have hc : sourceChart.symm x = v :=
    (congrArg sourceChart.symm he).symm.trans (sourceChart.left_inv hs)
  exact ⟨(congrArg sourceChart hc).trans he, hc.symm ▸ hv⟩

def northRemainderCoordinate (ε : ℝ) (hε : 0 < ε) (x : North) : Vector 3 :=
  sourceChart.symm (northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val)))

def southRemainderCoordinate (ε : ℝ) (hε : 0 < ε) (x : North) : Vector 3 :=
  sourceChart.symm (southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val)))

theorem northRemainderCoordinate_mem_ball (ε : ℝ) (hε : 0 < ε) (x : North) :
    northRemainderCoordinate ε hε x ∈ ball (0 : Vector 3) (ε * 4) :=
  (sourceCoordinate_of_removed (foldedNorthSource_mem_removed ε hε x)).2

theorem southRemainderCoordinate_mem_ball (ε : ℝ) (hε : 0 < ε) (x : North) :
    southRemainderCoordinate ε hε x ∈ ball (0 : Vector 3) (ε * 4) :=
  (sourceCoordinate_of_removed (foldedSouthSource_mem_removed ε hε x)).2

theorem sourceChart_northRemainderCoordinate (ε : ℝ) (hε : 0 < ε) (x : North) :
    sourceChart (northRemainderCoordinate ε hε x) =
      northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val)) :=
  (sourceCoordinate_of_removed (foldedNorthSource_mem_removed ε hε x)).1

theorem sourceChart_southRemainderCoordinate (ε : ℝ) (hε : 0 < ε) (x : North) :
    sourceChart (southRemainderCoordinate ε hε x) =
      southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val)) :=
  (sourceCoordinate_of_removed (foldedSouthSource_mem_removed ε hε x)).1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M)) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)

theorem remainderChartParameter_north (x : North) :
    (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG
      (northRetainedCap x.val)).val = (northRemainderCoordinate ε hε x, 0) := by
  have hs : (northRemainderCoordinate ε hε x, (0 : Vector 3)) ∈ Φ.source :=
    hprod ⟨ball_subset_closedBall (northRemainderCoordinate_mem_ball ε hε x),
      mem_closedBall_self (by positivity)⟩
  have he : Φ (northRemainderCoordinate ε hε x, 0) =
      F (northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val))) :=
    (hleft _ hs).trans (congrArg F (sourceChart_northRemainderCoordinate ε hε x))
  calc
    _ = Φ.symm (F (northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val)))) :=
      congrArg Φ.symm (remainderBasepoint_north Φ F G hε ha hprod hleft hright hF hG x)
    _ = _ := (congrArg Φ.symm he).symm.trans (Φ.left_inv hs)

theorem remainderChartParameter_south (x : North) :
    (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG
      (southRetainedCap x.val)).val = (0, southRemainderCoordinate ε hε x) := by
  have hs : ((0 : Vector 3), southRemainderCoordinate ε hε x) ∈ Φ.source :=
    hprod ⟨mem_closedBall_self (by positivity),
      ball_subset_closedBall (southRemainderCoordinate_mem_ball ε hε x)⟩
  have he : Φ (0, southRemainderCoordinate ε hε x) =
      G (southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val))) :=
    (hright _ hs).trans (congrArg G (sourceChart_southRemainderCoordinate ε hε x))
  calc
    _ = Φ.symm (G (southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val)))) :=
      congrArg Φ.symm (remainderBasepoint_south Φ F G hε ha hprod hleft hright hF hG x)
    _ = _ := (congrArg Φ.symm he).symm.trans (Φ.left_inv hs)

theorem remainderChartParameter_middle (x : Sphere 3)
    (hN : (northRetainedCap.symm x).val 0 ≤ 0)
    (hS : (southRetainedCap.symm x).val 0 ≤ 0) :
    (remainderChartParameter Φ F G hε ha hprod hleft hright hF hG x).val =
      ε • capPair a (SphereCylinder.inverse 2 x) := by
  have ht := neckRegion_time (between_retained_caps_mem_neckRegion x hN hS)
  have hs := hprod (scaled_capPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
    a (SphereCylinder.inverse 2 x) ⟨ht.1.le, ht.2.le⟩)
  exact (congrArg Φ.symm
    (remainderBasepoint_middle Φ F G hε ha hprod hleft hright hF hG x hN hS)).trans
      (Φ.left_inv hs)

end NoExoticSixSphere.SphereSumNeck
