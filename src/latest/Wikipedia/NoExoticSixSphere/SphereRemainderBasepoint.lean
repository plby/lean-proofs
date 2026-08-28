import Wikipedia.NoExoticSixSphere.SphereGluedFrameRemainder
import Wikipedia.NoExoticSixSphere.SphereRetainedCapImage

/-!
# A chart-contained basepoint map for the actual frame remainder

Perform the same two cap exchanges on the original manifold-valued maps.
The folded cap images lie on the two axis sheets in the removed chart disks,
and the middle lies in the retained neck chart. Thus the entire constructed
basepoint map lies in the image of the specified closed chart product.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction HemisphereExchange

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M)) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)

def remainderBasepoint : C(Sphere 3, M) :=
  twoCapRemainder (gluedSphereMap Φ F G hε ha hprod hleft hright hF hG)
    (F.comp (northCapHomeomorph ε hε : C(Sphere 3, Sphere 3)))
    (G.comp (southCapHomeomorph ε hε : C(Sphere 3, Sphere 3)))
    (fun x ↦ (gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ha hprod hleft x).eq_of_nhds)
    (fun x ↦ (gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ha hprod hright x).eq_of_nhds)

theorem remainderBasepoint_north (x : North) :
    remainderBasepoint Φ F G hε ha hprod hleft hright hF hG (northRetainedCap x.val) =
      F (northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val))) :=
  twoCapRemainder_north _ _ _ _ _ x

theorem remainderBasepoint_south (x : North) :
    remainderBasepoint Φ F G hε ha hprod hleft hright hF hG (southRetainedCap x.val) =
      G (southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val))) :=
  twoCapRemainder_south _ _ _ _ _ x

theorem remainderBasepoint_middle (x : Sphere 3)
    (hN : (northRetainedCap.symm x).val 0 ≤ 0)
    (hS : (southRetainedCap.symm x).val 0 ≤ 0) :
    remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x =
      Φ (ε • capPair a (SphereCylinder.inverse 2 x)) := by
  calc
    _ = gluedSphere Φ ε a F G x := twoCapRemainder_middle _ _ _ _ _ x hN hS
    _ = _ := gluedSphere_middle Φ F G (between_retained_caps_mem_neckRegion x hN hS)

theorem remainderBasepoint_mem_chartProduct_image (x : Sphere 3) :
    remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x ∈
      Φ '' (closedBall (0 : Vector 3) (ε * 4) ×ˢ closedBall (0 : Vector 3) (ε * 4)) := by
  by_cases hN : 0 ≤ (northRetainedCap.symm x).val 0
  · let y : North := ⟨northRetainedCap.symm x, (mem_north_iff _).mpr hN⟩
    have hy : northRetainedCap y.val = x := northRetainedCap.apply_symm_apply x
    rw [← hy, remainderBasepoint_north]
    obtain ⟨v, hv, he⟩ := foldedNorthSource_mem_removed ε hε y
    have hp : (v, (0 : Vector 3)) ∈
        closedBall (0 : Vector 3) (ε * 4) ×ˢ closedBall (0 : Vector 3) (ε * 4) :=
      ⟨ball_subset_closedBall hv, mem_closedBall_self (by positivity)⟩
    exact ⟨(v, 0), hp, (hleft v (hprod hp)).trans (congrArg F he)⟩
  · by_cases hS : 0 ≤ (southRetainedCap.symm x).val 0
    · let y : North := ⟨southRetainedCap.symm x, (mem_north_iff _).mpr hS⟩
      have hy : southRetainedCap y.val = x := southRetainedCap.apply_symm_apply x
      rw [← hy, remainderBasepoint_south]
      obtain ⟨v, hv, he⟩ := foldedSouthSource_mem_removed ε hε y
      have hp : ((0 : Vector 3), v) ∈
          closedBall (0 : Vector 3) (ε * 4) ×ˢ closedBall (0 : Vector 3) (ε * 4) :=
        ⟨mem_closedBall_self (by positivity), ball_subset_closedBall hv⟩
      exact ⟨(0, v), hp, (hright v (hprod hp)).trans (congrArg G he)⟩
    · have hn := between_retained_caps_mem_neckRegion x (le_of_not_ge hN) (le_of_not_ge hS)
      have ht := neckRegion_time hn
      rw [remainderBasepoint_middle Φ F G hε ha hprod hleft hright hF hG x
        (le_of_not_ge hN) (le_of_not_ge hS)]
      exact ⟨ε • capPair a (SphereCylinder.inverse 2 x),
        scaled_capPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
          a (SphereCylinder.inverse 2 x) ⟨ht.1.le, ht.2.le⟩, rfl⟩

theorem remainderBasepoint_mem_target (x : Sphere 3) :
    remainderBasepoint Φ F G hε ha hprod hleft hright hF hG x ∈ Φ.target := by
  obtain ⟨z, hz, he⟩ :=
    remainderBasepoint_mem_chartProduct_image Φ F G hε ha hprod hleft hright hF hG x
  rw [← he]
  exact Φ.map_source (hprod hz)

end NoExoticSixSphere.SphereSumNeck
