import Wikipedia.NoExoticSixSphere.SphereCollapsedProfileHomotopy
import Wikipedia.NoExoticSixSphere.SphereSourceFamilyGluing
import Wikipedia.NoExoticSixSphere.SphereSumOpeningHomotopy

/-!
# A whole-sphere homotopy from the collapsed neck to a linear collapse

The three actual source regions are fixed during the homotopy. The caps
are unchanged, and exact linear tails give agreement on both overlaps.
The family remains in the original target chart on its middle region.
This identifies the immersed resolution with a simpler linear collapsed
map, without yet asserting a sphere-addition convention.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) (ε : ℝ)

def linearizingMiddle (p : unitInterval × Sphere 3) : M :=
  Φ (ε • linearizingPair (p.1, SphereCylinder.inverse 2 p.2))

def sphereLinearization : unitInterval × Sphere 3 → M :=
  sourceFamilyGlue (linearizingMiddle Φ ε)
    (fun p ↦ northPiece ε F p.2) (fun p ↦ southPiece ε G p.2)

def linearSphere (x : Sphere 3) : M := by
  classical
  exact if x ∈ neckRegion then Φ (ε • linearPair (SphereCylinder.inverse 2 x))
    else if x ∈ northRegion then northPiece ε F x else southPiece ε G x

theorem sphereLinearization_zero (x : Sphere 3) :
    sphereLinearization Φ F G ε (0, x) = gluedSphere Φ ε 0 F G x := by
  simp only [sphereLinearization, sourceFamilyGlue, linearizingMiddle, linearizingPair_zero,
    gluedSphere, middlePiece, chartCapNeck]

theorem sphereLinearization_one (x : Sphere 3) :
    sphereLinearization Φ F G ε (1, x) = linearSphere Φ F G ε x := by
  simp only [sphereLinearization, sourceFamilyGlue, linearizingMiddle, linearizingPair_one,
    linearSphere]

variable {ε} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))

include hε hprod in
theorem continuousAt_linearizingMiddle (p : unitInterval × Sphere 3)
    (hb : p.2 ∈ neckRegion) : ContinuousAt (linearizingMiddle Φ ε) p := by
  have ht := neckRegion_time hb
  have hp : ContinuousAt (fun w : unitInterval × Sphere 3 ↦
      (w.1, SphereCylinder.inverse 2 w.2)) p :=
    continuous_fst.continuousAt.prodMk
      ((SphereCylinder.contMDiffAt_inverse 2 (neckRegion_mem_band hb)).continuousAt.comp
        continuous_snd.continuousAt)
  have hεc : Continuous (fun _ : unitInterval × Parameter ↦ ε) := continuous_const
  have hc : Continuous (fun w : unitInterval × Parameter ↦ ε • linearizingPair w) :=
    hεc.smul continuous_linearizingPair
  have hv : ContinuousAt (fun w : unitInterval × Sphere 3 ↦
      ε • linearizingPair (w.1, SphereCylinder.inverse 2 w.2)) p :=
    hc.continuousAt.comp
      (f := fun w : unitInterval × Sphere 3 ↦ (w.1, SphereCylinder.inverse 2 w.2)) hp
  have hsource := hprod (scaled_linearizingPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
    p.1 (SphereCylinder.inverse 2 p.2) ⟨ht.1.le, ht.2.le⟩)
  have hΦ : ContinuousAt Φ (ε • linearizingPair (p.1, SphereCylinder.inverse 2 p.2)) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hsource)).continuousAt
  exact hΦ.comp
    (f := fun w : unitInterval × Sphere 3 ↦ ε • linearizingPair (w.1,
      SphereCylinder.inverse 2 w.2)) hv

include hε hprod hleft in
theorem linearizingMiddle_eq_north (p : unitInterval × Sphere 3)
    (hb : p.2 ∈ neckRegion) (hn : p.2 ∈ northRegion) :
    linearizingMiddle Φ ε p = northPiece ε F p.2 := by
  let q := SphereCylinder.inverse 2 p.2
  have hband := neckRegion_mem_band hb
  have htime : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hb
  have ht : 2 < q.1 := northRegion_time hn hband
  have hs := hprod (scaled_linearizingPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
    p.1 q ⟨htime.1.le, htime.2.le⟩)
  have he : ε • linearizingPair (p.1, q) = ((ε * q.1) • q.2.val, 0) := by
    rw [linearizingPair_right p.1 q ht.le]
    simp [smul_smul]
  rw [he] at hs
  have hcap := sphereCap_cylinder hε q.1 q.2 (by linarith : 0 < q.1)
  rw [SphereCylinder.point_inverse 2 p.2 hband] at hcap
  change Φ (ε • linearizingPair (p.1, q)) = F (sphereCap ε p.2)
  rw [he, hleft _ hs, hcap]

include hε hprod hright in
theorem linearizingMiddle_eq_south (p : unitInterval × Sphere 3)
    (hb : p.2 ∈ neckRegion) (hn : p.2 ∈ southRegion) :
    linearizingMiddle Φ ε p = southPiece ε G p.2 := by
  let q := SphereCylinder.inverse 2 p.2
  have hband := neckRegion_mem_band hb
  have htime : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hb
  have ht : q.1 < -2 := southRegion_time hn hband
  have hs := hprod (scaled_linearizingPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
    p.1 q ⟨htime.1.le, htime.2.le⟩)
  have he : ε • linearizingPair (p.1, q) = (0, (ε * (-q.1)) • q.2.val) := by
    rw [linearizingPair_left p.1 q ht.le]
    simp [smul_smul]
  rw [he] at hs
  have href : reflectHead p.2 = SphereCylinder.point 2 (-q.1, q.2) := by
    have h := reflectHead_cylinder q.1 q.2
    rw [SphereCylinder.point_inverse 2 p.2 hband] at h
    exact h
  have hcap : sphereCap ε (reflectHead p.2) = sourceChart ((ε * (-q.1)) • q.2.val) := by
    rw [href]
    exact sphereCap_cylinder hε (-q.1) q.2 (by linarith)
  change Φ (ε • linearizingPair (p.1, q)) = G (sphereCap ε (reflectHead p.2))
  rw [he, hright _ hs, hcap]

include hε hprod hleft hright in
theorem continuous_sphereLinearization (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) : Continuous (sphereLinearization Φ F G ε) := by
  apply continuous_sourceFamilyGlue
  · exact continuousAt_linearizingMiddle Φ hε hprod
  · intro p hp
    exact (contMDiffAt_northPiece F hε hF hp).continuousAt.comp continuous_snd.continuousAt
  · intro p hp
    exact (contMDiffAt_southPiece G hε hG hp).continuousAt.comp continuous_snd.continuousAt
  · exact linearizingMiddle_eq_north Φ F hε hprod hleft
  · exact linearizingMiddle_eq_south Φ G hε hprod hright

def linearSphereMap (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) : C(Sphere 3, M) := by
  have hc : Continuous (fun x : Sphere 3 ↦ sphereLinearization Φ F G ε (1, x)) :=
    (continuous_sphereLinearization Φ F G hε hprod hleft hright hF hG).comp
      (continuous_const.prodMk continuous_id)
  refine ⟨linearSphere Φ F G ε, ?_⟩
  simpa only [sphereLinearization_one] using hc

def collapsedLinearizingHomotopy (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) :
    (gluedSphereMap Φ F G hε (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      hprod hleft hright hF hG).Homotopy
    (linearSphereMap Φ F G hε hprod hleft hright hF hG) where
  toFun := sphereLinearization Φ F G ε
  continuous_toFun := continuous_sphereLinearization Φ F G hε hprod hleft hright hF hG
  map_zero_left := sphereLinearization_zero Φ F G ε
  map_one_left := sphereLinearization_one Φ F G ε

def immersedToLinearHomotopy (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) :
    (gluedSphereMap Φ F G hε (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      hprod hleft hright hF hG).Homotopy
    (linearSphereMap Φ F G hε hprod hleft hright hF hG) :=
  (gluedOpeningHomotopy Φ F G hε hprod hleft hright hF hG).symm.trans
    (collapsedLinearizingHomotopy Φ F G hε hprod hleft hright hF hG)

end NoExoticSixSphere.SphereSumNeck
