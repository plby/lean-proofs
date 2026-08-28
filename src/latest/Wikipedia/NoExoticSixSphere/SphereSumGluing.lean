import Wikipedia.NoExoticSixSphere.SphereSumSourceCover
import Wikipedia.NoExoticSixSphere.SphereSumCapCoordinates
import Wikipedia.NoExoticSixSphere.SphereSumCappedNeck

/-!
# A smooth neck-and-cap map on the original three-sphere

The three actual open source regions cover the original sphere, including
both poles. Exact linear tails identify the neck with the original sphere
maps on both overlaps. Gluing gives a globally smooth map in the original
source and target atlases, without assuming a glued smooth structure.

The immersion, homotopy-class, double-point, and frame-obstruction comparisons
are separate remaining requirements; they are not asserted here.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (ε a : ℝ) (F G : Sphere 3 → M)

def middlePiece (x : Sphere 3) : M := chartCapNeck Φ ε (a, SphereCylinder.inverse 2 x)

def northPiece (x : Sphere 3) : M := F (sphereCap ε x)

def southPiece (x : Sphere 3) : M := G (sphereCap ε (reflectHead x))

def gluedSphere (x : Sphere 3) : M := by
  classical
  exact if x ∈ neckRegion then middlePiece Φ ε a x
    else if x ∈ northRegion then northPiece ε F x else southPiece ε G x

variable {ε a} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))

include hε ha hprod hleft in
theorem middlePiece_eq_north {x : Sphere 3} (hb : x ∈ neckRegion) (hn : x ∈ northRegion) :
    middlePiece Φ ε a x = northPiece ε F x := by
  let q := SphereCylinder.inverse 2 x
  have hband := neckRegion_mem_band hb
  have htime : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hb
  have ht : 2 < q.1 := northRegion_time hn hband
  have hs := hprod (scaled_capPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
    a q ⟨htime.1.le, htime.2.le⟩)
  have he : ε • capPair a q = ((ε * q.1) • q.2.val, 0) := by
    rw [show capPair a q = _ from capPair_right a ha q.1 q.2 ht.le]
    simp [smul_smul]
  rw [he] at hs
  have hcap := sphereCap_cylinder hε q.1 q.2 (by linarith : 0 < q.1)
  rw [SphereCylinder.point_inverse 2 x hband] at hcap
  change Φ (ε • capPair a q) = F (sphereCap ε x)
  rw [he, hleft _ hs, hcap]

include hε ha hprod hright in
theorem middlePiece_eq_south {x : Sphere 3} (hb : x ∈ neckRegion) (hn : x ∈ southRegion) :
    middlePiece Φ ε a x = southPiece ε G x := by
  let q := SphereCylinder.inverse 2 x
  have hband := neckRegion_mem_band hb
  have htime : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hb
  have ht : q.1 < -2 := southRegion_time hn hband
  have hs := hprod (scaled_capPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
    a q ⟨htime.1.le, htime.2.le⟩)
  have he : ε • capPair a q = (0, (ε * (-q.1)) • q.2.val) := by
    rw [show capPair a q = _ from capPair_left a ha q.1 q.2 ht.le]
    simp [smul_smul]
  rw [he] at hs
  have href : reflectHead x = SphereCylinder.point 2 (-q.1, q.2) := by
    have h := reflectHead_cylinder q.1 q.2
    rw [SphereCylinder.point_inverse 2 x hband] at h
    exact h
  have hcap : sphereCap ε (reflectHead x) = sourceChart ((ε * (-q.1)) • q.2.val) := by
    rw [href]
    exact sphereCap_cylinder hε (-q.1) q.2 (by linarith)
  change Φ (ε • capPair a q) = G (sphereCap ε (reflectHead x))
  rw [he, hright _ hs, hcap]

theorem gluedSphere_middle {x : Sphere 3} (hx : x ∈ neckRegion) :
    gluedSphere Φ ε a F G x = middlePiece Φ ε a x := by
  simp only [gluedSphere, if_pos hx]

include hε ha hprod hleft in
theorem gluedSphere_north {x : Sphere 3} (hx : x ∈ northRegion) :
    gluedSphere Φ ε a F G x = northPiece ε F x := by
  by_cases hb : x ∈ neckRegion
  · exact (gluedSphere_middle Φ F G hb).trans (middlePiece_eq_north Φ F hε ha hprod hleft hb hx)
  · simp only [gluedSphere, if_neg hb, if_pos hx]

include hε ha hprod hright in
theorem gluedSphere_south {x : Sphere 3} (hx : x ∈ southRegion) :
    gluedSphere Φ ε a F G x = southPiece ε G x := by
  by_cases hb : x ∈ neckRegion
  · exact (gluedSphere_middle Φ F G hb).trans (middlePiece_eq_south Φ G hε ha hprod hright hb hx)
  · have hn : x ∉ northRegion := fun hn ↦
      (not_lt_of_gt (northRegion_head_pos hn)) (southRegion_head_neg hx)
    simp only [gluedSphere, if_neg hb, if_neg hn]

include hε hprod in
theorem contMDiffAt_middlePiece {x : Sphere 3} (hx : x ∈ neckRegion) :
    ContMDiffAt (𝓡 3) (𝓡 6) ∞ (middlePiece Φ ε a) x := by
  have ht := neckRegion_time hx
  have hp : ContMDiffAt (𝓡 3) OpeningModel ∞
      (fun y : Sphere 3 ↦ (a, SphereCylinder.inverse 2 y)) x :=
    contMDiffAt_const.prodMk (SphereCylinder.contMDiffAt_inverse 2 (neckRegion_mem_band hx))
  exact (contMDiffAt_chartCapNeck Φ hε (by norm_num : (1 : ℝ) ≤ 4) hprod
    (a, SphereCylinder.inverse 2 x) ⟨ht.1.le, ht.2.le⟩).comp x hp

include hε in
theorem contMDiffAt_northPiece (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    {x : Sphere 3} (hx : x ∈ northRegion) :
    ContMDiffAt (𝓡 3) (𝓡 6) ∞ (northPiece ε F) x :=
  (hF _).comp x (contMDiffAt_sphereCap hε.ne' (northRegion_head_pos hx))

include hε in
theorem contMDiffAt_southPiece (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    {x : Sphere 3} (hx : x ∈ southRegion) :
    ContMDiffAt (𝓡 3) (𝓡 6) ∞ (southPiece ε G) x := by
  have hp : 0 < (reflectHead x).val 0 := by
    rw [reflectHead_head]
    exact neg_pos.mpr (southRegion_head_neg hx)
  exact (hG _).comp x ((contMDiffAt_sphereCap hε.ne' hp).comp x (contMDiff_reflectHead x))

include hε ha hprod hleft hright in
theorem contMDiff_gluedSphere (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) :
    ContMDiff (𝓡 3) (𝓡 6) ∞ (gluedSphere Φ ε a F G) := by
  intro x
  rcases sourceRegion_cover x with hb | hn | hs
  · have he : gluedSphere Φ ε a F G =ᶠ[𝓝 x] middlePiece Φ ε a := by
      filter_upwards [isOpen_neckRegion.mem_nhds hb] with y hy
      exact gluedSphere_middle Φ F G hy
    exact (contMDiffAt_middlePiece Φ hε hprod hb).congr_of_eventuallyEq he
  · have he : gluedSphere Φ ε a F G =ᶠ[𝓝 x] northPiece ε F := by
      filter_upwards [isOpen_northRegion.mem_nhds hn] with y hy
      exact gluedSphere_north Φ F G hε ha hprod hleft hy
    exact (contMDiffAt_northPiece F hε hF hn).congr_of_eventuallyEq he
  · have he : gluedSphere Φ ε a F G =ᶠ[𝓝 x] southPiece ε G := by
      filter_upwards [isOpen_southRegion.mem_nhds hs] with y hy
      exact gluedSphere_south Φ F G hε ha hprod hright hy
    exact (contMDiffAt_southPiece G hε hG hs).congr_of_eventuallyEq he

def gluedSphereMap (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) : C(Sphere 3, M) :=
  ⟨gluedSphere Φ ε a F G, (contMDiff_gluedSphere Φ F G hε ha hprod hleft hright hF hG).continuous⟩

end NoExoticSixSphere.SphereSumNeck
