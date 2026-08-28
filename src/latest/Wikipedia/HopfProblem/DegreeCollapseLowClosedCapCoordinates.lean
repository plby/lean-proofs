import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryPairParameters
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedZeroPoint
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarHomeomorph
import Wikipedia.SmoothSixDPoincare.PuncturedSurgeryModels

/-!

# Actual closed-cap parameters and their exact collar window

The scaled source disk crosses the unchanged handle and rounded collar.
The outer closed annulus maps into the actual collar parameter domain.
At its inner cut the graph is exactly the unchanged handle formula; at
the outer face it is the original tube at height zero.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

abbrev CapDomain (d : ℕ) :=
  UnitBall (Vector (d + 1)) × sphere (0 : Vector (7 - d)) 1

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

local instance : Fact (Module.finrank ℝ (Vector (d + 1)) = d + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def capDisk (p : CapDomain d) : Vector (d + 1) := oldRadius A • p.1.val

def capParameter (p : CapDomain d) : ℝ := ‖capDisk A p‖ ^ 2 - 1

def capCollar (p : CapDomain d) : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ :=
  let z := LowRoundedZeroPoint.point (bump A) 1 (p.2, capParameter A p)
  ((SphereRadialRetraction.retract (spherePole d) (capDisk A p), z.1), z.2)

theorem continuous_capDisk : Continuous (capDisk A) :=
  (continuous_subtype_val.comp continuous_fst).const_smul (oldRadius A)

theorem continuous_capParameter : Continuous (capParameter A) :=
  ((continuous_capDisk A).norm.pow 2).sub continuous_const

theorem capDisk_norm (p : CapDomain d) : ‖capDisk A p‖ = oldRadius A * ‖p.1.val‖ := by
  rw [capDisk, norm_smul, Real.norm_eq_abs, abs_of_pos (oldRadius_pos A)]

theorem capDisk_norm_le_old (p : CapDomain d) : ‖capDisk A p‖ ≤ oldRadius A := by
  rw [capDisk_norm]
  have h := mul_le_mul_of_nonneg_left p.1.property (oldRadius_pos A).le
  simpa only [mul_one] using h

theorem capParameter_mem_window (hR : A.radius = 2) (p : CapDomain d)
    (hp : cutRadius A ≤ ‖capDisk A p‖) :
    capParameter A p ∈ Ioo (-collarHeight A) (radialGap A) := by
  have hc := cutParameter_gt_neg_height A
  have ho := oldParameter_lt_gap A hR
  have hn := capDisk_norm_le_old A p
  change -collarHeight A < ‖capDisk A p‖ ^ 2 - 1 ∧
    ‖capDisk A p‖ ^ 2 - 1 < radialGap A
  constructor <;> nlinarith [norm_nonneg (capDisk A p), cutRadius_pos A, oldRadius_pos A]

theorem capCollar_norm (p : CapDomain d) :
    ‖(capCollar A p).1.2‖ = SmoothCornerRounding.graphRadius (bump A) 1 (capParameter A p) :=
  LowRoundedZeroPoint.norm_point (bump A) 1 (p.2, capParameter A p)

theorem capCollar_mem (hR : A.radius = 2) (p : CapDomain d)
    (hp : cutRadius A ≤ ‖capDisk A p‖) : capCollar A p ∈ collarParameters A := by
  have hw := (SmoothCornerRounding.graph_window_iff (bump A)
    (twice_outer_lt_height A) (twice_outer_lt_radialGap A)).mpr
      (capParameter_mem_window A hR p hp)
  have hg := SmoothCornerRounding.graphRadius_sq (bump A) 1 (capParameter A p)
  have hgap : radialGap A = A.radius ^ 2 - 1 := by
    rw [radialGap, handleRadius_eq_one A hR]
    norm_num
  refine ⟨?_, ⟨hw.1, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right, capCollar_norm]
    rw [hgap] at hw
    nlinarith [A.radius_pos,
      (SmoothCornerRounding.graphRadius_pos (bump A) (by norm_num : (0 : ℝ) < 1)
        (capParameter A p))]
  · exact (SmoothCornerRounding.graphHeight_nonpos (bump A) _).trans_lt
      (collarHeight_pos A)
  · change 0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)
      (LowRoundedZeroPoint.point (bump A) 1 (p.2, capParameter A p))
    rw [handleRadius_eq_one A hR, LowRoundedZeroPoint.level_point]

theorem continuousOn_capCollar :
    ContinuousOn (capCollar A) {p | cutRadius A ≤ ‖capDisk A p‖} := by
  intro p hp
  have hn : capDisk A p ≠ 0 := norm_pos_iff.mp ((cutRadius_pos A).trans_le hp)
  have hd := (SphereRadialRetraction.contMDiffAt_retract (n := d) (spherePole d) hn).continuousAt
  have hs := hd.comp (continuous_capDisk A).continuousAt
  have hz : Continuous (fun p : CapDomain d ↦
      LowRoundedZeroPoint.point (bump A) 1 (p.2, capParameter A p)) :=
    (LowRoundedZeroPoint.continuous_point (bump A) (by norm_num : (0 : ℝ) < 1)).comp
      (continuous_snd.prodMk (continuous_capParameter A))
  exact ((hs.prodMk hz.continuousAt.fst).prodMk hz.continuousAt.snd).continuousWithinAt

theorem capCollar_of_cut (p : CapDomain d) (hp : ‖capDisk A p‖ = cutRadius A) :
    capCollar A p =
      ((SphereRadialRetraction.retract (spherePole d) (capDisk A p), p.2.val),
        capParameter A p) := by
  have hu : capParameter A p ≤ -(bump A).rOut := by
    have hc := cutParameter_lt_neg_twice_outer A
    unfold capParameter
    rw [hp]
    linarith [(bump A).rOut_pos]
  simp only [capCollar,
    LowRoundedZeroPoint.point_of_left (bump A) (by norm_num : (0 : ℝ) < 1)
      (p.2, capParameter A p) hu,
    one_smul]

theorem capDisk_newBoundary (s : NoExoticSixSphere.Sphere d)
    (w : sphere (0 : Vector (7 - d)) 1) :
    capDisk A (newBoundary (s, w)) = oldRadius A • s.val := rfl

theorem capParameter_newBoundary (s : NoExoticSixSphere.Sphere d)
    (w : sphere (0 : Vector (7 - d)) 1) :
    capParameter A (newBoundary (s, w)) = (oldRadius A) ^ 2 - 1 := by
  rw [capParameter, capDisk_norm]
  change (oldRadius A * ‖s.val‖) ^ 2 - 1 = _
  rw [ClosedHemisphere.unit_norm, mul_one]

theorem capCollar_newBoundary (hR : A.radius = 2) (s : NoExoticSixSphere.Sphere d)
    (w : sphere (0 : Vector (7 - d)) 1) :
    capCollar A (newBoundary (s, w)) = ((s, oldRadius A • w.val), 0) := by
  have hu : (bump A).rOut ≤ capParameter A (newBoundary (s, w)) := by
    rw [capParameter_newBoundary]
    linarith [oldParameter_gt_twice_outer A hR, (bump A).rOut_pos]
  have hn : oldRadius A • s.val ≠ 0 :=
    smul_ne_zero (oldRadius_pos A).ne' (ne_zero_of_mem_unit_sphere s)
  have hs : SphereRadialRetraction.retract (spherePole d) (oldRadius A • s.val) = s := by
    apply Subtype.ext
    simp only [SphereRadialRetraction.retract, dif_neg hn]
    rw [NormedSpace.normalize_smul_of_pos (oldRadius_pos A),
      NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm s)]
  rw [capCollar, LowRoundedZeroPoint.point_of_right (bump A) 1
    ((newBoundary (s, w)).2, capParameter A (newBoundary (s, w))) hu]
  simp only [capDisk_newBoundary, hs, capParameter_newBoundary]
  have he : (1 : ℝ) ^ 2 + ((oldRadius A) ^ 2 - 1) = (oldRadius A) ^ 2 := by ring
  rw [he, Real.sqrt_sq (oldRadius_pos A).le]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
