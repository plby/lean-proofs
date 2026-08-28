import Wikipedia.HopfProblem.DegreeCollapseLowClosedCapMap

/-!

# The actual replacement cap is closed embedded

Both pieces are injective. A coincidence between the inner handle and the
outer collar forces the handle point outside the compact inner image, where
the actual tube coordinates apply. The difference coordinate and unit
transverse vector then recover the original cap parameter.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

theorem cap_eq_of_disk_transverse {p q : CapDomain d}
    (hx : capDisk A p = capDisk A q) (hw : p.2 = q.2) : p = q := by
  apply Prod.ext _ hw
  apply Subtype.ext
  exact (smul_right_injective _ (oldRadius_pos A).ne') hx

theorem capCollar_injective_of_ne_zero {p q : CapDomain d}
    (hp : capDisk A p ≠ 0) (hq : capDisk A q ≠ 0)
    (h : capCollar A p = capCollar A q) : p = q := by
  have hz := congrArg
    (fun z : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ ↦ (z.1.2, z.2)) h
  change LowRoundedZeroPoint.point (bump A) 1 (p.2, capParameter A p) =
    LowRoundedZeroPoint.point (bump A) 1 (q.2, capParameter A q) at hz
  have hpar := LowRoundedZeroPoint.point_injective (bump A)
    (by norm_num : (0 : ℝ) < 1) hz
  have hs := congrArg
    (fun z : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ ↦ z.1.1) h
  have ht : capParameter A p = capParameter A q := congrArg Prod.snd hpar
  have hc : LowRadialHeightCoordinates.inverse (spherePole d) (capDisk A p) =
      LowRadialHeightCoordinates.inverse (spherePole d) (capDisk A q) :=
    Prod.ext hs ht
  have hx := ((LowRadialHeightCoordinates.point_inverse (spherePole d) hp).symm.trans
    (congrArg LowRadialHeightCoordinates.point hc)).trans
      (LowRadialHeightCoordinates.point_inverse (spherePole d) hq)
  exact cap_eq_of_disk_transverse A hx (congrArg Prod.fst hpar)

theorem capInner_injective (hR : A.radius = 2) {p q : CapDomain d}
    (hp : ‖capDisk A p‖ ≤ cutRadius A) (hq : ‖capDisk A q‖ ≤ cutRadius A)
    (h : capInner A p = capInner A q) : p = q := by
  let p' : closedBall (0 : Vector (d + 1)) 1 ×
      closedBall (0 : Vector (7 - d)) A.radius :=
    (⟨capDisk A p, capDisk_mem_inner A p hp⟩, ⟨p.2.val, capTransverse_mem A hR p⟩)
  let q' : closedBall (0 : Vector (d + 1)) 1 ×
      closedBall (0 : Vector (7 - d)) A.radius :=
    (⟨capDisk A q, capDisk_mem_inner A q hq⟩, ⟨q.2.val, capTransverse_mem A hR q⟩)
  have he : p' = q' := A.embedded.injective h
  apply cap_eq_of_disk_transverse A
  · exact congrArg
      (fun z : closedBall (0 : Vector (d + 1)) 1 ×
        closedBall (0 : Vector (7 - d)) A.radius ↦ z.1.val) he
  · apply Subtype.ext
    exact congrArg
      (fun z : closedBall (0 : Vector (d + 1)) 1 ×
        closedBall (0 : Vector (7 - d)) A.radius ↦ z.2.val) he

theorem capCollar_of_inner (p : CapDomain d) (hp : ‖capDisk A p‖ ≤ cutRadius A) :
    capCollar A p =
      ((SphereRadialRetraction.retract (spherePole d) (capDisk A p), p.2.val),
        capParameter A p) := by
  have hu : capParameter A p ≤ -(bump A).rOut := by
    have hc := cutParameter_lt_neg_twice_outer A
    unfold capParameter
    nlinarith [cutRadius_pos A, norm_nonneg (capDisk A p), (bump A).rOut_pos]
  simp only [capCollar,
    LowRoundedZeroPoint.point_of_left (bump A) (by norm_num : (0 : ℝ) < 1)
      (p.2, capParameter A p) hu, one_smul]

theorem capOuter_injective (hR : A.radius = 2) {p q : CapDomain d}
    (hp : cutRadius A ≤ ‖capDisk A p‖) (hq : cutRadius A ≤ ‖capDisk A q‖)
    (h : capOuter A p = capOuter A q) : p = q :=
  capCollar_injective_of_ne_zero A
    (norm_pos_iff.mp ((cutRadius_pos A).trans_le hp))
    (norm_pos_iff.mp ((cutRadius_pos A).trans_le hq))
    (A.injOn_collarSheet
      (collarParameters_subset_source A (capCollar_mem A hR p hp))
      (collarParameters_subset_source A (capCollar_mem A hR q hq)) h)

theorem capInner_eq_outer_imp_eq (hR : A.radius = 2) {p q : CapDomain d}
    (hp : ‖capDisk A p‖ ≤ cutRadius A) (hq : cutRadius A ≤ ‖capDisk A q‖)
    (h : capInner A p = capOuter A q) : p = q := by
  have hqm := capCollar_mem A hR q hq
  have havoid := sheet_band_avoids_inner A (capCollar A q).1.1 hqm.1
    (collarParameter_time A ⟨capCollar A q, hqm⟩)
  have hi : A.innerRadius ≤ ‖capDisk A p‖ := by
    by_contra hn
    apply havoid
    refine ⟨(capDisk A p, p.2.val), ⟨?_, ?_⟩, h⟩
    · simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge hn).le
    · rw [handleRadius_eq_one A hR]
      exact sphere_subset_closedBall p.2.property
  have hs : capCollar A p ∈ A.tubeHeightCoordinates.source := by
    apply (A.mem_tubeHeightCoordinates_source _).mpr
    rw [capCollar_of_inner A p hp]
    change p.2.val ∈ ball (0 : Vector (7 - d)) A.radius
    rw [mem_ball, dist_zero_right, mem_sphere_zero_iff_norm.mp p.2.property, hR]
    norm_num
  have he : capInner A p = capOuter A p := by
    rw [capOuter, capCollar_of_inner A p hp]
    exact A.map_eq_cylinder_collarCoordinates (capDisk_mem_inner A p hp) hi
      (capTransverse_mem A hR p)
  exact capCollar_injective_of_ne_zero A
    (norm_pos_iff.mp (A.innerRadius_pos.trans_le hi))
    (norm_pos_iff.mp ((cutRadius_pos A).trans_le hq))
    (A.injOn_collarSheet hs (collarParameters_subset_source A hqm) (he.symm.trans h))

theorem capPoint_injective (hR : A.radius = 2) : Injective (capPoint A) := by
  intro p q h
  by_cases hp : ‖capDisk A p‖ ≤ cutRadius A
  · by_cases hq : ‖capDisk A q‖ ≤ cutRadius A
    · rw [capPoint_of_inner A p hp, capPoint_of_inner A q hq] at h
      exact capInner_injective A hR hp hq h
    · rw [capPoint_of_inner A p hp,
        capPoint_of_outer A hR q (lt_of_not_ge hq).le] at h
      exact capInner_eq_outer_imp_eq A hR hp (lt_of_not_ge hq).le h
  · by_cases hq : ‖capDisk A q‖ ≤ cutRadius A
    · rw [capPoint_of_outer A hR p (lt_of_not_ge hp).le,
        capPoint_of_inner A q hq] at h
      exact (capInner_eq_outer_imp_eq A hR hq (lt_of_not_ge hp).le h.symm).symm
    · rw [capPoint_of_outer A hR p (lt_of_not_ge hp).le,
        capPoint_of_outer A hR q (lt_of_not_ge hq).le] at h
      exact capOuter_injective A hR (lt_of_not_ge hp).le (lt_of_not_ge hq).le h

theorem compactSpace_unitBall (n : ℕ) : CompactSpace (UnitBall (Vector n)) := by
  have hB : IsCompact {x : Vector n | ‖x‖ ≤ 1} := by
    have hs : {x : Vector n | ‖x‖ ≤ 1} = closedBall (0 : Vector n) 1 := by
      ext x
      simp only [mem_ofPred_eq, mem_closedBall, dist_zero_right]
    rw [hs]
    exact isCompact_closedBall _ _
  exact isCompact_iff_compactSpace.mp hB

theorem compactSpace_capDomain (d : ℕ) : CompactSpace (CapDomain d) := by
  let := compactSpace_unitBall (d + 1)
  infer_instance

theorem isClosedEmbedding_capPoint (hR : A.radius = 2) : IsClosedEmbedding (capPoint A) := by
  let := compactSpace_capDomain d
  exact (continuous_capPoint A hR).isClosedEmbedding (capPoint_injective A hR)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
