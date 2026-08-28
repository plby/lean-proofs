import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryOldPiece

/-!

# The new cap and common exterior have exactly the prescribed common face

An inner handle point cannot lie at cylinder height zero. On the outer
annulus, equality with a height-zero exterior point makes the transverse
radius equal the scaled source radius. The exterior inequality and the
closed-disk bound then force the original source point onto its unit sphere.
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

theorem capInner_ne_bottom (hR : A.radius = 2) (p : CapDomain d)
    (hp : ‖capDisk A p‖ ≤ cutRadius A) (m : M) :
    capInner A p ≠ LowHeightCylinder.heightCylinder d e (m, 0) := by
  intro h
  obtain ⟨s, hs, _, _⟩ := (UnroundedTrace.intersection_iff A (capDisk_mem_inner A p hp)
    (capTransverse_mem A hR p) m ⟨le_rfl, (UnroundedTrace.height_pos A).le⟩).mp h
  have hn := hp.trans_lt (cutRadius_lt_one A)
  rw [← hs, ClosedHemisphere.unit_norm] at hn
  exact (lt_irrefl 1) hn

theorem capOuter_eq_exterior_imp_norm_one (hR : A.radius = 2) (p : CapDomain d)
    (hp : cutRadius A ≤ ‖capDisk A p‖) (r : closedExterior A)
    (h : capOuter A p = LowHeightCylinder.heightCylinder d e (r.val, 0)) :
    ‖p.1.val‖ = 1 := by
  have hc : (A.tube (capCollar A p).1, (capCollar A p).2) = (r.val, 0) :=
    (LowHeightCylinder.injective_heightCylinder d e) h
  have ht : (capCollar A p).2 = 0 := congrArg Prod.snd hc
  have hm : A.tube (capCollar A p).1 = r.val := congrArg Prod.fst hc
  have hr : A.tube (capCollar A p).1 ∈ closedExterior A := hm.symm ▸ r.property
  have hv := (tube_mem_closedExterior_iff A (capCollar A p).1.1
    (capCollar_mem A hR p hp).1).mp hr
  have hd : (capCollar A p).2 - ((1 : ℝ) ^ 2 - ‖(capCollar A p).1.2‖ ^ 2) =
      capParameter A p :=
    LowRoundedZeroPoint.point_difference (bump A) 1 (p.2, capParameter A p)
  rw [ht] at hd
  unfold capParameter at hd
  have hnv : ‖(capCollar A p).1.2‖ = ‖capDisk A p‖ := by
    nlinarith [norm_nonneg (capCollar A p).1.2, norm_nonneg (capDisk A p)]
  rw [hnv] at hv
  have hn := le_antisymm (capDisk_norm_le_old A p) hv
  rw [capDisk_norm] at hn
  nlinarith [oldRadius_pos A]

variable [IsManifold (𝓡 7) ∞ M]

theorem nativeCapPoint_eq_exterior_imp_norm_one (hR : A.radius = 2)
    (p : CapDomain d) (r : closedExterior A)
    (h : nativeCapPoint A hR p = newExterior A r) : ‖p.1.val‖ = 1 := by
  have he := congrArg (fun y : otherBoundaryPart A ↦ y.val.val.val) h
  rw [nativeCapPoint_ambient, newExterior_ambient] at he
  by_cases hp : ‖capDisk A p‖ ≤ cutRadius A
  · rw [capPoint_of_inner A p hp] at he
    exact False.elim (capInner_ne_bottom A hR p hp r.val he)
  · rw [capPoint_of_outer A hR p (lt_of_not_ge hp).le] at he
    exact capOuter_eq_exterior_imp_norm_one A hR p (lt_of_not_ge hp).le r he

theorem new_overlap (hR : A.radius = 2) (r : closedExterior A) (p : CapDomain d) :
    newExterior A r = nativeCapPoint A hR p ↔
      ∃ q : NoExoticSixSphere.Sphere d × sphere (0 : Vector (7 - d)) 1,
        r = commonFace A q ∧ p = newBoundary q := by
  constructor
  · intro h
    have hn := nativeCapPoint_eq_exterior_imp_norm_one A hR p r h.symm
    let s : NoExoticSixSphere.Sphere d := ⟨p.1.val, mem_sphere_zero_iff_norm.mpr hn⟩
    refine ⟨(s, p.2), ?_, rfl⟩
    apply newExterior_injective A
    exact h.trans (newExterior_commonFace A hR (s, p.2)).symm
  · rintro ⟨q, rfl, rfl⟩
    exact newExterior_commonFace A hR q

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
