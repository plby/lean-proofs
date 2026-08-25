import StackExchange.Puzzling139335.CentralRotation.InitialPlacement
import StackExchange.Puzzling139335.CentralRotation.FirstOverlap
import StackExchange.Puzzling139335.CentralRotation.LiftPropagation
import StackExchange.Puzzling139335.CentralRotation.RotationAlgebra
import StackExchange.Puzzling139335.QuarterTurnTopology.Iterates

/-!
# The boundary-orbit argument in compatible lifted coordinates

Every orbit containment, finite-termination step, reversed-overlap conclusion,
and affine center identity is proved here.  The only coordinate hypotheses
are the explicit circle traces and actual increasing real lifts.  The
geometric wrapper constructs those lifts from the two Jordan sides.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation

/-- Assembly of the rotation argument from compatible boundary coordinates
and their actual increasing real lifts.  No orbit or half-turn conclusion
is included among the hypotheses. -/
theorem center_mem_of_boundaryLifts {M Γ N : Set Plane}
    (d : BoundaryCoordinates M Γ N) (g : Plane ≃ᵃⁱ[ℝ] Plane) (c : Plane)
    (L : BoundaryLifts d g (AffineIsometryEquiv.pointReflection ℝ c))
    (a : Circle) (b : ℂ)
    (hg : ∀ x, PlaneIsometries.complexEquiv (g x) =
      (a : ℂ) * PlaneIsometries.complexEquiv x + b)
    (hnot : ∀ z, g ≠ AffineIsometryEquiv.pointReflection ℝ z)
    (hboundary : g '' (M ∪ Γ) = N ∪ Γ)
    (houter : AffineIsometryEquiv.pointReflection ℝ c '' M = N) : c ∈ Γ := by
  let h := AffineIsometryEquiv.pointReflection ℝ c
  let F : Plane ≃ᵃⁱ[ℝ] Plane := g.symm.trans h
  let p := circleParam d.leftParam (1 / 2)
  let q := circleParam d.leftParam 1
  let Jopen : Set Plane := g '' (Γ \ {p, q})
  have hF (x : Plane) : F x = AffineIsometryEquiv.pointReflection ℝ c (g.symm x) := rfl
  obtain ⟨hI, hJ⟩ := L.cut_images_subset_outer a b hg hnot
  have hfirst : F '' Γ ⊆ N := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hF]
    exact houter.subset (mem_image_of_mem h (hI (mem_image_of_mem g.symm hx)))
  have hgap : F '' (N \ Jopen) = N \ F '' (Γ \ {p, q}) :=
    GapIdentity.image_gap_of_boundary_intersections g.toHomeomorph h.toHomeomorph F.toHomeomorph
      d.leftCutPair.inter_eq d.rightCutPair.inter_eq hboundary houter hF
  have hJopen : Jopen = (g '' Γ) \ {g p, g q} := by
    dsimp only [Jopen]
    rw [image_sdiff g.injective, image_pair]
  have hgap' : F '' (N \ ((g '' Γ) \ {g p, g q})) = N \ F '' (Γ \ {p, q}) := by
    rwa [hJopen] at hgap
  obtain ⟨m, hm, hprefix, hmeet, havoid⟩ :=
    FirstOverlap.exists_first_overlap_of_image_gap d.rightCutPair.snd d.leftCutPair.fst
      (d.leftCutPair.fst.image_homeomorph g.toHomeomorph) hJ F.isometry hfirst hgap'
  change ((((F : Plane → Plane)^[m]) '' (Γ \ {p, q})) ∩
    ((g '' Γ) \ {g p, g q})).Nonempty at hmeet
  change ∀ k : ℕ, 1 ≤ k → k < m →
    Disjoint (((F : Plane → Plane)^[k]) '' (Γ \ {p, q})) ((g '' Γ) \ {g p, g q}) at havoid
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hbefore : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ((F : Plane → Plane)^[k]) '' Γ ⊆ N \ Jopen := by
    intro k hk hkn
    have hkarc := d.leftCutPair.fst.image_homeomorph (F ^ k).toHomeomorph
    change IsArcBetween ((F ^ k) '' Γ) ((F ^ k) p) ((F ^ k) q) at hkarc
    rw [QuarterTurnTopology.affineIsometry_coe_pow] at hkarc
    have hdisrel : Disjoint
        ((((F : Plane → Plane)^[k]) '' Γ) \
          {((F : Plane → Plane)^[k]) p, ((F : Plane → Plane)^[k]) q})
        ((g '' Γ) \ {g p, g q}) := by
      simpa only [image_sdiff (F.injective.iterate k), image_pair] using havoid k hk (by omega)
    have hdis := FirstOverlap.disjoint_of_disjoint_arc_interiors d.rightCutPair.snd
      (d.leftCutPair.fst.image_homeomorph g.toHomeomorph) hkarc hJ
      (hprefix k hk (by omega)) hdisrel
    intro x hx
    refine ⟨hprefix k hk (by omega) hx, ?_⟩
    rw [hJopen]
    exact disjoint_left.mp hdis hx
  have hpreimage : g.symm '' (N \ Jopen) ⊆ M := d.preimage_outer_gap_subset g hboundary
  let K : Plane ≃ᵃⁱ[ℝ] Plane := g.symm.trans (F ^ (n + 1))
  have hK (x : Plane) : K x = ((F : Plane → Plane)^[n + 1]) (g.symm x) := by
    change (F ^ (n + 1)) (g.symm x) = _
    exact congrFun (QuarterTurnTopology.affineIsometry_coe_pow F (n + 1)) _
  have hKimage (S : Set Plane) : K '' (g '' S) = ((F : Plane → Plane)^[n + 1]) '' S := by
    rw [← image_comp]
    have hcomp : (K ∘ g : Plane → Plane) = (F : Plane → Plane)^[n + 1] := by
      funext x
      simp only [Function.comp_apply, hK, g.symm_apply_apply]
    rw [hcomp]
  let r : Circle := -a⁻¹
  let vF : ℂ := 2 * PlaneIsometries.complexEquiv c + (a : ℂ)⁻¹ * b
  have hFform (x : Plane) : PlaneIsometries.complexEquiv (F x) =
      (r : ℂ) * PlaneIsometries.complexEquiv x + vF :=
    RotationAlgebra.direct_form_reflection_comp_inverse F g c a b hg hF x
  have hKform (x : Plane) : PlaneIsometries.complexEquiv (K x) =
      ((-(r ^ (n + 1 + 1)) : Circle) : ℂ) * PlaneIsometries.complexEquiv x +
        PlaneIsometries.complexEquiv (K 0) := by
    have hdiff := RotationAlgebra.overlap_map_coordinate_sub F g c r vF hFform hF (n + 1) x 0
    rw [← hK x, ← hK 0, map_zero PlaneIsometries.complexEquiv, sub_zero] at hdiff
    simpa only [Circle.coe_neg, Circle.coe_pow] using eq_add_of_sub_eq hdiff
  have hKsub : K '' (circleParam d.outerParam '' Icc (L.G (1 / 2)) (L.G 1)) ⊆
      range d.outerParam := by
    rw [← L.image_cut_interval hJ, hKimage]
    exact (hprefix (n + 1) (by omega) le_rfl).trans d.right_subset_outer_range
  have hKagree (t : ℝ) (ht : t ∈ Icc (L.G (1 / 2)) (L.G 1)) :
      K (circleParam d.outerParam t) = circleParam d.outerParam (L.overlapParameter n t) :=
    (hK _).trans (L.overlap_agrees F hF hI hJ hpreimage n hbefore ht)
  have hoverlap : (K '' (circleParam d.outerParam '' Ioo (L.G (1 / 2)) (L.G 1)) ∩
      (circleParam d.outerParam '' Ioo (L.G (1 / 2)) (L.G 1))).Nonempty := by
    rw [← L.image_cut_open_interval hJ, hKimage]
    simpa only [image_sdiff g.injective, image_pair] using hmeet
  obtain ⟨z, hz, hKeq⟩ := halfTurn_of_decreasing_lift_overlap d.outerContinuous d.outerInjective
    L.image_cut_interval_nondegenerate L.image_cut_interval_short K (-(r ^ (n + 1 + 1)))
    (PlaneIsometries.complexEquiv (K 0)) hKform hKsub
    (L.overlapParameter_continuous n).continuousOn
    ((L.overlapParameter_antitone n).strictAntiOn _) hKagree hoverlap
  have hKh (x : Plane) : ((F : Plane → Plane)^[n + 1]) (g.symm x) =
      AffineIsometryEquiv.pointReflection ℝ z x :=
    (hK x).symm.trans (congrArg (fun e : Plane ≃ᵃⁱ[ℝ] Plane => e x) hKeq)
  have hzJ : z ∈ g '' Γ := by
    rw [L.image_cut_interval hJ]
    exact image_mono Ioo_subset_Icc_self hz.1
  exact RotationAlgebra.first_overlap_forces_center_mem F g c a b hg hnot hF hKh hzJ

end Puzzling139335.CentralRotation
