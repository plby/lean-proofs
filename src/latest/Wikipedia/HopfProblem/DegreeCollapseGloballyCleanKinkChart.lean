import Wikipedia.HopfProblem.DegreeCollapseUniqueBranchSourceChart
import Wikipedia.HopfProblem.DegreeCollapseNativePlaneImmersionChart
import Wikipedia.NoExoticSixSphere.CompactFiberNeighborhood
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# A native kink chart recognizing the entire original sphere map

Choose a genuine unique value, complete its branch to the literal plane
chart, then shrink the target using compactness of the entire original
source. Every original preimage of a point in the final chart is exactly
the selected source-chart point on the literal zero section.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SupportedCusp
open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]

theorem exists_globally_clean_kink_chart (F : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (ht : ∀ x y, x ≠ y → F x = F y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) F x).coprod (mfderiv (𝓡 3) (𝓡 6) F y))) :
    ∃ a : Vector 3, ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph (𝓡 6) (𝓡 6) (Vector 6) M ∞,
        closedBall (0 : Vector 6) ε ⊆ Φ.source ∧
        (∀ x, plane x ∈ Φ.source → Φ (plane x) = F (shiftedSourceChart a x)) ∧
        ∀ q ∈ Φ.source, ∀ z : Sphere 3,
          F z = Φ q ↔ ∃ v : Vector 3, q = plane v ∧ z = shiftedSourceChart a v := by
  obtain ⟨a, ha⟩ := exists_shifted_unique_fiber F (SphereSelfIntersections.finite_pairs hf ht hi)
  let χ := shiftedSourceChart a
  have hχsource : χ.source = univ := shiftedSourceChart_source a
  have hχ : ContMDiff (𝓡 3) (𝓡 3) ∞ χ := contMDiff_shiftedSourceChart a
  have hcomp : ContMDiff (𝓡 3) (𝓡 6) ∞ (F ∘ χ) := hf.comp hχ
  have hicomp : Injective (mfderiv (𝓡 3) (𝓡 6) (F ∘ χ) 0) :=
    injective_mfderiv_shifted_branch hf hi a 0
  obtain ⟨δ, hδ, Φ, hball, _, hplane⟩ := exists_native_plane_immersion_chart
    isOpen_univ (mem_univ (0 : Vector 3)) hcomp.contMDiffOn hicomp isOpen_univ (mem_univ _)
  have h0Φ : (0 : Vector 6) ∈ Φ.source := hball (mem_closedBall_self hδ.le)
  have hplane0 : plane (0 : Vector 3) ∈ Φ.source := by rwa [plane_zero]
  have hΦ0 : Φ 0 = F (χ 0) := by simpa only [plane_zero, comp_apply] using hplane 0 hplane0
  have hpreopen : IsOpen (plane ⁻¹' Φ.source) := Φ.open_source.preimage contDiff_plane.continuous
  obtain ⟨ρ, hρ, hρΦ⟩ := nhds_basis_closedBall.mem_iff.mp (hpreopen.mem_nhds hplane0)
  let U : Set (Sphere 3) := χ '' ball (0 : Vector 3) ρ
  have hχopen : IsOpenMap χ :=
    (χ.toOpenPartialHomeomorph.isOpenEmbedding hχsource).isOpenMap
  have hU : IsOpen U := hχopen _ isOpen_ball
  have h0U : χ 0 ∈ U := ⟨0, mem_ball_self hρ, rfl⟩
  obtain ⟨O, hO, h0O, hpreO⟩ := exists_open_full_preimage_subset F.continuous hU
    (fun z hz ↦ (ha z hz).symm ▸ h0U)
  let Q := PartialChart.restrictTarget Φ hO
  have h0Q : (0 : Vector 6) ∈ Q.source := by
    refine ⟨h0Φ, ?_⟩
    change Φ 0 ∈ O
    rw [hΦ0]
    exact h0O
  obtain ⟨ε, hε, hεQ⟩ := nhds_basis_closedBall.mem_iff.mp (Q.open_source.mem_nhds h0Q)
  refine ⟨a, ε, hε, Q, hεQ, (fun v hv ↦ hplane v hv.1), ?_⟩
  intro q hq z
  constructor
  · intro he
    have hzO : F z ∈ O := he ▸ hq.2
    obtain ⟨v, hv, hzv⟩ := hpreO z hzO
    have hvΦ : plane v ∈ Φ.source := hρΦ (ball_subset_closedBall hv)
    have haxis : Φ (plane v) = F z := (hplane v hvΦ).trans (congrArg F hzv)
    have hqv : q = plane v := Φ.injOn hq.1 hvΦ (he.symm.trans haxis.symm)
    exact ⟨v, hqv, hzv.symm⟩
  · rintro ⟨v, rfl, rfl⟩
    exact (hplane v hq.1).symm

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
