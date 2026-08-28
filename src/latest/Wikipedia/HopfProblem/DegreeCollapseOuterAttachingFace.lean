import Wikipedia.NoExoticSixSphere.AttachingTubeCoordinates
import Wikipedia.NoExoticSixSphere.RoundedTraceExteriorWindow
import Wikipedia.NoExoticSixSphere.UnitSurgeryCoordinates
import Wikipedia.SmoothSixDPoincare.SmoothClosedFace

/-!
# An actual full framed face covering the entire rounding tube

Rescale the original native attaching chart to any positive radius below
its original radius. The full closed face has exactly the corresponding
closed tube as its range and retains the original core. In particular,
the constructed outer rounding radius gives a full face whose complement
is the genuine retained exterior used by the framing formulas.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.OuterFace

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (ρ : ℝ) (hρ : 0 < ρ) (hρA : ρ < A.radius)

def normalScale : Vector 3 ≃L[ℝ] Vector 3 :=
  (LinearEquiv.smulOfNeZero ℝ (Vector 3) ρ hρ.ne').toContinuousLinearEquiv

theorem normalScale_bound (v : Vector 3) (hv : v ∈ closedBall (0 : Vector 3) 1) :
    ‖normalScale ρ hρ v‖ ≤ ρ := by
  change ‖ρ • v‖ ≤ ρ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  exact mul_le_of_le_one_right hρ.le (mem_closedBall_zero_iff.mp hv)

def atRadius : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M := by
  let L := normalScale ρ hρ
  let j : Sphere 3 × MorseHandle.UnitDisk (Vector 3) →
      Sphere 3 × closedBall (0 : Vector 3) A.radius :=
    fun p ↦ (p.1, ⟨L p.2.val, mem_closedBall_zero_iff.mpr
      ((normalScale_bound ρ hρ p.2.val p.2.property).trans hρA.le)⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((L.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have hji : Injective j := by
    intro p q he
    apply Prod.ext
    · exact congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) A.radius ↦ z.1) he
    · apply Subtype.ext
      exact L.injective (congrArg
        (fun z : Sphere 3 × closedBall (0 : Vector 3) A.radius ↦ z.2.val) he)
  let D := (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞).prodCongr L.toDiffeomorph
  exact {
    map := ⟨fun p ↦ A.tube ((j p).1, (j p).2.val), A.tube_embedded.continuous.comp hj⟩
    closedEmbedding := A.tube_embedded.comp (hj.isClosedEmbedding hji)
    chart := D.toPartialDiffeomorph.trans A.tubeCoordinates
    source := fun p hp ↦ ⟨mem_univ _, mem_univ _, mem_ball_zero_iff.mpr
      ((normalScale_bound ρ hρ p.2 hp.2).trans_lt hρA)⟩
    point := fun _ _ ↦ rfl }

theorem atRadius_map (p : Sphere 3 × MorseHandle.UnitDisk (Vector 3)) :
    (atRadius A ρ hρ hρA).map p = A.tube (p.1, ρ • p.2.val) := rfl

theorem atRadius_core (s : Sphere 3) :
    FramedSurgery.coreMap (E := Vector 4) (atRadius A ρ hρ hρA) s = f s := by
  change A.tube (s, ρ • 0) = f s
  rw [smul_zero, A.tube_core]

theorem atRadius_range : range (atRadius A ρ hρ hρA).map =
    A.tube '' ((univ : Set (Sphere 3)) ×ˢ closedBall (0 : Vector 3) ρ) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p.1, ρ • p.2.val), ⟨mem_univ _, mem_closedBall_zero_iff.mpr
      (normalScale_bound ρ hρ p.2.val p.2.property)⟩, rfl⟩
  · rintro ⟨⟨s, v⟩, ⟨_, hv⟩, rfl⟩
    have hw : ρ⁻¹ • v ∈ closedBall (0 : Vector 3) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      calc
        ρ⁻¹ * ‖v‖ ≤ ρ⁻¹ * ρ :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hv) (inv_nonneg.mpr hρ.le)
        _ = 1 := inv_mul_cancel₀ hρ.ne'
    refine ⟨(s, ⟨ρ⁻¹ • v, hw⟩), ?_⟩
    rw [atRadius_map, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]

variable [CompactSpace M]

def outerFace : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M :=
  atRadius A (outerRadius A)
    ((UnroundedTrace.handleRadius_pos A).trans (outerRadius_gt_handle A)) (outerRadius_lt A)

theorem outerFace_range : range (outerFace A).map = outerTubeImage A := atRadius_range A _ _ _

theorem outerFace_core (s : Sphere 3) :
    FramedSurgery.coreMap (E := Vector 4) (outerFace A) s = f s := atRadius_core A _ _ _ s

theorem outerFace_core_eq_unit (hR : A.radius = 2) :
    FramedSurgery.coreMap (E := Vector 4) (outerFace A) =
      FramedSurgery.coreMap (E := Vector 4) (UnitSurgery.face A hR) := by
  apply ContinuousMap.ext
  intro s
  exact (outerFace_core A s).trans (A.tube_core s).symm

theorem unitFace_range_subset_outerTube (hR : A.radius = 2) :
    range (UnitSurgery.face A hR).map ⊆ outerTubeImage A := by
  have hhandle : UnroundedTrace.handleRadius A = 1 := by
    change A.radius / 2 = 1
    rw [hR]
    norm_num
  have hout : 1 < outerRadius A := hhandle ▸ outerRadius_gt_handle A
  rintro y ⟨p, rfl⟩
  exact ⟨(p.1, p.2.val), ⟨mem_univ _,
    (closedBall_subset_closedBall hout.le) p.2.property⟩, rfl⟩

theorem retainedExterior_subset_unitExterior (hR : A.radius = 2) :
    (retainedExterior A : Set M) ⊆ (range (UnitSurgery.face A hR).map)ᶜ :=
  fun _ hm hp ↦ hm (unitFace_range_subset_outerTube A hR hp)

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.OuterFace
