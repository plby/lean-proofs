import Wikipedia.HopfProblem.DegreeCollapseSurgeryTimeProfile
import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryLocalCoordinates
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothMaps

/-!
# A smooth defining time function on the actual seven-dimensional surgery

Flatten the old defining function above the positive attachment margin and
give the new handle the constant value one. The two functions agree on the
literal radial overlap, so they descend to the canonical surgery quotient.
Native patch smoothness proves smoothness in its independently built atlas.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

structure TimeData where
  time : M → ℝ
  smooth : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ time
  regular : ∀ p, time p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) time p)
  margin : ℝ
  margin_pos : 0 < margin
  tube_time : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius,
    margin ≤ time (A.tube (s, v))

variable [T2Space M] (hR : A.radius = 2) (T : TimeData A)

def oldTime (p : OldPatch A hR) : ℝ := SurgeryTimeProfile.profile T.margin (T.time p.val)

theorem oldTime_overlap (z : FramedSurgery.Overlap (Vector 4) (Vector 4)) :
    oldTime A hR T (FramedSurgery.oldOverlap (E := Vector 4) (face A hR) z) = 1 := by
  change SurgeryTimeProfile.profile T.margin (T.time (A.tube (z.1, z.2.val))) = 1
  apply SurgeryTimeProfile.profile_eq_one T.margin_pos
  apply T.tube_time
  apply closedBall_subset_closedBall (show (1 : ℝ) ≤ A.radius by rw [hR]; norm_num)
  exact mem_closedBall_zero_iff.mpr z.2.property.2.le

def timeFunction : Target A hR → ℝ :=
  Quotient.lift (Sum.elim (oldTime A hR T) (fun _ ↦ 1)) (by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg (oldTime A hR T) hxy
      | inr y =>
        have he : FramedSurgery.oldMap (E := Vector 4) (face A hR) 3 x =
            FramedSurgery.newMap (E := Vector 4) (face A hR) 3 y := Quotient.sound hxy
        obtain ⟨z, rfl, rfl⟩ :=
          (FramedSurgery.old_eq_new_iff (E := Vector 4) (face A hR) 3 x y).mp he
        exact oldTime_overlap A hR T z
    | inr x =>
      cases y with
      | inl y =>
        have he : FramedSurgery.newMap (E := Vector 4) (face A hR) 3 x =
            FramedSurgery.oldMap (E := Vector 4) (face A hR) 3 y := Quotient.sound hxy
        obtain ⟨z, rfl, rfl⟩ :=
          (FramedSurgery.old_eq_new_iff (E := Vector 4) (face A hR) 3 y x).mp he.symm
        exact (oldTime_overlap A hR T z).symm
      | inr y => rfl)

theorem timeFunction_old (p : OldPatch A hR) :
    timeFunction A hR T (FramedSurgery.oldMap (E := Vector 4) (face A hR) 3 p) =
      SurgeryTimeProfile.profile T.margin (T.time p.val) := rfl

theorem timeFunction_new (p : FramedSurgery.NewPatch (Vector 4) (Vector 4)) :
    timeFunction A hR T (FramedSurgery.newMap (E := Vector 4) (face A hR) 3 p) = 1 := rfl

theorem contMDiff_oldTime : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ (oldTime A hR T) :=
  (SurgeryTimeProfile.contDiff_profile T.margin).contMDiff.comp
    (T.smooth.comp contMDiff_subtype_val)

variable [IsManifold (𝓡 7) ∞ M]

theorem contMDiff_timeFunction : letI := targetChartedSpace A hR;
    ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ (timeFunction A hR T) := by
  let := targetChartedSpace A hR
  exact (boundaryData A hR).contMDiff_of_patches (timeFunction A hR T)
    (contMDiff_oldTime A hR T) contMDiff_const

theorem timeFunction_zero_iff (p : Target A hR) :
    timeFunction A hR T p = 0 ↔ ∃ q : OldPatch A hR,
      T.time q.val = 0 ∧ FramedSurgery.oldMap (E := Vector 4) (face A hR) 3 q = p := by
  constructor
  · intro hp
    rcases FramedSurgery.cover (E := Vector 4) (face A hR) 3 p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨q, (SurgeryTimeProfile.profile_eq_zero_iff T.margin_pos _).mp hp, rfl⟩
    · exact (one_ne_zero (timeFunction_new A hR T q ▸ hp)).elim
  · rintro ⟨q, hq, rfl⟩
    exact (SurgeryTimeProfile.profile_eq_zero_iff T.margin_pos _).mpr hq

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
