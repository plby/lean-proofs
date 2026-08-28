import Wikipedia.HopfProblem.DegreeCollapseUnitCoordinateIntersection
import Wikipedia.HopfProblem.DegreeCollapseBasinSectionCancellation

/-!
# Carry an actual level isotopy and its intersection count through a diffeomorphism

Conjugate the whole smooth isotopy, not only its endpoint. Injectivity
identifies the complete intersection set and preserves its exact cardinality.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V H X Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] {J : ModelWithCorners ℝ V H}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H Y]

theorem conjugate_level_isotopy
    (e : Diffeomorph J J X Y ∞) (D : Diffeomorph J J X X ∞)
    (hD : IsotopicToIdentity D) : IsotopicToIdentity (e.symm.trans (D.trans e)) := by
  obtain ⟨A, hA, hzero, hone, hslices⟩ := hD
  refine ⟨fun z : ℝ × Y => e (A (z.1, e.symm z.2)),
    e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk
      (e.symm.contMDiff.comp contMDiff_snd))), ?_, ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hzero, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (D (e.symm y))
    rw [hone]
  · intro t
    obtain ⟨Dt, hDt⟩ := hslices t
    refine ⟨e.symm.trans (Dt.trans e), ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (Dt (e.symm y))
    rw [hDt]

theorem intersection_count_under_injective_map {A B X Y : Type*}
    (e : X → Y) (he : Injective e) (α : A → X) (β : B → X) :
    (range (e ∘ α) ∩ range (e ∘ β)).ncard = (range α ∩ range β).ncard := by
  have hset : range (e ∘ α) ∩ range (e ∘ β) = e '' (range α ∩ range β) := by
    ext y
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hab : α a = β b := he (ha.trans hb.symm)
      exact ⟨α a, ⟨mem_range_self a, ⟨b, hab.symm⟩⟩, ha⟩
    · rintro ⟨x, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hx⟩
      exact ⟨⟨a, (congrArg e ha).trans hx⟩, ⟨b, (congrArg e hb).trans hx⟩⟩
  rw [hset]
  exact Set.ncard_image_of_injective _ he

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
