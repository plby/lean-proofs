import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCoordinateDisc

/-!
# Exact analytic disc parametrizations of the chosen filling patches

Each selected small patch is biholomorphic to its literal coordinate
ball by restriction of the original actual quotient chart.  The inverse
maps are holomorphic open embeddings in the existing compact-curve atlas
and have precisely the chosen patches as their ranges.  The regular
overlap corresponds exactly to the nonzero part of each coordinate disc.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.BaseCover

attribute [local instance] triangleCompactifiedChartedSpace

variable (C : BaseCover)

/-- The chosen filling patch with the unchanged actual local coordinate. -/
def fillingChart (i : Puncture) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (C.fillingPatch i) (coordinateBall (C.radius i)) ω :=
  coordinateDiscBiholomorph (puncturePartial i) (C.radius i)
    (C.coordinateBall_subset_target i)

@[simp] theorem fillingChart_coe (i : Puncture) (x : C.fillingPatch i) :
    (C.fillingChart i x : ℂ) = punctureChart i x := rfl

@[simp] theorem fillingChart_symm_coe (i : Puncture) (z : coordinateBall (C.radius i)) :
    ((C.fillingChart i).symm z : TriangleCompactifiedOrbitSpace) =
      (punctureChart i).symm z := rfl

/-- The actual inverse chart as an embedding into the whole compact base. -/
def fillingEmbedding (i : Puncture) : coordinateBall (C.radius i) →
    TriangleCompactifiedOrbitSpace :=
  fun z => ((C.fillingChart i).symm z : TriangleCompactifiedOrbitSpace)

@[simp] theorem fillingEmbedding_apply (i : Puncture) (z : coordinateBall (C.radius i)) :
    C.fillingEmbedding i z = (punctureChart i).symm z := rfl

theorem fillingEmbedding_mem (i : Puncture) (z : coordinateBall (C.radius i)) :
    C.fillingEmbedding i z ∈ C.fillingPatch i :=
  ((C.fillingChart i).symm z).property

theorem fillingEmbedding_holomorphic (i : Puncture) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (C.fillingEmbedding i) :=
  contMDiff_subtype_val.comp (C.fillingChart i).symm.contMDiff

theorem fillingEmbedding_isOpenEmbedding (i : Puncture) :
    IsOpenEmbedding (C.fillingEmbedding i) :=
  (C.fillingPatch i).isOpen.isOpenEmbedding_subtypeVal.comp
    (C.fillingChart i).symm.toHomeomorph.isOpenEmbedding

/-- This inverse chart covers the entire chosen filling patch. -/
theorem fillingEmbedding_range (i : Puncture) :
    range (C.fillingEmbedding i) = (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact C.fillingEmbedding_mem i z
  · intro hx
    refine ⟨C.fillingChart i ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((C.fillingChart i).symm_apply_apply ⟨x, hx⟩)

@[simp] theorem punctureChart_fillingEmbedding (i : Puncture)
    (z : coordinateBall (C.radius i)) :
    punctureChart i (C.fillingEmbedding i z) = (z : ℂ) :=
  (punctureChart i).right_inv (C.coordinateBall_subset_target i z.property)

/-- The local parameter is nonzero exactly above the regular base. -/
theorem fillingEmbedding_mem_regular_iff (i : Puncture)
    (z : coordinateBall (C.radius i)) :
    C.fillingEmbedding i z ∈ regularPatch ↔ (z : ℂ) ≠ 0 :=
  C.inverse_mem_regular_iff i z.property

/-- Zero is precisely the marked point of this filling patch. -/
theorem fillingEmbedding_eq_point_iff (i : Puncture)
    (z : coordinateBall (C.radius i)) :
    C.fillingEmbedding i z = puncturePoint i ↔ (z : ℂ) = 0 := by
  constructor
  · intro h
    have he := congrArg (punctureChart i) h
    simpa only [C.punctureChart_fillingEmbedding, punctureChart_point] using he
  · intro h
    change (punctureChart i).symm (z : ℂ) = puncturePoint i
    rw [h, punctureChart_symm_zero]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.BaseCover
