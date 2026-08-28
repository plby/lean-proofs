import Wikipedia.HopfProblem.DegreeCollapseTimeCollarHalf
import Wikipedia.NoExoticSixSphere.RelativeHomologyMapComparison
import Wikipedia.NoExoticSixSphere.RelativeSingularExcision

/-!
# The original half-to-ambient relative map away from a positive closed subset

The zero clamp fixes every nonnegative point and never moves a negative
point to positive time. It therefore preserves the complement of any
positive subset. Its actual restricted homotopy and open-cover excision
prove bijectivity of the original relative inclusion in every degree.
-/

noncomputable section

open Function Set ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology
open RelativeSingularHomology
open ReflectedCylinder (interiorSlideTime_bounds)

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B] {t : M → ℝ}
  (C : TimeCollar t B) (K : Set M) (hK : ∀ p ∈ K, 0 < t p)

abbrev halfComplement (_C : TimeCollar t B) (K : Set M) : Set (NonnegativeHalf t) :=
  Subtype.val ⁻¹' Kᶜ

def openComplement : Set C.positiveOpen := Subtype.val ⁻¹' Kᶜ

theorem halfToPositive_complement :
    MapsTo C.halfToPositive (C.halfComplement K) (C.openComplement K) := fun _ hp ↦ hp

include hK in
theorem positiveHalfSlide_complement (s : unitInterval) (p : C.positiveOpen)
    (hp : p ∈ C.openComplement K) : C.positiveHalfSlide (s, p) ∈ C.openComplement K := by
  change (C.clampSlide 0 C.width_pos (s, p)).val ∉ K
  by_cases ht : 0 ≤ t p.val
  · rw [C.clampSlide_fixed 0 C.width_pos s p ht]
    exact hp
  · intro hk
    have hb := hK _ hk
    have hu : t (C.clampSlide 0 C.width_pos (s, p)).val ≤ 0 := by
      rw [C.clampSlide_time]
      exact (interiorSlideTime_bounds 0 s (t p.val)).2.trans_eq
        (max_eq_right (le_of_not_ge ht))
    exact (not_lt_of_ge hu) hb

include hK in
theorem positiveHalfRetraction_complement :
    MapsTo C.positiveHalfRetraction (C.openComplement K) (C.halfComplement K) := by
  intro p hp
  exact C.positiveHalfSlide_complement K hK 1 p hp

def complementToPositive : C(C.halfComplement K, C.openComplement K) :=
  restrictedMap C.halfToPositive (C.halfToPositive_complement K)

def complementRetraction : C(C.openComplement K, C.halfComplement K) :=
  restrictedMap C.positiveHalfRetraction (C.positiveHalfRetraction_complement K hK)

def complementSlide : (ContinuousMap.id (C.openComplement K)).Homotopy
    ((C.complementToPositive K).comp (C.complementRetraction K hK)) where
  toFun q := ⟨C.positiveHalfSlide (q.1, q.2.val),
    C.positiveHalfSlide_complement K hK q.1 q.2.val q.2.property⟩
  continuous_toFun := (C.positiveHalfSlide.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := Subtype.ext (C.positiveHalfSlide.map_zero_left p.val)
  map_one_left p := Subtype.ext (C.positiveHalfSlide.map_one_left p.val)

def complementHomotopyEquiv : C.halfComplement K ≃ₕ C.openComplement K where
  toFun := C.complementToPositive K
  invFun := C.complementRetraction K hK
  left_inv := by
    have he : (C.complementRetraction K hK).comp (C.complementToPositive K) =
        ContinuousMap.id (C.halfComplement K) := by
      apply ContinuousMap.ext
      intro p
      exact Subtype.ext (C.positiveHalfRetraction_halfToPositive p.val)
    rw [he]
  right_inv := ⟨(C.complementSlide K hK).symm⟩

include hK in
theorem halfToPositive_relative_bijective (k : ℕ) :
    Bijective (RelativeSingularHomology.map C.halfToPositive (C.halfToPositive_complement K) k) := by
  apply map_bijective_of_absolute
  · intro j
    exact C.halfToPositive_homology_bijective j
  · intro j
    exact (homotopyEquivHomologyEquiv (C.complementHomotopyEquiv K hK) j).bijective

include hK in
theorem positiveOpen_complement_cover : (C.positiveOpen : Set M) ∪ Kᶜ = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  by_cases hp : p ∈ C.positiveOpen
  · exact Or.inl hp
  · right
    intro hk
    apply hp
    change -C.width / 2 < t p
    have hb := hK p hk
    linarith [C.width_pos]

theorem halfInclusion_complement : MapsTo (halfInclusion t) (C.halfComplement K) Kᶜ :=
  fun _ hp ↦ hp

include hK in
theorem halfInclusion_relative_bijective (hclosed : IsClosed K) (k : ℕ) :
    Bijective (RelativeSingularHomology.map (halfInclusion t) (C.halfInclusion_complement K) k) := by
  have he := excisionMap_bijective (C.positiveOpen : Set M) Kᶜ C.positiveOpen.isOpen
    hclosed.isOpen_compl (C.positiveOpen_complement_cover K hK) k
  have hh := C.halfToPositive_relative_bijective K hK k
  have hcomp := he.comp hh
  change Bijective ((RelativeSingularHomology.map (subtypeInclusion (C.positiveOpen : Set M))
    (show MapsTo (subtypeInclusion (C.positiveOpen : Set M)) (C.openComplement K) Kᶜ from
      fun _ hx ↦ hx) k).comp
        (RelativeSingularHomology.map C.halfToPositive (C.halfToPositive_complement K) k)) at hcomp
  rw [← RelativeSingularHomology.map_comp] at hcomp
  exact hcomp

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
