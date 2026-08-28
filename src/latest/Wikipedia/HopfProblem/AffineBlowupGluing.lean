import Wikipedia.HopfProblem.AffineBlowupManifold

/-!
# Gluing maps out of the actual affine blow-up

Maps on the two affine charts descend when they agree on the explicit
overlap. Continuity, holomorphicity, and openness can be checked there.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.AffineBlowup

open ToricCharts

instance space_nonempty : Nonempty Space := ⟨left 0⟩

theorem affineMap_cross_eq_iff (b : Bool) (z w : CoordinateSpace 2) :
    affineMap b z = affineMap (!b) w ↔
      z (directionCoordinate b) ≠ 0 ∧ w = crossCoordinates b z := by
  constructor
  · intro h
    have hm : z ∈ ((parametrization b).trans (parametrization (!b)).symm).source :=
      ⟨mem_univ _, by
        change affineMap b z ∈ affineTarget (!b)
        rw [h]
        exact affineMap_mem_target (!b) w⟩
    refine ⟨(transition_cross b z hm).1, ?_⟩
    apply (affineMap_isOpenEmbedding (!b)).injective
    exact h.symm.trans (affineMap_crossCoordinates b z (transition_cross b z hm).1).symm
  · rintro ⟨hz, rfl⟩
    exact (affineMap_crossCoordinates b z hz).symm

variable {Y : Type*} (f : Bool → CoordinateSpace 2 → Y)
    (hf : ∀ b z, z (directionCoordinate b) ≠ 0 →
      f (!b) (crossCoordinates b z) = f b z)

def descend (x : Space) : Y :=
  f (preferredChart x) (affineCoords (preferredChart x) x)

include hf

theorem maps_compatible (b c : Bool) (z w : CoordinateSpace 2)
    (h : affineMap b z = affineMap c w) : f b z = f c w := by
  by_cases hbc : b = c
  · subst c
    rw [(affineMap_isOpenEmbedding b).injective h]
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    obtain ⟨hz, hw⟩ := (affineMap_cross_eq_iff b z w).mp h
    rw [hw]
    exact (hf b z hz).symm

theorem descend_affineMap (b : Bool) (z : CoordinateSpace 2) :
    descend f (affineMap b z) = f b z := by
  let c := preferredChart (affineMap b z)
  let w := affineCoords c (affineMap b z)
  have hw : affineMap c w = affineMap b z :=
    affineMap_affineCoords c _ (preferred_mem _)
  exact maps_compatible f hf c b w z hw

theorem descend_eq_on_target (b : Bool) (x : Space) (hx : x ∈ affineTarget b) :
    descend f x = f b (affineCoords b x) := by
  rw [← affineMap_affineCoords b x hx]
  rw [descend_affineMap f hf, affineCoords_affineMap]

theorem descend_range : range (descend f) = ⋃ b, range (f b) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨b, z, rfl⟩ := affineMap_jointly_surjective x
    rw [descend_affineMap f hf]
    exact mem_iUnion.mpr ⟨b, mem_range_self z⟩
  · intro hy
    obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hy
    exact ⟨affineMap b z, descend_affineMap f hf b z⟩

theorem descend_injective
    (hinj : ∀ b c z w, f b z = f c w → affineMap b z = affineMap c w) :
    Function.Injective (descend f) := by
  intro x y h
  obtain ⟨b, z, rfl⟩ := affineMap_jointly_surjective x
  obtain ⟨c, w, rfl⟩ := affineMap_jointly_surjective y
  rw [descend_affineMap f hf, descend_affineMap f hf] at h
  exact hinj b c z w h

variable [TopologicalSpace Y]

theorem descend_continuous (hcont : ∀ b, Continuous (f b)) : Continuous (descend f) := by
  rw [continuous_iff_continuousAt]
  intro x
  let b := preferredChart x
  have h : ContinuousOn (descend f) (affineTarget b) := by
    apply ((hcont b).comp_continuousOn (affineCoords_continuousOn b)).congr
    intro y hy
    exact descend_eq_on_target f hf b y hy
  exact h.continuousAt ((affineTarget_isOpen b).mem_nhds (preferred_mem x))

theorem descend_isOpenMap (hopen : ∀ b, IsOpenMap (f b)) : IsOpenMap (descend f) := by
  intro U hU
  have he : descend f '' U = ⋃ b, f b '' (affineMap b ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b, z, rfl⟩ := affineMap_jointly_surjective x
      rw [descend_affineMap f hf]
      exact mem_iUnion.mpr ⟨b, z, hx, rfl⟩
    · intro hy
      obtain ⟨b, z, hz, rfl⟩ := mem_iUnion.mp hy
      exact ⟨affineMap b z, hz, descend_affineMap f hf b z⟩
  rw [he]
  exact isOpen_iUnion (fun b => hopen b _ (hU.preimage (affineMap_continuous b)))

theorem descend_holomorphic {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [ChartedSpace H Y] (I : ModelWithCorners ℂ F H)
    (hhol : ∀ b, ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω (f b)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω (descend f) := by
  apply contMDiff_of_comp_affineMaps
  intro b
  have he : descend f ∘ affineMap b = f b := by
    funext z
    exact descend_affineMap f hf b z
  rw [he]
  exact hhol b

end Wikipedia.HopfProblem.AffineBlowup
