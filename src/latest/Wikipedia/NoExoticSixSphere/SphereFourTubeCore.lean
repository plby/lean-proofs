import Wikipedia.NoExoticSixSphere.SphereFourTubeOldZeroFrame

/-!
# The literal core and core complement of the four-normal tube

The core is the range of the zero-normal-coordinate map. It is compact
and closed, and the tube inverse identifies its complement with nonzero
normal coordinates wherever those coordinates are defined.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def core : Set M := range (fun s : Sphere 3 ↦ Φ (s, 0))

abbrev CoreComplement := {x : M // x ∉ core Φ}

abbrev Exterior := {x : M // x ∉ openRegion Φ 1}

theorem core_eq_closedRegion_zero : core Φ = closedRegion Φ 0 := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(s, 0), ⟨mem_univ _, by simp⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hv : p.2 = 0 := norm_eq_zero.mp
      (le_antisymm (mem_closedBall_zero_iff.mp hp.2) (norm_nonneg _))
    exact ⟨p.1, by rw [← hv]⟩

theorem isCompact_core (hΦ : Φ.source = univ) : IsCompact (core Φ) := by
  rw [core_eq_closedRegion_zero]
  exact isCompact_closedRegion Φ hΦ 0

theorem isClosed_core [T2Space M] (hΦ : Φ.source = univ) : IsClosed (core Φ) :=
  (isCompact_core Φ hΦ).isClosed

theorem core_mem_iff (hΦ : Φ.source = univ) (x : M) :
    x ∈ core Φ ↔ x ∈ Φ.target ∧ (Φ.symm x).2 = 0 := by
  rw [core_eq_closedRegion_zero, mem_closedRegion_iff Φ hΦ]
  simp only [norm_le_zero_iff]

theorem inverse_normal_ne_zero (hΦ : Φ.source = univ) (x : CoreComplement Φ)
    (hx : x.val ∈ Φ.target) : (Φ.symm x.val).2 ≠ 0 :=
  fun hz ↦ x.property ((core_mem_iff Φ hΦ x.val).mpr ⟨hx, hz⟩)

theorem tube_mem_core_iff (hΦ : Φ.source = univ) (p : Sphere 3 × Vector 4) :
    Φ p ∈ core Φ ↔ p.2 = 0 := by
  have hinj : Injective Φ := (Φ.toOpenPartialHomeomorph.isOpenEmbedding hΦ).injective
  constructor
  · rintro ⟨s, hs⟩
    exact (congrArg Prod.snd (hinj hs)).symm
  · intro hp
    exact ⟨p.1, by rw [← hp]⟩

theorem core_subset_openRegion_one : core Φ ⊆ openRegion Φ 1 := by
  rw [core_eq_closedRegion_zero]
  exact closedRegion_subset_openRegion Φ zero_lt_one

theorem openRegion_one_subset_closedRegion_one : openRegion Φ 1 ⊆ closedRegion Φ 1 :=
  image_mono (prod_mono Subset.rfl ball_subset_closedBall)

end NoExoticSixSphere.SphereFourTube
