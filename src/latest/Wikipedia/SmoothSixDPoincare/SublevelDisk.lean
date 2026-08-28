import Wikipedia.SmoothSixDPoincare.TwoDiskRecognition

/-!
# A closed sublevel disk with its exact level-set boundary

This records a genuine standard-disk homeomorphism together with the
boundary-level identity. Its boundary restriction is a homeomorphism onto
the actual level set, including zero-dimensional and empty-boundary cases.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare

variable (n : ℕ) {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ)

/-- A standard closed disk parametrizing a sublevel, with boundary exactly its top level. -/
structure SublevelDisk where
  homeomorph : Hemisphere.Ball n ≃ₜ {x : M // f x ≤ a}
  boundary_iff : ∀ v, f (homeomorph v).1 = a ↔ ‖(v : Hemisphere.Ambient n)‖ = 1

namespace SublevelDisk

variable {n f a} (d : SublevelDisk n f a)

def map : C(Hemisphere.Ball n, M) where
  toFun v := (d.homeomorph v).1
  continuous_toFun := continuous_subtype_val.comp d.homeomorph.continuous

theorem map_injective : Function.Injective d.map := by
  intro v w h
  exact d.homeomorph.injective (Subtype.ext h)

/-- Restriction of the disk parametrization to its actual sphere boundary. -/
def boundaryMap : C(DiskDouble.Boundary (Hemisphere.Ambient n), {x : M // f x = a}) where
  toFun z := ⟨d.map (DiskDouble.boundary _ z), (d.boundary_iff _).mpr (by
    simpa only [DiskDouble.boundary, mem_sphere_zero_iff_norm] using z.2)⟩
  continuous_toFun := (d.map.continuous.comp
    (continuous_subtype_val.subtype_mk (fun z => sphere_subset_closedBall z.2))).subtype_mk _

theorem boundaryMap_injective : Function.Injective d.boundaryMap := by
  intro z w h
  have heq : d.map (DiskDouble.boundary _ z) = d.map (DiskDouble.boundary _ w) :=
    congrArg (fun y : {x : M // f x = a} => y.1) h
  have h' := d.map_injective heq
  apply Subtype.ext
  exact congrArg (fun v : Hemisphere.Ball n => (v : Hemisphere.Ambient n)) h'

theorem boundaryMap_surjective : Function.Surjective d.boundaryMap := by
  intro y
  let v := d.homeomorph.symm ⟨y.1, y.2.le⟩
  have hv : (d.homeomorph v).1 = y.1 :=
    congrArg Subtype.val (d.homeomorph.apply_symm_apply ⟨y.1, y.2.le⟩)
  have hnorm : ‖(v : Hemisphere.Ambient n)‖ = 1 := (d.boundary_iff v).mp (by rw [hv]; exact y.2)
  let z : DiskDouble.Boundary (Hemisphere.Ambient n) := ⟨v.1, mem_sphere_zero_iff_norm.mpr hnorm⟩
  refine ⟨z, Subtype.ext ?_⟩
  exact hv

/-- The sphere boundary of the disk is homeomorphic to the actual level set. -/
def boundaryHomeomorph [T2Space M] : DiskDouble.Boundary (Hemisphere.Ambient n) ≃ₜ
    {x : M // f x = a} :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective d.boundaryMap ⟨d.boundaryMap_injective, d.boundaryMap_surjective⟩)
    d.boundaryMap.continuous

end SublevelDisk
end Wikipedia.SmoothSixDPoincare
