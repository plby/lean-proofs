import ErdosProblems.Erdos633.FieldRealization
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite

/-!
# Coordinate maps fixing a real coefficient field

The coordinatewise map induced by a field retraction preserves addition,
conjugation, multiplication by complex constants with coordinates in the
base field, and supporting-line incidence. Such a map can be chosen
injective on any finite set of plane points. It is not assumed continuous
or order preserving, and no tiling preservation conclusion is built in.
-/

namespace Erdos633

noncomputable def fieldCoordinateMap (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (z : ℂ) : ℂ :=
  ⟨(f z.re : ℝ), (f z.im : ℝ)⟩

theorem fieldCoordinateMap_add (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (z w : ℂ) :
    fieldCoordinateMap F f (z + w) = fieldCoordinateMap F f z + fieldCoordinateMap F f w := by
  apply Complex.ext <;> simp [fieldCoordinateMap]

theorem fieldCoordinateMap_sub (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (z w : ℂ) :
    fieldCoordinateMap F f (z - w) = fieldCoordinateMap F f z - fieldCoordinateMap F f w := by
  apply Complex.ext <;> simp [fieldCoordinateMap]

theorem fieldCoordinateMap_conj (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (z : ℂ) :
    fieldCoordinateMap F f (star z) = star (fieldCoordinateMap F f z) := by
  apply Complex.ext <;> simp [fieldCoordinateMap]

theorem fieldCoordinateMap_ofReal (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (x : ℝ) :
    fieldCoordinateMap F f (x : ℂ) = ((f x : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [fieldCoordinateMap]

theorem fieldCoordinateMap_fixed (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (hf : ∀ a : F, f (a : ℝ) = a) (z : ℂ) (hre : z.re ∈ F) (him : z.im ∈ F) :
    fieldCoordinateMap F f z = z := by
  apply Complex.ext
  · exact congrArg (fun a : F => (a : ℝ)) (hf ⟨z.re, hre⟩)
  · exact congrArg (fun a : F => (a : ℝ)) (hf ⟨z.im, him⟩)

theorem fieldCoordinateMap_sub_eq (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (hf : ∀ a : F, f (a : ℝ) = a) (z w : ℂ)
    (hre : (z - w).re ∈ F) (him : (z - w).im ∈ F) :
    fieldCoordinateMap F f z - fieldCoordinateMap F f w = z - w := by
  rw [← fieldCoordinateMap_sub]
  exact fieldCoordinateMap_fixed F f hf (z - w) hre him

theorem fieldCoordinateMap_eq_translation (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (hf : ∀ a : F, f (a : ℝ) = a) (p z : ℂ)
    (hre : (z - p).re ∈ F) (him : (z - p).im ∈ F) :
    fieldCoordinateMap F f z = fieldCoordinateMap F f p + (z - p) := by
  have h := fieldCoordinateMap_sub_eq F f hf z p hre him
  linear_combination h

theorem field_retraction_mul_coefficient (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (a x : ℝ) (ha : a ∈ F) : (f (a * x) : ℝ) = a * (f x : ℝ) := by
  have h := f.map_smul (⟨a, ha⟩ : F) x
  change f (a * x) = (⟨a, ha⟩ : F) * f x at h
  exact congrArg (fun y : F => (y : ℝ)) h

theorem fieldCoordinateMap_mul_coefficient (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (w z : ℂ) (hre : w.re ∈ F) (him : w.im ∈ F) :
    fieldCoordinateMap F f (w * z) = w * fieldCoordinateMap F f z := by
  apply Complex.ext <;> simp [fieldCoordinateMap, Complex.mul_re, Complex.mul_im,
    field_retraction_mul_coefficient F f w.re _ hre,
    field_retraction_mul_coefficient F f w.im _ him]

theorem fieldCoordinateMap_line (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (p d : ℂ) (t : ℝ) (hre : d.re ∈ F) (him : d.im ∈ F) :
    fieldCoordinateMap F f (p + (t : ℂ) * d) =
      fieldCoordinateMap F f p + ((f t : ℝ) : ℂ) * d := by
  rw [fieldCoordinateMap_add, mul_comm (t : ℂ) d,
    fieldCoordinateMap_mul_coefficient F f d (t : ℂ) hre him,
    fieldCoordinateMap_ofReal, mul_comm d]

theorem exists_fieldCoordinateMap_injective_on (F : Subfield ℝ) (s : Finset ℂ) :
    ∃ f : ℝ →ₗ[F] F, (∀ a : F, f (a : ℝ) = a) ∧ Set.InjOn (fieldCoordinateMap F f) s := by
  classical
  let coordinates : Finset ℝ := s.image Complex.re ∪ s.image Complex.im
  obtain ⟨f, hf, hinj⟩ := exists_field_retraction_injective_on (F := F) coordinates
  refine ⟨f, hf, ?_⟩
  intro z hz w hw heq
  apply Complex.ext
  · apply hinj
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩))
    exact Subtype.coe_injective (congrArg Complex.re heq)
  · apply hinj
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩))
    exact Subtype.coe_injective (congrArg Complex.im heq)

end Erdos633
