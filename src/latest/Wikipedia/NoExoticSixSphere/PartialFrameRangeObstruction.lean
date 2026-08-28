import Wikipedia.NoExoticSixSphere.PartialFrameSphereObstruction
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates

/-!
# Extension obstruction for partial frames in an actual family of subspaces

A full orthonormal frame on the closed four-ball trivializes its actual
range subspaces. Extracting coordinates on the boundary defines parity.
Its vanishing is equivalent to extending the prescribed partial frame into
those same subspaces with exact boundary values. This criterion proves that
the value does not depend on the chosen full orthonormal trivialization.

Existence of a normal-bundle trivialization and the geometric quadratic
refinement are not supplied by this statement.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.RangeObstruction

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N : ℕ} (r : ℕ)
variable (t : C(Disk (E := Vector 4), Space N (3 + (r + 2))))
variable (a : C(NoExoticSixSphere.Sphere 3, Space N (r + 2)))
variable (ha : ∀ s, (a s).val.range ≤ (t (boundaryToDisk s)).val.range)

def boundaryCoordinates : C(NoExoticSixSphere.Sphere 3, Space (3 + (r + 2)) (r + 2)) :=
  RangeCoordinates.map (t.comp boundaryToDisk) a ha

def parity : ZMod 2 := sphereThirdObstruction r (boundaryCoordinates r t a ha)

theorem parity_zero_iff_extension : parity r t a ha = 0 ↔
    ∃ A : C(Disk (E := Vector 4), Space N (r + 2)),
      (∀ x, (A x).val.range ≤ (t x).val.range) ∧
      ∀ s, A (boundaryToDisk s) = a s := by
  change sphereThirdObstruction r (boundaryCoordinates r t a ha) = 0 ↔ _
  rw [sphereThirdObstruction_zero_iff_extension]
  constructor
  · rintro ⟨F, hF⟩
    let A : C(Disk (E := Vector 4), Space N (r + 2)) :=
      ⟨fun x ↦ Stiefel.comp (t x) (F x),
        continuous_comp t F t.continuous F.continuous⟩
    refine ⟨A, fun x ↦ RangeCoordinates.range_comp_le (t x) (F x), ?_⟩
    intro s
    change Stiefel.comp (t (boundaryToDisk s)) (F (boundaryToDisk s)) = a s
    rw [hF s]
    exact RangeCoordinates.comp_extract _ _ (ha s)
  · rintro ⟨A, hA, hAb⟩
    refine ⟨RangeCoordinates.map t A hA, ?_⟩
    intro s
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change (t (boundaryToDisk s)).val.adjoint ((A (boundaryToDisk s)).val x) =
      (t (boundaryToDisk s)).val.adjoint ((a s).val x)
    rw [hAb s]

theorem parity_independent_of_trivialization
    (u : C(Disk (E := Vector 4), Space N (3 + (r + 2))))
    (hu : ∀ x, (t x).val.range = (u x).val.range)
    (hau : ∀ s, (a s).val.range ≤ (u (boundaryToDisk s)).val.range) :
    parity r t a ha = parity r u a hau := by
  apply zmodTwo_eq_of_zero_iff
  rw [parity_zero_iff_extension, parity_zero_iff_extension]
  constructor
  · rintro ⟨A, hA, hAb⟩
    exact ⟨A, fun x ↦ (hA x).trans_eq (hu x), hAb⟩
  · rintro ⟨A, hA, hAb⟩
    exact ⟨A, fun x ↦ (hA x).trans_eq (hu x).symm, hAb⟩

end NoExoticSixSphere.Stiefel.RangeObstruction
