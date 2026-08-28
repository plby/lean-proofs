import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureSegments
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicLocalSegment

/-!
# Local logarithmic path replacement stays in the complex-structure locus

Both logarithms in the interpolation anticommute with the starting complex
structure. Their linear combination is therefore an actual tangent direction,
and its exponential curve is the given symplectic replacement after inclusion.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

variable {n : ℕ}

def symplecticFamily {Y : Type*} [TopologicalSpace Y] (H : C(Y, Space n)) :
    C(Y, symplecticSubgroup n) :=
  ⟨fun y ↦ toSymplectic (H y), continuous_toSymplectic.comp H.continuous⟩

namespace LocalReplacement

variable {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, Space n))
  (h : ∀ p : I × X, (H (0, p.2), H p) ∈ ShortLog.domain n)

include h in
theorem groupCondition (p : I × X) :
    (symplecticFamily H (0, p.2))⁻¹ * symplecticFamily H p ∈ Exponential.compatibleDomain n :=
  ShortLog.relative_mem_compatibleDomain (h p)

def direction (s t : I) (x : X) : AntiSkewSpace (H (0, x)) :=
  (1 - (s : ℝ)) • ShortLog.direction (H (0, x)) (H (t, x)) (h (t, x)) +
    (s : ℝ) • ((t : ℝ) • ShortLog.direction (H (0, x)) (H (1, x)) (h (1, x)))

theorem direction_toSkew (s t : I) (x : X) :
    antiSkewToSkew (H (0, x)) (direction H h s t x) =
      (1 - (s : ℝ)) • Exponential.LocalSegment.logs (symplecticFamily H) (groupCondition H h)
        (t, x) + (s : ℝ) • ((t : ℝ) •
          Exponential.LocalSegment.logs (symplecticFamily H) (groupCondition H h) (1, x)) := by
  apply Subtype.ext
  rfl

def point (q : I × (I × X)) : Space n :=
  exponentialCurve (H (0, q.2.2)) (direction H h q.1 q.2.1 q.2.2) 1

theorem point_toSymplectic (q : I × (I × X)) :
    toSymplectic (point H h q) =
      Exponential.LocalSegment.replacement (symplecticFamily H) (groupCondition H h) q := by
  rw [point, exponentialCurve_toSymplectic, one_smul, direction_toSkew]
  rfl

def replacement : C(I × (I × X), Space n) :=
  ⟨point H h, continuous_of_toSymplectic
    ((Exponential.LocalSegment.replacement (symplecticFamily H)
      (groupCondition H h)).continuous.congr
      (fun q ↦ (point_toSymplectic H h q).symm))⟩

theorem replacement_toSymplectic (q : I × (I × X)) :
    toSymplectic (replacement H h q) =
      Exponential.LocalSegment.replacement (symplecticFamily H) (groupCondition H h) q :=
  point_toSymplectic H h q

theorem replacement_zero (p : I × X) : replacement H h (0, p) = H p := by
  apply toSymplectic_injective
  rw [replacement_toSymplectic, Exponential.LocalSegment.replacement_zero]
  rfl

theorem replacement_time_zero (s : I) (x : X) : replacement H h (s, (0, x)) = H (0, x) := by
  apply toSymplectic_injective
  rw [replacement_toSymplectic, Exponential.LocalSegment.replacement_time_zero]
  rfl

theorem replacement_time_one (s : I) (x : X) : replacement H h (s, (1, x)) = H (1, x) := by
  apply toSymplectic_injective
  rw [replacement_toSymplectic, Exponential.LocalSegment.replacement_time_one]
  rfl

end LocalReplacement
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
