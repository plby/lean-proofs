import Wikipedia.HopfProblem.DegreeCollapseReflectedOpenHalf

/-!
# The actual overlap of the reflected open halves contracts to the original endpoint fiber

The overlap is the literal strip with time between minus epsilon and
epsilon. Multiplication of time by one minus the homotopy parameter stays
in that strip and in the original constant collar. The resulting equivalence
uses the original endpoint projection and its original zero-time section.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (ε : ℝ) (hε : 0 < ε) (hc : Icc (-ε) ε ⊆ seamCollarTimes d)

abbrev CollarOverlap := (positiveOpen d ε ∩ negativeOpen d ε : Set (Fiber d))

def overlapProjection : C(CollarOverlap d ε, EndpointFiber d) :=
  ⟨fun p ↦ ⟨p.val.val.2,
    (map_on_seamCollar d p.val.val.1 (hc ⟨p.property.1.le, p.property.2.le⟩)
      p.val.val.2).symm.trans p.val.property⟩,
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

def overlapSection : C(EndpointFiber d, CollarOverlap d ε) :=
  ⟨fun x ↦ ⟨seamCollarPoint d 0 (zero_mem_seamCollarTimes d) x,
    ⟨neg_lt_zero.mpr hε, hε⟩⟩,
    ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem overlap_time_mem (s : unitInterval) (p : CollarOverlap d ε) :
    (1 - s.val) * p.val.val.1 ∈ Ioo (-ε) ε := by
  have hs0 : 0 ≤ 1 - s.val := sub_nonneg.mpr s.property.2
  have hs1 : 1 - s.val ≤ 1 := by linarith [s.property.1]
  apply abs_lt.mp
  calc
    |(1 - s.val) * p.val.val.1| = (1 - s.val) * |p.val.val.1| := by
      rw [abs_mul, abs_of_nonneg hs0]
    _ ≤ |p.val.val.1| := mul_le_of_le_one_left (abs_nonneg _) hs1
    _ < ε := abs_lt.mpr p.property

def overlapSlide :
    (ContinuousMap.id (CollarOverlap d ε)).Homotopy
      ((overlapSection d ε hε).comp (overlapProjection d ε hc)) where
  toFun q :=
    ⟨⟨((1 - q.1.val) * q.2.val.val.1, q.2.val.val.2),
      (map_on_seamCollar d _
        (hc ⟨(overlap_time_mem d ε q.1 q.2).1.le,
          (overlap_time_mem d ε q.1 q.2).2.le⟩) _).trans
        (overlapProjection d ε hc q.2).property⟩,
      overlap_time_mem d ε q.1 q.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_fst.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))))
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp) rfl
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp [overlapSection, seamCollarPoint]) rfl

def overlapHomotopyEquiv : CollarOverlap d ε ≃ₕ EndpointFiber d where
  toFun := overlapProjection d ε hc
  invFun := overlapSection d ε hε
  left_inv := ⟨(overlapSlide d ε hε hc).symm⟩
  right_inv := by
    have he : (overlapProjection d ε hc).comp (overlapSection d ε hε) =
        ContinuousMap.id (EndpointFiber d) := rfl
    rw [he]

def negativeHalfHomotopyEquiv : negativeOpen d ε ≃ₕ NonnegativeHalf d :=
  (negativePositiveHomeomorph d ε).toHomotopyEquiv.trans
    (positiveHalfHomotopyEquiv d ε hε hc)

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
