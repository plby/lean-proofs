import Wikipedia.HopfProblem.TriangleClosedDomainBasic
import Wikipedia.HopfProblem.TriangleClosedDomainBoundaryGeometry
import Wikipedia.HopfProblem.TriangleClosedDomainInfinity

/-!
# Every boundary point of the actual compactified triangle

The finite frontier consists of the three open sides and the two elliptic
endpoints. The only additional boundary point in the one-point plane is
the actual point at infinity. This gives an exhaustive classification on
the concrete closed-source subtype, with no Jordan-domain or closed-disc
homeomorphism assumption.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary

/-- The right circular endpoint as an actual point of the compact source. -/
def triangleClosedCenterOne : TriangleClosedDomain :=
  ⟨((centerOne : ℂ) : OnePoint ℂ),
    (coe_mem_triangleClosedSet_iff_closure _).mpr centerOne_mem_closure_triangleInterior⟩

/-- The left circular endpoint as an actual point of the compact source. -/
def triangleClosedCenterTwo : TriangleClosedDomain :=
  ⟨((centerTwo : ℂ) : OnePoint ℂ),
    (coe_mem_triangleClosedSet_iff_closure _).mpr centerTwo_mem_closure_triangleInterior⟩

@[simp] theorem triangleClosedCenterOne_val :
    (triangleClosedCenterOne : OnePoint ℂ) = ((centerOne : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem triangleClosedCenterTwo_val :
    (triangleClosedCenterTwo : OnePoint ℂ) = ((centerTwo : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem triangleClosedCenterOne_notMem_interior :
    triangleClosedCenterOne ∉ triangleClosedInterior := by
  change ((centerOne : ℂ) : OnePoint ℂ) ∉ onePointDomain triangleInterior
  simpa only [coe_mem_onePointDomain] using centerOne_not_mem_triangleInterior

@[simp] theorem triangleClosedCenterTwo_notMem_interior :
    triangleClosedCenterTwo ∉ triangleClosedInterior := by
  change ((centerTwo : ℂ) : OnePoint ℂ) ∉ onePointDomain triangleInterior
  simpa only [coe_mem_onePointDomain] using centerTwo_not_mem_triangleInterior

theorem triangleClosedCenterOne_ne_centerTwo :
    triangleClosedCenterOne ≠ triangleClosedCenterTwo := by
  intro h
  exact centerOne_coe_ne_centerTwo (OnePoint.coe_injective (congrArg Subtype.val h))

@[simp] theorem triangleClosedCenterOne_ne_infty :
    triangleClosedCenterOne ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty (centerOne : ℂ) (congrArg Subtype.val h)

@[simp] theorem triangleClosedCenterTwo_ne_infty :
    triangleClosedCenterTwo ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty (centerTwo : ℂ) (congrArg Subtype.val h)

/-- The entire ambient frontier consists of infinity and the five proved
finite pieces, with the finite coordinates unchanged. -/
theorem mem_triangleOnePoint_frontier_iff {x : OnePoint ℂ} :
    x ∈ frontier (onePointDomain triangleInterior) ↔
      x = ∞ ∨ x ∈ onePointDomain triangleOpenLeftSide ∨
        x ∈ onePointDomain triangleOpenRightSide ∨ x ∈ onePointDomain triangleOpenCircleSide ∨
          x = ((centerOne : ℂ) : OnePoint ℂ) ∨ x = ((centerTwo : ℂ) : OnePoint ℂ) := by
  induction x using OnePoint.rec with
  | infty => exact iff_of_true triangle_infty_mem_frontier (Or.inl rfl)
  | coe z =>
    simpa only [coe_mem_triangleOnePoint_frontier_iff, OnePoint.coe_ne_infty, false_or,
      coe_mem_onePointDomain, OnePoint.coe_eq_coe] using
      (mem_frontier_triangleInterior_iff (z := z))

/-- The same classification on the actual compact-source subtype. -/
theorem triangleClosedBoundary_iff_cases (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔
      x = triangleClosedInfinity ∨ x.val ∈ onePointDomain triangleOpenLeftSide ∨
        x.val ∈ onePointDomain triangleOpenRightSide ∨
          x.val ∈ onePointDomain triangleOpenCircleSide ∨
            x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  rw [triangleClosedBoundary_iff_frontier]
  simpa only [Subtype.ext_iff, triangleClosedInfinity,
    triangleClosedCenterOne_val, triangleClosedCenterTwo_val] using
    (mem_triangleOnePoint_frontier_iff (x := x.val))

/-- Every actual boundary point is an ideal or elliptic vertex, or has
an explicit finite coordinate on one of the three open sides. -/
theorem triangleClosedBoundary_cases (x : TriangleClosedDomain)
    (hx : x ∉ triangleClosedInterior) :
    x = triangleClosedInfinity ∨
      (∃ z : ℂ, z ∈ triangleOpenLeftSide ∧ x.val = (z : OnePoint ℂ)) ∨
      (∃ z : ℂ, z ∈ triangleOpenRightSide ∧ x.val = (z : OnePoint ℂ)) ∨
      (∃ z : ℂ, z ∈ triangleOpenCircleSide ∧ x.val = (z : OnePoint ℂ)) ∨
      x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  rcases (triangleClosedBoundary_iff_cases x).mp hx with hi | hL | hR | hC | h₁ | h₂
  · exact Or.inl hi
  · obtain ⟨z, hz, he⟩ := hL
    exact Or.inr (Or.inl ⟨z, hz, he.symm⟩)
  · obtain ⟨z, hz, he⟩ := hR
    exact Or.inr (Or.inr (Or.inl ⟨z, hz, he.symm⟩))
  · obtain ⟨z, hz, he⟩ := hC
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨z, hz, he.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂))))

/-- Every point of the concrete closed source is either in its original
open interior or in one of the boundary pieces classified above. -/
theorem triangleClosedDomain_cases (x : TriangleClosedDomain) :
    x ∈ triangleClosedInterior ∨ x = triangleClosedInfinity ∨
      x.val ∈ onePointDomain triangleOpenLeftSide ∨
        x.val ∈ onePointDomain triangleOpenRightSide ∨
          x.val ∈ onePointDomain triangleOpenCircleSide ∨
            x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  classical
  by_cases hx : x ∈ triangleClosedInterior
  · exact Or.inl hx
  · exact Or.inr ((triangleClosedBoundary_iff_cases x).mp hx)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
