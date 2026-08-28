import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesFibre

/-!
# The coordinate branch orderings at the actual triple points

At `P` the source orders its branches as `(b₁,b₂,b₃)`. At `Q` the order
giving the same alternating differential is `(c₁,c₃,c₂)`, with the source
curve list reversed. These finite tables concern the actual translated
chart origins and the actual lift coordinates proved in the preceding files.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan ToricSpace ToricComponent Triangle NormalizationCurves
open CuspNormalization.Germs

/-- The source vertex reached by each translated coordinate-plane origin. -/
def originBranchVertexIndex (s : Triangle) (j : Fin 3) : Fin 6 :=
  if s.upper then ![4, 0, 2] j else ![5, 3, 1] j

theorem shiftedTriangle_origin (s : Triangle) (j : Fin 3) :
    s.shift (-s.vertex j) = sourceTriangle (originBranchVertexIndex s j) := by
  rcases s with ⟨a, b, u⟩
  cases u <;> fin_cases j <;> ext <;>
    simp [originBranchVertexIndex, shift, vertex, rays, sourceTriangle,
      sourceTriangleIndex, zeroTriangle]

/-- The coordinate-plane centres are the literal six source toric vertices. -/
theorem branchAffine_zero_sourceVertex (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    branchAffine C s j 0 = sourceVertex (originBranchVertexIndex s j) := by
  apply Subtype.ext
  rw [branchAffine_coe, insertZero_zero, twistedTranslate_origin, cuspVector_cuspVector,
    shiftedTriangle_origin]
  rfl

/-- The coordinates of the source branch order `(b₁,b₂,b₃)` at `P`. -/
def pBranchLabel : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The coordinates of the source order `(c₁,c₃,c₂)` used for the Čech
differential at `Q`. -/
def qBranchLabel : Fin 3 → Fin 3 := ![2, 0, 1]

theorem pBranchLabel_bijective : Function.Bijective pBranchLabel := by decide

theorem qBranchLabel_bijective : Function.Bijective qBranchLabel := by decide

theorem pBranchLabel_sourceVertex (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (hs : s.upper = true) (j : Fin 3) :
    branchAffine C s (pBranchLabel j) 0 = sourceVertex (![0, 2, 4] j) := by
  rw [branchAffine_zero_sourceVertex]
  congr 1
  fin_cases j <;> simp [originBranchVertexIndex, hs, pBranchLabel]

theorem qBranchLabel_sourceVertex (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (hs : s.upper = false) (j : Fin 3) :
    branchAffine C s (qBranchLabel j) 0 = sourceVertex (![1, 5, 3] j) := by
  rw [branchAffine_zero_sourceVertex]
  congr 1
  fin_cases j <;> simp [originBranchVertexIndex, hs, qBranchLabel]

theorem plusBranch_upper (s : Triangle) (hs : s.upper = true) (k : Fin 3) :
    plusBranch s k = ![1, 1, 2] k := by
  fin_cases k <;> simp [plusBranch, sourceEdgeIndex, edgeStart, edgeEnd, hs]

theorem minusBranch_upper (s : Triangle) (hs : s.upper = true) (k : Fin 3) :
    minusBranch s k = ![2, 0, 0] k := by
  fin_cases k <;> simp [minusBranch, sourceEdgeIndex, edgeStart, edgeEnd, hs]

theorem plusBranch_lower (s : Triangle) (hs : s.upper = false) (k : Fin 3) :
    plusBranch s k = ![0, 2, 2] k := by
  fin_cases k <;> simp [plusBranch, sourceEdgeIndex, edgeStart, edgeEnd, hs]

theorem minusBranch_lower (s : Triangle) (hs : s.upper = false) (k : Fin 3) :
    minusBranch s k = ![1, 1, 0] k := by
  fin_cases k <;> simp [minusBranch, sourceEdgeIndex, edgeStart, edgeEnd, hs]

theorem plusBranch_upper_order (s : Triangle) (hs : s.upper = true) (k : Fin 3) :
    plusBranch s k = pBranchLabel (![0, 0, 1] k) := by
  rw [plusBranch_upper s hs]
  fin_cases k <;> rfl

theorem minusBranch_upper_order (s : Triangle) (hs : s.upper = true) (k : Fin 3) :
    minusBranch s k = pBranchLabel (![1, 2, 2] k) := by
  rw [minusBranch_upper s hs]
  fin_cases k <;> rfl

theorem plusBranch_lower_order (s : Triangle) (hs : s.upper = false) (k : Fin 3) :
    plusBranch s k = qBranchLabel (![0, 0, 1] k.rev) := by
  rw [plusBranch_lower s hs]
  fin_cases k <;> rfl

theorem minusBranch_lower_order (s : Triangle) (hs : s.upper = false) (k : Fin 3) :
    minusBranch s k = qBranchLabel (![1, 2, 2] k.rev) := by
  rw [minusBranch_lower s hs]
  fin_cases k <;> rfl

theorem plusAxisIndex_upper (s : Triangle) (hs : s.upper = true) (k : Fin 3) :
    plusAxisIndex s k = ![0, 1, 1] k := by
  apply (Fin.succAbove_right_injective (p := plusBranch s k))
  rw [show (plusBranch s k).succAbove (plusAxisIndex s k) =
    s.axisIndex (sourceEdgeIndex k) from succAbove_branchAxisIndex _ _ _]
  rw [plusBranch_upper s hs]
  fin_cases k <;> simp [axisIndex, sourceEdgeIndex, hs, Fin.succAbove]

theorem minusAxisIndex_upper (s : Triangle) (hs : s.upper = true) (k : Fin 3) :
    minusAxisIndex s k = ![0, 1, 0] k := by
  apply (Fin.succAbove_right_injective (p := minusBranch s k))
  rw [show (minusBranch s k).succAbove (minusAxisIndex s k) =
    s.axisIndex (sourceEdgeIndex k) from succAbove_branchAxisIndex _ _ _]
  rw [minusBranch_upper s hs]
  fin_cases k <;> simp [axisIndex, sourceEdgeIndex, hs, Fin.succAbove]

theorem plusAxisIndex_lower (s : Triangle) (hs : s.upper = false) (k : Fin 3) :
    plusAxisIndex s k = ![1, 0, 1] k := by
  apply (Fin.succAbove_right_injective (p := plusBranch s k))
  rw [show (plusBranch s k).succAbove (plusAxisIndex s k) =
    s.axisIndex (sourceEdgeIndex k) from succAbove_branchAxisIndex _ _ _]
  rw [plusBranch_lower s hs]
  fin_cases k <;> simp [axisIndex, sourceEdgeIndex, hs, Fin.succAbove]

theorem minusAxisIndex_lower (s : Triangle) (hs : s.upper = false) (k : Fin 3) :
    minusAxisIndex s k = ![1, 0, 0] k := by
  apply (Fin.succAbove_right_injective (p := minusBranch s k))
  rw [show (minusBranch s k).succAbove (minusAxisIndex s k) =
    s.axisIndex (sourceEdgeIndex k) from succAbove_branchAxisIndex _ _ _]
  rw [minusBranch_lower s hs]
  fin_cases k <;> simp [axisIndex, sourceEdgeIndex, hs, Fin.succAbove]

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
