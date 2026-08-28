import Wikipedia.HopfProblem.ToricTranslations

/-!
# The actual central symmetry of the cusp fan

Negating the two horizontal coordinates carries a lower triangle to the
opposite upper triangle.  Reversing the three affine coordinates makes this
symmetry compatible with the original Laurent chart changes, including their
domains on the boundary.  These identities concern the fan of the full cusp
filling and do not require shrinking its base disc.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspNegation

open ToricCharts ToricFan Triangle

/-- Central symmetry of the horizontal integral triangulation. -/
def triangleNeg (s : Triangle) : Triangle :=
  ⟨-s.a - 1, -s.b - 1, !s.upper⟩

/-- Reversal of the ray order, exchanging coordinates zero and two. -/
def permute (z : CoordinateSpace 3) : CoordinateSpace 3 :=
  fun j => z j.rev

theorem triangleNeg_involutive : Function.Involutive triangleNeg := by
  intro s
  ext <;> simp [triangleNeg]

theorem permute_involutive : Function.Involutive permute := by
  intro z
  funext j
  simp [permute]

theorem permute_holomorphic : ContDiff ℂ ω permute :=
  contDiff_pi.mpr fun j => contDiff_apply ℂ ℂ j.rev

theorem time_permute (z : CoordinateSpace 3) : time (permute z) = time z := by
  simp [time, permute, Fin.rev]
  ring

theorem triangleNeg_shift (s : Triangle) (v : Fin 2 → ℤ) :
    triangleNeg (s.shift v) = (triangleNeg s).shift (-v) := by
  ext <;> simp [triangleNeg, shift] <;> ring

theorem transition_triangleNeg (s t : Triangle) (i j : Fin 3) :
    transition (triangleNeg s) (triangleNeg t) i j = transition s t i.rev j.rev := by
  cases hs : s.upper <;> cases ht : t.upper <;> fin_cases i <;> fin_cases j <;>
    simp [transition, dual, rays, triangleNeg, hs, ht, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.rev] <;> ring

theorem chartChange_triangleNeg_source_iff (s t : Triangle) (z : CoordinateSpace 3) :
    permute z ∈ (chartChange (triangleNeg s) (triangleNeg t)).source ↔
      z ∈ (chartChange s t).source := by
  simp only [chartChange_source]
  constructor
  · intro h i j hij
    have hneg : transition (triangleNeg s) (triangleNeg t) i.rev j.rev < 0 := by
      simpa only [transition_triangleNeg, Fin.rev_rev] using hij
    simpa only [permute, Fin.rev_rev] using h i.rev j.rev hneg
  · intro h i j hij
    exact h i.rev j.rev (by simpa only [transition_triangleNeg] using hij)

theorem chartChange_triangleNeg_apply (s t : Triangle) (z : CoordinateSpace 3) :
    chartChange (triangleNeg s) (triangleNeg t) (permute z) =
      permute (chartChange s t z) := by
  funext i
  change (∏ j, z j.rev ^ transition (triangleNeg s) (triangleNeg t) i j) =
    ∏ j, z j ^ transition s t i.rev j
  simp only [transition_triangleNeg]
  simp [Fin.prod_univ_succ, Fin.rev, mul_comm, mul_left_comm, mul_assoc]

end Wikipedia.HopfProblem.CuspNegation
