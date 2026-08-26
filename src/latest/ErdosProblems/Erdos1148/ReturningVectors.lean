import ErdosProblems.Erdos1148.NearbyGaussParameters
import ErdosProblems.Erdos1148.LatticeVectorAction

/-! # Returning lattice vectors and integral changes of representatives -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def HasReturningVector (S c : ℝ) (g : SL(2, ℝ)) : Prop :=
  ∃ q : ℤ × ℤ, c ≤ modularVectorLengthSq g q.1 q.2 ∧
    modularVectorLengthSq g q.1 q.2 ≤ 1 ∧
      modularVectorLengthSq (g * diagonalFlow S) q.1 q.2 ≤ 1

theorem HasReturningVector.integral_mul {S c : ℝ} {g : SL(2, ℝ)}
    (hg : HasReturningVector S c g) (γ : SL(2, ℤ)) :
    HasReturningVector S c ((γ : SL(2, ℝ)) * g) := by
  obtain ⟨q, hlow, hstart, hend⟩ := hg
  refine ⟨(γ.toLin' ![q.1, q.2] 0, γ.toLin' ![q.1, q.2] 1), ?_, ?_, ?_⟩
  · simpa only [modularVectorLengthSq, modularVector_integral_change] using hlow
  · simpa only [modularVectorLengthSq, modularVector_integral_change] using hstart
  · simpa only [mul_assoc, modularVectorLengthSq, modularVector_integral_change] using hend

theorem exists_returningGaussParameters_of_close {η S c : ℝ} (hη : η ≤ 1 / 2)
    (g h : SL(2, ℝ)) (hclose : EntryCloseOne η (g⁻¹ * h))
    (hreturn : HasReturningVector S c h) :
    ∃ p ∈ ReturningGaussParameters g S c, gaussParameterFrame g p = h := by
  obtain ⟨p, hp⟩ := exists_boundedGaussParameters_of_close hη g h hclose
  refine ⟨p, ?_, hp⟩
  change HasReturningVector S c (gaussParameterFrame g p)
  rwa [hp]

end Erdos1148.DukeArithmetic
