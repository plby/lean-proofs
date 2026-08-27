import Arxiv.Arxiv2411_18291.ModularIntegralLift

/-!
# Substituting integral generators

Replacing each supporting clique by an integer combination of a new family
preserves every generated vector, with no bound on its coefficients.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem GeneratedBy.trans {D F : Finset (Block V q)} {J : Block V r → ℤ}
    (hJ : GeneratedBy D J)
    (hD : ∀ Q ∈ D, GeneratedBy F (indicator (cliqueEdges r Q))) : GeneratedBy F J := by
  obtain ⟨Φ, rfl, hsΦ⟩ := hJ
  rw [boundary_eq_sum_zsmul]
  apply GeneratedBy.sum
  intro Q _
  by_cases hQ : Q ∈ D
  · convert (hD Q hQ).mul (Φ Q) using 1
    funext e
    simp only [zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_id]
  · rw [hsΦ Q hQ, zero_zsmul]
    exact GeneratedBy.zero F

end Arxiv2411_18291
