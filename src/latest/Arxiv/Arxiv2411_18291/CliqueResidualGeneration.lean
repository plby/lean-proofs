import Arxiv.Arxiv2411_18291.IntegralSpan

/-!
# Generating supported vectors from clique residuals

Assign an arbitrary reference vector to each edge outside a target graph.
If each clique boundary minus its outside-edge references is generated,
then every integral boundary supported on the target graph is generated.
The references cancel by double counting, so no pairing of signed copies
or bound on their coefficients is required.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem sum_clique_edge_weights (Φ : Block V q → ℤ) (w : Block V r → ℤ) :
    (∑ Q : Block V q, Φ Q * ∑ e ∈ cliqueEdges r Q, w e) =
      ∑ e : Block V r, boundary r Φ e * w e := by
  simp only [cliqueEdges, sum_filter, mul_sum, mul_ite, mul_zero, boundary, sum_mul, ite_mul,
    zero_mul]
  rw [sum_comm]

theorem generatedBy_of_clique_residuals (D : Finset (Block V q)) (E : Hypergraph V r)
    (w : Block V r → Block V r → ℤ)
    (hres : ∀ Q : Block V q, GeneratedBy D
      (indicator (cliqueEdges r Q) - ∑ e ∈ cliqueEdges r Q, if e ∈ E then 0 else w e))
    (J : Block V r → ℤ) (hJ : IntegrallyDecomposable q J)
    (hsupport : ∀ e, e ∉ E → J e = 0) : GeneratedBy D J := by
  classical
  obtain ⟨Φ, hΦ⟩ := hJ
  have hgen := GeneratedBy.sum univ
    (fun Q : Block V q => fun f => Φ Q *
      (indicator (cliqueEdges r Q) - ∑ e ∈ cliqueEdges r Q, if e ∈ E then 0 else w e) f)
    (fun Q _ => (hres Q).mul (Φ Q))
  have heq : (∑ Q : Block V q, fun f => Φ Q *
      (indicator (cliqueEdges r Q) - ∑ e ∈ cliqueEdges r Q, if e ∈ E then 0 else w e) f) = J := by
    funext f
    simp only [Finset.sum_apply, Pi.sub_apply, ite_apply, Pi.zero_apply, mul_sub]
    rw [sum_sub_distrib]
    have hfirst : (∑ Q : Block V q, Φ Q * indicator (cliqueEdges r Q) f) = boundary r Φ f := by
      simp only [indicator, mem_cliqueEdges, mul_ite, mul_one, mul_zero, boundary]
    rw [hfirst, sum_clique_edge_weights, hΦ]
    have hzero : (∑ e : Block V r, J e * (if e ∈ E then 0 else w e f)) = 0 := by
      apply sum_eq_zero
      intro e _
      by_cases he : e ∈ E
      · rw [if_pos he, mul_zero]
      · rw [if_neg he, hsupport e he, zero_mul]
    rw [hzero, sub_zero]
  exact heq ▸ hgen

end Arxiv2411_18291
