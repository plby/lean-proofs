import ErdosProblems.Erdos19.DilutedArithmetic

/-! # The diluted collision mean on the neighborhood product space -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem dilutedTentative_average_lower_bound {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} [Nonempty (Fin A × Fin C)]
    (active : Fin A) (v : V) (hC : 0 < C)
    (hdegree : 2 ≤ (G.neighborSet v).ncard)
    (hpalette : 2 * (G.neighborSet v).ncard ≤ A * C) :
    ((nonadjacentNeighborPairGraph G v).edgeSet.ncard : ℝ) / (2 * (A : ℝ) ^ 2 * C) ≤
      finiteAverage (fun sample : V → Fin A × Fin C ↦
        ((tentativeCollisionColors G (dilutedSample active sample) v).ncard : ℝ)) := by
  classical
  have hAR : (0 : ℝ) < A := by exact_mod_cast Nat.zero_lt_of_lt active.isLt
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hq : (0 : ℝ) < Fintype.card (V → Fin A × Fin C) := by exact_mod_cast Fintype.card_pos
  have h := dilutedTentative_expectation_scaled G active v hC hdegree hpalette
  have hR : (C : ℝ) * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
      Fintype.card (V → Fin A × Fin C) ≤ 2 * ((A : ℝ) * C) ^ 2 *
        ∑ sample : V → Fin A × Fin C,
          ((tentativeCollisionColors G (dilutedSample active sample) v).ncard : ℝ) := by
    exact_mod_cast h
  unfold finiteAverage
  apply (div_le_div_iff₀ (by positivity) hq).mpr
  apply (mul_le_mul_iff_right₀ hCR).mp
  nlinarith only [hR]

theorem dilutedTentativeFinStatistic_finiteAverage_eq
    {V : Type*} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    {A C : ℕ} [Nonempty (Fin A × Fin C)] (active : Fin A)
    (v : V) [Fintype (G.neighborSet v)] (default : Fin A × Fin C) :
    finiteAverage (fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ)) =
      finiteAverage (fun sample : V → Fin A × Fin C ↦
        ((tentativeCollisionColors G (dilutedSample active sample) v).ncard : ℝ)) := by
  classical
  let S := G.neighborFinset v
  let e := Fintype.equivFin S
  let assignmentEquiv : (S → Fin A × Fin C) ≃
      (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) :=
    { toFun := fun g i ↦ g (e.symm i)
      invFun := fun z x ↦ z (e x)
      left_inv := fun g ↦ by funext x; simp
      right_inv := fun z ↦ by funext i; simp }
  let X : (S → Fin A × Fin C) → ℕ := fun g ↦
    dilutedTentativeFinStatistic G active v default (assignmentEquiv g)
  have hrestrict := finiteAverage_eq_of_restriction S X
  calc
    finiteAverage (fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ)) =
        finiteAverage (fun g : S → Fin A × Fin C ↦ (X g : ℝ)) := by
      symm
      simpa only [X] using finiteAverage_comp_equiv assignmentEquiv
        (fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ))
    _ = (∑ sample : V → Fin A × Fin C, (X (fun x : S ↦ sample x.1) : ℝ)) /
        Fintype.card (V → Fin A × Fin C) := hrestrict
    _ = _ := by
      unfold finiteAverage
      congr 1
      apply Finset.sum_congr rfl
      intro sample _
      change (dilutedTentativeFinStatistic G active v default
        (fun i ↦ sample (e.symm i).1) : ℝ) = _
      rw [dilutedTentativeFinStatistic_restrict]

#print axioms dilutedTentative_average_lower_bound
#print axioms dilutedTentativeFinStatistic_finiteAverage_eq

end Erdos19
