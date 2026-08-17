import ErdosProblems.Erdos113.Conflict

open scoped Real SimpleGraph BigOperators

namespace Lower

noncomputable def walkMass {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (x : W) : ℝ :=
  ∑ y : W, (Conflict.walkCount A m x y : ℝ)

lemma walkMass_eq_matrix_sum {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (x : W) :
    walkMass A m x = ∑ y : W, (A.adjMatrix ℝ ^ m) x y := by
  unfold walkMass
  apply Finset.sum_congr rfl
  intro y _
  rw [A.adjMatrix_pow_apply_eq_card_walk]
  rfl

@[simp] lemma walkMass_zero {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (x : W) :
    walkMass A 0 x = 1 := by
  rw [walkMass_eq_matrix_sum]
  simp [Matrix.one_apply]

lemma walkMass_succ {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (x : W) :
    walkMass A (m + 1) x = ∑ y ∈ A.neighborFinset x, walkMass A m y := by
  classical
  rw [walkMass_eq_matrix_sum]
  simp_rw [pow_succ']
  simp only [Matrix.mul_apply]
  calc
    (∑ z, ∑ y, A.adjMatrix ℝ x y * (A.adjMatrix ℝ ^ m) y z) =
        ∑ y, ∑ z, A.adjMatrix ℝ x y * (A.adjMatrix ℝ ^ m) y z :=
      Finset.sum_comm
    _ = ∑ y, if A.Adj x y then walkMass A m y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, ← walkMass_eq_matrix_sum]
      simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> simp
    _ = ∑ y ∈ A.neighborFinset x, walkMass A m y := by
      rw [← Finset.sum_filter]
      congr 1
      ext y
      simp

lemma walkMass_lower {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (d : ℝ)
    (hd : 0 ≤ d) (hdeg : ∀ x, d ≤ (A.degree x : ℝ)) (m : ℕ) (x : W) :
    d ^ m ≤ walkMass A m x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, pow_succ, walkMass_succ]
      calc
        d ^ m * d ≤ d ^ m * (A.degree x : ℝ) := by
          apply mul_le_mul_of_nonneg_left (hdeg x)
          positivity
        _ = ∑ _y ∈ A.neighborFinset x, d ^ m := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
          ring
        _ ≤ ∑ y ∈ A.neighborFinset x, walkMass A m y := by
          apply Finset.sum_le_sum
          intro y _
          exact ih y

lemma walkMass_upper {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (D : ℝ)
    (hD : 0 ≤ D) (hdeg : ∀ x, (A.degree x : ℝ) ≤ D) (m : ℕ) (x : W) :
    walkMass A m x ≤ D ^ m := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, pow_succ, walkMass_succ]
      calc
        (∑ y ∈ A.neighborFinset x, walkMass A m y) ≤
            ∑ _y ∈ A.neighborFinset x, D ^ m := by
          apply Finset.sum_le_sum
          intro y _
          exact ih y
        _ = D ^ m * (A.degree x : ℝ) := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
          ring
        _ ≤ D ^ m * D := by
          apply mul_le_mul_of_nonneg_left (hdeg x)
          positivity

lemma closedWalkCount_lower_of_minDegree {W : Type*} [Fintype W]
    [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (d : ℝ)
    (hd : 0 ≤ d) (hdeg : ∀ x, d ≤ (A.degree x : ℝ)) (m : ℕ) :
    d ^ (2 * m) ≤ (Conflict.closedWalkCount A (2 * m) : ℝ) := by
  let n : ℝ := Fintype.card W
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hmass_nonneg (x : W) : 0 ≤ walkMass A m x := by
    unfold walkMass
    positivity
  have hmass (x : W) : d ^ m ≤ walkMass A m x :=
    walkMass_lower A d hd hdeg m x
  have hsumlower : n * d ^ (2 * m) ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
    rw [show d ^ (2 * m) = (d ^ m) ^ 2 by ring]
    calc
      n * (d ^ m) ^ 2 = ∑ _x : W, (d ^ m) ^ 2 := by
        simp [n]
      _ ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact (sq_le_sq₀ (by positivity) (hmass_nonneg x)).2 (hmass x)
  have hcs : (∑ x : W, (walkMass A m x) ^ 2) ≤
      n * (Conflict.closedWalkCount A (2 * m) : ℝ) := by
    rw [Conflict.closedWalkCount_cast_eq_sum_walkCount_sq]
    calc
      (∑ x : W, (walkMass A m x) ^ 2) ≤
          ∑ x : W, n * ∑ y : W, (Conflict.walkCount A m x y : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [walkMass, n, Finset.card_univ, Nat.cast_ofNat] using
          (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset W))
            (f := fun y ↦ (Conflict.walkCount A m x y : ℝ)))
      _ = n * ∑ x : W, ∑ y : W,
          (Conflict.walkCount A m x y : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
  have hmul : n * d ^ (2 * m) ≤
      n * (Conflict.closedWalkCount A (2 * m) : ℝ) := hsumlower.trans hcs
  exact (mul_le_mul_iff_right₀ hn).mp hmul

end Lower
