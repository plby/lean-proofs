import ErdosProblems.Erdos113.Moments

open scoped Real SimpleGraph BigOperators

namespace Erdos113LowerBipartite

open Conflict Lower

def alternatingProduct (d : Bool → ℝ) : Bool → ℕ → ℝ
  | _b, 0 => 1
  | b, m + 1 => d b * alternatingProduct d (!b) m

lemma alternatingProduct_nonneg (d : Bool → ℝ) (hd : ∀ b, 0 ≤ d b)
    (b : Bool) (m : ℕ) : 0 ≤ alternatingProduct d b m := by
  induction m generalizing b with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [alternatingProduct]
      exact mul_nonneg (hd b) (ih (!b))

lemma alternatingProduct_even (d : Bool → ℝ) (b : Bool) (m : ℕ) :
    alternatingProduct d b (2 * m) = (d b * d (!b)) ^ m := by
  induction m with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
        alternatingProduct, alternatingProduct]
      simp only [Bool.not_not]
      rw [ih, pow_succ]
      ring

lemma walkMass_lower_bipartite {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (d : Bool → ℝ)
    (hd : ∀ b, 0 ≤ d b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdeg : ∀ x, d (side x) ≤ (A.degree x : ℝ))
    (m : ℕ) (x : W) :
    alternatingProduct d (side x) m ≤ walkMass A m x := by
  induction m generalizing x with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, alternatingProduct, walkMass_succ]
      calc
        d (side x) * alternatingProduct d (!side x) m ≤
            (A.degree x : ℝ) * alternatingProduct d (!side x) m := by
          exact mul_le_mul_of_nonneg_right (hdeg x)
            (alternatingProduct_nonneg d hd (!side x) m)
        _ = ∑ _y ∈ A.neighborFinset x,
              alternatingProduct d (!side x) m := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ ∑ y ∈ A.neighborFinset x, walkMass A m y := by
          apply Finset.sum_le_sum
          intro y hy
          have hadj : A.Adj x y := (A.mem_neighborFinset x y).mp hy
          simpa [hcross hadj] using ih y

/-- The matching two-sided upper bound for walk mass. -/
lemma walkMass_upper_bipartite {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (D : Bool → ℝ)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdeg : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (m : ℕ) (x : W) :
    walkMass A m x ≤ alternatingProduct D (side x) m := by
  induction m generalizing x with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, alternatingProduct, walkMass_succ]
      calc
        (∑ y ∈ A.neighborFinset x, walkMass A m y) ≤
            ∑ _y ∈ A.neighborFinset x,
              alternatingProduct D (!side x) m := by
          apply Finset.sum_le_sum
          intro y hy
          have hadj : A.Adj x y := (A.mem_neighborFinset x y).mp hy
          simpa [hcross hadj] using ih y
        _ = (A.degree x : ℝ) * alternatingProduct D (!side x) m := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ D (side x) * alternatingProduct D (!side x) m := by
          exact mul_le_mul_of_nonneg_right (hdeg x)
            (alternatingProduct_nonneg D hD (!side x) m)

lemma alternatingProduct_odd (D : Bool → ℝ) (b : Bool) (m : ℕ) :
    alternatingProduct D b (2 * m + 1) =
      D b ^ (m + 1) * D (!b) ^ m := by
  rw [show 2 * m + 1 = (2 * m) + 1 by omega, alternatingProduct,
    alternatingProduct_even]
  cases b <;> simp only [Bool.not_false, Bool.not_true]
  · rw [pow_succ]
    ring
  · rw [pow_succ]
    ring

lemma closedWalkCount_lower_of_walkMass {W : Type*} [Fintype W]
    [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (q : ℝ) (hq : 0 ≤ q)
    (m : ℕ) (hmass : ∀ x, q ≤ walkMass A m x) :
    q ^ 2 ≤ (closedWalkCount A (2 * m) : ℝ) := by
  let n : ℝ := Fintype.card W
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hmass_nonneg (x : W) : 0 ≤ walkMass A m x := by
    unfold walkMass
    positivity
  have hsumlower : n * q ^ 2 ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
    calc
      n * q ^ 2 = ∑ _x : W, q ^ 2 := by simp [n]
      _ ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact (sq_le_sq₀ hq (hmass_nonneg x)).2 (hmass x)
  have hcs : (∑ x : W, (walkMass A m x) ^ 2) ≤
      n * (closedWalkCount A (2 * m) : ℝ) := by
    rw [closedWalkCount_cast_eq_sum_walkCount_sq]
    calc
      (∑ x : W, (walkMass A m x) ^ 2) ≤
          ∑ x : W, n * ∑ y : W, (walkCount A m x y : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [walkMass, n, Finset.card_univ, Nat.cast_ofNat] using
          (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset W))
            (f := fun y ↦ (walkCount A m x y : ℝ)))
      _ = n * ∑ x : W, ∑ y : W, (walkCount A m x y : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
  exact (mul_le_mul_iff_right₀ hn).mp (hsumlower.trans hcs)

lemma closedWalkCount_1568_lower_bipartite {W : Type*} [Fintype W]
    [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (d : Bool → ℝ)
    (hd : ∀ b, 0 ≤ d b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdeg : ∀ x, d (side x) ≤ (A.degree x : ℝ)) :
    (d false * d true) ^ 784 ≤ (closedWalkCount A 1568 : ℝ) := by
  let q := (d false * d true) ^ 392
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hmass (x : W) : q ≤ walkMass A 784 x := by
    have h := walkMass_lower_bipartite A side d hd hcross hdeg 784 x
    rw [show 784 = 2 * 392 by norm_num, alternatingProduct_even] at h
    cases hx : side x <;> simpa [q, hx, mul_comm] using h
  have h := closedWalkCount_lower_of_walkMass A q hq 784 hmass
  rw [show 2 * 784 = 1568 by norm_num] at h
  calc
    (d false * d true) ^ 784 = q ^ 2 := by dsimp [q]; ring
    _ ≤ (closedWalkCount A 1568 : ℝ) := h

end Erdos113LowerBipartite
