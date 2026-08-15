import Mathlib

open scoped BigOperators Topology

namespace QApery

noncomputable section

/-- The specialization `q = 1/2`. -/
def q : ℝ := 1 / 2

/-- The finite `q`-Pochhammer symbol. -/
def qPochhammer (a : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (1 - a * q ^ j)

/-- Nesterenko--Duverney rational function specialized at `q = 1/2`.
The use of powers of `2` avoids integer exponents in Lean. -/
def R (n : ℕ) (T : ℝ) : ℝ :=
  T ^ n *
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * T)) *
    (∏ j ∈ Finset.range (n + 1), (1 - T / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)

def term (n l : ℕ) : ℝ := q ^ l * R n (q ^ l)

lemma q_pos : 0 < q := by norm_num [q]
lemma q_lt_one : q < 1 := by norm_num [q]

lemma pow_two_mul_q_pow (k : ℕ) :
    (2 : ℝ) ^ k * q ^ k = 1 := by
  rw [← mul_pow]
  norm_num [q]

lemma numerator_zero {n l : ℕ} (hl : l < n) :
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) = 0 := by
  let j := n - 1 - l
  have hj : j < n := by omega
  have hexp : n - 1 - j = l := by
    dsimp [j]
    omega
  apply Finset.prod_eq_zero (Finset.mem_range.2 hj)
  rw [hexp, pow_two_mul_q_pow]
  norm_num

lemma R_pow_zero {n l : ℕ} (hl : l < n) : R n (q ^ l) = 0 := by
  simp [R, numerator_zero hl]

lemma term_zero {n l : ℕ} (hl : l < n) : term n l = 0 := by
  simp [term, R_pow_zero hl]

lemma numerator_factor_pos {n l j : ℕ} (_hn : 1 ≤ n) (hnl : n ≤ l) (hj : j < n) :
    0 < 1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l := by
  have he : n - 1 - j < l := by omega
  have hp : (2 : ℝ) ^ (n - 1 - j) < 2 ^ l :=
    pow_lt_pow_right₀ (by norm_num) he
  rw [show q ^ l = 1 / (2 : ℝ) ^ l by simp [q]]
  rw [sub_pos, mul_one_div]
  exact (div_lt_one (by positivity)).2 hp

lemma numerator_prod_pos {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    0 < ∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l) := by
  exact Finset.prod_pos fun j hj ↦
    numerator_factor_pos hn hnl (Finset.mem_range.1 hj)

lemma denominator_factor_pos {l j : ℕ} :
    0 < 1 - q ^ l / (2 : ℝ) ^ (j + 1) := by
  rw [sub_pos]
  have hq : q ^ l ≤ 1 := (pow_le_one₀ (le_of_lt q_pos) (le_of_lt q_lt_one))
  have ht : (1 : ℝ) < 2 ^ (j + 1) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  exact (div_lt_one (by positivity)).2 (hq.trans_lt ht)

lemma denominator_ratio_eq (l j : ℕ) :
    q ^ l / (2 : ℝ) ^ (j + 1) = 1 / (2 : ℝ) ^ (l + j + 1) := by
  rw [show q ^ l = 1 / (2 : ℝ) ^ l by simp [q]]
  rw [div_div, ← pow_add]
  congr 2

lemma denominator_factor_ge_three_quarters {n l j : ℕ}
    (hn : 1 ≤ n) (hnl : n ≤ l) :
    (3 : ℝ) / 4 ≤ 1 - q ^ l / (2 : ℝ) ^ (j + 1) := by
  have hexp : 2 ≤ l + j + 1 := by omega
  have hratio : q ^ l / (2 : ℝ) ^ (j + 1) ≤ (1 : ℝ) / 2 ^ 2 := by
    rw [denominator_ratio_eq]
    exact one_div_pow_le_one_div_pow_of_le (by norm_num) hexp
  norm_num at hratio ⊢
  linarith

lemma denominator_inv_sq_le {n l j : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2 ≤ ((4 : ℝ) / 3) ^ 2 := by
  have hpos := denominator_factor_pos (l := l) (j := j)
  have hge := denominator_factor_ge_three_quarters (j := j) hn hnl
  have hinv : (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ≤ (4 : ℝ) / 3 := by
    have := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3 / 4)).2 hge
    norm_num at this ⊢
    exact this
  exact pow_le_pow_left₀ (le_of_lt (inv_pos.2 hpos)) hinv _

lemma denominator_prod_le {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    (∏ j ∈ Finset.range (n + 1),
        (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)
      ≤ ((4 : ℝ) / 3) ^ (2 * n + 2) := by
  calc
    (∏ j ∈ Finset.range (n + 1),
        (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)
        ≤ ∏ _j ∈ Finset.range (n + 1), ((4 : ℝ) / 3) ^ 2 := by
          apply Finset.prod_le_prod
          · intro j hj
            positivity
          · intro j hj
            exact denominator_inv_sq_le hn hnl
    _ = (((4 : ℝ) / 3) ^ 2) ^ (n + 1) := by simp
    _ = ((4 : ℝ) / 3) ^ (2 * n + 2) := by
      rw [← pow_mul]
      congr 2

lemma numerator_prod_le_one {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    exact (numerator_factor_pos hn hnl (Finset.mem_range.1 hj)).le
  · intro j hj
    have : 0 ≤ (2 : ℝ) ^ (n - 1 - j) * q ^ l :=
      mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg q_pos.le _)
    linarith

lemma term_eq_products (n l : ℕ) : term n l =
    q ^ ((n + 1) * l) *
      (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) *
      (∏ j ∈ Finset.range (n + 1),
        (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2) := by
  unfold term R
  rw [← pow_mul]
  have hp : q ^ l * q ^ (l * n) = q ^ ((n + 1) * l) := by
    rw [← pow_add]
    congr 2
    simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]
  rw [← hp]
  ring

lemma term_le_geometric {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    term n l ≤ ((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * l) := by
  rw [term_eq_products]
  have hq0 : 0 ≤ q ^ ((n + 1) * l) := pow_nonneg q_pos.le _
  have hnum0 : 0 ≤ ∏ j ∈ Finset.range n,
      (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l) :=
    (numerator_prod_pos hn hnl).le
  have hden0 : 0 ≤ ∏ j ∈ Finset.range (n + 1),
      (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2 := by positivity
  have hnum := numerator_prod_le_one hn hnl
  have hden := denominator_prod_le hn hnl
  calc
    q ^ ((n + 1) * l) *
          (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) *
          (∏ j ∈ Finset.range (n + 1),
            (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)
        ≤ q ^ ((n + 1) * l) * 1 *
          (∏ j ∈ Finset.range (n + 1),
            (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hnum hq0) hden0
    _ ≤ q ^ ((n + 1) * l) * 1 * ((4 : ℝ) / 3) ^ (2 * n + 2) := by
          exact mul_le_mul_of_nonneg_left hden (mul_nonneg hq0 zero_le_one)
    _ = ((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * l) := by ring

lemma R_pow_pos {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    0 < R n (q ^ l) := by
  have hqpow : 0 < q ^ l := pow_pos q_pos _
  have hnum := numerator_prod_pos hn hnl
  have hden : 0 < ∏ j ∈ Finset.range (n + 1),
      (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2 := by
    exact Finset.prod_pos fun j hj ↦
      pow_pos (inv_pos.2 denominator_factor_pos) _
  exact mul_pos (mul_pos (pow_pos hqpow _) hnum) hden

lemma term_pos {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    0 < term n l := by
  exact mul_pos (pow_pos q_pos _) (R_pow_pos hn hnl)

lemma geom_ratio_nonneg (n : ℕ) : 0 ≤ q ^ (n + 1) := pow_nonneg q_pos.le _

lemma geom_ratio_lt_one (n : ℕ) : q ^ (n + 1) < 1 :=
  pow_lt_one₀ q_pos.le q_lt_one (by omega)

lemma summable_term {n : ℕ} (hn : 1 ≤ n) : Summable (term n) := by
  have hgeom : Summable (fun l : ℕ ↦
      ((4 : ℝ) / 3) ^ (2 * n + 2) * (q ^ (n + 1)) ^ l) :=
    Summable.mul_left _
      (summable_geometric_of_lt_one (geom_ratio_nonneg n) (geom_ratio_lt_one n))
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro l
    by_cases hl : l < n
    · rw [term_zero hl]
    · exact (term_pos hn (Nat.le_of_not_gt hl)).le
  · intro l
    by_cases hl : l < n
    · rw [term_zero hl]
      exact mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (geom_ratio_nonneg n) _)
    · simpa only [pow_mul] using term_le_geometric hn (Nat.le_of_not_gt hl)

/-- The positive q-Apéry remainder. -/
def S (n : ℕ) : ℝ := ∑' l : ℕ, term n l

lemma term_nonneg {n : ℕ} (hn : 1 ≤ n) (l : ℕ) : 0 ≤ term n l := by
  by_cases hl : l < n
  · rw [term_zero hl]
  · exact (term_pos hn (Nat.le_of_not_gt hl)).le

lemma S_pos {n : ℕ} (hn : 1 ≤ n) : 0 < S n := by
  exact (summable_term hn).tsum_pos (term_nonneg hn) n (term_pos hn le_rfl)

lemma S_eq_shift {n : ℕ} (hn : 1 ≤ n) :
    S n = ∑' k : ℕ, term n (n + k) := by
  unfold S
  rw [← (summable_term hn).sum_add_tsum_nat_add n]
  have hprefix : ∑ i ∈ Finset.range n, term n i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact term_zero (Finset.mem_range.1 hi)
  rw [hprefix, zero_add]
  congr 1
  funext k
  rw [Nat.add_comm]

def tailMajor (n k : ℕ) : ℝ :=
  ((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * (n + k))

lemma tailMajor_eq (n k : ℕ) : tailMajor n k =
    (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
      (q ^ (n + 1)) ^ k := by
  simp only [tailMajor, Nat.mul_add, pow_add, pow_mul]
  ring

lemma summable_tailMajor (n : ℕ) : Summable (tailMajor n) := by
  have hgeom := summable_geometric_of_lt_one (geom_ratio_nonneg n) (geom_ratio_lt_one n)
  exact (Summable.mul_left
    (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) hgeom).congr
      fun k ↦ (tailMajor_eq n k).symm

lemma tsum_tailMajor (n : ℕ) :
    ∑' k : ℕ, tailMajor n k =
      (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
        (1 - q ^ (n + 1))⁻¹ := by
  simp_rw [tailMajor_eq]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (geom_ratio_nonneg n) (geom_ratio_lt_one n)]

lemma geom_inv_le_four_thirds {n : ℕ} (hn : 1 ≤ n) :
    (1 - q ^ (n + 1))⁻¹ ≤ (4 : ℝ) / 3 := by
  have hpow : q ^ (n + 1) ≤ (1 : ℝ) / 2 ^ 2 := by
    rw [show q ^ (n + 1) = 1 / (2 : ℝ) ^ (n + 1) by simp [q]]
    exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
  have hsub : (3 : ℝ) / 4 ≤ 1 - q ^ (n + 1) := by
    norm_num at hpow ⊢
    linarith
  have hpos : 0 < 1 - q ^ (n + 1) := sub_pos.2 (geom_ratio_lt_one n)
  have := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3 / 4)).2 hsub
  norm_num at this ⊢
  exact this

lemma S_le_explicit {n : ℕ} (hn : 1 ≤ n) :
    S n ≤ ((4 : ℝ) / 3) ^ (2 * n + 3) * q ^ (n * (n + 1)) := by
  rw [S_eq_shift hn]
  calc
    (∑' k : ℕ, term n (n + k)) ≤ ∑' k : ℕ, tailMajor n k := by
      apply Summable.tsum_le_tsum
      · intro k
        exact term_le_geometric hn (Nat.le_add_right n k)
      · exact (summable_term hn).comp_injective (add_right_injective n)
      · exact summable_tailMajor n
    _ = (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
        (1 - q ^ (n + 1))⁻¹ := tsum_tailMajor n
    _ ≤ (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
        ((4 : ℝ) / 3) := by
      exact mul_le_mul_of_nonneg_left (geom_inv_le_four_thirds hn)
        (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg q_pos.le _))
    _ = ((4 : ℝ) / 3) ^ (2 * n + 3) * q ^ (n * (n + 1)) := by
      rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_add]
      rw [Nat.mul_comm (n + 1) n]
      ring

end

end QApery
