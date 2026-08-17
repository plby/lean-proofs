import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.LenzOptimization

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223

noncomputable section

private def point2 (x y : ℝ) : Point 2 := !₂[x, y]

private lemma inner_eq_coordinates (u v : Point 2) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma norm_sq_eq_coordinates (u : Point 2) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coordinates]
  ring

private lemma dist_point2_sq (x₁ y₁ x₂ y₂ : ℝ) :
    dist (point2 x₁ y₁) (point2 x₂ y₂) ^ 2 =
      (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [real_inner_self_eq_norm_sq, norm_sq_eq_coordinates]
  simp [point2]

private def circlePoint (r θ : ℝ) : Point 2 :=
  point2 (r * Real.cos θ) (r * Real.sin θ)

private lemma norm_circlePoint_sq (r θ : ℝ) :
    ‖circlePoint r θ‖ ^ 2 = r ^ 2 := by
  rw [norm_sq_eq_coordinates]
  simp [circlePoint, point2]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private lemma dist_circlePoint_sq (r θ ψ : ℝ) :
    dist (circlePoint r θ) (circlePoint r ψ) ^ 2 =
      r ^ 2 * (2 - 2 * Real.cos (θ - ψ)) := by
  rw [circlePoint, circlePoint, dist_point2_sq]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq ψ]

/-- The angle of vertex `i` in the regular `M`-gon. -/
private def regularAngle (M : ℕ) (i : Fin M) : ℝ :=
  2 * Real.pi * (i : ℝ) / M

private lemma regularAngle_nonneg {M : ℕ} (i : Fin M) :
    0 ≤ regularAngle M i := by
  simp only [regularAngle]
  positivity

private lemma regularAngle_lt_two_pi {M : ℕ} (hM : 0 < M) (i : Fin M) :
    regularAngle M i < 2 * Real.pi := by
  have hi : (i : ℝ) < M := by exact_mod_cast i.isLt
  have hMℝ : (0 : ℝ) < M := by exact_mod_cast hM
  have hpi : 0 < Real.pi := Real.pi_pos
  dsimp [regularAngle]
  rw [div_lt_iff₀ hMℝ]
  nlinarith

private lemma regularAngle_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (regularAngle M) := by
  intro i j hij
  have hMℝ : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  dsimp [regularAngle] at hij
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hMℝ] at hij
  exact Fin.ext (by
    have : (i : ℝ) = j := by nlinarith
    exact_mod_cast this)

private def regularPoint (M : ℕ) (r : ℝ) (i : Fin M) : Point 2 :=
  circlePoint r (regularAngle M i)

private lemma regularPoint_injective {M : ℕ} (hM : 0 < M) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (regularPoint M r) := by
  intro i j hij
  have hcos := congrArg (fun z : Point 2 ↦ z 0) hij
  have hsin := congrArg (fun z : Point 2 ↦ z 1) hij
  simp only [regularPoint, circlePoint, point2, Matrix.cons_val_zero] at hcos
  simp only [regularPoint, circlePoint, point2, Matrix.cons_val_one, Matrix.cons_val_zero,
    ] at hsin
  have hcos' : Real.cos (regularAngle M i) = Real.cos (regularAngle M j) :=
    mul_left_cancel₀ hr hcos
  have hsin' : Real.sin (regularAngle M i) = Real.sin (regularAngle M j) :=
    mul_left_cancel₀ hr hsin
  have hang : (regularAngle M i : Real.Angle) = regularAngle M j :=
    Real.Angle.cos_sin_inj hcos' hsin'
  have hi0 := regularAngle_nonneg i
  have hj0 := regularAngle_nonneg j
  have hi2 := regularAngle_lt_two_pi hM i
  have hj2 := regularAngle_lt_two_pi hM j
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have heq : regularAngle M i = regularAngle M j :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (p := 2 * Real.pi)
      ⟨hi0, by simpa using hi2⟩ ⟨hj0, by simpa using hj2⟩).mp hang
  exact regularAngle_injective hM heq

private def maximalAngle (M : ℕ) : ℝ :=
  2 * Real.pi * (((M - 1) / 2 : ℕ) : ℝ) / M

private lemma maximalAngle_eq {M : ℕ} (hodd : M % 2 = 1) :
    maximalAngle M = Real.pi - Real.pi / M := by
  have hM : 0 < M := by omega
  have hhalf : 2 * ((M - 1) / 2) = M - 1 := by omega
  have hhalfℝ : (2 : ℝ) * (((M - 1) / 2 : ℕ) : ℝ) = ((M - 1 : ℕ) : ℝ) := by
    exact_mod_cast hhalf
  have hsubℝ : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) (show 1 ≤ M by omega))
  have hMℝ : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  dsimp [maximalAngle]
  field_simp [hMℝ]
  rw [hhalfℝ, hsubℝ]

private lemma maximalAngle_nonneg (M : ℕ) : 0 ≤ maximalAngle M := by
  unfold maximalAngle
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Nat.cast_nonneg ((M - 1) / 2)))
    (Nat.cast_nonneg M)

private lemma maximalAngle_lt_pi {M : ℕ} (hM : 0 < M) (hodd : M % 2 = 1) :
    maximalAngle M < Real.pi := by
  rw [maximalAngle_eq hodd]
  have hMℝ : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiv : 0 < Real.pi / (M : ℝ) := div_pos Real.pi_pos hMℝ
  linarith

private def regularRadius (M : ℕ) : ℝ :=
  (Real.sqrt (2 - 2 * Real.cos (maximalAngle M)))⁻¹

private lemma regularRadius_pos {M : ℕ} (hM : 1 < M) (hodd : M % 2 = 1) :
    0 < regularRadius M := by
  have ha0 : 0 ≤ maximalAngle M := maximalAngle_nonneg M
  have haπ : maximalAngle M ≤ Real.pi :=
    (maximalAngle_lt_pi (M := M) (by omega) hodd).le
  have ha : 0 < maximalAngle M := by
    rw [maximalAngle_eq hodd]
    have hMℝ : (1 : ℝ) < M := by exact_mod_cast hM
    exact sub_pos.mpr (div_lt_self Real.pi_pos hMℝ)
  have hc : Real.cos (maximalAngle M) < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := maximalAngle M) (by norm_num) haπ ha
  dsimp [regularRadius]
  exact inv_pos.mpr (Real.sqrt_pos.2 (by nlinarith))

private lemma regularRadius_sq_mul (M : ℕ) (hM : 1 < M) (hodd : M % 2 = 1) :
    regularRadius M ^ 2 * (2 - 2 * Real.cos (maximalAngle M)) = 1 := by
  have ha0 : 0 ≤ maximalAngle M := maximalAngle_nonneg M
  have haπ : maximalAngle M ≤ Real.pi :=
    (maximalAngle_lt_pi (M := M) (by omega) hodd).le
  have ha : 0 < maximalAngle M := by
    rw [maximalAngle_eq hodd]
    have hMℝ : (1 : ℝ) < M := by exact_mod_cast hM
    exact sub_pos.mpr (div_lt_self Real.pi_pos hMℝ)
  have hc : 0 < 2 - 2 * Real.cos (maximalAngle M) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := maximalAngle M) (by norm_num) haπ ha
    simpa using (show Real.cos (maximalAngle M) < 1 by simpa using this)
  have hs : Real.sqrt (2 - 2 * Real.cos (maximalAngle M)) ^ 2 =
      2 - 2 * Real.cos (maximalAngle M) := Real.sq_sqrt hc.le
  dsimp [regularRadius]
  rw [inv_pow, hs]
  exact inv_mul_cancel₀ hc.ne'

private lemma regularRadius_sq_le_half {M : ℕ} (hM : 3 ≤ M) (hodd : M % 2 = 1) :
    regularRadius M ^ 2 ≤ 1 / 2 := by
  have hmaxLower : Real.pi / 2 ≤ maximalAngle M := by
    rw [maximalAngle_eq hodd]
    have hMℝ : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
    have hMpos : (0 : ℝ) < M := by positivity
    have hdiv : Real.pi / (M : ℝ) ≤ Real.pi / 2 := by
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hMℝ
    linarith
  have hmaxUpper : maximalAngle M ≤ Real.pi + Real.pi / 2 := by
    have := (maximalAngle_lt_pi (M := M) (by omega) hodd).le
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (maximalAngle M) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hmaxLower hmaxUpper
  have hr := regularRadius_sq_mul M (by omega) hodd
  nlinarith [sq_nonneg (regularRadius M)]

private def separationAngle (M q : ℕ) : ℝ :=
  2 * Real.pi * (q : ℝ) / M

private lemma cos_regularAngle_sub (M : ℕ) (hM : 0 < M) (i j : Fin M) :
    Real.cos (regularAngle M i - regularAngle M j) =
      Real.cos (separationAngle M (Nat.dist i j)) := by
  have hMℝ : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  rcases le_total (i : ℕ) j with hij | hji
  · have hsub : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by
      exact_mod_cast (Nat.cast_sub (R := ℝ) hij)
    rw [Nat.dist_eq_sub_of_le (by omega : (i : ℕ) ≤ j)]
    dsimp [regularAngle, separationAngle]
    rw [show 2 * Real.pi * (i : ℝ) / M - 2 * Real.pi * (j : ℝ) / M =
        -(2 * Real.pi * ((j - i : ℕ) : ℝ) / M) by rw [hsub]; field_simp; ring,
      Real.cos_neg]
  · have hsub : ((i - j : ℕ) : ℝ) = (i : ℝ) - j := by
      exact_mod_cast (Nat.cast_sub (R := ℝ) hji)
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega : (j : ℕ) ≤ i)]
    dsimp [regularAngle, separationAngle]
    rw [hsub]
    field_simp

private lemma separationAngle_nonneg (M q : ℕ) : 0 ≤ separationAngle M q := by
  unfold separationAngle
  positivity

private lemma separationAngle_le_maximalAngle {M q : ℕ} (hM : 0 < M)
    (hq : q ≤ (M - 1) / 2) : separationAngle M q ≤ maximalAngle M := by
  have hqℝ : (q : ℝ) ≤ (((M - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hq
  have hMℝ : (0 : ℝ) < M := by exact_mod_cast hM
  unfold separationAngle maximalAngle
  exact (div_le_div_iff_of_pos_right hMℝ).2 (by
    have hp : 0 ≤ 2 * Real.pi := by positivity
    exact mul_le_mul_of_nonneg_left hqℝ hp)

private lemma cos_separation_complement {M q : ℕ} (hM : 0 < M) (hq : q ≤ M) :
    Real.cos (separationAngle M q) = Real.cos (separationAngle M (M - q)) := by
  have hMℝ : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hsub : ((M - q : ℕ) : ℝ) = (M : ℝ) - q := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) hq)
  have harg : separationAngle M (M - q) = 2 * Real.pi - separationAngle M q := by
    unfold separationAngle
    rw [hsub]
    field_simp
  rw [harg, Real.cos_two_pi_sub]

private lemma cos_maximalAngle_le_cos_separation {M q : ℕ}
    (hM : 1 < M) (hodd : M % 2 = 1) (hq : q < M) :
    Real.cos (maximalAngle M) ≤ Real.cos (separationAngle M q) := by
  let k := (M - 1) / 2
  have hMform : M = 2 * k + 1 := by
    dsimp [k]
    omega
  by_cases hqk : q ≤ k
  · apply Real.cos_le_cos_of_nonneg_of_le_pi
      (separationAngle_nonneg M q)
      (maximalAngle_lt_pi (M := M) (by omega) hodd).le
    exact separationAngle_le_maximalAngle (by omega) hqk
  · have hcomp : M - q ≤ k := by omega
    rw [cos_separation_complement (by omega) hq.le]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
      (separationAngle_nonneg M (M - q))
      (maximalAngle_lt_pi (M := M) (by omega) hodd).le
    exact separationAngle_le_maximalAngle (by omega) hcomp

private lemma regularPoint_dist_le_one {M : ℕ} (hM : 1 < M) (hodd : M % 2 = 1)
    (i j : Fin M) :
    dist (regularPoint M (regularRadius M) i)
      (regularPoint M (regularRadius M) j) ≤ 1 := by
  have hdist : Nat.dist (i : ℕ) j < M := by
    rcases le_total (i : ℕ) j with hij | hji
    · rw [Nat.dist_eq_sub_of_le hij]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
      omega
  have hcos := cos_maximalAngle_le_cos_separation hM hodd hdist
  rw [← cos_regularAngle_sub M (by omega) i j] at hcos
  have hsq := dist_circlePoint_sq (regularRadius M) (regularAngle M i) (regularAngle M j)
  have hr := regularRadius_sq_mul M hM hodd
  change dist (circlePoint (regularRadius M) (regularAngle M i))
    (circlePoint (regularRadius M) (regularAngle M j)) ≤ 1
  have hsquare : dist (circlePoint (regularRadius M) (regularAngle M i))
      (circlePoint (regularRadius M) (regularAngle M j)) ^ 2 ≤ 1 := by
    rw [hsq]
    nlinarith [sq_nonneg (regularRadius M)]
  have hd0 : 0 ≤ dist (circlePoint (regularRadius M) (regularAngle M i))
      (circlePoint (regularRadius M) (regularAngle M j)) := dist_nonneg
  nlinarith

private lemma separationAngle_half_eq_maximal (M : ℕ) :
    separationAngle M ((M - 1) / 2) = maximalAngle M := rfl

private lemma regularPoint_dist_eq_one_of_dist_half {M : ℕ}
    (hM : 1 < M) (hodd : M % 2 = 1) (i j : Fin M)
    (hij : Nat.dist (i : ℕ) j = (M - 1) / 2) :
    dist (regularPoint M (regularRadius M) i)
      (regularPoint M (regularRadius M) j) = 1 := by
  have hcos := cos_regularAngle_sub M (by omega) i j
  rw [hij, separationAngle_half_eq_maximal] at hcos
  have hsq := dist_circlePoint_sq (regularRadius M) (regularAngle M i) (regularAngle M j)
  have hr := regularRadius_sq_mul M hM hodd
  change dist (circlePoint (regularRadius M) (regularAngle M i))
    (circlePoint (regularRadius M) (regularAngle M j)) = 1
  rw [hcos] at hsq
  rw [hr] at hsq
  have hd0 : 0 ≤ dist (circlePoint (regularRadius M) (regularAngle M i))
      (circlePoint (regularRadius M) (regularAngle M j)) := dist_nonneg
  nlinarith

private lemma regularPoint_dist_eq_one_of_dist_half_or_succ {M : ℕ}
    (hM : 1 < M) (hodd : M % 2 = 1) (i j : Fin M)
    (hij : Nat.dist (i : ℕ) j = (M - 1) / 2 ∨
      Nat.dist (i : ℕ) j = (M - 1) / 2 + 1) :
    dist (regularPoint M (regularRadius M) i)
      (regularPoint M (regularRadius M) j) = 1 := by
  rcases hij with hij | hij
  · exact regularPoint_dist_eq_one_of_dist_half hM hodd i j hij
  · have hMform : M = 2 * ((M - 1) / 2) + 1 := by omega
    have hcomp : M - Nat.dist (i : ℕ) j = (M - 1) / 2 := by omega
    have hdistlt : Nat.dist (i : ℕ) j < M := by omega
    have hcos := cos_regularAngle_sub M (by omega) i j
    have hccomp := cos_separation_complement (M := M) (q := Nat.dist (i : ℕ) j)
      (by omega) hdistlt.le
    rw [hcomp, separationAngle_half_eq_maximal] at hccomp
    rw [hccomp] at hcos
    have hsq := dist_circlePoint_sq (regularRadius M) (regularAngle M i) (regularAngle M j)
    have hr := regularRadius_sq_mul M hM hodd
    change dist (circlePoint (regularRadius M) (regularAngle M i))
      (circlePoint (regularRadius M) (regularAngle M j)) = 1
    rw [hcos, hr] at hsq
    have hd0 : 0 ≤ dist (circlePoint (regularRadius M) (regularAngle M i))
        (circlePoint (regularRadius M) (regularAngle M j)) := dist_nonneg
    nlinarith

/-- The odd regular polygon from which the active `m`-point circle is cut.
For even `m`, one vertex of the `(m+1)`-gon is omitted. -/
private def polygonSize (m : ℕ) : ℕ := if m % 2 = 1 then m else m + 1

private lemma polygonSize_odd (m : ℕ) : polygonSize m % 2 = 1 := by
  unfold polygonSize
  split_ifs with h
  · exact h
  · omega

private lemma polygonSize_pos_of_pos {m : ℕ} (hm : 0 < m) : 0 < polygonSize m := by
  unfold polygonSize
  split_ifs <;> omega

private lemma polygonSize_eq_of_odd {m : ℕ} (hm : m % 2 = 1) : polygonSize m = m := by
  simp [polygonSize, hm]

private lemma polygonSize_eq_succ_of_even {m : ℕ} (hm : m % 2 = 0) :
    polygonSize m = m + 1 := by
  simp [polygonSize, hm]

/-- Path/cycle order on the retained regular-polygon vertices. -/
private def activeIndex {m : ℕ} (t : Fin m) : Fin (polygonSize m) := by
  let M := polygonSize m
  let k := (M - 1) / 2
  by_cases hm : m % 2 = 1
  · by_cases ht : (t : ℕ) % 2 = 0
    · exact ⟨(t : ℕ) / 2, by
        have hM : M = m := polygonSize_eq_of_odd hm
        omega⟩
    · exact ⟨k + 1 + (t : ℕ) / 2, by
        have hM : M = m := polygonSize_eq_of_odd hm
        dsimp [k]
        omega⟩
  · have hmeven : m % 2 = 0 := by omega
    by_cases ht : (t : ℕ) % 2 = 0
    · exact ⟨k + (t : ℕ) / 2, by
        have hM : M = m + 1 := polygonSize_eq_succ_of_even hmeven
        dsimp [k]
        omega⟩
    · exact ⟨(t : ℕ) / 2, by
        have hM : M = m + 1 := polygonSize_eq_succ_of_even hmeven
        omega⟩

private lemma activeIndex_injective {m : ℕ} : Function.Injective (@activeIndex m) := by
  intro t u h
  have hv := congrArg Fin.val h
  unfold activeIndex at hv
  dsimp only at hv
  split_ifs at hv with hm ht hu hmt htu huu
  all_goals apply Fin.ext
  all_goals simp only [Fin.val_mk] at hv
  all_goals try unfold polygonSize at hv
  all_goals try split_ifs at hv
  all_goals omega

private lemma nat_dist_eq_of_le {a b k : ℕ} (hab : a ≤ b) (hsub : b - a = k) :
    Nat.dist a b = k := by rw [Nat.dist_eq_sub_of_le hab, hsub]

private lemma nat_dist_eq_of_ge {a b k : ℕ} (hba : b ≤ a) (hsub : a - b = k) :
    Nat.dist a b = k := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba, hsub]

private lemma activeIndex_consecutive_dist {m : ℕ} (hm : 3 ≤ m)
    (t : Fin (m - 1)) :
    Nat.dist (activeIndex (⟨(t : ℕ), by omega⟩ : Fin m) : ℕ)
        (activeIndex (⟨(t : ℕ) + 1, by omega⟩ : Fin m) : ℕ) =
          (polygonSize m - 1) / 2 ∨
    Nat.dist (activeIndex (⟨(t : ℕ), by omega⟩ : Fin m) : ℕ)
        (activeIndex (⟨(t : ℕ) + 1, by omega⟩ : Fin m) : ℕ) =
          (polygonSize m - 1) / 2 + 1 := by
  unfold activeIndex
  dsimp only
  split_ifs with hm' ht hu hmt htu huu
  all_goals
    simp only [Fin.val_mk]
    unfold polygonSize
    split_ifs
  all_goals first
    | exact Or.inl (nat_dist_eq_of_le (by omega) (by omega))
    | exact Or.inl (nat_dist_eq_of_ge (by omega) (by omega))
    | exact Or.inr (nat_dist_eq_of_le (by omega) (by omega))
    | exact Or.inr (nat_dist_eq_of_ge (by omega) (by omega))

private lemma activeIndex_last_dist_zero {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    Nat.dist (activeIndex (⟨0, by omega⟩ : Fin m) : ℕ)
      (activeIndex (⟨m - 1, by omega⟩ : Fin m) : ℕ) =
        (polygonSize m - 1) / 2 := by
  have hlastEven : (m - 1) % 2 = 0 := by omega
  have hzero : (activeIndex (⟨0, by omega⟩ : Fin m) : ℕ) = 0 := by
    simp [activeIndex, hodd]
  have hlast : (activeIndex (⟨m - 1, by omega⟩ : Fin m) : ℕ) = (m - 1) / 2 := by
    simp [activeIndex, hodd, hlastEven, polygonSize_eq_of_odd]
  rw [hzero, hlast, polygonSize_eq_of_odd hodd]
  exact nat_dist_eq_of_le (by omega) (by omega)

private def activePoint (m : ℕ) (t : Fin m) : Point 2 :=
  regularPoint (polygonSize m) (regularRadius (polygonSize m)) (activeIndex t)

private lemma activePoint_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (activePoint m) := by
  have hM2 : 1 < polygonSize m := by
    unfold polygonSize
    split_ifs <;> omega
  apply (regularPoint_injective (polygonSize_pos_of_pos (by omega))
    (regularRadius_pos hM2 (polygonSize_odd m)).ne').comp
  exact activeIndex_injective

private lemma activePoint_dist_le_one {m : ℕ} (hm : 3 ≤ m) (t u : Fin m) :
    dist (activePoint m t) (activePoint m u) ≤ 1 := by
  exact regularPoint_dist_le_one
    (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m) _ _

private lemma activePoint_consecutive_dist_eq_one {m : ℕ} (hm : 3 ≤ m)
    (t : Fin (m - 1)) :
    dist (activePoint m ⟨t, by omega⟩) (activePoint m ⟨(t : ℕ) + 1, by omega⟩) = 1 := by
  apply regularPoint_dist_eq_one_of_dist_half_or_succ
    (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  exact activeIndex_consecutive_dist hm t

private lemma activePoint_last_dist_zero_eq_one {m : ℕ} (hm : 3 ≤ m)
    (hodd : m % 2 = 1) :
    dist (activePoint m ⟨m - 1, by omega⟩) (activePoint m ⟨0, by omega⟩) = 1 := by
  rw [dist_comm]
  apply regularPoint_dist_eq_one_of_dist_half
    (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  exact activeIndex_last_dist_zero hm hodd

private def activeConfiguration (m : ℕ) : Finset (Point 2) :=
  Finset.univ.image (activePoint m)

private lemma card_activeConfiguration {m : ℕ} (hm : 3 ≤ m) :
    (activeConfiguration m).card = m := by
  rw [activeConfiguration, Finset.card_image_iff.mpr (activePoint_injective hm).injOn]
  simp

private lemma mem_activeConfiguration {m : ℕ} (t : Fin m) :
    activePoint m t ∈ activeConfiguration m := by simp [activeConfiguration]

private lemma activeConfiguration_pairwise_dist_le_one {m : ℕ} (hm : 3 ≤ m) :
    ∀ x ∈ activeConfiguration m, ∀ y ∈ activeConfiguration m, dist x y ≤ 1 := by
  simp only [activeConfiguration, Finset.mem_image, Finset.mem_univ, true_and]
  rintro x ⟨t, rfl⟩ y ⟨u, rfl⟩
  exact activePoint_dist_le_one hm t u

private def activeVertexEmbedding {m : ℕ} (hm : 3 ≤ m) :
    Fin m ↪ {x // x ∈ activeConfiguration m} where
  toFun t := ⟨activePoint m t, mem_activeConfiguration t⟩
  inj' _ _ h := activePoint_injective hm (congrArg Subtype.val h)

private def pathEdge {m : ℕ} (t : Fin (m - 1)) : Sym2 (Fin m) :=
  s((⟨(t : ℕ), by omega⟩ : Fin m), ⟨(t : ℕ) + 1, by omega⟩)

private lemma pathEdge_injective {m : ℕ} : Function.Injective (@pathEdge m) := by
  intro t u h
  unfold pathEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · apply Fin.ext
    exact congrArg (fun z : Fin m ↦ z.val) h.1
  · have h1 := congrArg (fun z : Fin m ↦ z.val) h.1
    have h2 := congrArg (fun z : Fin m ↦ z.val) h.2
    simp only [Fin.val_mk] at h1 h2
    apply Fin.ext
    omega

private def closingEdge {m : ℕ} (hm : 2 ≤ m) : Sym2 (Fin m) :=
  s((⟨m - 1, by omega⟩ : Fin m), ⟨0, by omega⟩)

private lemma pathEdge_ne_closingEdge {m : ℕ} (hm : 3 ≤ m) (t : Fin (m - 1)) :
    pathEdge t ≠ closingEdge (by omega : 2 ≤ m) := by
  intro h
  unfold pathEdge closingEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have h1 := congrArg (fun z : Fin m ↦ z.val) h.1
    have h2 := congrArg (fun z : Fin m ↦ z.val) h.2
    simp only [Fin.val_mk] at h1 h2
    omega
  · have h1 := congrArg (fun z : Fin m ↦ z.val) h.1
    have h2 := congrArg (fun z : Fin m ↦ z.val) h.2
    simp only [Fin.val_mk] at h1 h2
    omega

private def activeExtraCount (m : ℕ) : ℕ := if m % 2 = 1 then 1 else 0

private def activeLocalDomain (m : ℕ) :
    Finset (Fin (m - 1) ⊕ Fin (activeExtraCount m)) :=
  Finset.univ.disjSum Finset.univ

private lemma card_activeLocalDomain {m : ℕ} (hm : 3 ≤ m) :
    (activeLocalDomain m).card = cyclicDiameterAllowance m := by
  unfold activeLocalDomain
  rw [Finset.card_disjSum]
  simp only [Finset.card_univ, Fintype.card_fin]
  unfold activeExtraCount cyclicDiameterAllowance
  split_ifs <;> omega

private def activeLocalMap {m : ℕ} (hm : 3 ≤ m) :
    Fin (m - 1) ⊕ Fin (activeExtraCount m) →
      Sym2 {x // x ∈ activeConfiguration m}
  | .inl t => Sym2.map (activeVertexEmbedding (m := m) hm) (pathEdge t)
  | .inr _ => Sym2.map (activeVertexEmbedding (m := m) hm) (closingEdge (by omega))

private lemma activeLocalMap_injOn {m : ℕ} (hm : 3 ≤ m) :
    Set.InjOn (activeLocalMap hm) (activeLocalDomain m) := by
  intro a ha b hb hab
  cases a with
  | inl t =>
      cases b with
      | inl u =>
          congr 1
          apply pathEdge_injective
          exact Sym2.map.injective (activeVertexEmbedding (m := m) hm).injective hab
      | inr u =>
          exfalso
          apply pathEdge_ne_closingEdge hm t
          exact Sym2.map.injective (activeVertexEmbedding (m := m) hm).injective hab
  | inr t =>
      cases b with
      | inl u =>
          exfalso
          apply pathEdge_ne_closingEdge hm u
          exact Sym2.map.injective (activeVertexEmbedding (m := m) hm).injective hab.symm
      | inr u =>
          congr 1
          have hextra : activeExtraCount m ≤ 1 := by
            unfold activeExtraCount
            split_ifs <;> omega
          apply Fin.ext
          omega

private lemma activeLocalMap_mem_diameterEdge {m : ℕ} (hm : 3 ≤ m)
    {z : Fin (m - 1) ⊕ Fin (activeExtraCount m)} (hz : z ∈ activeLocalDomain m) :
    activeLocalMap hm z ∈ (diameterGraph (activeConfiguration m)).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  cases z with
  | inl t =>
      change dist (activePoint m ⟨t, by omega⟩)
        (activePoint m ⟨(t : ℕ) + 1, by omega⟩) = 1
      exact activePoint_consecutive_dist_eq_one hm t
  | inr u =>
      have hextra : 0 < activeExtraCount m := by
        simpa using (Fintype.card_pos_iff.mpr ⟨u⟩ : 0 < Fintype.card (Fin (activeExtraCount m)))
      have hodd : m % 2 = 1 := by
        unfold activeExtraCount at hextra
        split_ifs at hextra with h
        · exact h
        · omega
      change dist (activePoint m ⟨m - 1, by omega⟩) (activePoint m ⟨0, by omega⟩) = 1
      exact activePoint_last_dist_zero_eq_one hm hodd

private lemma active_local_count_le_diameterPairCount {m : ℕ} (hm : 3 ≤ m) :
    cyclicDiameterAllowance m ≤ diameterPairCount (activeConfiguration m) := by
  rw [diameterPairCount, ← card_activeLocalDomain hm]
  exact Finset.card_le_card_of_injOn (activeLocalMap hm)
    (fun _ hz ↦ activeLocalMap_mem_diameterEdge hm hz)
    (activeLocalMap_injOn hm)

/-! A unit-circle rational parametrization for the passive carrier. -/

private def gamma (t : ℝ) : Point 2 :=
  point2 ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))

private lemma norm_gamma_sq (t : ℝ) : ‖gamma t‖ ^ 2 = 1 := by
  rw [norm_sq_eq_coordinates]
  simp [gamma, point2]
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

private lemma dist_gamma_sq (s t : ℝ) :
    dist (gamma s) (gamma t) ^ 2 =
      4 * (t - s) ^ 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by
  rw [gamma, gamma, dist_point2_sq]
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hs, ht]
  ring

private lemma gamma_injective_on_unit {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h : gamma s = gamma t) : s = t := by
  have hc := congrArg (fun z : Point 2 ↦ z 1) h
  simp [gamma, point2] at hc
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hs, ht] at hc
  have hfactor : (s - t) * (1 - s * t) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hst | hprod
  · linarith
  · have hst1 : s = 1 ∧ t = 1 := by
      have : s * t = 1 := by linarith
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs1) ht0,
        mul_nonneg (sub_nonneg.mpr ht1) hs0]
    linarith

private def passiveRadius (m : ℕ) : ℝ :=
  Real.sqrt (1 - regularRadius (polygonSize m) ^ 2)

private lemma passiveRadius_sq {m : ℕ} (hm : 3 ≤ m) :
    passiveRadius m ^ 2 = 1 - regularRadius (polygonSize m) ^ 2 := by
  apply Real.sq_sqrt
  have hr := regularRadius_sq_le_half
    (M := polygonSize m) (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  linarith

private lemma passiveRadius_pos {m : ℕ} (hm : 3 ≤ m) : 0 < passiveRadius m := by
  unfold passiveRadius
  apply Real.sqrt_pos.2
  have hr := regularRadius_sq_le_half
    (M := polygonSize m) (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  linarith

private def passiveEnd (m : ℕ) : ℝ :=
  (Real.sqrt (4 * passiveRadius m ^ 2 - 1))⁻¹

private lemma passiveEnd_pos {m : ℕ} (hm : 3 ≤ m) : 0 < passiveEnd m := by
  have hr := passiveRadius_sq hm
  have hs := regularRadius_sq_le_half
    (M := polygonSize m) (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  unfold passiveEnd
  apply inv_pos.mpr (Real.sqrt_pos.2 ?_)
  nlinarith

private lemma passiveEnd_le_one {m : ℕ} (hm : 3 ≤ m) : passiveEnd m ≤ 1 := by
  have hr := passiveRadius_sq hm
  have hs := regularRadius_sq_le_half
    (M := polygonSize m) (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  have hrad : 1 ≤ 4 * passiveRadius m ^ 2 - 1 := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt (4 * passiveRadius m ^ 2 - 1) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 4 * passiveRadius m ^ 2 - 1 by linarith)
    have hsn := Real.sqrt_nonneg (4 * passiveRadius m ^ 2 - 1)
    nlinarith
  unfold passiveEnd
  exact (inv_le_one₀ (by linarith)).2 hsqrt

private lemma passive_endpoint_equation {m : ℕ} (hm : 3 ≤ m) :
    4 * passiveRadius m ^ 2 * passiveEnd m ^ 2 /
      (1 + passiveEnd m ^ 2) = 1 := by
  have hpos := passiveEnd_pos hm
  have hrad : 0 < 4 * passiveRadius m ^ 2 - 1 := by
    have hr := passiveRadius_sq hm
    have hs := regularRadius_sq_le_half
      (M := polygonSize m) (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
    nlinarith
  have hsqrt : Real.sqrt (4 * passiveRadius m ^ 2 - 1) ^ 2 =
      4 * passiveRadius m ^ 2 - 1 := Real.sq_sqrt hrad.le
  unfold passiveEnd
  rw [inv_pow, hsqrt]
  field_simp
  ring

private def passiveParameter {m b : ℕ} (hb : 2 ≤ b) (i : Fin b) : ℝ :=
  (i : ℝ) / ((b - 1 : ℕ) : ℝ) * passiveEnd m

private lemma passiveParameter_nonneg {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b) (i : Fin b) :
    0 ≤ passiveParameter (m := m) hb i := by
  unfold passiveParameter
  exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (passiveEnd_pos hm).le

private lemma passiveParameter_le_end {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b)
    (i : Fin b) : passiveParameter (m := m) hb i ≤ passiveEnd m := by
  have hd : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - 1 by omega)
  have hi : (i : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pred_of_lt i.isLt
  unfold passiveParameter
  have hfrac : (i : ℝ) / ((b - 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hd).2 hi
  nlinarith [passiveEnd_pos hm]

private lemma passiveParameter_injective {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b) :
    Function.Injective (@passiveParameter m b hb) := by
  intro i j h
  have hd : (((b - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show b - 1 ≠ 0 by omega)
  have he : passiveEnd m ≠ 0 := (passiveEnd_pos hm).ne'
  unfold passiveParameter at h
  apply Fin.ext
  have hc : (i : ℝ) = j := by
    apply (div_left_inj' hd).mp
    apply mul_right_cancel₀ he
    exact h
  exact_mod_cast hc

private def passivePoint (m b : ℕ) (hm : 3 ≤ m) (hb : 2 ≤ b) (i : Fin b) : Point 2 :=
  passiveRadius m • gamma (passiveParameter (m := m) hb i)

private lemma passivePoint_injective {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b) :
    Function.Injective (passivePoint m b hm hb) := by
  intro i j h
  have hr : passiveRadius m ≠ 0 := (passiveRadius_pos hm).ne'
  have hg : gamma (passiveParameter (m := m) hb i) =
      gamma (passiveParameter (m := m) hb j) := by
    exact (smul_right_injective (Point 2) hr) h
  apply passiveParameter_injective hm hb
  apply gamma_injective_on_unit
  · exact passiveParameter_nonneg hm hb i
  · exact (passiveParameter_le_end hm hb i).trans (passiveEnd_le_one hm)
  · exact passiveParameter_nonneg hm hb j
  · exact (passiveParameter_le_end hm hb j).trans (passiveEnd_le_one hm)
  · exact hg

private lemma norm_passivePoint_sq {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b) (i : Fin b) :
    ‖passivePoint m b hm hb i‖ ^ 2 = passiveRadius m ^ 2 := by
  rw [passivePoint, norm_smul, Real.norm_eq_abs, abs_of_pos (passiveRadius_pos hm),
    mul_pow, norm_gamma_sq]
  ring

private lemma dist_passivePoint_sq {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b) (i j : Fin b) :
    dist (passivePoint m b hm hb i) (passivePoint m b hm hb j) ^ 2 =
      passiveRadius m ^ 2 *
        (4 * (passiveParameter (m := m) hb j - passiveParameter (m := m) hb i) ^ 2 /
          ((1 + passiveParameter (m := m) hb i ^ 2) *
            (1 + passiveParameter (m := m) hb j ^ 2))) := by
  rw [passivePoint, passivePoint, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos (passiveRadius_pos hm), mul_pow, dist_gamma_sq]

private lemma passive_chord_fraction_le_endpoint {m : ℕ} (hm : 3 ≤ m)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ passiveEnd m) :
    4 * passiveRadius m ^ 2 * (t - s) ^ 2 /
        ((1 + s ^ 2) * (1 + t ^ 2)) ≤ 1 := by
  let T := passiveEnd m
  have hT : 0 ≤ T := (passiveEnd_pos hm).le
  have ht0 : 0 ≤ t := hs.trans hst
  have hsqst : (t - s) ^ 2 ≤ t ^ 2 * (1 + s ^ 2) := by
    have haux : 0 ≤ s * (t ^ 2 * s + 2 * t - s) := by
      have hinner : 0 ≤ t ^ 2 * s + 2 * t - s := by
        nlinarith [mul_nonneg (sq_nonneg t) hs]
      exact mul_nonneg hs hinner
    nlinarith
  have htt : t ^ 2 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - t)]
  have hfrac : t ^ 2 * (1 + T ^ 2) ≤ T ^ 2 * (1 + t ^ 2) := by nlinarith
  have hchain : (t - s) ^ 2 * (1 + T ^ 2) ≤
      T ^ 2 * ((1 + s ^ 2) * (1 + t ^ 2)) := calc
    _ ≤ (t ^ 2 * (1 + s ^ 2)) * (1 + T ^ 2) :=
      mul_le_mul_of_nonneg_right hsqst (by positivity)
    _ = (1 + s ^ 2) * (t ^ 2 * (1 + T ^ 2)) := by ring
    _ ≤ (1 + s ^ 2) * (T ^ 2 * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by ring
  have hden1 : 0 < (1 + s ^ 2) * (1 + t ^ 2) := by positivity
  have hden2 : 0 < 1 + T ^ 2 := by positivity
  have hmul : 0 ≤ 4 * passiveRadius m ^ 2 := by positivity
  calc
    _ ≤ 4 * passiveRadius m ^ 2 * T ^ 2 / (1 + T ^ 2) := by
      rw [div_le_div_iff₀ hden1 hden2]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hchain hmul
    _ = 1 := by simpa [T] using passive_endpoint_equation hm

private lemma dist_passivePoint_le_one_of_parameter_le {m b : ℕ}
    (hm : 3 ≤ m) (hb : 2 ≤ b) (i j : Fin b)
    (h : passiveParameter (m := m) hb i ≤ passiveParameter (m := m) hb j) :
    dist (passivePoint m b hm hb i) (passivePoint m b hm hb j) ≤ 1 := by
  have hsq := dist_passivePoint_sq hm hb i j
  have hfrac := passive_chord_fraction_le_endpoint hm
    (passiveParameter_nonneg hm hb i) h (passiveParameter_le_end hm hb j)
  have hsquare : dist (passivePoint m b hm hb i) (passivePoint m b hm hb j) ^ 2 ≤ 1 := by
    calc
      _ = passiveRadius m ^ 2 *
          (4 * (passiveParameter (m := m) hb j - passiveParameter (m := m) hb i) ^ 2 /
            ((1 + passiveParameter (m := m) hb i ^ 2) *
              (1 + passiveParameter (m := m) hb j ^ 2))) := hsq
      _ = 4 * passiveRadius m ^ 2 *
          (passiveParameter (m := m) hb j - passiveParameter (m := m) hb i) ^ 2 /
            ((1 + passiveParameter (m := m) hb i ^ 2) *
              (1 + passiveParameter (m := m) hb j ^ 2)) := by ring
      _ ≤ 1 := hfrac
  have hd := dist_nonneg (x := passivePoint m b hm hb i) (y := passivePoint m b hm hb j)
  nlinarith

private lemma dist_passivePoint_le_one {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b)
    (i j : Fin b) : dist (passivePoint m b hm hb i) (passivePoint m b hm hb j) ≤ 1 := by
  rcases le_total (passiveParameter (m := m) hb i) (passiveParameter (m := m) hb j) with h | h
  · exact dist_passivePoint_le_one_of_parameter_le hm hb i j h
  · rw [dist_comm]
    exact dist_passivePoint_le_one_of_parameter_le hm hb j i h

private lemma passiveParameter_zero {m b : ℕ} (hb : 2 ≤ b) :
    passiveParameter (m := m) hb (⟨0, by omega⟩ : Fin b) = 0 := by
  simp [passiveParameter]

private lemma passiveParameter_last {m b : ℕ} (hb : 2 ≤ b) :
    passiveParameter (m := m) hb (⟨b - 1, by omega⟩ : Fin b) = passiveEnd m := by
  have hd : (((b - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show b - 1 ≠ 0 by omega)
  simp [passiveParameter, hd]

private lemma dist_passive_endpoints_eq_one {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b) :
    dist (passivePoint m b hm hb ⟨0, by omega⟩)
      (passivePoint m b hm hb ⟨b - 1, by omega⟩) = 1 := by
  have hsq := dist_passivePoint_sq hm hb
    (⟨0, by omega⟩ : Fin b) (⟨b - 1, by omega⟩ : Fin b)
  rw [passiveParameter_zero, passiveParameter_last] at hsq
  have hsquare : dist (passivePoint m b hm hb ⟨0, by omega⟩)
      (passivePoint m b hm hb ⟨b - 1, by omega⟩) ^ 2 = 1 := calc
    _ = passiveRadius m ^ 2 * (4 * passiveEnd m ^ 2 / (1 + passiveEnd m ^ 2)) := by
      simpa using hsq
    _ = 4 * passiveRadius m ^ 2 * passiveEnd m ^ 2 / (1 + passiveEnd m ^ 2) := by ring
    _ = 1 := passive_endpoint_equation hm
  have hd := dist_nonneg (x := passivePoint m b hm hb ⟨0, by omega⟩)
    (y := passivePoint m b hm hb ⟨b - 1, by omega⟩)
  nlinarith

/-! Orthogonal join in four-space. -/

private def firstEmbed (x : Point 2) : Point 4 :=
  EuclideanSpace.single (0 : Fin 4) (x 0) + EuclideanSpace.single (1 : Fin 4) (x 1)
private def secondEmbed (x : Point 2) : Point 4 :=
  EuclideanSpace.single (2 : Fin 4) (x 0) + EuclideanSpace.single (3 : Fin 4) (x 1)

private lemma inner_point4_coordinates (x y : Point 4) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_four]
  ring

private lemma norm_sq_point4 (x : Point 4) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [inner_point4_coordinates]
  ring

private lemma dist_firstEmbed (x y : Point 2) : dist (firstEmbed x) (firstEmbed y) = dist x y := by
  have hsq : dist (firstEmbed x) (firstEmbed y) ^ 2 = dist x y ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, norm_sq_point4, norm_sq_eq_coordinates]
    simp [firstEmbed]
  nlinarith [dist_nonneg (x := firstEmbed x) (y := firstEmbed y),
    dist_nonneg (x := x) (y := y)]

private lemma dist_secondEmbed (x y : Point 2) : dist (secondEmbed x) (secondEmbed y) = dist x y := by
  have hsq : dist (secondEmbed x) (secondEmbed y) ^ 2 = dist x y ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, norm_sq_point4, norm_sq_eq_coordinates]
    simp [secondEmbed]
  nlinarith [dist_nonneg (x := secondEmbed x) (y := secondEmbed y),
    dist_nonneg (x := x) (y := y)]

private lemma dist_cross_sq (x y : Point 2) :
    dist (firstEmbed x) (secondEmbed y) ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [dist_eq_norm, norm_sq_point4, norm_sq_eq_coordinates, norm_sq_eq_coordinates]
  simp [firstEmbed, secondEmbed]
  ring

private def joinedPoint (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) :
    Fin a ⊕ Fin b → Point 4
  | .inl i => firstEmbed (activePoint a i)
  | .inr j => secondEmbed (passivePoint a b ha hb j)

private lemma joinedPoint_injective {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    Function.Injective (joinedPoint a b ha hb) := by
  intro u v h
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          congr 1
          apply activePoint_injective ha
          apply PiLp.ext
          intro k
          fin_cases k
          · have hc := congrArg (fun z : Point 4 ↦ z 0) h
            simpa [joinedPoint, firstEmbed] using hc
          · have hc := congrArg (fun z : Point 4 ↦ z 1) h
            simpa [joinedPoint, firstEmbed] using hc
      | inr j =>
          exfalso
          have hc0 := congrArg (fun z : Point 4 ↦ z 0) h
          have hc1 := congrArg (fun z : Point 4 ↦ z 1) h
          have hz : activePoint a i = 0 := by
            apply PiLp.ext
            intro k
            fin_cases k
            · simpa [joinedPoint, firstEmbed, secondEmbed] using hc0
            · simpa [joinedPoint, firstEmbed, secondEmbed] using hc1
          have hn := norm_circlePoint_sq (regularRadius (polygonSize a))
            (regularAngle (polygonSize a) (activeIndex i))
          change ‖activePoint a i‖ ^ 2 = _ at hn
          rw [hz] at hn
          have hp := regularRadius_pos (M := polygonSize a)
            (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd a)
          norm_num at hn
          nlinarith
  | inr i =>
      cases v with
      | inl j =>
          exfalso
          have hc2 := congrArg (fun z : Point 4 ↦ z 2) h
          have hc3 := congrArg (fun z : Point 4 ↦ z 3) h
          have hz : passivePoint a b ha hb i = 0 := by
            apply PiLp.ext
            intro k
            fin_cases k
            · simpa [joinedPoint, firstEmbed, secondEmbed] using hc2
            · simpa [joinedPoint, firstEmbed, secondEmbed] using hc3
          have hn := norm_passivePoint_sq ha hb i
          rw [hz] at hn
          have hp := passiveRadius_pos ha
          norm_num at hn
          nlinarith
      | inr j =>
          congr 1
          apply passivePoint_injective ha hb
          apply PiLp.ext
          intro k
          fin_cases k
          · have hc := congrArg (fun z : Point 4 ↦ z 2) h
            simpa [joinedPoint, secondEmbed] using hc
          · have hc := congrArg (fun z : Point 4 ↦ z 3) h
            simpa [joinedPoint, secondEmbed] using hc

private def joinedConfiguration (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) :
    Finset (Point 4) := Finset.univ.image (joinedPoint a b ha hb)

private lemma card_joinedConfiguration {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    (joinedConfiguration a b ha hb).card = a + b := by
  rw [joinedConfiguration, Finset.card_image_iff.mpr (joinedPoint_injective ha hb).injOn]
  simp

private lemma mem_joinedConfiguration {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b)
    (u : Fin a ⊕ Fin b) : joinedPoint a b ha hb u ∈ joinedConfiguration a b ha hb := by
  simp [joinedConfiguration]

private lemma dist_joined_cross_eq_one {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b)
    (i : Fin a) (j : Fin b) :
    dist (firstEmbed (activePoint a i)) (secondEmbed (passivePoint a b ha hb j)) = 1 := by
  have hs := dist_cross_sq (activePoint a i) (passivePoint a b ha hb j)
  have haNorm := norm_circlePoint_sq (regularRadius (polygonSize a))
    (regularAngle (polygonSize a) (activeIndex i))
  change ‖activePoint a i‖ ^ 2 = _ at haNorm
  have hbNorm := norm_passivePoint_sq ha hb j
  have hr := passiveRadius_sq ha
  have hd := dist_nonneg (x := firstEmbed (activePoint a i))
    (y := secondEmbed (passivePoint a b ha hb j))
  nlinarith

private lemma dist_joined_le_one {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b)
    (u v : Fin a ⊕ Fin b) :
    dist (joinedPoint a b ha hb u) (joinedPoint a b ha hb v) ≤ 1 := by
  cases u with
  | inl i =>
      cases v with
      | inl j => simpa [joinedPoint, dist_firstEmbed] using activePoint_dist_le_one ha i j
      | inr j => exact (dist_joined_cross_eq_one ha hb i j).le
  | inr i =>
      cases v with
      | inl j => simpa [joinedPoint, dist_comm] using (dist_joined_cross_eq_one ha hb j i).le
      | inr j => simpa [joinedPoint, dist_secondEmbed] using dist_passivePoint_le_one ha hb i j

private lemma isDiameterOne_joinedConfiguration {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    IsDiameterOne (joinedConfiguration a b ha hb) := by
  rw [isDiameterOne_iff]
  constructor
  · simp only [joinedConfiguration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    exact dist_joined_le_one ha hb u v
  · let i : Fin a := ⟨0, by omega⟩
    let j : Fin b := ⟨0, by omega⟩
    refine ⟨joinedPoint a b ha hb (.inl i), mem_joinedConfiguration ha hb _,
      joinedPoint a b ha hb (.inr j), mem_joinedConfiguration ha hb _, ?_⟩
    exact dist_joined_cross_eq_one ha hb i j

private def joinedVertexEmbedding {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    Fin a ⊕ Fin b ↪ {x // x ∈ joinedConfiguration a b ha hb} where
  toFun u := ⟨joinedPoint a b ha hb u, mem_joinedConfiguration ha hb u⟩
  inj' _ _ h := joinedPoint_injective ha hb (congrArg Subtype.val h)

private def baseActiveLocalEdge {a b : ℕ} (ha : 3 ≤ a) :
    Fin (a - 1) ⊕ Fin (activeExtraCount a) → Sym2 (Fin a ⊕ Fin b)
  | .inl t => Sym2.map Sum.inl (pathEdge t)
  | .inr _ => Sym2.map Sum.inl (closingEdge (by omega))

private def joinedCountDomain (a b : ℕ) :
    Finset ((Fin a × Fin b) ⊕ ((Fin (a - 1) ⊕ Fin (activeExtraCount a)) ⊕ Fin 1)) :=
  Finset.univ.disjSum (Finset.univ.disjSum Finset.univ)

private lemma card_joinedCountDomain {a b : ℕ} (ha : 3 ≤ a) :
    (joinedCountDomain a b).card = a * b + cyclicDiameterAllowance a + 1 := by
  unfold joinedCountDomain
  simp only [Finset.card_disjSum, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    add_left_inj]
  rw [show Fintype.card (Fin (a - 1) ⊕ Fin (activeExtraCount a)) =
      (activeLocalDomain a).card by simp [activeLocalDomain]]
  rw [card_activeLocalDomain ha]
  omega

private def joinedCountMap {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    (Fin a × Fin b) ⊕ ((Fin (a - 1) ⊕ Fin (activeExtraCount a)) ⊕ Fin 1) →
      Sym2 {x // x ∈ joinedConfiguration a b ha hb}
  | .inl (i, j) => s(joinedVertexEmbedding ha hb (.inl i), joinedVertexEmbedding ha hb (.inr j))
  | .inr (.inl z) => Sym2.map (joinedVertexEmbedding ha hb) (baseActiveLocalEdge ha z)
  | .inr (.inr _) => s(joinedVertexEmbedding ha hb (.inr ⟨0, by omega⟩),
      joinedVertexEmbedding ha hb (.inr ⟨b - 1, by omega⟩))

private lemma baseActiveLocalEdge_injective {a b : ℕ} (ha : 3 ≤ a) :
    Function.Injective (baseActiveLocalEdge (b := b) ha) := by
  intro u v h
  cases u with
  | inl t =>
      cases v with
      | inl s =>
          congr 1
          apply pathEdge_injective
          exact Sym2.map.injective Sum.inl_injective h
      | inr s =>
          exfalso
          apply pathEdge_ne_closingEdge ha t
          exact Sym2.map.injective Sum.inl_injective h
  | inr t =>
      cases v with
      | inl s =>
          exfalso
          apply pathEdge_ne_closingEdge ha s
          exact Sym2.map.injective Sum.inl_injective h.symm
      | inr s =>
          congr 1
          have hextra : activeExtraCount a ≤ 1 := by unfold activeExtraCount; split_ifs <;> omega
          apply Fin.ext
          omega

private lemma active_edge_both_left {a b : ℕ} (ha : 3 ≤ a)
    (z : Fin (a - 1) ⊕ Fin (activeExtraCount a)) :
    ∃ i j : Fin a, baseActiveLocalEdge (b := b) ha z = s((.inl i), (.inl j)) := by
  cases z with
  | inl t => exact ⟨⟨t, by omega⟩, ⟨(t : ℕ) + 1, by omega⟩, rfl⟩
  | inr t => exact ⟨⟨a - 1, by omega⟩, ⟨0, by omega⟩, rfl⟩

private lemma joinedCountMap_injOn {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    Set.InjOn (joinedCountMap ha hb) (joinedCountDomain a b) := by
  intro u hu v hv h
  have hinj := Sym2.map.injective (joinedVertexEmbedding ha hb).injective
  cases u with
  | inl p =>
      cases v with
      | inl q =>
          congr 1
          have hbase : s((.inl p.1 : Fin a ⊕ Fin b), .inr p.2) =
              s((.inl q.1 : Fin a ⊕ Fin b), .inr q.2) := by
            apply hinj
            simpa [joinedCountMap, Sym2.map_mk] using h
          rw [Sym2.eq_iff] at hbase
          rcases hbase with h | h
          · exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
          · simp at h
      | inr r =>
          exfalso
          cases r with
          | inl z =>
              obtain ⟨i, j, hz⟩ := active_edge_both_left (b := b) ha z
              have hbase : s((.inl p.1 : Fin a ⊕ Fin b), .inr p.2) =
                  baseActiveLocalEdge (b := b) ha z := by
                apply hinj
                simpa [joinedCountMap, Sym2.map_mk] using h
              rw [hz, Sym2.eq_iff] at hbase
              rcases hbase with h | h <;> simp at h
          | inr z =>
              have hbase : s((.inl p.1 : Fin a ⊕ Fin b), .inr p.2) =
                  s((.inr (⟨0, by omega⟩ : Fin b)), .inr ⟨b - 1, by omega⟩) := by
                apply hinj
                simpa [joinedCountMap, Sym2.map_mk] using h
              rw [Sym2.eq_iff] at hbase
              rcases hbase with h | h <;> simp at h
  | inr r =>
      cases v with
      | inl q =>
          exfalso
          cases r with
          | inl z =>
              obtain ⟨i, j, hz⟩ := active_edge_both_left (b := b) ha z
              have hbase : baseActiveLocalEdge (b := b) ha z =
                  s((.inl q.1 : Fin a ⊕ Fin b), .inr q.2) := by
                apply hinj
                simpa [joinedCountMap, Sym2.map_mk] using h
              rw [hz, Sym2.eq_iff] at hbase
              rcases hbase with h | h <;> simp at h
          | inr z =>
              have hbase : s((.inr (⟨0, by omega⟩ : Fin b)), .inr ⟨b - 1, by omega⟩) =
                  s((.inl q.1 : Fin a ⊕ Fin b), .inr q.2) := by
                apply hinj
                simpa [joinedCountMap, Sym2.map_mk] using h
              rw [Sym2.eq_iff] at hbase
              rcases hbase with h | h <;> simp at h
      | inr s =>
          cases r with
          | inl z =>
              cases s with
              | inl w =>
                  congr 2
                  apply baseActiveLocalEdge_injective ha
                  apply hinj
                  simpa [joinedCountMap] using h
              | inr w =>
                  exfalso
                  obtain ⟨i, j, hz⟩ := active_edge_both_left (b := b) ha z
                  have hbase : baseActiveLocalEdge (b := b) ha z =
                      s((.inr (⟨0, by omega⟩ : Fin b)), .inr ⟨b - 1, by omega⟩) := by
                    apply hinj
                    simpa [joinedCountMap, Sym2.map_mk] using h
                  rw [hz, Sym2.eq_iff] at hbase
                  rcases hbase with h | h <;> simp at h
          | inr z =>
              cases s with
              | inl w =>
                  exfalso
                  obtain ⟨i, j, hw⟩ := active_edge_both_left (b := b) ha w
                  have hbase : s((.inr (⟨0, by omega⟩ : Fin b)), .inr ⟨b - 1, by omega⟩) =
                      baseActiveLocalEdge (b := b) ha w := by
                    apply hinj
                    simpa [joinedCountMap, Sym2.map_mk] using h
                  rw [hw, Sym2.eq_iff] at hbase
                  rcases hbase with h | h <;> simp at h
              | inr w =>
                  congr 2
                  exact Fin.ext (by omega)

private lemma joinedCountMap_mem_diameterEdge {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b)
    {z : (Fin a × Fin b) ⊕ ((Fin (a - 1) ⊕ Fin (activeExtraCount a)) ⊕ Fin 1)}
    (hz : z ∈ joinedCountDomain a b) :
    joinedCountMap ha hb z ∈ (diameterGraph (joinedConfiguration a b ha hb)).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  cases z with
  | inl p =>
      change dist (firstEmbed (activePoint a p.1))
        (secondEmbed (passivePoint a b ha hb p.2)) = 1
      exact dist_joined_cross_eq_one ha hb p.1 p.2
  | inr r =>
      cases r with
      | inl z =>
          cases z with
          | inl t =>
              change dist (firstEmbed (activePoint a ⟨t, by omega⟩))
                (firstEmbed (activePoint a ⟨(t : ℕ) + 1, by omega⟩)) = 1
              rw [dist_firstEmbed]
              exact activePoint_consecutive_dist_eq_one ha t
          | inr u =>
              have hextra : 0 < activeExtraCount a := by
                simpa using
                  (Fintype.card_pos_iff.mpr ⟨u⟩ : 0 < Fintype.card (Fin (activeExtraCount a)))
              have hodd : a % 2 = 1 := by
                unfold activeExtraCount at hextra
                split_ifs at hextra with h
                · exact h
                · omega
              change dist (firstEmbed (activePoint a ⟨a - 1, by omega⟩))
                (firstEmbed (activePoint a ⟨0, by omega⟩)) = 1
              rw [dist_firstEmbed]
              exact activePoint_last_dist_zero_eq_one ha hodd
      | inr u =>
          change dist (secondEmbed (passivePoint a b ha hb ⟨0, by omega⟩))
            (secondEmbed (passivePoint a b ha hb ⟨b - 1, by omega⟩)) = 1
          rw [dist_secondEmbed]
          exact dist_passive_endpoints_eq_one ha hb

private theorem joined_exact_count_le {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    a * b + cyclicDiameterAllowance a + 1 ≤
      diameterPairCount (joinedConfiguration a b ha hb) := by
  rw [diameterPairCount, ← card_joinedCountDomain (b := b) ha]
  exact Finset.card_le_card_of_injOn (joinedCountMap ha hb)
    (fun _ hz ↦ joinedCountMap_mem_diameterEdge ha hb hz)
    (joinedCountMap_injOn ha hb)

private lemma dist_activePoint_zero {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    dist (activePoint m i) 0 = regularRadius (polygonSize m) := by
  rw [dist_zero_right]
  have hsq := norm_circlePoint_sq (regularRadius (polygonSize m))
    (regularAngle (polygonSize m) (activeIndex i))
  change ‖activePoint m i‖ ^ 2 = regularRadius (polygonSize m) ^ 2 at hsq
  have hr : 0 < regularRadius (polygonSize m) := regularRadius_pos
    (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  nlinarith [norm_nonneg (activePoint m i)]

private lemma isDiameterOne_activeConfiguration {m : ℕ} (hm : 3 ≤ m) :
    IsDiameterOne (activeConfiguration m) := by
  rw [isDiameterOne_iff]
  refine ⟨activeConfiguration_pairwise_dist_le_one hm, ?_⟩
  let t : Fin (m - 1) := ⟨0, by omega⟩
  refine ⟨activePoint m ⟨t, by omega⟩, mem_activeConfiguration _,
    activePoint m ⟨(t : ℕ) + 1, by omega⟩, mem_activeConfiguration _, ?_⟩
  exact activePoint_consecutive_dist_eq_one hm t

/-- A centered two-dimensional circle block realizing the sharp cyclic
allowance.  For odd `m` it is the regular star cycle; for even `m` it is the
path obtained by deleting one vertex from the corresponding odd cycle. -/
theorem exists_activeCircleConfiguration (m : ℕ) (hm : 3 ≤ m) :
    ∃ (B : Finset (Point 2)) (s : ℝ),
      B.card = m ∧
      (∀ y ∈ B, dist y 0 = s) ∧
      0 < s ∧
      s ^ 2 ≤ 1 / 2 ∧
      IsDiameterOne B ∧
      cyclicDiameterAllowance m ≤ diameterPairCount B := by
  refine ⟨activeConfiguration m, regularRadius (polygonSize m),
    card_activeConfiguration hm, ?_, ?_, ?_, isDiameterOne_activeConfiguration hm,
    active_local_count_le_diameterPairCount hm⟩
  · simp only [activeConfiguration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro y ⟨i, rfl⟩
    exact dist_activePoint_zero hm i
  · exact regularRadius_pos
      (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)
  · exact regularRadius_sq_le_half
      (by unfold polygonSize; split_ifs <;> omega) (polygonSize_odd m)

/-- A variable-radius orthogonal two-circle construction in four dimensions.
The first carrier contributes its full odd cycle (or an even path), and the
second carrier contributes one endpoint diameter in addition to all cross
diameters. -/
theorem four_exact_lower_raw {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) :
    a * b + cyclicDiameterAllowance a + 1 ≤ f 4 (a + b) := by
  exact (joined_exact_count_le ha hb).trans
    (diameterPairCount_le_f (card_joinedConfiguration ha hb)
      (isDiameterOne_joinedConfiguration ha hb))

/-- The sharp four-dimensional lower bound, realized by the variable-radius
two-circle construction.  The conservative threshold `8` is enough to make
both carriers nondegenerate in every residue class modulo four. -/
theorem four_exact_lower {n : ℕ} (hn : 8 ≤ n) :
    turanNumber 2 n + ceilQuot n 2 + fourCorrection n ≤ f 4 n := by
  let k := n / 4
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr
  · have hnform : n = 4 * k := by dsimp [k]; omega
    have h := four_exact_lower_raw
      (a := 2 * k + 1) (b := 2 * k - 1) (by omega) (by omega)
    rw [show 2 * k + 1 + (2 * k - 1) = n by omega] at h
    have hdiv : n / 2 = 2 * k := by omega
    have hsub : n - n / 2 = 2 * k := by omega
    have hceil : ceilQuot n 2 = 2 * k := by unfold ceilQuot; omega
    calc
      turanNumber 2 n + ceilQuot n 2 + fourCorrection n =
          (2 * k + 1) * (2 * k - 1) + cyclicDiameterAllowance (2 * k + 1) + 1 := by
        rw [turanNumber_two, hsub, hdiv, hceil]
        simp [fourCorrection, cyclicDiameterAllowance, hr]
        have hcancel : 2 * k - 1 + 1 = 2 * k := by omega
        nlinarith
      _ ≤ f 4 n := h
  · have hnform : n = 4 * k + 1 := by dsimp [k]; omega
    have h := four_exact_lower_raw
      (a := 2 * k + 1) (b := 2 * k) (by omega) (by omega)
    rw [show 2 * k + 1 + 2 * k = n by omega] at h
    have hdiv : n / 2 = 2 * k := by omega
    have hsub : n - n / 2 = 2 * k + 1 := by omega
    have hceil : ceilQuot n 2 = 2 * k + 1 := by unfold ceilQuot; omega
    calc
      turanNumber 2 n + ceilQuot n 2 + fourCorrection n =
          (2 * k + 1) * (2 * k) + cyclicDiameterAllowance (2 * k + 1) + 1 := by
        rw [turanNumber_two, hsub, hdiv, hceil]
        simp [fourCorrection, cyclicDiameterAllowance, hr]
        ring
      _ ≤ f 4 n := h
  · have hnform : n = 4 * k + 2 := by dsimp [k]; omega
    have h := four_exact_lower_raw
      (a := 2 * k + 1) (b := 2 * k + 1) (by omega) (by omega)
    rw [show 2 * k + 1 + (2 * k + 1) = n by omega] at h
    have hdiv : n / 2 = 2 * k + 1 := by omega
    have hsub : n - n / 2 = 2 * k + 1 := by omega
    have hceil : ceilQuot n 2 = 2 * k + 1 := by unfold ceilQuot; omega
    calc
      turanNumber 2 n + ceilQuot n 2 + fourCorrection n =
          (2 * k + 1) * (2 * k + 1) + cyclicDiameterAllowance (2 * k + 1) + 1 := by
        rw [turanNumber_two, hsub, hdiv, hceil]
        simp [fourCorrection, cyclicDiameterAllowance, hr]
      _ ≤ f 4 n := h
  · have hnform : n = 4 * k + 3 := by dsimp [k]; omega
    have h := four_exact_lower_raw
      (a := 2 * k + 1) (b := 2 * k + 2) (by omega) (by omega)
    rw [show 2 * k + 1 + (2 * k + 2) = n by omega] at h
    have hdiv : n / 2 = 2 * k + 1 := by omega
    have hsub : n - n / 2 = 2 * k + 2 := by omega
    have hceil : ceilQuot n 2 = 2 * k + 2 := by unfold ceilQuot; omega
    calc
      turanNumber 2 n + ceilQuot n 2 + fourCorrection n =
          (2 * k + 1) * (2 * k + 2) + cyclicDiameterAllowance (2 * k + 1) + 1 := by
        rw [turanNumber_two, hsub, hdiv, hceil]
        simp [fourCorrection, cyclicDiameterAllowance, hr]
        omega
      _ ≤ f 4 n := h

end

end Erdos223
