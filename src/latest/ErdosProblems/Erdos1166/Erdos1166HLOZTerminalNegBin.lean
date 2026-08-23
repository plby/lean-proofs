import Mathlib

open scoped BigOperators

namespace Erdos1166.HLOZTerminalNegBin

noncomputable def nbMass (p q : ℝ) (b t : ℕ) : ℝ :=
  (Nat.choose (b + t - 1) t : ℝ) * p ^ b * q ^ t

lemma factorial_choose_shift (b k s : ℕ) (hb : 1 ≤ b) :
    (((s + k).descFactorial k : ℕ) : ℝ) *
        (Nat.choose (b + (s + k) - 1) (s + k) : ℝ) =
      (b.ascFactorial k : ℝ) *
        (Nat.choose (s + (b + k - 1)) (b + k - 1) : ℝ) := by
  have hleft : s + k ≤ b + (s + k) - 1 := by omega
  have hright : b + k - 1 ≤ s + (b + k - 1) := Nat.le_add_left _ _
  rw [Nat.cast_choose ℝ hleft, Nat.cast_choose ℝ hright]
  have hsub1 : b + (s + k) - 1 - (s + k) = b - 1 := by omega
  have hsub2 : s + (b + k - 1) - (b + k - 1) = s := by omega
  rw [hsub1, hsub2]
  have hindex : b + (s + k) - 1 = s + (b + k - 1) := by omega
  have hfact1 : (((b + (s + k) - 1).factorial : ℕ) : ℝ) =
      (((s + (b + k - 1)).factorial : ℕ) : ℝ) := by rw [hindex]
  rw [hfact1]
  have hsFac : (0 : ℝ) < (s.factorial : ℕ) := by positivity
  have hbFac : (0 : ℝ) < ((b - 1).factorial : ℕ) := by positivity
  have hbkFac : (0 : ℝ) < ((b + k - 1).factorial : ℕ) := by positivity
  have htFac : (0 : ℝ) < ((s + k).factorial : ℕ) := by positivity
  have hdescNat := Nat.factorial_mul_descFactorial (n := s + k) (k := k) (by omega)
  have hdesc : ((s + k).descFactorial k : ℝ) =
      ((s + k).factorial : ℝ) / s.factorial := by
    rw [eq_div_iff (ne_of_gt hsFac)]
    rw [mul_comm]
    exact_mod_cast (by simpa using hdescNat)
  have hasc : (b.ascFactorial k : ℝ) =
      ((b + k - 1).factorial : ℝ) / ((b - 1).factorial : ℝ) := by
    rw [eq_div_iff (ne_of_gt hbFac)]
    rw [mul_comm]
    exact_mod_cast Nat.factorial_mul_ascFactorial' b k (by omega)
  rw [hdesc, hasc]
  field_simp

lemma nb_factorial_moment_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) (k : ℕ) :
    HasSum (fun t : ℕ ↦ (t.descFactorial k : ℝ) * nbMass p q b t)
      ((b.ascFactorial k : ℝ) * (q / p) ^ k) := by
  let f : ℕ → ℝ := fun t ↦ (t.descFactorial k : ℝ) * nbMass p q b t
  have hprefix : ∑ t ∈ Finset.range k, f t = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have htk : t < k := Finset.mem_range.mp ht
    simp [f, Nat.descFactorial_eq_zero_iff_lt.mpr htk]
  rw [← hasSum_nat_add_iff' k]
  rw [hprefix, sub_zero]
  have hseries := hasSum_choose_mul_geometric_of_norm_lt_one
    (b + k - 1) (show ‖q‖ < 1 by simpa [Real.norm_eq_abs] using hq)
  have hmul := hseries.mul_left
    ((b.ascFactorial k : ℝ) * p ^ b * q ^ k)
  have hshift : HasSum (fun s : ℕ ↦ f (s + k))
      ((b.ascFactorial k : ℝ) * p ^ b * q ^ k *
        (1 / (1 - q) ^ (b + k - 1 + 1))) := by
    refine HasSum.congr_fun hmul ?_
    intro s
    dsimp [f, nbMass]
    calc
      (s + k).descFactorial k *
          ((b + (s + k) - 1).choose (s + k) * p ^ b * q ^ (s + k)) =
          ((s + k).descFactorial k *
            (b + (s + k) - 1).choose (s + k)) * p ^ b * q ^ (s + k) := by ring
      _ = (b.ascFactorial k *
            (s + (b + k - 1)).choose (b + k - 1)) * p ^ b * q ^ (s + k) := by
          rw [factorial_choose_shift b k s hb]
      _ = b.ascFactorial k * p ^ b * q ^ k *
            ((s + (b + k - 1)).choose (b + k - 1) * q ^ s) := by
          rw [pow_add]
          ring
  have hvalue :
      (b.ascFactorial k : ℝ) * (q / p) ^ k =
        (b.ascFactorial k : ℝ) * p ^ b * q ^ k *
          (1 / (1 - q) ^ (b + k - 1 + 1)) := by
    rw [hp]
    have hp0 : 1 - q ≠ 0 := by linarith [lt_of_abs_lt hq]
    have hexp : b + k - 1 + 1 = b + k := by omega
    rw [hexp]
    simp only [div_pow, one_div, inv_pow, pow_add]
    field_simp [pow_ne_zero _ hp0]
  rwa [hvalue]

lemma nb_total_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (nbMass p q b) 1 := by
  convert nb_factorial_moment_hasSum hb hq hp 0 using 1
  · funext t
    simp [nbMass]
  · simp [Nat.ascFactorial]

private lemma pow_two_eq_desc (t : ℕ) :
    (t : ℝ) ^ 2 = (t.descFactorial 2 : ℝ) + t.descFactorial 1 := by
  by_cases ht : t < 2
  · interval_cases t <;> norm_num [Nat.descFactorial]
  · have h1 : 1 ≤ t := by omega
    simp only [Nat.descFactorial, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one,
      Nat.sub_zero, Nat.cast_id]
    ring

private lemma pow_three_eq_desc (t : ℕ) :
    (t : ℝ) ^ 3 = (t.descFactorial 3 : ℝ) +
      3 * t.descFactorial 2 + t.descFactorial 1 := by
  by_cases ht : t < 3
  · interval_cases t <;> norm_num [Nat.descFactorial]
  · have h1 : 1 ≤ t := by omega
    have h2 : 2 ≤ t := by omega
    simp only [Nat.descFactorial, Nat.cast_mul, Nat.cast_sub h1,
      Nat.cast_sub h2, Nat.cast_one, Nat.cast_ofNat, Nat.sub_zero, Nat.cast_id]
    ring

private lemma pow_four_eq_desc (t : ℕ) :
    (t : ℝ) ^ 4 = (t.descFactorial 4 : ℝ) +
      6 * t.descFactorial 3 + 7 * t.descFactorial 2 + t.descFactorial 1 := by
  by_cases ht : t < 4
  · interval_cases t <;> norm_num [Nat.descFactorial]
  · have h1 : 1 ≤ t := by omega
    have h2 : 2 ≤ t := by omega
    have h3 : 3 ≤ t := by omega
    simp only [Nat.descFactorial, Nat.cast_mul, Nat.cast_sub h1,
      Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_one, Nat.cast_ofNat,
      Nat.sub_zero, Nat.cast_id]
    ring

lemma nb_raw_one_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (fun t : ℕ ↦ nbMass p q b t * t)
      ((b : ℝ) * (q / p)) := by
  simpa [Nat.descFactorial, Nat.ascFactorial, mul_comm] using
    nb_factorial_moment_hasSum hb hq hp 1

lemma nb_raw_two_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (fun t : ℕ ↦ nbMass p q b t * (t : ℝ) ^ 2)
      ((b : ℝ) * (b + 1) * (q / p) ^ 2 + (b : ℝ) * (q / p)) := by
  have h2 := nb_factorial_moment_hasSum hb hq hp 2
  have h1 := nb_factorial_moment_hasSum hb hq hp 1
  convert h2.add h1 using 1
  · funext t
    rw [pow_two_eq_desc]
    ring
  · simp only [Nat.ascFactorial]
    push_cast
    ring

lemma nb_raw_three_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (fun t : ℕ ↦ nbMass p q b t * (t : ℝ) ^ 3)
      ((b : ℝ) * (b + 1) * (b + 2) * (q / p) ^ 3 +
        3 * (b : ℝ) * (b + 1) * (q / p) ^ 2 + (b : ℝ) * (q / p)) := by
  have h3 := nb_factorial_moment_hasSum hb hq hp 3
  have h2 := (nb_factorial_moment_hasSum hb hq hp 2).mul_left 3
  have h1 := nb_factorial_moment_hasSum hb hq hp 1
  convert (h3.add h2).add h1 using 1
  · funext t
    rw [pow_three_eq_desc]
    ring
  · simp only [Nat.ascFactorial]
    push_cast
    ring

lemma nb_raw_four_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (fun t : ℕ ↦ nbMass p q b t * (t : ℝ) ^ 4)
      ((b : ℝ) * (b + 1) * (b + 2) * (b + 3) * (q / p) ^ 4 +
        6 * (b : ℝ) * (b + 1) * (b + 2) * (q / p) ^ 3 +
        7 * (b : ℝ) * (b + 1) * (q / p) ^ 2 + (b : ℝ) * (q / p)) := by
  have h4 := nb_factorial_moment_hasSum hb hq hp 4
  have h3 := (nb_factorial_moment_hasSum hb hq hp 3).mul_left 6
  have h2 := (nb_factorial_moment_hasSum hb hq hp 2).mul_left 7
  have h1 := nb_factorial_moment_hasSum hb hq hp 1
  convert ((h4.add h3).add h2).add h1 using 1
  · funext t
    rw [pow_four_eq_desc]
    ring
  · simp only [Nat.ascFactorial]
    push_cast
    ring

lemma nb_centered_second_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - (b : ℝ) * (q / p)) ^ 2)
      ((b : ℝ) * (q / p) * (1 + q / p)) := by
  let mu : ℝ := (b : ℝ) * (q / p)
  have h2 := nb_raw_two_hasSum hb hq hp
  have h1 := (nb_raw_one_hasSum hb hq hp).mul_left (-2 * mu)
  have h0 := (nb_total_hasSum hb hq hp).mul_left (mu ^ 2)
  convert (h2.add h1).add h0 using 1
  · funext t
    dsimp [mu]
    ring
  · dsimp [mu]
    ring

lemma nb_centered_four_hasSum {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hq : |q| < 1) (hp : p = 1 - q) :
    HasSum (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - (b : ℝ) * (q / p)) ^ 4)
      (3 * ((b : ℝ) * (q / p) * (1 + q / p)) ^ 2 +
        (b : ℝ) * (q / p) * (1 + q / p) *
          (1 + 6 * (q / p) + 6 * (q / p) ^ 2)) := by
  let mu : ℝ := (b : ℝ) * (q / p)
  have h4 := nb_raw_four_hasSum hb hq hp
  have h3 := (nb_raw_three_hasSum hb hq hp).mul_left (-4 * mu)
  have h2 := (nb_raw_two_hasSum hb hq hp).mul_left (6 * mu ^ 2)
  have h1 := (nb_raw_one_hasSum hb hq hp).mul_left (-4 * mu ^ 3)
  have h0 := (nb_total_hasSum hb hq hp).mul_left (mu ^ 4)
  convert ((((h4.add h3).add h2).add h1).add h0) using 1
  · funext t
    dsimp [mu]
    ring
  · dsimp [mu]
    ring

private lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  have ha := abs_nonneg x
  have hs := sq_nonneg (|x| - 1 / 2)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith

private lemma square_le_two_mul_abs_add_fourth_div
    {s x : ℝ} (hs : 0 < s) :
    x ^ 2 ≤ 2 * s * |x| + x ^ 4 / (16 * s ^ 2) := by
  let y := |x| / s
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyineq : y ^ 2 ≤ 2 * y + y ^ 4 / 16 := by
    by_cases h2 : y ≤ 2
    · have hm : 0 ≤ y * (2 - y) := mul_nonneg hy (sub_nonneg.mpr h2)
      have h4 : 0 ≤ y ^ 4 := by positivity
      nlinarith
    · have hsq := sq_nonneg (y ^ 2 - 8)
      have hy2 : 2 ≤ y := le_of_not_ge h2
      nlinarith
  have hs0 : s ≠ 0 := ne_of_gt hs
  have habsq : |x| ^ 2 = x ^ 2 := sq_abs x
  have habfour : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [habsq]
      _ = x ^ 4 := by ring
  dsimp [y] at hyineq
  rw [div_pow, div_pow, habsq, habfour] at hyineq
  field_simp [hs0] at hyineq ⊢
  nlinarith [sq_pos_of_pos hs]

private lemma positive_part_le_indicator_add_square
    {s x : ℝ} (hs : 0 < s) :
    max x 0 ≤ 2 * s * (if 0 ≤ x then 1 else 0) + (max x 0) ^ 2 / (8 * s) := by
  by_cases hx : 0 ≤ x
  · simp only [hx, if_pos, max_eq_left]
    have hsq := sq_nonneg (x - 4 * s)
    have hs0 : s ≠ 0 := ne_of_gt hs
    have haux : x - 2 * s ≤ x ^ 2 / (8 * s) := by
      apply (le_div_iff₀ (show 0 < 8 * s by positivity)).2
      nlinarith
    nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [hx, max_eq_right hx']

private theorem above_mean_mass_lower
    (m : ℕ → ℝ) (z : ℕ → ℝ) {v e4 : ℝ}
    (hm : ∀ t, 0 ≤ m t)
    (htotal : HasSum m 1)
    (hcentered : HasSum (fun t ↦ m t * z t) 0)
    (hsecond : HasSum (fun t ↦ m t * (z t) ^ 2) v)
    (hfourth : HasSum (fun t ↦ m t * (z t) ^ 4) e4)
    (hv : 0 < v) (he4 : e4 ≤ 4 * v ^ 2) :
    1 / 32 ≤ ∑' t : ℕ, if 0 ≤ z t then m t else 0 := by
  let s := Real.sqrt v
  let a : ℕ → ℝ := fun t ↦ m t * |z t|
  let pos : ℕ → ℝ := fun t ↦ m t * max (z t) 0
  let neg : ℕ → ℝ := fun t ↦ m t * max (-z t) 0
  let ind : ℕ → ℝ := fun t ↦ if 0 ≤ z t then m t else 0
  have hs : 0 < s := Real.sqrt_pos.2 hv
  have hs_sq : s ^ 2 = v := Real.sq_sqrt hv.le
  have ha : Summable a := by
    apply Summable.of_nonneg_of_le
      (fun t ↦ mul_nonneg (hm t) (abs_nonneg _))
      (fun t ↦ ?_) (htotal.add hsecond).summable
    calc
      m t * |z t| ≤ m t * (1 + z t ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_le_one_add_sq _) (hm t)
      _ = m t + m t * z t ^ 2 := by ring
  have hpos : Summable pos := by
    apply Summable.of_nonneg_of_le
      (fun t ↦ mul_nonneg (hm t) (le_max_right _ _))
      (fun t ↦ ?_) ha
    dsimp [pos, a]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (hm t)
  have hneg : Summable neg := by
    apply Summable.of_nonneg_of_le
      (fun t ↦ mul_nonneg (hm t) (le_max_right _ _))
      (fun t ↦ ?_) ha
    dsimp [neg, a]
    have habs : |-z t| = |z t| := abs_neg _
    rw [← habs]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (hm t)
  have hind : Summable ind := by
    apply Summable.of_nonneg_of_le
      (fun t ↦ by dsimp [ind]; split_ifs <;> simp [hm])
      (fun t ↦ ?_) htotal.summable
    dsimp [ind]
    split_ifs <;> simp [hm]
  have hpos_sub_neg : HasSum (fun t ↦ pos t - neg t) 0 := by
    convert hcentered using 1
    funext t
    dsimp [pos, neg]
    by_cases hz : 0 ≤ z t
    · simp [hz]
    · have hz' : z t ≤ 0 := le_of_not_ge hz
      simp [hz, hz']
  have hpos_eq_neg : ∑' t, pos t = ∑' t, neg t := by
    have hvsum := (hpos.hasSum.sub hneg.hasSum).unique hpos_sub_neg
    linarith
  have habs_eq_two_pos : ∑' t, a t = 2 * ∑' t, pos t := by
    have hfun : a = fun t ↦ pos t + neg t := by
      funext t
      dsimp [a, pos, neg]
      by_cases hz : 0 ≤ z t
      · simp [abs_of_nonneg hz, hz]
      · have hz' : z t ≤ 0 := le_of_not_ge hz
        simp [abs_of_nonpos hz', hz']
    rw [hfun, hpos.tsum_add hneg, hpos_eq_neg]
    ring
  have hinterp : v ≤ 2 * s * (∑' t, a t) + e4 / (16 * s ^ 2) := by
    have hrhs := (ha.hasSum.mul_left (2 * s)).add
      (hfourth.mul_left (1 / (16 * s ^ 2)))
    have hle : ∀ t, m t * z t ^ 2 ≤
        2 * s * a t + 1 / (16 * s ^ 2) * (m t * z t ^ 4) := by
      intro t
      dsimp [a]
      calc
        m t * z t ^ 2 ≤ m t *
            (2 * s * |z t| + z t ^ 4 / (16 * s ^ 2)) :=
          mul_le_mul_of_nonneg_left (square_le_two_mul_abs_add_fourth_div hs) (hm t)
        _ = 2 * s * (m t * |z t|) + 1 / (16 * s ^ 2) * (m t * z t ^ 4) := by ring
    have h := hasSum_le hle hsecond hrhs
    calc
      v ≤ 2 * s * (∑' t, a t) + 1 / (16 * s ^ 2) * e4 := h
      _ = 2 * s * (∑' t, a t) + e4 / (16 * s ^ 2) := by ring
  have ha_lower : 3 * s / 8 ≤ ∑' t, a t := by
    rw [hs_sq] at hinterp
    have hv0 : v ≠ 0 := ne_of_gt hv
    have hfrac : e4 / (16 * v) ≤ v / 4 := by
      apply (div_le_iff₀ (show 0 < 16 * v by positivity)).2
      nlinarith
    have hupper : 2 * s * (∑' t, a t) + e4 / (16 * v) ≤
        2 * s * (∑' t, a t) + v / 4 := by linarith
    have h := hinterp.trans hupper
    nlinarith [h, hs_sq]
  have hpos_lower : 3 * s / 16 ≤ ∑' t, pos t := by
    rw [habs_eq_two_pos] at ha_lower
    linarith
  have hpos_upper : ∑' t, pos t ≤
      2 * s * (∑' t, ind t) + v / (8 * s) := by
    have hrhs := (hind.hasSum.mul_left (2 * s)).add
      (hsecond.mul_left (1 / (8 * s)))
    have hle : ∀ t, pos t ≤
        2 * s * ind t + 1 / (8 * s) * (m t * z t ^ 2) := by
      intro t
      dsimp [pos, ind]
      have hpartSq : (max (z t) 0) ^ 2 ≤ z t ^ 2 := by
        by_cases hz : 0 ≤ z t
        · simp [hz]
        · have hz' : z t ≤ 0 := le_of_not_ge hz
          simp [hz']
          exact sq_nonneg _
      calc
        m t * max (z t) 0 ≤ m t *
            (2 * s * (if 0 ≤ z t then 1 else 0) +
              (max (z t) 0) ^ 2 / (8 * s)) :=
          mul_le_mul_of_nonneg_left (positive_part_le_indicator_add_square hs) (hm t)
        _ ≤ m t *
            (2 * s * (if 0 ≤ z t then 1 else 0) + z t ^ 2 / (8 * s)) := by
          gcongr
          exact hm t
        _ = 2 * s * (if 0 ≤ z t then m t else 0) +
            1 / (8 * s) * (m t * z t ^ 2) := by
          split_ifs <;> ring
    have h := hasSum_le hle hpos.hasSum hrhs
    calc
      ∑' t, pos t ≤ 2 * s * (∑' t, ind t) + 1 / (8 * s) * v := h
      _ = 2 * s * (∑' t, ind t) + v / (8 * s) := by ring
  have hvs : v / (8 * s) = s / 8 := by
    rw [← hs_sq]
    field_simp [ne_of_gt hs]
  rw [hvs] at hpos_upper
  have hprob : 1 / 32 ≤ ∑' t, ind t := by
    nlinarith
  exact hprob

theorem nb_above_mean_lower {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hp0 : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hp : p = 1 - q) (hr1 : q / p ≤ 1)
    (hbr : 13 ≤ (b : ℝ) * (q / p)) :
    1 / 32 ≤ ∑' t : ℕ,
      if (b : ℝ) * (q / p) ≤ t then nbMass p q b t else 0 := by
  let r : ℝ := q / p
  let mu : ℝ := (b : ℝ) * r
  let v : ℝ := (b : ℝ) * r * (1 + r)
  let e4 : ℝ := 3 * v ^ 2 + v * (1 + 6 * r + 6 * r ^ 2)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hv : 0 < v := by
    dsimp [v, r] at ⊢ hbr
    have : 0 < (b : ℝ) * (q / p) := lt_of_lt_of_le (by norm_num) hbr
    positivity
  have hm : ∀ t, 0 ≤ nbMass p q b t := by
    intro t
    unfold nbMass
    positivity
  have htotal := nb_total_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have hraw1 := nb_raw_one_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have hcentered : HasSum
      (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - mu)) 0 := by
    have h := hraw1.add (htotal.mul_left (-mu))
    convert h using 1
    · funext t
      dsimp [mu, r]
      ring
    · dsimp [mu, r]
      ring
  have hsecond : HasSum
      (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - mu) ^ 2) v := by
    simpa [mu, v, r] using
      (nb_centered_second_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp)
  have hfourth : HasSum
      (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - mu) ^ 4) e4 := by
    simpa [mu, v, e4, r] using
      (nb_centered_four_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp)
  have hc : 1 + 6 * r + 6 * r ^ 2 ≤ 13 := by
    have hm := mul_nonneg hr0 (sub_nonneg.mpr hr1)
    nlinarith
  have hv13 : 13 ≤ v := by
    dsimp [v, r] at ⊢ hbr
    have hnonneg : 0 ≤ (b : ℝ) * (q / p) * (q / p) := by positivity
    nlinarith
  have he4 : e4 ≤ 4 * v ^ 2 := by
    dsimp [e4]
    have hvc : v * (1 + 6 * r + 6 * r ^ 2) ≤ v * v :=
      mul_le_mul_of_nonneg_left (hc.trans hv13) hv.le
    nlinarith
  simpa [mu, r] using
    (above_mean_mass_lower (nbMass p q b)
      (fun t ↦ (t : ℝ) - mu) hm htotal hcentered hsecond hfourth hv he4)

/-- A concrete finite-window consequence of the one-sided moment bound.  The
only loss is the first-moment estimate for the part above `N`. -/
theorem nb_interval_lower {p q : ℝ} {b N : ℕ} {L : ℝ}
    (hb : 1 ≤ b) (hp0 : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hp : p = 1 - q) (hr1 : q / p ≤ 1)
    (hbr : 13 ≤ (b : ℝ) * (q / p)) (hN : 1 ≤ N)
    (hL : L ≤ (b : ℝ) * (q / p))
    (htail : ((b : ℝ) * (q / p)) / N ≤ 1 / 64) :
    1 / 64 ≤ ∑ t ∈ Finset.range (N + 1),
      if L ≤ (t : ℝ) then nbMass p q b t else 0 := by
  let mu : ℝ := (b : ℝ) * (q / p)
  let f : ℕ → ℝ := fun t ↦ if mu ≤ (t : ℝ) then nbMass p q b t else 0
  have hmass : ∀ t, 0 ≤ nbMass p q b t := by
    intro t
    unfold nbMass
    positivity
  have htotal := nb_total_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun t ↦ ?_) (fun t ↦ ?_) htotal.summable
    · dsimp [f]
      split_ifs <;> simp [hmass]
    · dsimp [f]
      split_ifs <;> simp [hmass]
  have habove : 1 / 32 ≤ ∑' t, f t := by
    simpa [f, mu] using
      (nb_above_mean_lower hb hp0 hq0 hq1 hp hr1 hbr)
  have hraw := nb_raw_one_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have htailSummable : Summable (fun j ↦ f (j + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 hf
  have htailBound : ∑' j, f (j + (N + 1)) ≤ mu / N := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hdom := hraw.mul_left (1 / (N : ℝ))
    have hle : ∀ j : ℕ, f (j + (N + 1)) ≤
        (1 / (N : ℝ)) *
          (nbMass p q b (j + (N + 1)) * ((j + (N + 1) : ℕ) : ℝ)) := by
      intro j
      dsimp [f]
      split_ifs with hj
      · have htN : (N : ℝ) ≤ ((j + (N + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show N ≤ j + (N + 1) by omega)
        calc
          nbMass p q b (j + (N + 1)) ≤
              nbMass p q b (j + (N + 1)) *
                (((j + (N + 1) : ℕ) : ℝ) / N) := by
            have hratio : (1 : ℝ) ≤ ((j + (N + 1) : ℕ) : ℝ) / N := by
              apply (le_div_iff₀ hNreal).2
              simpa using htN
            calc
              nbMass p q b (j + (N + 1)) =
                  nbMass p q b (j + (N + 1)) * 1 := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hratio (hmass _)
          _ = (1 / (N : ℝ)) *
              (nbMass p q b (j + (N + 1)) * ((j + (N + 1) : ℕ) : ℝ)) := by ring
      · exact mul_nonneg (by positivity) (mul_nonneg (hmass _) (by positivity))
    have h := Summable.tsum_le_tsum_of_inj
      (fun j : ℕ ↦ j + (N + 1)) (fun a c hac ↦ Nat.add_right_cancel hac)
      (fun t ht ↦ mul_nonneg (by positivity) (mul_nonneg (hmass t) (by positivity)))
      hle htailSummable hdom.summable
    rw [hdom.tsum_eq] at h
    calc
      ∑' j, f (j + (N + 1)) ≤
          (1 / (N : ℝ)) * ((b : ℝ) * (q / p)) := h
      _ = mu / N := by dsimp [mu]; ring
  have hsplit :
      (∑ t ∈ Finset.range (N + 1), f t) +
          ∑' j, f (j + (N + 1)) = ∑' t, f t :=
    hf.sum_add_tsum_nat_add (N + 1)
  have hprefix : 1 / 64 ≤ ∑ t ∈ Finset.range (N + 1), f t := by
    nlinarith
  calc
    1 / 64 ≤ ∑ t ∈ Finset.range (N + 1), f t := hprefix
    _ ≤ ∑ t ∈ Finset.range (N + 1),
        if L ≤ (t : ℝ) then nbMass p q b t else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      dsimp [f]
      split_ifs with hmu hlow
      · rfl
      · exact False.elim (hlow (hL.trans hmu))
      · exact hmass t
      · exact le_rfl

/-! The terminal recentering in Erdős 1164 needs the same estimate when the
failure/success ratio approaches one from either side.  The fourth-moment
argument above only used `r ≤ 1` to bound a fixed polynomial.  On the wider
compact range `r ≤ 2`, replacing `13` by `37` gives the identical conclusion.
-/

theorem nb_above_mean_lower_of_ratio_le_two {p q : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hp0 : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hp : p = 1 - q) (hr2 : q / p ≤ 2)
    (hbr : 37 ≤ (b : ℝ) * (q / p)) :
    1 / 32 ≤ ∑' t : ℕ,
      if (b : ℝ) * (q / p) ≤ t then nbMass p q b t else 0 := by
  let r : ℝ := q / p
  let mu : ℝ := (b : ℝ) * r
  let v : ℝ := (b : ℝ) * r * (1 + r)
  let e4 : ℝ := 3 * v ^ 2 + v * (1 + 6 * r + 6 * r ^ 2)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hv : 0 < v := by
    dsimp [v, r] at ⊢ hbr
    have : 0 < (b : ℝ) * (q / p) := lt_of_lt_of_le (by norm_num) hbr
    positivity
  have hm : ∀ t, 0 ≤ nbMass p q b t := by
    intro t
    unfold nbMass
    positivity
  have htotal := nb_total_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have hraw1 := nb_raw_one_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have hcentered : HasSum
      (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - mu)) 0 := by
    have h := hraw1.add (htotal.mul_left (-mu))
    convert h using 1
    · funext t
      dsimp [mu, r]
      ring
    · dsimp [mu, r]
      ring
  have hsecond : HasSum
      (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - mu) ^ 2) v := by
    simpa [mu, v, r] using
      (nb_centered_second_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp)
  have hfourth : HasSum
      (fun t : ℕ ↦ nbMass p q b t * ((t : ℝ) - mu) ^ 4) e4 := by
    simpa [mu, v, e4, r] using
      (nb_centered_four_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp)
  have hc : 1 + 6 * r + 6 * r ^ 2 ≤ 37 := by
    have hm := mul_nonneg hr0 (sub_nonneg.mpr hr2)
    nlinarith
  have hv37 : 37 ≤ v := by
    dsimp [v, r] at ⊢ hbr
    have hnonneg : 0 ≤ (b : ℝ) * (q / p) * (q / p) := by positivity
    nlinarith
  have he4 : e4 ≤ 4 * v ^ 2 := by
    dsimp [e4]
    have hvc : v * (1 + 6 * r + 6 * r ^ 2) ≤ v * v :=
      mul_le_mul_of_nonneg_left (hc.trans hv37) hv.le
    nlinarith
  simpa [mu, r] using
    (above_mean_mass_lower (nbMass p q b)
      (fun t ↦ (t : ℝ) - mu) hm htotal hcentered hsecond hfourth hv he4)

theorem nb_interval_lower_of_ratio_le_two {p q : ℝ} {b N : ℕ} {L : ℝ}
    (hb : 1 ≤ b) (hp0 : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hp : p = 1 - q) (hr2 : q / p ≤ 2)
    (hbr : 37 ≤ (b : ℝ) * (q / p)) (hN : 1 ≤ N)
    (hL : L ≤ (b : ℝ) * (q / p))
    (htail : ((b : ℝ) * (q / p)) / N ≤ 1 / 64) :
    1 / 64 ≤ ∑ t ∈ Finset.range (N + 1),
      if L ≤ (t : ℝ) then nbMass p q b t else 0 := by
  let mu : ℝ := (b : ℝ) * (q / p)
  let f : ℕ → ℝ := fun t ↦ if mu ≤ (t : ℝ) then nbMass p q b t else 0
  have hmass : ∀ t, 0 ≤ nbMass p q b t := by
    intro t
    unfold nbMass
    positivity
  have htotal := nb_total_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun t ↦ ?_) (fun t ↦ ?_) htotal.summable
    · dsimp [f]
      split_ifs <;> simp [hmass]
    · dsimp [f]
      split_ifs <;> simp [hmass]
  have habove : 1 / 32 ≤ ∑' t, f t := by
    simpa [f, mu] using
      (nb_above_mean_lower_of_ratio_le_two hb hp0 hq0 hq1 hp hr2 hbr)
  have hraw := nb_raw_one_hasSum hb (by rw [abs_of_nonneg hq0]; exact hq1) hp
  have htailSummable : Summable (fun j ↦ f (j + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 hf
  have htailBound : ∑' j, f (j + (N + 1)) ≤ mu / N := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hdom := hraw.mul_left (1 / (N : ℝ))
    have hle : ∀ j : ℕ, f (j + (N + 1)) ≤
        (1 / (N : ℝ)) *
          (nbMass p q b (j + (N + 1)) * ((j + (N + 1) : ℕ) : ℝ)) := by
      intro j
      dsimp [f]
      split_ifs with hj
      · have htN : (N : ℝ) ≤ ((j + (N + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show N ≤ j + (N + 1) by omega)
        calc
          nbMass p q b (j + (N + 1)) ≤
              nbMass p q b (j + (N + 1)) *
                (((j + (N + 1) : ℕ) : ℝ) / N) := by
            have hratio : (1 : ℝ) ≤ ((j + (N + 1) : ℕ) : ℝ) / N := by
              apply (le_div_iff₀ hNreal).2
              simpa using htN
            calc
              nbMass p q b (j + (N + 1)) =
                  nbMass p q b (j + (N + 1)) * 1 := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hratio (hmass _)
          _ = (1 / (N : ℝ)) *
              (nbMass p q b (j + (N + 1)) * ((j + (N + 1) : ℕ) : ℝ)) := by ring
      · exact mul_nonneg (by positivity) (mul_nonneg (hmass _) (by positivity))
    have h := Summable.tsum_le_tsum_of_inj
      (fun j : ℕ ↦ j + (N + 1)) (fun a c hac ↦ Nat.add_right_cancel hac)
      (fun t ht ↦ mul_nonneg (by positivity) (mul_nonneg (hmass t) (by positivity)))
      hle htailSummable hdom.summable
    rw [hdom.tsum_eq] at h
    calc
      ∑' j, f (j + (N + 1)) ≤
          (1 / (N : ℝ)) * ((b : ℝ) * (q / p)) := h
      _ = mu / N := by dsimp [mu]; ring
  have hsplit :
      (∑ t ∈ Finset.range (N + 1), f t) +
          ∑' j, f (j + (N + 1)) = ∑' t, f t :=
    hf.sum_add_tsum_nat_add (N + 1)
  have hprefix : 1 / 64 ≤ ∑ t ∈ Finset.range (N + 1), f t := by
    nlinarith
  calc
    1 / 64 ≤ ∑ t ∈ Finset.range (N + 1), f t := hprefix
    _ ≤ ∑ t ∈ Finset.range (N + 1),
        if L ≤ (t : ℝ) then nbMass p q b t else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      dsimp [f]
      split_ifs with hmu hlow
      · rfl
      · exact False.elim (hlow (hL.trans hmu))
      · exact hmass t
      · exact le_rfl

end Erdos1166.HLOZTerminalNegBin
