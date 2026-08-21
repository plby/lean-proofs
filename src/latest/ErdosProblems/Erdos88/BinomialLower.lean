import ErdosProblems.Erdos88.SwitchingHalasz

/-!
# Near-central binomial lower bounds

Explicit square-root-scale lower bounds for the binomial coefficients used
in the conditioned-state count in KSSS Lemma 13.6(2).
-/

namespace Erdos88.Switching

/-- A uniform lower estimate for the central binomial coefficient. -/
lemma two_pow_div_four_sqrt_le_choose_middle :
    ∀ k : ℕ, 1 ≤ k →
      (2 : ℝ) ^ k / (4 * Real.sqrt k) ≤ Nat.choose k (k / 2) := by
  have hEven : ∀ m : ℕ, 1 ≤ m →
      (4 : ℝ) ^ m / (2 * Real.sqrt m) ≤ Nat.choose (2 * m) m := by
    intro m hm
    have hsq : (4 : ℝ) ^ (2 * m) ≤
        4 * m * (Nat.choose (2 * m) m : ℝ) ^ 2 := by
      induction m with
      | zero => omega
      | succ m ih =>
          by_cases hm0 : m = 0
          · subst m
            norm_num
          · have ihm := ih (by omega)
            have hsucc :
                (Nat.choose (2 * m + 2) (m + 1) : ℝ) =
                  (Nat.choose (2 * m) m : ℝ) * (2 * m + 1) * 2 / (m + 1) := by
              rw [Nat.cast_choose, Nat.cast_choose] <;> try omega
              norm_num [two_mul, add_assoc, Nat.factorial]
              ring_nf
              rw [show 2 + m * 2 - (1 + m) = m + 1 by
                rw [Nat.sub_eq_of_eq_add]
                ring]
              norm_num [Nat.factorial_succ]
              ring_nf
              field_simp
              ring
            rw [show 2 * (m + 1) = 2 * m + 2 by ring, hsucc]
            push_cast at ihm ⊢
            field_simp
            have hscale := mul_le_mul_of_nonneg_left ihm
              (show (0 : ℝ) ≤ 16 * (m + 1) by positivity)
            have hpoly : 4 * (m : ℝ) * (m + 1) ≤ (2 * m + 1) ^ 2 := by
              nlinarith
            have hscale2 := mul_le_mul_of_nonneg_left hpoly
              (show (0 : ℝ) ≤ 16 * (Nat.choose (2 * m) m : ℝ) ^ 2 by
                positivity)
            norm_num [pow_add] at hscale ⊢
            nlinarith
    have hsq' :
        ((4 : ℝ) ^ m / (2 * Real.sqrt m)) ^ 2 ≤
          (Nat.choose (2 * m) m : ℝ) ^ 2 := by
      rw [div_pow]
      have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = m := by
        rw [Real.sq_sqrt]
        positivity
      rw [mul_pow, hsqrt]
      norm_num
      rw [div_le_iff₀]
      · simpa only [pow_mul, mul_comm] using hsq
      · positivity
    exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsq'
  intro k hk
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by omega
    have h := hEven m hm
    calc
      (2 : ℝ) ^ (2 * m) / (4 * Real.sqrt ((2 * m : ℕ) : ℝ)) ≤
          (4 : ℝ) ^ m / (2 * Real.sqrt m) := by
        rw [pow_mul]
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have hsqrt : Real.sqrt (m : ℝ) ≤
            Real.sqrt (((2 * m : ℕ) : ℝ)) :=
          Real.sqrt_le_sqrt (by push_cast; nlinarith)
        have hsqrtm0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
        have hsqrt0 : 0 ≤ Real.sqrt (((2 * m : ℕ) : ℝ)) := Real.sqrt_nonneg _
        nlinarith
      _ ≤ Nat.choose (2 * m) m := h
      _ = Nat.choose (2 * m) ((2 * m) / 2) := by
        rw [show (2 * m) / 2 = m by omega]
  · have hm : 0 ≤ m := Nat.zero_le m
    by_cases hm0 : m = 0
    · subst m
      norm_num
    · have h := hEven m (by omega)
      have hchoose : Nat.choose (2 * m) m ≤ Nat.choose (2 * m + 1) m := by
        exact Nat.choose_le_choose m (by omega)
      calc
        (2 : ℝ) ^ (2 * m + 1) /
            (4 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) =
            (4 : ℝ) ^ m /
              (2 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) := by
          rw [pow_add, pow_one, pow_mul]
          ring
        _ ≤ (4 : ℝ) ^ m / (2 * Real.sqrt m) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          have hsqrt : Real.sqrt (m : ℝ) ≤
              Real.sqrt (((2 * m + 1 : ℕ) : ℝ)) :=
            Real.sqrt_le_sqrt (by push_cast; nlinarith)
          exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        _ ≤ Nat.choose (2 * m) m := h
        _ ≤ Nat.choose (2 * m + 1) m := by exact_mod_cast hchoose
        _ = Nat.choose (2 * m + 1) ((2 * m + 1) / 2) := by
          congr 1
          norm_num [Nat.add_div]

/-- Moving at most `D` places below the middle loses at most a fixed power
of `1 - 4D/m`. -/
lemma choose_two_mul_sub_ge_middle_mul_pow (m D d : ℕ)
    (hd : d ≤ D) (hD : 4 * D ≤ m) :
    (Nat.choose (2 * m) m : ℝ) * (1 - (4 * D : ℝ) / m) ^ d ≤
      Nat.choose (2 * m) (m - d) := by
  by_cases hm0 : m = 0
  · subst m
    have hD0 : D = 0 := by omega
    subst D
    have hd0 : d = 0 := by omega
    subst d
    norm_num
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hb0 : 0 ≤ 1 - (4 * D : ℝ) / m := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast hD
  induction d with
  | zero => simp
  | succ d ih =>
      have hdD : d ≤ D := (Nat.le_succ d).trans hd
      have hdltm : d + 1 ≤ m := by omega
      let k := m - (d + 1)
      have hk1 : k + 1 = m - d := by dsimp only [k]; omega
      have hden : 2 * m - k = m + d + 1 := by dsimp only [k]; omega
      have hrecNat := Nat.choose_succ_right_eq (2 * m) k
      have hrec := congrArg (fun z : ℕ ↦ (z : ℝ)) hrecNat
      push_cast at hrec
      have hfactor :
          (1 - (4 * D : ℝ) / m) * (2 * m - k : ℕ) ≤ (k + 1 : ℕ) := by
        rw [hden, hk1]
        push_cast
        rw [Nat.cast_sub (by omega : d ≤ m)]
        have heq :
            (1 - (4 * (D : ℝ)) / m) * (m + d + 1) =
              ((m : ℝ) - 4 * D) * (m + d + 1) / m := by
          field_simp
        rw [heq, div_le_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)]
        have hsmall : (2 * d + 1 : ℕ) ≤ 4 * D := by omega
        have hmul : (m : ℝ) * (2 * d + 1) ≤ (m : ℝ) * (4 * D) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hsmall) (by positivity)
        have hmul' : (m : ℝ) * (4 * D) ≤
            (4 * D : ℝ) * (m + d + 1) := by
          have : (m : ℝ) ≤ m + d + 1 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this
            (show (0 : ℝ) ≤ 4 * D by positivity)]
        nlinarith
      have hdenPos : (0 : ℝ) < (2 * m - k : ℕ) := by
        rw [hden]
        positivity
      have hstep :
          (Nat.choose (2 * m) (m - d) : ℝ) *
              (1 - (4 * D : ℝ) / m) ≤
            Nat.choose (2 * m) k := by
        apply (le_of_mul_le_mul_right · hdenPos)
        calc
          ((Nat.choose (2 * m) (m - d) : ℝ) *
              (1 - (4 * D : ℝ) / m)) * (2 * m - k : ℕ) =
              (Nat.choose (2 * m) (m - d) : ℝ) *
                ((1 - (4 * D : ℝ) / m) * (2 * m - k : ℕ)) := by ring
          _ ≤ (Nat.choose (2 * m) (m - d) : ℝ) * (k + 1 : ℕ) :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = (Nat.choose (2 * m) k : ℝ) * (2 * m - k : ℕ) := by
            rw [← hk1]
            simpa using hrec
      calc
        (Nat.choose (2 * m) m : ℝ) *
            (1 - (4 * D : ℝ) / m) ^ (d + 1) =
            ((Nat.choose (2 * m) m : ℝ) *
              (1 - (4 * D : ℝ) / m) ^ d) *
                (1 - (4 * D : ℝ) / m) := by rw [pow_succ]; ring
        _ ≤ (Nat.choose (2 * m) (m - d) : ℝ) *
              (1 - (4 * D : ℝ) / m) :=
          mul_le_mul_of_nonneg_right (ih hdD) hb0
        _ ≤ Nat.choose (2 * m) k := hstep
        _ = Nat.choose (2 * m) (m - (d + 1)) := rfl

lemma exp_neg_two_mul_le_one_sub {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hden : 0 < 1 - x := by linarith
  have hinvLinear : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [show (1 - x)⁻¹ = 1 / (1 - x) by simp]
    rw [div_le_iff₀ hden]
    nlinarith
  have hlinearExp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 * x)
  have hinvExp : (Real.exp (2 * x))⁻¹ ≤ ((1 - x)⁻¹)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (inv_pos.mpr hden)).2
      (hinvLinear.trans hlinearExp)
  rw [← Real.exp_neg, inv_inv] at hinvExp
  convert hinvExp using 1 <;> ring

lemma exp_neg_eight_sq_div_le_one_sub_pow (m D : ℕ)
    (hD : 8 * D ≤ m) :
    Real.exp (-8 * (D : ℝ) ^ 2 / m) ≤
      (1 - (4 * D : ℝ) / m) ^ D := by
  by_cases hm0 : m = 0
  · subst m
    have hD0 : D = 0 := by omega
    subst D
    norm_num
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  let x : ℝ := (4 * D : ℝ) / m
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_iff₀ hm]
    have hDreal : (8 * D : ℝ) ≤ m := by exact_mod_cast hD
    nlinarith
  have hbase := exp_neg_two_mul_le_one_sub hx0 hx
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hbase D
  calc
    Real.exp (-8 * (D : ℝ) ^ 2 / m) =
        Real.exp (-2 * x) ^ D := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp only [x]
      field_simp
      ring
    _ ≤ (1 - x) ^ D := hpow
    _ = (1 - (4 * D : ℝ) / m) ^ D := rfl

/-- Uniform Gaussian-scale lower bound for every even-row binomial
coefficient within `D` of the middle. -/
lemma choose_two_mul_near_middle_lower (m D ell : ℕ)
    (hD : 8 * D ≤ m) (hell : ell ≤ 2 * m)
    (hnear : Nat.dist ell m ≤ D) :
    (Nat.choose (2 * m) m : ℝ) *
        Real.exp (-8 * (D : ℝ) ^ 2 / m) ≤
      Nat.choose (2 * m) ell := by
  by_cases hm0 : m = 0
  · subst m
    have hD0 : D = 0 := by omega
    subst D
    have hell0 : ell = 0 := by omega
    subst ell
    norm_num
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have h4D : 4 * D ≤ m := by omega
  have hb0 : 0 ≤ 1 - (4 * D : ℝ) / m := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast h4D
  have hb1 : 1 - (4 * D : ℝ) / m ≤ 1 := by
    have : 0 ≤ (4 * D : ℝ) / m := by positivity
    linarith
  have hexp := exp_neg_eight_sq_div_le_one_sub_pow m D hD
  by_cases hleft : ell ≤ m
  · let d := m - ell
    have hd : d ≤ D := by
      rw [Nat.dist_eq_sub_of_le hleft] at hnear
      exact hnear
    have hpow : (1 - (4 * D : ℝ) / m) ^ D ≤
        (1 - (4 * D : ℝ) / m) ^ d :=
      pow_le_pow_of_le_one hb0 hb1 hd
    have hrec := choose_two_mul_sub_ge_middle_mul_pow m D d hd h4D
    have hdEq : m - d = ell := by dsimp only [d]; omega
    calc
      (Nat.choose (2 * m) m : ℝ) *
          Real.exp (-8 * (D : ℝ) ^ 2 / m) ≤
          (Nat.choose (2 * m) m : ℝ) *
            (1 - (4 * D : ℝ) / m) ^ D :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (Nat.choose (2 * m) m : ℝ) *
            (1 - (4 * D : ℝ) / m) ^ d :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ Nat.choose (2 * m) (m - d) := hrec
      _ = Nat.choose (2 * m) ell := by rw [hdEq]
  · have hmle : m ≤ ell := Nat.le_of_lt (Nat.lt_of_not_ge hleft)
    let d := ell - m
    have hd : d ≤ D := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hmle] at hnear
      exact hnear
    have hpow : (1 - (4 * D : ℝ) / m) ^ D ≤
        (1 - (4 * D : ℝ) / m) ^ d :=
      pow_le_pow_of_le_one hb0 hb1 hd
    have hrec := choose_two_mul_sub_ge_middle_mul_pow m D d hd h4D
    have hcomp : 2 * m - ell = m - d := by dsimp only [d]; omega
    have hsymm := Nat.choose_symm hell
    calc
      (Nat.choose (2 * m) m : ℝ) *
          Real.exp (-8 * (D : ℝ) ^ 2 / m) ≤
          (Nat.choose (2 * m) m : ℝ) *
            (1 - (4 * D : ℝ) / m) ^ D :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (Nat.choose (2 * m) m : ℝ) *
            (1 - (4 * D : ℝ) / m) ^ d :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ Nat.choose (2 * m) (m - d) := hrec
      _ = Nat.choose (2 * m) (2 * m - ell) := by rw [hcomp]
      _ = Nat.choose (2 * m) ell := by exact_mod_cast hsymm

/-- A uniform square-root local lower bound for every binomial coefficient
within `D` of the middle. -/
lemma choose_near_middle_lower (n D ell : ℕ)
    (hn : 1 ≤ n) (hD : 8 * D ≤ n / 2)
    (hell : ell ≤ n) (hnear : Nat.dist ell (n / 2) ≤ D) :
    ((2 : ℝ) ^ n / (8 * Real.sqrt n)) *
        Real.exp (-8 * (D : ℝ) ^ 2 / (n / 2 : ℕ)) ≤
      Nat.choose n ell := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by omega
    have hevenHalf : (2 * m) / 2 = m := by omega
    have hDm : 8 * D ≤ m := by omega
    have hnear' : Nat.dist ell m ≤ D := by
      rw [hevenHalf] at hnear
      exact hnear
    have hrec := choose_two_mul_near_middle_lower m D ell hDm hell hnear'
    have hcentral := two_pow_div_four_sqrt_le_choose_middle (2 * m) (by omega)
    have hpre :
        (2 : ℝ) ^ (2 * m) / (8 * Real.sqrt ((2 * m : ℕ) : ℝ)) ≤
          Nat.choose (2 * m) m := by
      calc
        (2 : ℝ) ^ (2 * m) / (8 * Real.sqrt ((2 * m : ℕ) : ℝ)) ≤
            (2 : ℝ) ^ (2 * m) / (4 * Real.sqrt ((2 * m : ℕ) : ℝ)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [Real.sqrt_nonneg (((2 * m : ℕ) : ℝ))]
        _ ≤ Nat.choose (2 * m) ((2 * m) / 2) := hcentral
        _ = Nat.choose (2 * m) m := by rw [show (2 * m) / 2 = m by omega]
    have hmul := mul_le_mul_of_nonneg_right hpre
      (Real.exp_nonneg (-8 * (D : ℝ) ^ 2 / (m : ℕ)))
    rw [hevenHalf]
    exact hmul.trans hrec
  · by_cases hm0 : m = 0
    · subst m
      have hD0 : D = 0 := by omega
      subst D
      have hell0 : ell = 0 := by
        norm_num [Nat.dist_zero_right] at hnear
        exact hnear
      subst ell
      norm_num
    · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hoddHalf : (2 * m + 1) / 2 = m := by omega
      have hDm : 8 * D ≤ m := by
        rw [hoddHalf] at hD
        exact hD
      have hpre :
          (2 : ℝ) ^ (2 * m + 1) /
              (8 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) ≤
            Nat.choose (2 * m) m := by
        have hcentral := two_pow_div_four_sqrt_le_choose_middle (2 * m) (by omega)
        calc
          (2 : ℝ) ^ (2 * m + 1) /
              (8 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) =
              (2 : ℝ) ^ (2 * m) /
                (4 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) := by
            rw [pow_add, pow_one]
            ring
          _ ≤ (2 : ℝ) ^ (2 * m) /
                (4 * Real.sqrt ((2 * m : ℕ) : ℝ)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have hsqrt : Real.sqrt (((2 * m : ℕ) : ℝ)) ≤
                Real.sqrt (((2 * m + 1 : ℕ) : ℝ)) :=
              Real.sqrt_le_sqrt (by push_cast; nlinarith)
            exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
          _ ≤ Nat.choose (2 * m) ((2 * m) / 2) := hcentral
          _ = Nat.choose (2 * m) m := by rw [show (2 * m) / 2 = m by omega]
      have hnearMiddle : Nat.dist ell m ≤ D := by
        rw [hoddHalf] at hnear
        exact hnear
      by_cases hleft : ell ≤ m
      · have hellEven : ell ≤ 2 * m := by omega
        have hrec := choose_two_mul_near_middle_lower
          m D ell hDm hellEven hnearMiddle
        have hchoose : Nat.choose (2 * m) ell ≤ Nat.choose (2 * m + 1) ell :=
          Nat.choose_le_choose ell (by omega)
        have hchooseReal : (Nat.choose (2 * m) ell : ℝ) ≤
            Nat.choose (2 * m + 1) ell := by exact_mod_cast hchoose
        have hmul := mul_le_mul_of_nonneg_right hpre
          (Real.exp_nonneg (-8 * (D : ℝ) ^ 2 / (m : ℕ)))
        have hchain := hmul.trans (hrec.trans hchooseReal)
        rw [hoddHalf]
        exact hchain
      · have hmell : m < ell := Nat.lt_of_not_ge hleft
        let k := 2 * m + 1 - ell
        have hk : k ≤ m := by dsimp only [k]; omega
        have hkEven : k ≤ 2 * m := by omega
        have hkNear : Nat.dist k m ≤ D := by
          have hdist : Nat.dist k m ≤ Nat.dist ell m := by
            rw [Nat.dist_eq_sub_of_le hk,
              Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt hmell)]
            dsimp only [k]
            omega
          exact hdist.trans hnearMiddle
        have hrec := choose_two_mul_near_middle_lower m D k hDm hkEven hkNear
        have hchoose : Nat.choose (2 * m) k ≤ Nat.choose (2 * m + 1) k :=
          Nat.choose_le_choose k (by omega)
        have hchooseReal : (Nat.choose (2 * m) k : ℝ) ≤
            Nat.choose (2 * m + 1) k := by exact_mod_cast hchoose
        have hsymm := Nat.choose_symm hell
        have hmul := mul_le_mul_of_nonneg_right hpre
          (Real.exp_nonneg (-8 * (D : ℝ) ^ 2 / (m : ℕ)))
        have hchain := hmul.trans (hrec.trans hchooseReal)
        calc
          ((2 : ℝ) ^ (2 * m + 1) /
              (8 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ))) *
                Real.exp (-8 * (D : ℝ) ^ 2 /
                  ((2 * m + 1) / 2 : ℕ)) =
              ((2 : ℝ) ^ (2 * m + 1) /
                (8 * Real.sqrt ((2 * m + 1 : ℕ) : ℝ))) *
                  Real.exp (-8 * (D : ℝ) ^ 2 / (m : ℕ)) := by
            rw [show (2 * m + 1) / 2 = m by omega]
          _ ≤ Nat.choose (2 * m + 1) k := hchain
          _ = Nat.choose (2 * m + 1) ell := by
            dsimp only [k]
            exact_mod_cast hsymm

/-- Product form of the near-central binomial lower bound. -/
lemma prod_choose_near_middle_lower {ι : Type*} [Fintype ι]
    (N ell : ι → ℕ) (D : ℕ)
    (hN : ∀ i, 1 ≤ N i) (hD : ∀ i, 8 * D ≤ N i / 2)
    (hell : ∀ i, ell i ≤ N i)
    (hnear : ∀ i, Nat.dist (ell i) (N i / 2) ≤ D) :
    ∏ i : ι, (((2 : ℝ) ^ N i / (8 * Real.sqrt (N i))) *
        Real.exp (-8 * (D : ℝ) ^ 2 / (N i / 2 : ℕ))) ≤
      ∏ i : ι, (Nat.choose (N i) (ell i) : ℝ) := by
  apply Finset.prod_le_prod
  · intro i _hi
    positivity
  · intro i _hi
    exact choose_near_middle_lower (N i) D (ell i)
      (hN i) (hD i) (hell i) (hnear i)

/-- An ambient-size version: a block coefficient retains a uniform
`2^N / sqrt n` lower bound when its Gaussian loss is at most `C`. -/
lemma choose_near_middle_lower_of_ambient (n N D ell : ℕ) (C : ℝ)
    (hN : 1 ≤ N) (hNn : N ≤ n) (hhalf : 1 ≤ N / 2)
    (hD : 8 * D ≤ N / 2) (hell : ell ≤ N)
    (hnear : Nat.dist ell (N / 2) ≤ D)
    (hquad : (D : ℝ) ^ 2 ≤ C * (N / 2 : ℕ)) :
    ((2 : ℝ) ^ N / (8 * Real.sqrt n)) * Real.exp (-8 * C) ≤
      Nat.choose N ell := by
  have hbase := choose_near_middle_lower N D ell hN hD hell hnear
  have hsqrt : Real.sqrt (N : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hNn)
  have hfrac :
      (2 : ℝ) ^ N / (8 * Real.sqrt n) ≤
        (2 : ℝ) ^ N / (8 * Real.sqrt N) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hhalfPos : (0 : ℝ) < (N / 2 : ℕ) := by exact_mod_cast hhalf
  have hratio : (D : ℝ) ^ 2 / (N / 2 : ℕ) ≤ C := by
    rw [div_le_iff₀ hhalfPos]
    exact hquad
  have hexp : Real.exp (-8 * C) ≤
      Real.exp (-8 * (D : ℝ) ^ 2 / (N / 2 : ℕ)) := by
    apply Real.exp_le_exp.mpr
    calc
      -8 * C ≤ -8 * ((D : ℝ) ^ 2 / (N / 2 : ℕ)) :=
        mul_le_mul_of_nonpos_left hratio (by norm_num)
      _ = -8 * (D : ℝ) ^ 2 / (N / 2 : ℕ) := by ring
  calc
    ((2 : ℝ) ^ N / (8 * Real.sqrt n)) * Real.exp (-8 * C) ≤
        ((2 : ℝ) ^ N / (8 * Real.sqrt N)) *
          Real.exp (-8 * (D : ℝ) ^ 2 / (N / 2 : ℕ)) :=
      mul_le_mul hfrac hexp (Real.exp_nonneg _) (by positivity)
    _ ≤ Nat.choose N ell := hbase

/-- Product version of `choose_near_middle_lower_of_ambient`. -/
lemma prod_choose_near_middle_lower_of_ambient {ι : Type*} [Fintype ι]
    (n : ℕ) (N ell : ι → ℕ) (D : ℕ) (C : ℝ)
    (hN : ∀ i, 1 ≤ N i) (hNn : ∀ i, N i ≤ n)
    (hhalf : ∀ i, 1 ≤ N i / 2) (hD : ∀ i, 8 * D ≤ N i / 2)
    (hell : ∀ i, ell i ≤ N i)
    (hnear : ∀ i, Nat.dist (ell i) (N i / 2) ≤ D)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤ C * (N i / 2 : ℕ)) :
    ∏ i : ι, (((2 : ℝ) ^ N i / (8 * Real.sqrt n)) *
        Real.exp (-8 * C)) ≤
      ∏ i : ι, (Nat.choose (N i) (ell i) : ℝ) := by
  apply Finset.prod_le_prod
  · intro i _hi
    positivity
  · intro i _hi
    exact choose_near_middle_lower_of_ambient n (N i) D (ell i) C
      (hN i) (hNn i) (hhalf i) (hD i) (hell i) (hnear i) (hquad i)

end Erdos88.Switching
