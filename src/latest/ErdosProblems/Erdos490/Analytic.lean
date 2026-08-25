import ErdosProblems.Erdos490.Basic
import Util.MertensProduct

noncomputable section

namespace Erdos490

open Finset BigOperators Nat Real Filter Asymptotics
open scoped Topology

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 800000

lemma primesUpTo_eq_Ioc (x : ℝ) :
    primesUpTo x = (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, by omega⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨by omega, hprime⟩

/-- Qualitative Mertens, obtained from the proved elementary development. -/
theorem mertens_product_estimate (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ x : ℝ, x ≥ X₀ →
      |∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) -
        Real.exp (-γ) / Real.log x| ≤ ε / Real.log x := by
  have h := Mertens.E₃.bound''.isLittleO.def (div_pos hε (Real.exp_pos (-γ)))
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X₀ 2, fun x hx => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith [le_max_right X₀ 2])
  have hbound := hX₀ x (le_trans (le_max_left _ _) hx)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_pos (div_pos (Real.exp_pos _) hlog)] at hbound
  simpa [primesUpTo_eq_Ioc, γ, div_eq_mul_inv, mul_assoc] using hbound

theorem log_convolution_bound (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (_hX : X ≥ 1) :
    L_count f X ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1),
      f a * chebyshevPsi (X / (a : ℝ)) := by
  unfold L_count chebyshevPsi;
  have h_log_convolution : ∀ m ∈ Finset.range (⌊X⌋₊ + 1), m ≠ 0 → f m * Real.log m ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1), ArithmeticFunction.vonMangoldt n * (if n * a = m then 1 else 0) := by
    intro m hm hm_ne_zero
    have h_log_convolution_step : f m * Real.log m ≤ ∑ a ∈ Nat.divisors m, f a * ArithmeticFunction.vonMangoldt (m / a) := by
      have h_log_convolution_step : Real.log m = ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt (m / a) := by
        have h_log_convolution_step : Real.log m = ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt a := by
          rw [ ArithmeticFunction.vonMangoldt_sum ];
        rw [ h_log_convolution_step, ← Nat.sum_div_divisors ];
      rw [ h_log_convolution_step, Finset.mul_sum _ _ _ ];
      refine Finset.sum_le_sum fun i hi => ?_;
      have h_f_mul : f m = f i * f (m / i) := by
        rw [ ← hf.2.2 i ( m / i ) ( Nat.pos_of_mem_divisors hi ) ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm_ne_zero ) ( Nat.dvd_of_mem_divisors hi ) ) ( Nat.pos_of_mem_divisors hi ) ), Nat.mul_div_cancel' ( Nat.dvd_of_mem_divisors hi ) ];
      cases hf.1 i <;> cases hf.1 ( m / i ) <;> simp_all +decide;
    refine le_trans h_log_convolution_step ?_;
    rw [ ← Finset.sum_subset ( show m.divisors ⊆ Finset.range ( ⌊X⌋₊ + 1 ) from fun x hx => Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.divisor_le hx ) <| Finset.mem_range_succ_iff.mp hm ) ];
    · gcongr;
      · cases hf.1 ‹_› <;> aesop;
      · rw [ Finset.sum_eq_single ( m / ‹_› ) ] <;> norm_num;
        · rw [ if_pos ( Nat.div_mul_cancel ( Nat.dvd_of_mem_divisors ‹_› ) ) ];
        · aesop;
        · intro h₁ h₂; contrapose! h₁; simp_all +decide [ Nat.floor_div_natCast ] ;
          exact Nat.div_le_div_right hm;
    · simp +zetaDelta at *;
      exact fun x hx hx' => Or.inr <| Finset.sum_eq_zero fun y hy => if_neg <| by intro H; exact hm_ne_zero <| hx' <| dvd_of_mul_left_eq _ H;
  have h_log_convolution_sum : ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log m ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1), ArithmeticFunction.vonMangoldt n * ∑ m ∈ Finset.range (⌊X⌋₊ + 1), (if n * a = m then 1 else 0) := by
    have hsum :
        ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log m ≤
          ∑ m ∈ Finset.range (⌊X⌋₊ + 1),
            ∑ a ∈ Finset.range (⌊X⌋₊ + 1),
              f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1),
                ArithmeticFunction.vonMangoldt n * (if n * a = m then 1 else 0) := by
      refine Finset.sum_le_sum fun m hm => ?_
      by_cases hm0 : m = 0
      · subst m
        simp
        refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
        · cases hf.1 i <;> linarith
        · exact Finset.sum_nonneg fun _ _ => by
            split_ifs <;> simp +decide [ArithmeticFunction.vonMangoldt_nonneg]
      · exact h_log_convolution m hm hm0
    refine hsum.trans_eq ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n hn => by
      rw [← Finset.mul_sum]
  refine le_trans h_log_convolution_sum <| Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ <| ?_;
  · gcongr;
    aesop;
  · cases hf.1 a <;> linarith

/-
Let A > log 2 and C_A = ψ(e^A), with ψ(x) ≤ 1.11x for x ≥ e^A.
    If f is completely multiplicative {0,1}-valued and X > e^{A+C_A}, then
    F_f(X) - F_f(X·e^{-A}) ≤ 1.11·X·H_f(X)/(log X - A - C_A).
-/
theorem block_estimate (A : ℝ) (hA : A > Real.log 2)
    (hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x) (f : ℕ → ℝ)
    (hf : CompMult01 f) (X : ℝ)
    (hX : X > Real.exp (A + chebyshevPsi (Real.exp A))) :
    F_count f X - F_count f (X * Real.exp (-A)) ≤
      ((111 / 100 : ℝ)) * X * H_count f X /
        (Real.log X - A - chebyshevPsi (Real.exp A)) := by
  -- By log_convolution_bound, L_f(X) ≤ ∑_{a≤X} f(a)·ψ(X/a).
  have h_log_conv : L_count f X ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) := by
    apply log_convolution_bound f hf X (by
    exact le_trans ( Real.one_le_exp ( by linarith [ Real.log_nonneg one_le_two, show 0 ≤ chebyshevPsi ( Real.exp A ) from Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ] ) ) hX.le);
  -- Split the sum at a = X·e^{-A}:
  have h_split_sum : ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * X * H_count f (X * Real.exp (-A)) + chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
    have h_split_sum : ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * X * H_count f (X * Real.exp (-A)) := by
      have h_split_sum : ∀ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1), a ≠ 0 → f a * chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * X * (f a / a) := by
        intros a ha ha_ne_zero
        have h_chebyshev : chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * (X / a) := by
          apply hψ;
          rw [ le_div_iff₀ ] <;> norm_num at *;
          · rw [ Nat.le_floor_iff ( mul_nonneg ( le_of_lt ( show 0 < X by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) ) ( Real.exp_nonneg _ ) ) ] at ha;
            rw [ Real.exp_neg ] at ha ; nlinarith [ Real.exp_pos A, mul_inv_cancel_left₀ ( ne_of_gt ( Real.exp_pos A ) ) X ];
          · positivity;
        calc
          f a * chebyshevPsi (X / a) ≤
              f a * (((111 / 100 : ℝ)) * (X / a)) :=
            mul_le_mul_of_nonneg_left h_chebyshev
              (show 0 ≤ f a by cases hf.1 a <;> linarith)
          _ = ((111 / 100 : ℝ)) * X * (f a / a) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      have hsum :
          ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1),
              f a * chebyshevPsi (X / a) ≤
            ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1),
              ((111 / 100 : ℝ)) * X * (f a / a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        by_cases ha0 : a = 0
        · subst a
          unfold chebyshevPsi
          norm_num
        · exact h_split_sum a ha ha0
      refine hsum.trans_eq ?_
      rw [H_count, ← Finset.mul_sum]
    have h_split_sum : ∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
      have h_split_sum : ∀ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ f a * chebyshevPsi (Real.exp A) := by
        intros a ha
        have h_chebyshevPsi_le : chebyshevPsi (X / a) ≤ chebyshevPsi (Real.exp A) := by
          have h_chebyshevPsi_le : X / a ≤ Real.exp A := by
            rw [ div_le_iff₀ ] <;> norm_num at *;
            · have := Nat.lt_of_floor_lt ha.1;
              rw [ Real.exp_neg ] at this ; nlinarith [ Real.exp_pos A, mul_inv_cancel_left₀ ( ne_of_gt ( Real.exp_pos A ) ) X ];
            · grind;
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
          · exact Finset.range_mono ( Nat.succ_le_succ <| Nat.floor_mono h_chebyshevPsi_le );
          · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg;
        exact mul_le_mul_of_nonneg_left h_chebyshevPsi_le <| by cases hf.1 a <;> linarith;
      refine (Finset.sum_le_sum h_split_sum).trans_eq ?_
      calc
        (∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1),
            f a * chebyshevPsi (Real.exp A))
            = chebyshevPsi (Real.exp A) *
                ∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
        _ = chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
              congr 1
              rw [Finset.sum_Ico_eq_sub _] <;> norm_num [Finset.sum_range_succ, F_count]
              exact Nat.floor_mono <|
                mul_le_of_le_one_right
                  (by linarith [Real.exp_pos (A + chebyshevPsi (Real.exp A))])
                  (Real.exp_le_one_iff.mpr <| by linarith [Real.log_nonneg one_le_two])
    rw [ ← Finset.sum_range_add_sum_Ico _ ( show ⌊X * Real.exp ( -A ) ⌋₊ + 1 ≤ ⌊X⌋₊ + 1 from Nat.succ_le_succ <| Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] ) ] ; linarith;
  -- By log_convolution_bound, L_f(X) ≥ (F_f(X) - F_f(X·e^{-A})) · (log X - A).
  have h_log_conv_lower : L_count f X ≥ (F_count f X - F_count f (X * Real.exp (-A))) * (Real.log X - A) := by
    -- Every integer counted by $D$ is larger than $X \cdot e^{-A}$, so $D \cdot (\log X - A) \leq L_f(X)$.
    have h_log_conv_lower : ∑ a ∈ Finset.Icc (⌊X * Real.exp (-A)⌋₊ + 1) ⌊X⌋₊, f a * Real.log a ≥ (F_count f X - F_count f (X * Real.exp (-A))) * (Real.log X - A) := by
      have h_log_conv_lower : ∀ a ∈ Finset.Icc (⌊X * Real.exp (-A)⌋₊ + 1) ⌊X⌋₊, f a * Real.log a ≥ f a * (Real.log X - A) := by
        intros a ha
        have h_log_a : Real.log a ≥ Real.log X - A := by
          have h_log_a : Real.log a ≥ Real.log (X * Real.exp (-A)) := by
            exact Real.log_le_log ( mul_pos ( lt_trans ( by positivity ) hX ) ( Real.exp_pos _ ) ) ( Nat.lt_of_floor_lt ( Finset.mem_Icc.mp ha |>.1 ) |> le_of_lt );
          rw [ Real.log_mul ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) ( by positivity ), Real.log_exp ] at h_log_a ; linarith;
        exact mul_le_mul_of_nonneg_left h_log_a <| by cases hf.1 a <;> linarith;
      refine le_trans ?_ ( Finset.sum_le_sum h_log_conv_lower );
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, F_count ];
      · norm_num [ ← Finset.sum_mul _ _ _ ] ; ring_nf ; norm_num;
      · exact Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] ;
    refine le_trans h_log_conv_lower ?_;
    refine le_trans
      ( Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range ( ⌊X⌋₊ + 1 )) ?_ ?_ ) ?_;
    · exact fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] );
    · exact fun i hi₁ hi₂ => mul_nonneg ( by cases hf.1 i <;> linarith ) ( by positivity );
    · exact Finset.sum_le_sum fun _ _ => by aesop;
  rw [ le_div_iff₀ ];
  · -- Since $H_f(X) \geq H_f(X \cdot e^{-A})$, we can replace $H_f(X \cdot e^{-A})$ with $H_f(X)$ in the inequality.
    have h_H_ge : H_count f X ≥ H_count f (X * Real.exp (-A)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
      · exact Finset.range_mono ( Nat.succ_le_succ <| Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] );
      · exact fun i hi₁ hi₂ => div_nonneg ( by cases hf.1 i <;> linarith ) ( Nat.cast_nonneg _ );
    nlinarith [ show 0 ≤ ( (111 / 100 : ℝ) ) * X by exact mul_nonneg (by norm_num) (le_of_lt <| lt_trans (by positivity) hX) ];
  · linarith [ Real.log_exp ( A + chebyshevPsi ( Real.exp A ) ), Real.log_lt_log ( by positivity ) hX ]

/-
Trivial bound: F_f(X) ≤ 1 + X · H_f(X)
-/
lemma F_le_one_add_X_H (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) :
    F_count f X ≤ 1 + X * H_count f X := by
  -- Apply the trivial bound to each term in the sum.
  have h_sum_bound : ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m ≤ ∑ m ∈ Finset.range (⌊X⌋₊ + 1), (if m = 0 then 1 else X * f m / m) := by
    -- For each term in the sum, if m is not zero, then f(m) ≤ X * f(m) / m. This follows from the fact that m ≤ X.
    have h_term_bound : ∀ m ∈ Finset.range (⌊X⌋₊ + 1), m ≠ 0 → f m ≤ X * f m / m := by
      intro m hm hm'; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hm' ) ] ; nlinarith [ show ( m : ℝ ) ≤ X by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp hm ) <| Nat.floor_le <| by positivity, show ( f m : ℝ ) ≥ 0 by cases hf.1 m <;> linarith ] ;
    gcongr;
    split_ifs <;> simp_all +decide;
    cases hf.1 0 <;> linarith;
  simp_all +decide [ Finset.sum_range_succ', F_count, H_count ];
  simpa only [ mul_div_assoc, Finset.mul_sum _ _ _, add_comm ] using h_sum_bound

/-
H_f is monotone: H_f(Y) ≤ H_f(X) for Y ≤ X
-/
lemma H_count_mono (f : ℕ → ℝ) (hf : CompMult01 f) (X Y : ℝ) (hY : Y ≤ X) :
    H_count f Y ≤ H_count f X := by
  apply Finset.sum_le_sum_of_subset_of_nonneg;
  · exact Finset.range_mono ( Nat.succ_le_succ ( Nat.floor_mono hY ) );
  · exact fun i hi₁ hi₂ => div_nonneg ( by cases hf.1 i <;> linarith ) ( Nat.cast_nonneg _ )

lemma H_count_ge_one (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) :
    1 ≤ H_count f X := by
  unfold H_count
  have h1 : (1 : ℕ) ∈ Finset.range (⌊X⌋₊ + 1) := by
    simp only [Finset.mem_range]; have : ⌊X⌋₊ ≥ 1 := Nat.floor_pos.mpr hX; omega
  have h2 : ∀ i ∈ Finset.range (⌊X⌋₊ + 1), 0 ≤ f i / (i : ℝ) := by
    intro m _; rcases hf.1 m with h | h <;> simp [h, Nat.cast_nonneg]
  have h3 := Finset.single_le_sum h2 h1
  simp [hf.2.1] at h3; linarith

lemma H_count_nonneg (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) :
    0 ≤ H_count f X := by
  unfold H_count
  exact Finset.sum_nonneg fun m _ => by
    rcases hf.1 m with h | h <;> simp [h, Nat.cast_nonneg]

/-
Block estimate iterated J times with uniform denominator bound L
-/
lemma block_estimate_iter (A : ℝ) (hA : A > Real.log 2)
    (hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x) (f : ℕ → ℝ)
    (hf : CompMult01 f) (X : ℝ) (J : ℕ)
    (hXj : ∀ j : ℕ, j < J → X * Real.exp (-(j : ℝ) * A) >
      Real.exp (A + chebyshevPsi (Real.exp A)))
    (hXpos : X > 0) (L : ℝ) (hLpos : L > 0)
    (hLbound : ∀ j : ℕ, j < J → Real.log (X * Real.exp (-(j : ℝ) * A)) -
      A - chebyshevPsi (Real.exp A) ≥ L) :
    F_count f X ≤ F_count f (X * Real.exp (-(J : ℝ) * A)) +
      ((111 / 100 : ℝ)) * X * H_count f X / L *
        ∑ j ∈ Finset.range J, Real.exp (-(j : ℝ) * A) := by
  induction J with
  | zero => norm_num;
  | succ J ih =>
    have h_block :
        F_count f (X * Real.exp (-J * A)) -
            F_count f (X * Real.exp (-(J + 1) * A)) ≤
          ((111 / 100 : ℝ)) * X * Real.exp (-J * A) *
              H_count f (X * Real.exp (-J * A)) / L := by
      have hbe :=
        block_estimate A hA hψ f hf (X * Real.exp (-(J : ℝ) * A))
          (hXj J (Nat.lt_succ_self J))
      have hden :
          L ≤
            Real.log (X * Real.exp (-(J : ℝ) * A)) - A -
              chebyshevPsi (Real.exp A) :=
        hLbound J (Nat.lt_succ_self J)
      have hnum_nonneg :
          0 ≤
            ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
              H_count f (X * Real.exp (-(J : ℝ) * A)) := by
        refine mul_nonneg (mul_nonneg ?_ ?_) (H_count_nonneg f hf _)
        · positivity
        · exact mul_nonneg hXpos.le (Real.exp_nonneg _)
      have hden_step :
          ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) /
              (Real.log (X * Real.exp (-(J : ℝ) * A)) - A -
                chebyshevPsi (Real.exp A)) ≤
            ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) / L := by
        exact div_le_div_of_nonneg_left hnum_nonneg hLpos hden
      have hstep := le_trans hbe hden_step
      have hxexp :
          X * Real.exp (-(J + 1 : ℝ) * A) =
            X * Real.exp (-(J : ℝ) * A) * Real.exp (-A) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        norm_num
        ring
      have hrhs :
          ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) / L =
            ((111 / 100 : ℝ)) * X * Real.exp (-J * A) *
                H_count f (X * Real.exp (-J * A)) / L := by
        ring
      rw [hxexp]
      rw [← hrhs]
      exact hstep
    have h_monotone : H_count f (X * Real.exp (-J * A)) ≤ H_count f X := by
      apply H_count_mono;
      · exact hf;
      · exact mul_le_of_le_one_right hXpos.le ( Real.exp_le_one_iff.mpr <| by nlinarith [ Real.log_nonneg one_le_two ] );
    have h_combined : F_count f X ≤ F_count f (X * Real.exp (-(J + 1) * A)) + ((111 / 100 : ℝ)) * X * H_count f X / L * (∑ j ∈ Finset.range J, Real.exp (-j * A)) + ((111 / 100 : ℝ)) * X * Real.exp (-J * A) * H_count f X / L := by
      have h_combined : F_count f X ≤ F_count f (X * Real.exp (-J * A)) + ((111 / 100 : ℝ)) * X * H_count f X / L * (∑ j ∈ Finset.range J, Real.exp (-j * A)) := by
        exact ih ( fun j hj => hXj j ( Nat.lt_succ_of_lt hj ) ) ( fun j hj => hLbound j ( Nat.lt_succ_of_lt hj ) );
      have h_combined : ((111 / 100 : ℝ)) * X * Real.exp (-J * A) * H_count f (X * Real.exp (-J * A)) / L ≤ ((111 / 100 : ℝ)) * X * Real.exp (-J * A) * H_count f X / L := by
        gcongr;
      grind;
    convert h_combined using 1 ; push_cast [ Finset.sum_range_succ ] ; ring

lemma geom_sum_le (A : ℝ) (hA : A > 0) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(j : ℝ) * A) ≤ 1 / (1 - Real.exp (-A)) := by
  have h_geo_series : ∑ j ∈ Finset.range J, (Real.exp (-A)) ^ j ≤ 1 / (1 - Real.exp (-A)) := by
    rw [ le_div_iff₀ ] <;> nlinarith [ Real.exp_pos ( -A ), Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ), pow_pos ( Real.exp_pos ( -A ) ) J, geom_sum_mul ( Real.exp ( -A ) ) J ];
  convert h_geo_series using 2 ; norm_num [ ← Real.exp_nat_mul ]

lemma log_div_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
  -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
  suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
    exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
  norm_num;
  exact tendsto_nhdsWithin_of_tendsto_nhds ( by
    have h := Real.continuous_mul_log.tendsto 0
    simpa using h.neg )

/-
For large X, the denominator in the block estimate is close to log X.
-/
lemma mean_L_improved (A : ℝ) (hA : A > 0) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ X₀ : ℝ, X₀ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₀ →
      ∀ J : ℕ, (J : ℝ) ≤ 2 * Real.log (Real.log X) / A + 1 →
        ∀ j : ℕ, j < J →
          Real.log (X * Real.exp (-(j : ℝ) * A)) - A - chebyshevPsi (Real.exp A) ≥
            (1 - ε₁) * Real.log X := by
  -- We need to ensure that $2 \log(\log X) + A + \psi(e^A) \leq \epsilon_1 \log X$ for sufficiently large $X$.
  have h_log_log : Filter.Tendsto (fun X : ℝ => (2 * Real.log (Real.log X) + A + chebyshevPsi (Real.exp A)) / Real.log X) Filter.atTop (nhds 0) := by
    ring_nf;
    -- We'll use the fact that $\frac{\log(\log X)}{\log X}$ tends to $0$ as $X$ tends to infinity.
    have h_log_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X) Filter.atTop (nhds 0) := by
      refine (log_div_tendsto_zero.comp Real.tendsto_log_atTop).congr' ?_
      exact Filter.Eventually.of_forall fun X => by rfl
    have h_inv_log :
        Filter.Tendsto (fun X : ℝ => (Real.log X)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hAterm :
        Filter.Tendsto (fun X : ℝ => A * (Real.log X)⁻¹) Filter.atTop (nhds 0) :=
      by simpa using tendsto_const_nhds.mul h_inv_log
    have hPterm :
        Filter.Tendsto
          (fun X : ℝ => chebyshevPsi (Real.exp A) * (Real.log X)⁻¹)
          Filter.atTop (nhds 0) :=
      by simpa using tendsto_const_nhds.mul h_inv_log
    have hsum :
        Filter.Tendsto
          (fun X : ℝ =>
            2 * (Real.log (Real.log X) / Real.log X) +
              A * (Real.log X)⁻¹ +
              chebyshevPsi (Real.exp A) * (Real.log X)⁻¹)
          Filter.atTop (nhds 0) :=
      by simpa [add_assoc] using (h_log_log.const_mul 2).add (hAterm.add hPterm)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, add_assoc] using hsum
  -- By the definition of limit, there exists an X₀ such that for all X ≥ X₀, (2 * log(log X) + A + ψ(e^A)) / log X < ε₁.
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ X ≥ X₀, (2 * Real.log (Real.log X) + A + chebyshevPsi (Real.exp A)) / Real.log X < ε₁ := by
    simpa using h_log_log.eventually ( gt_mem_nhds hε₁ );
  refine ⟨ Max.max X₀ 2, le_max_right _ _, fun X hX J hJ j hj => ?_ ⟩ ; specialize hX₀ X ( le_trans ( le_max_left _ _ ) hX ) ; rw [ div_lt_iff₀ ] at hX₀ <;> norm_num at *;
  · rw [ Real.log_mul ( by linarith ) ( by positivity ), Real.log_exp ];
    rw [ div_add_one, le_div_iff₀ ] at hJ <;> nlinarith [ show ( j : ℝ ) + 1 ≤ J by norm_cast ];
  · exact Real.log_pos <| by linarith

/-
For large X, the tail F_f(X·e^{-JA}) + 1 is bounded by ε * X/log X * H_f(X).
-/
set_option maxHeartbeats 1600000 in
-- The tail estimate combines several asymptotic bounds through generated arithmetic.
lemma mean_tail_small (A : ℝ) (hA : A > Real.log 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, X₀ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      ∀ J : ℕ, (J : ℝ) * A ≥ 2 * Real.log (Real.log X) →
        F_count f (X * Real.exp (-(J : ℝ) * A)) + 1 ≤
          ε * X / Real.log X * H_count f X := by
  -- By definition of $F_count$, we know that $F_count f (X * Real.exp (-J * A)) \leq 1 + X * Real.exp (-J * A) * H_count f X$.
  have hF_count_bound : ∀ (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) (J : ℕ), F_count f (X * Real.exp (-J * A)) ≤ 1 + X * Real.exp (-J * A) * H_count f X := by
    intros f hf X hX J
    have hF_count_bound : F_count f (X * Real.exp (-J * A)) ≤ 1 + (X * Real.exp (-J * A)) * H_count f (X * Real.exp (-J * A)) := by
      by_cases hX' : X * Real.exp ( -J * A ) ≥ 1;
      · convert F_le_one_add_X_H f hf ( X * Real.exp ( -J * A ) ) hX' using 1;
      · unfold F_count H_count; norm_num [ Nat.floor_eq_zero.mpr ( not_le.mp hX' ) ] ;
        norm_num [ show ⌊X * Real.exp ( - ( J * A ) ) ⌋₊ = 0 by exact Nat.floor_eq_zero.mpr <| by simpa using hX' ];
        cases hf.1 0 <;> linarith;
    refine le_trans hF_count_bound ?_;
    gcongr;
    exact H_count_mono f hf X _ ( mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr ( by nlinarith [ Real.log_pos one_lt_two ] ) ) );
  -- For large X, X·e^{-JA} ≤ X/(log X)².
  have h_exp_bound : ∃ X₀ ≥ 2, ∀ X ≥ X₀, ∀ J : ℕ, J * A ≥ 2 * Real.log (Real.log X) → X * Real.exp (-J * A) ≤ X / (Real.log X) ^ 2 := by
    refine ⟨ Real.exp 2, ?_, ?_ ⟩ <;> norm_num;
    · linarith [ Real.add_one_le_exp 2 ];
    · intro X hX J hJ; rw [ div_eq_mul_inv ] ; rw [ ← Real.log_le_log_iff ( by exact mul_pos ( by linarith [ Real.exp_pos 2 ] ) ( Real.exp_pos _ ) ) ( by exact mul_pos ( by linarith [ Real.exp_pos 2 ] ) ( inv_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) ) ), Real.log_mul ( by linarith [ Real.exp_pos 2 ] ) ( by positivity ), Real.log_exp ] ; ring_nf;
      rw [ Real.log_mul ( by linarith [ Real.exp_pos 2 ] ) ( by exact ne_of_gt ( sq_pos_of_pos ( inv_pos.mpr ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) ) ), Real.log_pow, Real.log_inv ] ; norm_num ; linarith [ Real.log_pos ( show 1 < X by linarith [ Real.add_one_le_exp 2 ] ) ];
  -- By combining the results from hF_count_bound and h_exp_bound, we can derive the desired inequality.
  obtain ⟨X₀, hX₀_ge_2, hX₀_bound⟩ := h_exp_bound;
  have h_combined_bound : ∃ X₁ ≥ X₀, ∀ X ≥ X₁, ∀ f : ℕ → ℝ, CompMult01 f → ∀ J : ℕ, J * A ≥ 2 * Real.log (Real.log X) → 2 + X * Real.exp (-J * A) * H_count f X ≤ ε * X / Real.log X * H_count f X := by
    have h_combined_bound : ∃ X₁ ≥ X₀, ∀ X ≥ X₁, 2 + X / (Real.log X) ^ 2 ≤ ε * X / Real.log X := by
      have h_combined_bound : Filter.Tendsto (fun X : ℝ => (2 + X / (Real.log X) ^ 2) / (X / Real.log X)) Filter.atTop (nhds 0) := by
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun X : ℝ => 2 * Real.log X / X + 1 / Real.log X) Filter.atTop (nhds 0) by
          refine h_simplify.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with X hX;
          grind;
        -- We'll use the fact that $\frac{\log X}{X}$ tends to $0$ as $X$ tends to infinity.
        have h_log_div_X : Filter.Tendsto (fun X : ℝ => Real.log X / X) Filter.atTop (nhds 0) := by
          grind +suggestions;
        simpa [ mul_div_assoc ] using Filter.Tendsto.add ( h_log_div_X.const_mul 2 ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) );
      have := h_combined_bound.eventually ( gt_mem_nhds <| show 0 < ε by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₁, hX₁ ⟩ ; exact ⟨ Max.max X₀ X₁, le_max_left _ _, fun X hX => by have := hX₁ X ( le_trans ( le_max_right _ _ ) hX ) ; rw [ div_lt_iff₀ ( div_pos ( by linarith [ le_max_left X₀ X₁, le_max_right X₀ X₁ ] ) ( Real.log_pos ( by linarith [ le_max_left X₀ X₁, le_max_right X₀ X₁ ] ) ) ) ] at this; ring_nf at *; linarith ⟩ ;
    obtain ⟨ X₁, hX₁₁, hX₁₂ ⟩ := h_combined_bound;
    use X₁, hX₁₁;
    intros X hX f hf J hJ;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( hX₁₂ X hX ) ( H_count_nonneg f hf X ) );
    rw [ add_mul ];
    gcongr;
    · exact le_mul_of_one_le_right ( by norm_num ) ( H_count_ge_one f hf X ( by linarith ) );
    · exact H_count_nonneg f hf X;
    · exact hX₀_bound X ( by linarith ) J hJ;
  obtain ⟨ X₁, hX₁₁, hX₁₂ ⟩ := h_combined_bound; exact ⟨ X₁, by linarith, fun X hX f hf J hJ => by linarith [ hF_count_bound f hf X ( by linarith ) J, hX₁₂ X hX f hf J hJ ] ⟩ ;

set_option maxHeartbeats 6400000 in
-- The fixed-A mean estimate contains the largest generated block estimate.
lemma mean_estimate_fixed_A (A : ℝ) (hA : A > Real.log 2)
    (hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x) (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      F_count f X ≤ (((111 / 100 : ℝ)) / (1 - Real.exp (-A)) + ε) *
        X / Real.log X * H_count f X := by
  -- Choose ε₁ ∈ (0,1) small enough that 1.11/((1-ε₁)·(1-e^{-A})) ≤ 1.11/(1-e^{-A}) + ε/2.
  obtain ⟨ε₁, hε₁_pos, hε₁_small⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 ∧ ((111 / 100 : ℝ)) / ((1 - ε₁) * (1 - Real.exp (-A))) ≤ ((111 / 100 : ℝ)) / (1 - Real.exp (-A)) + ε / 2 := by
    have h_lim : Filter.Tendsto (fun ε₁ : ℝ => ((111 / 100 : ℝ)) / ((1 - ε₁) * (1 - Real.exp (-A)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (((111 / 100 : ℝ)) / (1 - Real.exp (-A)))) := by
      have hlim0 :
          Filter.Tendsto
            ((fun _ : ℝ => (111 / 100 : ℝ)) /
              fun ε₁ : ℝ => (1 - ε₁) * (1 - Real.exp (-A)))
            (nhds 0) (nhds (((111 / 100 : ℝ)) / (1 - Real.exp (-A)))) :=
        tendsto_const_nhds.div
          (by
            simpa using
              Continuous.tendsto
                (show Continuous fun ε₁ : ℝ =>
                  (1 - ε₁) * (1 - Real.exp (-A)) by continuity)
                0)
          (show 1 - Real.exp (-A) ≠ 0 by
            exact sub_ne_zero_of_ne
              (Ne.symm
                (by
                  norm_num
                  linarith [Real.log_pos one_lt_two])))
      exact tendsto_nhdsWithin_of_tendsto_nhds
        (hlim0.congr' <| Filter.Eventually.of_forall fun ε₁ => by rfl)
    have := h_lim.eventually ( ge_mem_nhds <| show ( (111 / 100 : ℝ) ) / ( 1 - Real.exp ( -A ) ) < ( (111 / 100 : ℝ) ) / ( 1 - Real.exp ( -A ) ) + ε / 2 by linarith ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ; obtain ⟨ ε₁, hε₁₁, hε₁₂ ⟩ := this.exists ; exact ⟨ ε₁, hε₁₂.1, hε₁₂.2, hε₁₁ ⟩ ;
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₁ → ∀ J : ℕ, (J : ℝ) ≤ 2 * Real.log (Real.log X) / A + 1 → ∀ j : ℕ, j < J → Real.log (X * Real.exp (-(j : ℝ) * A)) - A - chebyshevPsi (Real.exp A) ≥ (1 - ε₁) * Real.log X := by
    apply mean_L_improved A (by linarith [Real.log_pos one_lt_two]) ε₁ hε₁_pos;
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, X₂ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₂ → ∀ f : ℕ → ℝ, CompMult01 f → ∀ J : ℕ, (J : ℝ) * A ≥ 2 * Real.log (Real.log X) → F_count f (X * Real.exp (-(J : ℝ) * A)) + 1 ≤ ε / 2 * X / Real.log X * H_count f X := by
    convert mean_tail_small A hA ( ε / 2 ) ( half_pos hε ) using 1;
  refine ⟨ Max.max X₁ X₂, fun X hX f hf => ?_ ⟩;
  by_cases hX_pos : 0 < X;
  · by_cases h_log_pos : 0 < Real.log X;
    · have h_block : F_count f X ≤ F_count f (X * Real.exp (-(Nat.ceil (2 * Real.log (Real.log X) / A) : ℝ) * A)) + ((111 / 100 : ℝ)) * X * H_count f X / ((1 - ε₁) * Real.log X) * (∑ j ∈ Finset.range (Nat.ceil (2 * Real.log (Real.log X) / A)), Real.exp (-(j : ℝ) * A)) := by
        apply block_estimate_iter A hA hψ;
        all_goals norm_num [ hA, hε₁_pos, hε₁_small, hX_pos, h_log_pos ];
        · exact hf;
        · intro j hj;
          have := hX₁.2 X ( le_trans ( le_max_left _ _ ) hX ) ( Nat.ceil ( 2 * Real.log ( Real.log X ) / A ) ) ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Real.log X ) / A by exact div_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg ( show 1 ≤ Real.log X from by
                                                                                                                                                                                                                                                                contrapose! hj;
                                                                                                                                                                                                                                                                rw [ Nat.ceil_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                                                                                                exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos zero_le_two ( Real.log_nonpos h_log_pos.le hj.le ) ) ( by linarith [ Real.log_pos one_lt_two ] ) ) ) ) ( by linarith [ Real.log_pos one_lt_two ] ) ) ] ) j hj;
          rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] at this;
          rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ];
          norm_num; nlinarith [ Real.log_pos one_lt_two ];
        · simp +zetaDelta at *;
          exact fun j hj => hX₁.2 X hX.1 _ ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Real.log X ) / A by exact div_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg ( show 1 ≤ Real.log X from by
                                                                                                                                                                                            contrapose! hj;
                                                                                                                                                                                            rw [ Nat.ceil_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                            exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos zero_le_two ( Real.log_nonpos h_log_pos.le hj.le ) ) ( by linarith [ Real.log_nonneg one_le_two ] ) ) ) ) ( by linarith [ Real.log_nonneg one_le_two ] ) ) ] ) _ hj;
      have h_tail : F_count f (X * Real.exp (-(Nat.ceil (2 * Real.log (Real.log X) / A) : ℝ) * A)) + 1 ≤ ε / 2 * X / Real.log X * H_count f X := by
        apply hX₂.right X (by
        exact le_trans ( le_max_right _ _ ) hX) f hf (Nat.ceil (2 * Real.log (Real.log X) / A)) (by
        nlinarith [ Nat.le_ceil ( 2 * Real.log ( Real.log X ) / A ), show 0 < A by linarith [ Real.log_pos one_lt_two ], mul_div_cancel₀ ( 2 * Real.log ( Real.log X ) ) ( show A ≠ 0 by linarith [ Real.log_pos one_lt_two ] ) ]);
      have h_geom_sum : ∑ j ∈ Finset.range (Nat.ceil (2 * Real.log (Real.log X) / A)), Real.exp (-(j : ℝ) * A) ≤ 1 / (1 - Real.exp (-A)) := by
        convert geom_sum_le A ( show 0 < A by linarith [ Real.log_pos one_lt_two ] ) ⌈2 * Real.log ( Real.log X ) / A⌉₊ using 1;
      have h_combined : F_count f X ≤ (ε / 2 * X / Real.log X * H_count f X - 1) + ((111 / 100 : ℝ)) * X * H_count f X / ((1 - ε₁) * Real.log X) * (1 / (1 - Real.exp (-A))) := by
        refine le_trans h_block ?_;
        refine add_le_add ?_ ?_;
        · linarith;
        · exact mul_le_mul_of_nonneg_left h_geom_sum <| div_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by positivity ) <| H_count_nonneg f hf X ) <| mul_nonneg ( by linarith ) <| by positivity;
      have h_combined : F_count f X ≤ (ε / 2 * X / Real.log X * H_count f X - 1) + (((111 / 100 : ℝ)) / (1 - Real.exp (-A)) + ε / 2) * X / Real.log X * H_count f X := by
        refine le_trans h_combined ?_;
        norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] at *;
        exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( by nlinarith [ inv_pos.mpr h_log_pos ] ) ( H_count_nonneg f hf X ) ) hX_pos.le;
      grind;
    · exact False.elim <| h_log_pos <| Real.log_pos <| by linarith [ le_max_left X₁ X₂, le_max_right X₁ X₂ ] ;
  · linarith [ le_max_left X₁ X₂, le_max_right X₁ X₂ ]


/-- The only Chebyshev input required by the sieve. -/
def ElementaryChebyshevBound : Prop :=
  ∃ T : ℝ, ∀ x : ℝ, T ≤ x → chebyshevPsi x ≤ (111 / 100) * x

lemma choose_mean_block (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    ∃ A : ℝ, Real.log 2 < A ∧ T ≤ Real.exp A ∧
      (111 / 100 : ℝ) / (1 - Real.exp (-A)) < 111 / 100 + ε := by
  have hlim : Tendsto (fun A : ℝ => (111 / 100 : ℝ) / (1 - Real.exp (-A)))
      atTop (𝓝 (111 / 100)) := by
    have hnum : Tendsto (fun _ : ℝ => (111 / 100 : ℝ)) atTop (𝓝 (111 / 100)) :=
      tendsto_const_nhds
    have hden : Tendsto (fun A : ℝ => 1 - Real.exp (-A)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot) :
        Tendsto (fun A : ℝ => 1 - Real.exp (-A)) atTop (𝓝 (1 - 0)))
    have hdiv := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at hdiv
    exact hdiv.congr' (Filter.Eventually.of_forall fun A => by rfl)
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    (111 / 100 : ℝ) < 111 / 100 + ε))
  obtain ⟨A, hA, hT, hbound⟩ :=
    ((eventually_gt_atTop (Real.log 2)).and
      ((Real.tendsto_exp_atTop.eventually_ge_atTop T).and hbound)).exists
  exact ⟨A, hA, hT, hbound⟩

/-- Uniform mean-value estimate; its proof uses only a one-sided elementary
Chebyshev bound, not the prime number theorem. -/
theorem mean_estimate (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      F_count f X ≤ (111 / 100 + ε) * X / Real.log X * H_count f X := by
  obtain ⟨T, hT⟩ := hCheb
  obtain ⟨A, hA, hAT, hcoeff⟩ := choose_mean_block (ε / 2) (half_pos hε) T
  have hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x :=
    fun x hx => hT x (hAT.trans hx)
  obtain ⟨X₀, hX₀⟩ := mean_estimate_fixed_A A hA hψ (ε / 2) (half_pos hε)
  refine ⟨max X₀ 1, fun X hX f hf => (hX₀ X (le_of_max_le_left hX) f hf).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (H_count_nonneg f hf X)
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (le_of_max_le_right hX))
  exact mul_le_mul_of_nonneg_right (by linarith) (by linarith [le_of_max_le_right hX])

theorem sieve_bound (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ →
      ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ X) →
        (((Finset.range (⌊X⌋₊ + 1)).filter
          (fun m => m ≥ 1 ∧ ∀ p ∈ P, ¬(p ∣ m))).card : ℝ) ≤
          ((111 / 100) * Real.exp γ + ε) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  obtain ⟨ X₁, hX₁ ⟩ := mean_estimate hCheb ( ε / 2 / ( Real.exp γ + ε ) ) ( by positivity );
  -- By Mertens' product theorem, there exists $X₂$ such that for all $X ≥ X₂$, $\prod_{p ≤ X} (1 - 1/p)^{-1} ≤ (e^γ + ε/2) \log X$.
  obtain ⟨ X₂, hX₂ ⟩ : ∃ X₂ : ℝ, ∀ X ≥ X₂, (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) ≤ (Real.exp γ + 50 * ε / 111) * Real.log X := by
    have h_mertens : Filter.Tendsto (fun X : ℝ => (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))) * Real.log X) Filter.atTop (nhds (Real.exp (-γ))) := by
      have := mertens_product_estimate;
      rw [ Metric.tendsto_nhds ];
      intro ε hε; rcases this ( ε / 2 ) ( half_pos hε ) with ⟨ X₀, HX₀ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop X₀, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂; specialize HX₀ x hx₁; rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ abs_le.mp HX₀, Real.log_pos hx₂, mul_div_cancel₀ ( ε / 2 ) ( ne_of_gt ( Real.log_pos hx₂ ) ), mul_div_cancel₀ ( Real.exp ( -γ ) ) ( ne_of_gt ( Real.log_pos hx₂ ) ) ] ;
    have h_mertens_inv : Filter.Tendsto (fun X : ℝ => (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) / Real.log X) Filter.atTop (nhds (Real.exp γ)) := by
      have := h_mertens.inv₀ ; simp_all +decide [ Real.exp_neg ];
      simpa only [ div_eq_inv_mul ] using this;
    have := h_mertens_inv.eventually ( gt_mem_nhds <| show Real.exp γ < Real.exp γ + 50 * ε / 111 by linarith );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₂, hX₂ ⟩ ; exact ⟨ Max.max X₂ 2, fun X hX => by have := hX₂ X ( le_trans ( le_max_left _ _ ) hX ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₂ 2 ] ) ] at this; linarith ⟩ ;
  refine ⟨ Max.max X₁ ( Max.max X₂ 2 ), fun X hX P hP => ?_ ⟩ ; specialize hX₁ X ( le_trans ( le_max_left ?_ ?_ ) hX ) ( fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0 ) ?_
  focus
    simp_all +decide [ F_count, H_count ]
  · constructor <;> norm_num;
    · exact fun m => Classical.or_iff_not_imp_left.2 fun h => by push Not at h; exact h;
    · constructor;
      · exact fun h => Nat.not_prime_one ( hP _ h |>.1 );
      · intro a b ha hb; split_ifs <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
  · -- By Euler product bound, we have $H_f(X) \leq \prod_{p \leq X, p \notin P} (1 - 1/p)^{-1}$.
    have h_euler : H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X ≤ (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) := by
      have h_euler : H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X ≤ ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) := by
        unfold H_count; simp +decide ;
        erw [ Finset.sum_filter, Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
        exact Finset.sum_le_sum fun _ _ => by split_ifs <;> ring_nf <;> norm_num;
      -- The sum $\sum_{m \leq X, \forall p \in P, \neg p \mid m} \frac{1}{m}$ is bounded above by the product $\prod_{p \leq X, p \notin P} (1 - 1/p)^{-1}$.
      have h_sum_bound : ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) ≤ ∏ p ∈ primesUpTo X \ P, (∑ k ∈ Finset.range (Nat.log p ⌊X⌋₊ + 1), (1 / (p ^ k : ℝ))) := by
        have h_sum_bound : ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) ≤ ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (∏ p ∈ primesUpTo X \ P, (1 / (p ^ (Nat.factorization m p) : ℝ))) := by
          refine Finset.sum_le_sum fun m hm => ?_;
          have h_factorization : m = ∏ p ∈ primesUpTo X \ P, p ^ (Nat.factorization m p) := by
            conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) ] : m ≠ 0 ) ] ;
            rw [ Finsupp.prod_of_support_subset ] <;> simp_all +decide [ Finset.subset_iff ];
            exact fun p pp dp _ => ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_dvd hm.1.1 dp ) hm.1.2 ) ), pp ⟩, fun hp => hm.2 p hp dp ⟩;
          rw [ h_factorization, Nat.cast_prod ];
          norm_num [ ← h_factorization ];
        refine le_trans h_sum_bound ?_;
        rw [ Finset.prod_sum ];
        refine le_trans ?_
          ( Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.image ( fun m => fun p hp => Nat.factorization m p )
              ( Finset.filter ( fun m => ∀ p ∈ P, ¬p ∣ m ) ( Finset.Icc 1 ⌊X⌋₊ ) ))
            ?_ fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity );
        rotate_left;
        · simp +decide [ Finset.subset_iff ];
          rintro x m hm₁ hm₂ hm₃ rfl p hp hq; exact Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( by unfold primesUpTo at hp; aesop ) ) ( Nat.le_trans ( Nat.le_of_dvd hm₁ ( Nat.ordProj_dvd _ _ ) ) hm₂ ) ;
        · rw [ Finset.sum_image ];
          · exact Finset.sum_le_sum fun x hx => by rw [ ← Finset.prod_attach ] ;
          · intro m hm m' hm' h_eq; simp_all +decide [ funext_iff ] ;
            rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : m ≠ 0 ), ← Nat.prod_factorization_pow_eq_self ( by linarith : m' ≠ 0 ) ];
            congr! 1;
            ext p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ≤ ⌊X⌋₊ <;> simp_all +decide [ primesUpTo ] ;
            · by_cases hp'' : p ∈ P <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
            · rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; linarith ), Nat.factorization_eq_zero_of_not_dvd ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; linarith ) ];
      refine le_trans h_euler <| h_sum_bound.trans ?_;
      gcongr;
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by unfold primesUpTo at *; aesop ) ];
      simpa using Summable.sum_le_tsum ( Finset.range ( Nat.log _ ⌊X⌋₊ + 1 ) ) ( fun _ _ => by positivity ) ( summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by unfold primesUpTo at *; aesop ) ) ) ) );
    -- By Mertens' product theorem, we have $\prod_{p \leq X, p \notin P} (1 - 1/p)^{-1} \leq (e^γ + ε/2) \log X \prod_{p \in P} (1 - 1/p)$.
    have h_mertens : (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) ≤ (Real.exp γ + 50 * ε / 111) * Real.log X * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
      have h_mertens : (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) = (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
        rw [ ← Finset.prod_sdiff <| show P ⊆ primesUpTo X from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| hP p hp |>.2, hP p hp |>.1 ⟩ ];
        simp +decide ;
        rw [ mul_assoc, inv_mul_cancel₀ ( Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero_of_ne <| by norm_num; linarith [ Nat.Prime.one_lt ( hP p hp |>.1 ) ] ), mul_one ];
      exact h_mertens.symm ▸ mul_le_mul_of_nonneg_right ( hX₂ X ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hX ) ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop );
    refine le_trans ?_ (hX₁.trans ?_)
    · unfold F_count
      simp +decide
      exact Finset.card_mono fun x hx => by aesop
    · have hxpos : 0 < X := by
        have := le_max_right X₁ (max X₂ 2)
        have := le_max_right X₂ (2 : ℝ)
        linarith
      have hlog : 0 < Real.log X := Real.log_pos (by
        have := le_max_right X₁ (max X₂ 2)
        have := le_max_right X₂ (2 : ℝ)
        linarith)
      have hbpos : 0 < Real.exp γ + ε := by positivity
      have hPnonneg : 0 ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
        apply Finset.prod_nonneg
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_lt.le
        exact sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le (by norm_num) hp1)
      have hcoeff :
          (111 / 100 + ε / 2 / (Real.exp γ + ε)) * (Real.exp γ + 50 * ε / 111) ≤
            (111 / 100) * Real.exp γ + ε := by
        have hδpos : 0 ≤ ε / 2 / (Real.exp γ + ε) := by positivity
        have hcancel := div_mul_cancel₀ (ε / 2) hbpos.ne'
        nlinarith
      calc
        (111 / 100 + ε / 2 / (Real.exp γ + ε)) * X / Real.log X *
            H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X
          ≤ (111 / 100 + ε / 2 / (Real.exp γ + ε)) * X / Real.log X *
              ((Real.exp γ + 50 * ε / 111) * Real.log X *
                ∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
                  exact mul_le_mul_of_nonneg_left (h_euler.trans h_mertens) (by positivity)
        _ = ((111 / 100 + ε / 2 / (Real.exp γ + ε)) *
              (Real.exp γ + 50 * ε / 111)) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
                field_simp
        _ ≤ ((111 / 100) * Real.exp γ + ε) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hxpos.le) hPnonneg

theorem sifted_bound_set (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0) (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
      ((S.card : ℝ) ≤ (((111 / 100) * Real.exp γ) + ε) * n * Pi_sieve n lam k S) := by
  obtain ⟨ N₀, hN₀ ⟩ := sieve_bound hCheb ε hε;
  refine ⟨ ⌈N₀⌉₊, fun n hn k S hS =>
    le_trans ?_ ( hN₀ n ( Nat.le_of_ceil_le hn ) (P_sieve n lam k S) ?_ ) ⟩;
  · refine mod_cast Finset.card_le_card ?_;
    intro m hm;
    have hmIcc := Finset.mem_Icc.mp ( hS hm );
    refine Finset.mem_filter.mpr ⟨ ?_, hmIcc.1, ?_ ⟩;
    · simpa using Nat.lt_succ_of_le hmIcc.2;
    intro p hp hp_dvd;
    exact ( Finset.mem_filter.mp hp |>.2 )
      ⟨ m, Finset.mem_filter.mpr ⟨ hm, hp_dvd ⟩ ⟩;
  · simp +zetaDelta at *;
    intro p hp;
    refine ⟨ ?_, ?_ ⟩;
    · exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
    · refine le_trans ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ?_;
      exact Nat.floor_le_of_le ( div_le_self ( Nat.cast_nonneg _ ) ( by exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( one_le_pow₀ hlam.le ) zero_le_two ) ) )

theorem sifted_bound_union (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0) (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
      ∀ L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty),
        (((L.biUnion (sinv S ·)).card : ℝ) ≤
          (((111 / 100) * Real.exp γ) + ε) * n / Y_val lam k * Pi_sieve n lam k S) := by
  obtain ⟨ X₀, hX₀ ⟩ := sieve_bound hCheb ε hε;
  refine ⟨ ⌈X₀ ^ 2 / lam⌉₊ + 1, fun n hn k S hS L hL => ?_ ⟩;
  by_cases hP : P_sieve n lam k S = ∅;
  · have h_card : (L.biUnion (sinv S ·)).card ≤ n / Y_val lam k := by
      have h_card : (L.biUnion (sinv S ·)).card ≤ Finset.card (Finset.Icc 1 (Nat.floor (n / Y_val lam k))) := by
        refine Finset.card_le_card ?_;
        intro x hx; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ a, ha₁, ha₂ ⟩ := hx; specialize hL ha₁; simp_all +decide [ sinv ] ;
        obtain ⟨ y, hy₁, hy₂ ⟩ := ha₂; have := hS ( Finset.mem_filter.mp hy₁ |>.1 ) ; simp_all +decide [ sdiv ] ;
        have h_div : a ≥ Y_val lam k := by
          exact Nat.le_of_ceil_le ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hL.1 |>.1 ) |>.1 );
        exact ⟨ hy₂ ▸ Nat.div_pos ( Nat.le_of_dvd ( hS hy₁.1 |>.1 ) hy₁.2 ) ( Nat.pos_of_dvd_of_pos hy₁.2 ( hS hy₁.1 |>.1 ) ), Nat.le_floor <| by rw [ le_div_iff₀ <| by exact mul_pos zero_lt_two <| pow_pos ( by positivity ) _ ] ; nlinarith [ show ( y : ℝ ) ≤ n by exact_mod_cast hS hy₁.1 |>.2, show ( a : ℝ ) ≥ Y_val lam k by exact_mod_cast h_div, Nat.div_mul_le_self y a, show ( y : ℝ ) = a * x by exact_mod_cast by nlinarith [ Nat.div_mul_cancel hy₁.2 ] ] ⟩;
      exact le_trans ( Nat.cast_le.mpr h_card ) ( by simpa using Nat.floor_le ( show 0 ≤ ( n : ℝ ) / Y_val lam k by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) );
    refine le_trans h_card ?_;
    rw [ show Pi_sieve n lam k S = 1 from _ ];
    · rw [ mul_one ] ; gcongr;
      · exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ );
      · refine le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ?_;
        refine le_add_of_le_of_nonneg ?_ hε.le;
        refine le_trans (Real.one_le_exp (x := γ) ?_)
          (le_mul_of_one_le_left (Real.exp_nonneg γ) (by norm_num : (1 : ℝ) ≤ 111 / 100));
        refine le_of_tendsto_of_tendsto tendsto_const_nhds ( Real.tendsto_eulerMascheroniSeq ) ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        simp +decide [ eulerMascheroniSeq ];
        induction hn <;> simp_all +decide [ harmonic ];
        · exact le_trans ( Real.log_le_sub_one_of_pos ( by norm_num ) ) ( by norm_num );
        · rw [ Finset.sum_range_succ, Real.log_le_iff_le_exp ( by positivity ) ] at *;
          rw [ Real.exp_add ];
          nlinarith [ Real.add_one_le_exp ( ( ↑‹ℕ› : ℝ ) + 1 ) ⁻¹, Real.exp_pos ( ( ↑‹ℕ› : ℝ ) + 1 ) ⁻¹, mul_inv_cancel₀ ( by positivity : ( ( ↑‹ℕ› : ℝ ) + 1 ) ≠ 0 ) ];
    · unfold Pi_sieve; aesop;
  · have h_n_Yk_ge_X₀ : (n : ℝ) / Y_val lam k ≥ X₀ := by
      have h_n_Yk_ge_X₀ : (n : ℝ) ≥ X₀^2 / lam ∧ (n : ℝ) / Y_val lam k ≥ Y_val lam (k + 1) := by
        have h_n_Yk_ge_X₀ : (n : ℝ) ≥ X₀^2 / lam := by
          exact le_of_lt ( Nat.lt_of_ceil_lt hn );
        obtain ⟨ p, hp ⟩ := Finset.nonempty_of_ne_empty hP;
        simp_all +decide [ P_sieve ];
        exact le_trans ( Nat.lt_of_floor_lt hp.1.1.1 |> le_of_lt ) ( Nat.floor_le ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) |> le_trans ( Nat.cast_le.mpr hp.1.1.2 ) );
      unfold Y_val at *;
      field_simp at *;
      ring_nf at *;
      norm_num [ pow_mul ] at *;
      nlinarith [ show ( lam : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ hlam.le, show ( lam : ℝ ) ^ k * lam ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ hlam.le ) hlam.le ];
    have h_card_sifted :
        ((L.biUnion (sinv S ·)).card : ℝ) ≤
          ((Finset.range (⌊(n : ℝ) / Y_val lam k⌋₊ + 1)).filter
            (fun m => m ≥ 1 ∧ ∀ r ∈ P_sieve n lam k S, ¬r ∣ m)).card := by
      exact_mod_cast Finset.card_le_card (biUnion_sinv_subset_sifted hS hlam hL)
    have hP_bound :
        ∀ p ∈ P_sieve n lam k S, Nat.Prime p ∧ (p : ℝ) ≤ (n : ℝ) / Y_val lam k := by
      intro p hp
      exact
        ⟨Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.2,
          by
            exact le_trans
              (Nat.cast_le.mpr <|
                Finset.mem_Ioc.mp
                  (Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1) |>.2)
              (Nat.floor_le <|
                by
                  exact div_nonneg (Nat.cast_nonneg _) <|
                    by exact mul_nonneg zero_le_two <| pow_nonneg (by positivity) _)⟩
    refine le_trans h_card_sifted ?_
    simpa [Pi_sieve, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hX₀ ((n : ℝ) / Y_val lam k) h_n_Yk_ge_X₀ (P_sieve n lam k S) hP_bound

lemma wip_finitely_many (lam : ℝ) (hlam : 1 < lam)
    (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (ε : ℝ) (hε : ε > 0) (K : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, k ≤ K →
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ k ≤ K, ∀ n ≥ N₁, M_layer lam k / g k * (∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
    have h_case1 : ∀ k ≤ K, ∃ N₁ : ℕ, ∀ n ≥ N₁, M_layer lam k * (∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
      intro k hk
      obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, n ≥ N₁ → (∏ p ∈ primesUpTo (⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
        have := mertens_product_estimate ( ε / 4 ) ( by positivity );
        obtain ⟨ X₀, hX₀ ⟩ := this;
        -- Choose N₁ such that for all n ≥ N₁, ⌊n/Y_k⌋ ≥ X₀.
        obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ⌊(n : ℝ) / Y_val lam k⌋₊ ≥ X₀ := by
          have h_floor : Filter.Tendsto (fun n : ℕ => ⌊(n : ℝ) / Y_val lam k⌋₊ : ℕ → ℝ) Filter.atTop Filter.atTop := by
            exact tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| Filter.Tendsto.atTop_div_const ( show 0 < Y_val lam k from mul_pos zero_lt_two <| pow_pos ( by positivity ) _ ) <| tendsto_natCast_atTop_atTop;
          exact Filter.eventually_atTop.mp ( h_floor.eventually_ge_atTop X₀ );
        use N₁ + 2; intros n hn; specialize hX₀ ⌊ ( n : ℝ ) / Y_val lam k⌋₊ ( hN₁ n ( by linarith ) ) ; rw [ abs_le ] at hX₀; ring_nf at *; linarith;
      use N₁ + ⌈Y_val lam (k + 1) * Y_val lam k⌉₊ + 1;
      intro n hn
      have h_prod : M_layer lam k * (∏ p ∈ (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) = (∏ p ∈ primesUpTo (⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) := by
        apply M_layer_prod_eq;
        refine Nat.le_floor ?_;
        rw [ le_div_iff₀ ] <;> norm_num [ Y_val ] at *;
        · nlinarith [ Nat.floor_le ( show 0 ≤ 2 * lam ^ ( k + 1 ) by positivity ), Nat.le_ceil ( 2 * lam ^ ( k + 1 ) * ( 2 * lam ^ k ) ), show ( n : ℝ ) ≥ N₁ + ⌈2 * lam ^ ( k + 1 ) * ( 2 * lam ^ k ) ⌉₊ + 1 by exact_mod_cast hn, pow_pos ( zero_lt_one.trans hlam ) k, pow_succ' lam k ];
        · positivity;
      exact h_prod.symm ▸ hN₁ n ( by linarith );
    choose! N₁ hN₁ using h_case1;
    use Finset.sup (Finset.range (K + 1)) N₁;
    intro k hk n hn; specialize hN₁ k hk n ( le_trans ( Finset.le_sup ( f := N₁ ) ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hk ) ) ) hn ) ; simp_all +decide [ div_mul_eq_mul_div ] ;
    exact le_trans ( div_le_self ( mul_nonneg ( M_layer_nonneg _ _ ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ) ) <| hg1 _ ) hN₁;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ k ≤ K, ∀ n ≥ N₂, Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) ≥ (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) * Real.log n := by
    have h_log_floor : ∀ k ≤ K, Filter.Tendsto (fun n : ℕ => Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log n) Filter.atTop (nhds 1) := by
      intro k hk
      have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => Real.log (n / Y_val lam k) / Real.log n) Filter.atTop (nhds 1) := by
        have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => (Real.log n - Real.log (Y_val lam k)) / Real.log n) Filter.atTop (nhds 1) := by
          ring_nf;
          exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( mod_cast hx ) ) ) ] ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num );
        refine h_log_floor_aux.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt ( show 0 < Y_val lam k from mul_pos zero_lt_two ( pow_pos ( by positivity ) _ ) ) ) ] );
      have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log (n / Y_val lam k)) Filter.atTop (nhds 1) := by
        have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => Real.log (⌊x⌋₊) / Real.log x) Filter.atTop (nhds 1) := by
          have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => Real.log (x - 1) / Real.log x) Filter.atTop (nhds 1) := by
            have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => (Real.log x + Real.log (1 - 1 / x)) / Real.log x) Filter.atTop (nhds 1) := by
              ring_nf;
              exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
            refine h_log_floor_aux.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_sub_div ( by linarith ) ] ; rw [ Real.log_div ] <;> ring_nf <;> linarith );
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_log_floor_aux tendsto_const_nhds ?_ ?_;
          · filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using div_le_div_of_nonneg_right ( Real.log_le_log ( by linarith ) ( by linarith [ Nat.lt_floor_add_one x ] ) ) ( Real.log_nonneg ( by linarith ) );
          · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using div_le_one_of_le₀ ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by linarith ) <| Real.log_nonneg <| by linarith;
        exact h_log_floor_aux.comp <| tendsto_natCast_atTop_atTop.atTop_div_const <| show 0 < Y_val lam k from mul_pos zero_lt_two <| pow_pos ( by positivity ) _;
      have := h_log_floor_aux.mul ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n / Y_val lam k ) / Real.log n ) Filter.atTop ( nhds 1 ) ›;
      simp_all +decide ;
      refine this.congr' ( by filter_upwards [ ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n / Y_val lam k ) / Real.log n ) Filter.atTop ( nhds 1 ) ›.eventually_ne one_ne_zero ] with n hn using by rw [ div_mul_div_cancel₀ ( by aesop ) ] );
    have h_log_floor : ∀ k ≤ K, ∃ N₂ : ℕ, ∀ n ≥ N₂, Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log n ≥ (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) := by
      exact fun k hk => by rcases Metric.tendsto_atTop.mp ( h_log_floor k hk ) ( 1 - ( Real.exp ( -γ ) + ε / 2 ) / ( Real.exp ( -γ ) + ε ) ) ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ Real.exp_pos ( -γ ) ] ) with ⟨ N₂, hN₂ ⟩ ; exact ⟨ N₂, fun n hn => by linarith [ abs_lt.mp ( hN₂ n hn ) ] ⟩ ;
    choose! N₂ hN₂ using h_log_floor;
    exact ⟨ Finset.sup ( Finset.Iic K ) N₂ + 2, fun k hk n hn => by have := hN₂ k hk n ( by linarith [ Finset.le_sup ( f := N₂ ) ( Finset.mem_Iic.mpr hk ) ] ) ; rwa [ ge_iff_le, le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Finset.le_sup ( f := N₂ ) ( Finset.mem_Iic.mpr hk ) ] ) ] at this ⟩;
  use Max.max N₁ N₂ + 2;
  intro n hn k hk; specialize hN₁ k hk n ( by linarith [ Nat.le_max_left N₁ N₂ ] ) ; specialize hN₂ k hk n ( by linarith [ Nat.le_max_right N₁ N₂ ] ) ;
  refine le_trans hN₁ ?_;
  rw [ div_le_div_iff₀ ];
  · rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀ ] at hN₂ <;> first | positivity | linarith;
  · refine lt_of_lt_of_le ?_ hN₂;
    exact mul_pos ( div_pos ( by positivity ) ( by positivity ) ) ( Real.log_pos ( by norm_cast; linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) );
  · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ;

/-
M_k * product ≤ (e^{-γ}+δ)/log(max(Y_{k+1}, n/Y_k)). Combined with log(max(...))≥ log(n)/2, this gives
M_k * product ≤ 2(e^{-γ}+δ)/log n.
-/
lemma wip_mertens_bound (lam : ℝ) (hlam : 1 < lam)
    (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      M_layer lam k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        2 * (Real.exp (-γ) + δ) / Real.log n := by
  have := @mertens_product_estimate;
  obtain ⟨ X₀, hX₀ ⟩ := this ( δ / 2 ) ( half_pos hδ );
  refine ⟨ ⌈X₀⌉₊ ^ 2 + ⌈lam ^ 2⌉₊ ^ 2 + 2, fun n hn k => ?_ ⟩;
  -- Let $x = \max(Y_{k+1}, n/Y_k)$.
  set x := max (Y_val lam (k + 1)) (n / Y_val lam k) with hx;
  -- By definition of $x$, we have $M_k * \prod_{Y_{k+1}<p\le n/Y_k}(1-1/p) \le \prod_{p\le x}(1-1/p)$.
  have h_prod_le : M_layer lam k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) := by
    by_cases h : ⌊Y_val lam ( k + 1 ) ⌋₊ ≤ ⌊ ( n : ℝ ) / Y_val lam k ⌋₊ <;> simp_all +decide [ M_layer, primesUpTo ];
    · rw [ ← Finset.prod_union ];
      · refine le_of_eq ?_;
        refine Finset.prod_bij ( fun x hx => x ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_union, Finset.mem_filter ];
        · rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ ) <;> [ exact ⟨ le_trans ha₁ ( Nat.floor_mono <| le_max_left _ _ ), ha₂ ⟩ ; exact ⟨ le_trans ha₂ ( Nat.floor_mono <| le_max_right _ _ ), ha₃ ⟩ ];
        · grind;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    · rw [ max_eq_left ];
      · norm_num [ Finset.Ioc_eq_empty_of_le h.le ];
      · contrapose! h;
        exact Nat.floor_mono h.le;
  -- By definition of $x$, we have $x \geq \sqrt{\lambda n}$.
  have hx_ge_sqrt : x ≥ Real.sqrt (lam * n) := by
    have hx_ge_sqrt : Y_val lam (k + 1) * (n / Y_val lam k) ≥ lam * n := by
      unfold Y_val; ring_nf; norm_num [ show lam ≠ 0 by positivity ] ;
      nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( lam ^ k : ℝ ) ≠ 0 ) ( lam * n ) ];
    refine Real.sqrt_le_iff.mpr ⟨ ?_, ?_ ⟩;
    · exact le_max_of_le_left ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) );
    · cases max_cases ( Y_val lam ( k + 1 ) ) ( n / Y_val lam k ) <;> nlinarith [ show 0 ≤ Y_val lam ( k + 1 ) from by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ), show 0 ≤ ( n : ℝ ) / Y_val lam k from by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ];
  -- Since $x \geq \sqrt{\lambda n}$, we have $\log x \geq \frac{1}{2} \log n$.
  have hlogx_ge_halflogn : Real.log x ≥ (1 / 2) * Real.log n := by
    have hlogx_ge_halflogn : Real.log x ≥ Real.log (Real.sqrt (lam * n)) := by
      exact Real.log_le_log ( Real.sqrt_pos.mpr ( mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by nlinarith ) ) ) ) hx_ge_sqrt;
    rw [ Real.log_sqrt ( by positivity ), Real.log_mul ( by positivity ) ( by norm_cast; nlinarith ) ] at hlogx_ge_halflogn ; linarith [ Real.log_nonneg hlam.le ];
  -- Since $x \geq \sqrt{\lambda n}$, we have $x \geq X₀$.
  have hx_ge_X₀ : x ≥ X₀ := by
    refine le_trans ?_ hx_ge_sqrt;
    refine le_trans ?_ ( Real.sqrt_le_sqrt <| show lam * n ≥ ⌈X₀⌉₊ ^ 2 by nlinarith [ Nat.le_ceil X₀, show ( n : ℝ ) ≥ ⌈X₀⌉₊ ^ 2 + ⌈lam ^ 2⌉₊ ^ 2 + 2 by exact_mod_cast hn, show ( ⌈lam ^ 2⌉₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ] );
    rw [ Real.sqrt_sq ] <;> linarith [ Nat.le_ceil X₀ ];
  refine le_trans h_prod_le ?_;
  refine le_trans ( show ∏ p ∈ primesUpTo x, ( 1 - 1 / ( p : ℝ ) ) ≤ Real.exp ( -γ ) / Real.log x + δ / 2 / Real.log x from ?_ ) ?_;
  · linarith [ abs_le.mp ( hX₀ x hx_ge_X₀ ) ];
  · rw [ ← add_div, div_le_div_iff₀ ];
    · nlinarith [ Real.exp_pos ( -γ ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; nlinarith ) ];
    · exact lt_of_lt_of_le ( mul_pos ( by norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by nlinarith ) ) ) ) hlogx_ge_halflogn;
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by nlinarith;

lemma wip_large_k (lam : ℝ) (hlam : 1 < lam)
    (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : ε > 0) :
    ∃ K : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, K < k →
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, M_layer lam k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ 2 * (Real.exp (-γ) + ε / 2) / Real.log n := by
    apply wip_mertens_bound lam hlam (ε / 2) (half_pos hε);
  -- Choose K such that for all k > K, g_k ≥ 2(e^{-γ} + ε/2)/(e^{-γ} + ε).
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k : ℕ, k > K → g k ≥ 2 * (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) := by
    exact Filter.eventually_atTop.mp ( hg.eventually_ge_atTop _ ) |> fun ⟨ K, hK ⟩ => ⟨ K, fun k hk => hK k hk.le ⟩;
  use K, N₁;
  intro n hn k hk; specialize hN₁ n hn k; specialize hK k hk; rw [ div_mul_eq_mul_div, div_le_iff₀ ] at * <;> try linarith [ hg1 k ];
  rw [ div_mul_eq_mul_div, le_div_iff₀ ] at *;
  · rw [ ge_iff_le, div_le_iff₀ ] at hK <;> nlinarith [ Real.exp_pos ( -γ ) ];
  · rcases n with ( _ | _ | n ) <;> norm_num at *;
    · contrapose! hN₁;
      exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    · contrapose! hN₁;
      refine mul_pos ?_ ?_;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
    · exact Real.log_pos <| by linarith;
  · rcases n with ( _ | _ | n ) <;> norm_num at *;
    · contrapose! hN₁;
      exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    · contrapose! hN₁;
      refine mul_pos ?_ ?_;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
    · exact Real.log_pos <| by linarith

/-- M_{λ,k}/g_k · ∏_{Y_{λ,k+1} < p ≤ n/Y_{λ,k}} (1-1/p) ≤ (e^{-γ}+o(1))/log n -/
theorem weighted_interval_product (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (hlam : 1 < lam) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨K, N₂, hN₂⟩ := wip_large_k lam hlam g hg1 hg ε hε
  obtain ⟨N₁, hN₁⟩ := wip_finitely_many lam hlam g hg1 ε hε K
  exact ⟨max N₁ N₂, fun n hn k => by
    by_cases hk : k ≤ K
    · exact hN₁ n (le_of_max_le_left hn) k hk
    · exact hN₂ n (le_of_max_le_right hn) k (by omega)⟩


end Erdos490
