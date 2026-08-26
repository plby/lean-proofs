/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 512, Littlewood's conjecture on exponential sums.
Informal authors: O. Carruth McGehee, Louis Pigno, Brent Smith.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/512#post-7140
https://aristotle.harmonic.fun/dashboard/requests/b663fac0-b653-4148-8d0a-9ae5c7dbdaea
The supplied files do not state a toolchain, Mathlib revision, or license.
-/
import ErdosProblems.Erdos512.Hardy

open MeasureTheory Complex

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos512

/-- The recursively-defined dual function `F_m` of McGehee–Pigno–Smith:
`F₀ = α f₀`, `F_{m+1} = F_m · exp(-h_{m+1}) + α f_{m+1}`. -/
noncomputable def Frec (α : ℂ) (f h : ℕ → AddCircle (1 : ℝ) → ℂ) : ℕ → AddCircle (1 : ℝ) → ℂ
  | 0 => fun x => α * f 0 x
  | (m + 1) => fun x => Frec α f h m x * Complex.exp (- h (m + 1) x) + α * f (m + 1) x

/-- The cumulative exponential factor `exp(-∑_{i < l ≤ m} h_l)`. -/
noncomputable def prodexp (h : ℕ → AddCircle (1 : ℝ) → ℂ) (i m : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fun x => Complex.exp (- ∑ l ∈ Finset.Ioc i m, h l x)

theorem prodexp_self (h : ℕ → AddCircle (1 : ℝ) → ℂ) (m : ℕ) (x) : prodexp h m m x = 1 := by
  classical
  -- By definition of `prodexp`, we have `prodexp h m m x = Complex.exp (- ∑ l ∈ Finset.Ioc m m, h l x)`.
  simp [prodexp]

theorem prodexp_succ (h : ℕ → AddCircle (1 : ℝ) → ℂ) {i m : ℕ} (him : i ≤ m) (x) :
    prodexp h i (m + 1) x = prodexp h i m x * Complex.exp (- h (m + 1) x) := by
  classical
  unfold prodexp; simp +decide [ *, Finset.sum_Ioc_succ_top, Complex.exp_add ] ;
  ring

theorem prodexp_continuous {h : ℕ → AddCircle (1 : ℝ) → ℂ} (hh : ∀ l, Continuous (h l))
    (i m : ℕ) : Continuous (prodexp h i m) := by
  classical
  exact Complex.continuous_exp.comp ( Continuous.neg ( continuous_finsetSum _ fun l hl => hh l ) )

theorem prodexp_coAnalytic {h : ℕ → AddCircle (1 : ℝ) → ℂ} (hh : ∀ l, TrigPolyNeg (h l))
    (i m : ℕ) : CoAnalytic (prodexp h i m) := by
  classical
  -- The function ψ is the negative of a sum of trigonometric polynomials, hence it's a trigonometric polynomial itself. We can use the fact that the sum of trigonometric polynomials is a trigonometric polynomial.
  have h_psi : TrigPolyNeg (fun x => -∑ l ∈ Finset.Ioc i m, h l x) := by
    convert TrigPolyNeg.neg ( TrigPolyNeg.sum ( Finset.Ioc i m ) ( fun l => h l ) fun l hl => hh l ) using 1;
  exact TrigPolyNeg.coAnalytic_exp h_psi

/-
Closed form for `Frec`.
-/
theorem Frec_closed (α : ℂ) (f h : ℕ → AddCircle (1 : ℝ) → ℂ) (m : ℕ) (x) :
    Frec α f h m x = α * ∑ i ∈ Finset.range (m + 1), f i x * prodexp h i m x := by
  classical
  induction' m with m ih generalizing x;
  · simp +decide [ Frec, prodexp ];
  · simp_all +decide [ Finset.sum_range_succ, Frec ];
    simp +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, prodexp ];
    exact Finset.sum_congr rfl fun i hi => by rw [ ← Complex.exp_add ] ; rw [ Finset.sum_Ioc_succ_top ( by linarith [ Finset.mem_range.mp hi ] ) ] ; ring;

/-
Calculus inequality `exp(-t/4) + t/5 ≤ 1` for `t ∈ [0,1]`.
-/
theorem exp_calc_ineq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp (-(t / 4)) + t / 5 ≤ 1 := by
  classical
  rw [ Real.exp_neg ];
  rw [ inv_eq_one_div, div_add_div, div_le_iff₀ ] <;> try positivity;
  nlinarith [ Real.add_one_le_exp ( t / 4 ), Real.exp_pos ( t / 4 ), sq_nonneg ( t - 1 ) ]

/-
The sup-norm bound `‖F_m‖∞ ≤ 1`.
-/
theorem Frec_norm_le {f h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hf : ∀ j x, ‖f j x‖ ≤ 1) (hh : ∀ j x, (1 / 4 : ℝ) * ‖f j x‖ ≤ (h j x).re) (m : ℕ) (x) :
    ‖Frec (1 / 5 : ℂ) f h m x‖ ≤ 1 := by
  classical
  induction' m with m ih generalizing x;
  · exact le_trans ( by simpa [ Frec ] using mul_le_mul_of_nonneg_left ( hf 0 x ) ( by norm_num ) ) ( by norm_num );
  · rw [Frec]
    refine (norm_add_le _ _).trans ?_
    norm_num [Complex.norm_exp]
    refine' le_trans ( add_le_add ( mul_le_of_le_one_left ( Real.exp_nonneg _ ) ( by linarith [ ih x ] ) ) le_rfl ) _;
    have := exp_calc_ineq ( show 0 ≤ ‖f ( m + 1 ) x‖ by positivity ) ( show ‖f ( m + 1 ) x‖ ≤ 1 by exact hf _ _ );
    linarith [ Real.exp_le_exp.mpr ( show - ( h ( m + 1 ) x |> Complex.re ) ≤ - ( ‖f ( m + 1 ) x‖ / 4 ) by linarith [ hh ( m + 1 ) x ] ) ]

/-
Fourier coefficient of `Frec` in expanded (telescoped) form.
-/
theorem Frec_coeff (α : ℂ) {f h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hfc : ∀ i, Continuous (f i)) (hhc : ∀ l, Continuous (h l)) (m : ℕ) (n : ℤ) :
    fourierCoeff (Frec α f h m) n
      = α * ∑ i ∈ Finset.range (m + 1),
          fourierCoeff (fun x => f i x * prodexp h i m x) n := by
  classical
  rw [show Frec α f h m = (fun x => α * ∑ i ∈ Finset.range (m + 1),
      f i x * prodexp h i m x) from funext (Frec_closed α f h m)]
  rw [fourierCoeff.const_mul]
  congr 1
  have hsum := congr_fun (fourierCoeff.sum (Finset.range (m + 1))
    (fun i x => f i x * prodexp h i m x)
    (fun i _ => ((hfc i).mul (prodexp_continuous hhc i m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))) n
  have heq : (∑ i ∈ Finset.range (m + 1), fun x => f i x * prodexp h i m x) =
      (fun x => ∑ i ∈ Finset.range (m + 1), f i x * prodexp h i m x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq] at hsum
  simpa only [Finset.sum_apply] using hsum

/-
Geometric tail bound `∑_{i < l ≤ m} (1/2)^l ≤ (1/2)^i`.
-/
theorem geom_sum_half_Ioc (i m : ℕ) :
    ∑ l ∈ Finset.Ioc i m, (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ i := by
  classical
  by_cases vim : m ≤ i;
  · aesop;
  · induction' m with m ih <;> norm_num [ pow_succ', Finset.sum_Ioc_succ_top ] at *;
    cases vim.eq_or_lt <;> simp_all +decide [ Finset.sum_Ioc_succ_top ];
    · gcongr <;> norm_num;
    · have h_sum : ∑ k ∈ Finset.Ioc i m, (2 ^ k : ℝ)⁻¹ = (2 ^ i : ℝ)⁻¹ - (2 ^ m : ℝ)⁻¹ := by
        exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by rw [ Finset.sum_Ioc_succ_top ( by linarith ), pow_succ' ] ; norm_num ; linarith ) m vim;
      norm_num [ pow_succ' ] at * ; linarith [ inv_pos.mpr ( pow_pos ( zero_lt_two' ℝ ) m ) ]

/-
`L²` bound on `exp(-∑ h) - 1`.
-/
theorem L2nrm_prodexp_sub_one_le {h : ℕ → AddCircle (1 : ℝ) → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hhc : ∀ l, Continuous (h l)) (hhre : ∀ l x, 0 ≤ (h l x).re)
    (hh2 : ∀ l, L2nrm (h l) ≤ B * (1 / 2 : ℝ) ^ l) (i m : ℕ) :
    L2nrm (fun x => prodexp h i m x - 1) ≤ B * (1 / 2 : ℝ) ^ i := by
  classical
  -- Apply `L2nrm_exp_neg_sub_one_le` to the function `φ = fun x => ∑ l ∈ Finset.Ioc i m, h l x`.
  have hφ_cont : Continuous (fun x => ∑ l ∈ Finset.Ioc i m, h l x) := by
    exact continuous_finsetSum _ fun _ _ => hhc _
  have hφ_re : ∀ x, 0 ≤ (∑ l ∈ Finset.Ioc i m, h l x).re := by
    exact fun x => by simpa using Finset.sum_nonneg fun l hl => hhre l x;
  have hL2 : L2nrm (fun x => Complex.exp (- ∑ l ∈ Finset.Ioc i m, h l x) - 1) ≤ L2nrm (fun x => ∑ l ∈ Finset.Ioc i m, h l x) := by
    convert L2nrm_exp_neg_sub_one_le hφ_cont hφ_re using 1;
  refine le_trans ?_ ( hL2.trans ?_ );
  · unfold prodexp; norm_num;
  · refine le_trans ( L2nrm_sum_le ( Finset.Ioc i m ) ( fun l => h l ) ( fun l hl => hhc l ) ) ?_;
    refine le_trans ( Finset.sum_le_sum fun l hl => hh2 l ) ?_;
    rw [ ← Finset.mul_sum _ _ _ ] ; exact mul_le_mul_of_nonneg_left ( geom_sum_half_Ioc i m ) hB;

/-
`Frec` is continuous when the data are.
-/
theorem Frec_continuous (α : ℂ) {f h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hfc : ∀ i, Continuous (f i)) (hhc : ∀ l, Continuous (h l)) (m : ℕ) :
    Continuous (Frec α f h m) := by
  classical
  induction' m with m ih;
  · exact continuous_const.mul ( hfc 0 );
  · exact Continuous.add ( ih.mul ( Complex.continuous_exp.comp ( Continuous.neg ( hhc _ ) ) ) ) ( continuous_const.mul ( hfc _ ) )

/-
Geometric tail bound `∑_{j ≤ i ≤ m} (1/4)^i ≤ (4/3)(1/4)^j`.
-/
theorem geom_sum_quarter_Ico (j m : ℕ) :
    ∑ i ∈ Finset.Ico j (m + 1), (1 / 4 : ℝ) ^ i ≤ (4 / 3) * (1 / 4 : ℝ) ^ j := by
  classical
  by_cases h : j ≤ m;
  · rw [ geom_sum_Ico ] <;> ring <;> norm_num;
    linarith;
  · rw [ Finset.Ico_eq_empty ] <;> norm_num ; linarith

/-
**The per-element coefficient estimate.**
-/
theorem re_coeff_ge {f h : ℕ → AddCircle (1 : ℝ) → ℂ} {B : ℝ} (hB : 0 ≤ B) (m : ℕ)
    (hfc : ∀ i, Continuous (f i)) (hhc : ∀ l, Continuous (h l))
    (hhre : ∀ l x, 0 ≤ (h l x).re)
    (hf2 : ∀ i, L2nrm (f i) ≤ (1 / 2 : ℝ) ^ i) (hh2 : ∀ l, L2nrm (h l) ≤ B * (1 / 2 : ℝ) ^ l)
    {j : ℕ} (hj : j ≤ m) {n : ℤ}
    (hmain : (∑ i ∈ Finset.range (m + 1), fourierCoeff (f i) n) = (((1 / 4 : ℝ) ^ j : ℝ) : ℂ))
    (hvanish : ∀ i, i < j → fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n = 0) :
    (1 / 5 : ℝ) * ((1 / 4 : ℝ) ^ j - B * (4 / 3) * (1 / 4 : ℝ) ^ j)
      ≤ (fourierCoeff (Frec (1 / 5 : ℂ) f h m) n).re := by
  classical
  -- Let `D := ∑ i ∈ Finset.range (m+1), fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n`.
  set D := ∑ i ∈ Finset.range (m + 1), fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n;
  have hD : (fourierCoeff (Frec (1 / 5) f h m) n).re = (1 / 5 : ℝ) * (D.re + (1 / 4 : ℝ) ^ j) := by
    convert congr_arg Complex.re ( Frec_coeff ( 1 / 5 ) hfc hhc m n ) using 1;
    rw [ Finset.sum_congr rfl fun i hi => show fourierCoeff ( fun x => f i x * prodexp h i m x ) n = fourierCoeff ( fun x => f i x * ( prodexp h i m x - 1 ) ) n + fourierCoeff ( f i ) n from ?_ ];
    · norm_num [ Finset.sum_add_distrib, hmain ];
      norm_num [ D ];
      norm_num [ show ( 1 / 4 : ℂ ) ^ j = ( 1 / 4 : ℝ ) ^ j by norm_num [ Complex.ext_iff, pow_succ ] ];
      norm_cast;
    · unfold fourierCoeff; simp +decide [ mul_sub ] ; ring;
      rw [ MeasureTheory.integral_add ];
      · rw [ MeasureTheory.integral_neg ] ; ring;
      · refine' Continuous.integrable_of_hasCompactSupport _ _;
        · fun_prop;
        · rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ];
      · refine' Continuous.integrable_of_hasCompactSupport _ _;
        · refine' Continuous.mul _ _;
          · refine' Continuous.mul _ ( hfc i );
            exact Complex.continuous_conj.comp ( by continuity );
          · exact prodexp_continuous hhc i m;
        · rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ];
  -- By definition of $D$, we know that $‖D‖ ≤ ∑ i ∈ Finset.Ico j (m+1), B * (1/4)^i$.
  have hD_norm : ‖D‖ ≤ ∑ i ∈ Finset.Ico j (m + 1), B * (1 / 4 : ℝ) ^ i := by
    have hD_bound : ∀ i ∈ Finset.Ico j (m + 1), ‖fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n‖ ≤ B * (1 / 4 : ℝ) ^ i := by
      intros i hi
      have h_bound : ‖fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n‖ ≤ L2nrm (f i) * L2nrm (fun x => prodexp h i m x - 1) := by
        apply_rules [ norm_fourierCoeff_mul_le ];
        exact Continuous.sub ( prodexp_continuous hhc i m ) continuous_const;
      refine le_trans h_bound ?_;
      refine' le_trans ( mul_le_mul ( hf2 i ) ( L2nrm_prodexp_sub_one_le hB hhc hhre hh2 i m ) ( by exact L2nrm_nonneg _ ) ( by positivity ) ) _ ; ring ; norm_num;
      norm_num [ pow_mul' ];
    convert norm_sum_le _ _ |> le_trans <| Finset.sum_le_sum hD_bound using 1 <;> try rfl
    rw [ Finset.sum_Ico_eq_sub _ ( by linarith ) ];
    rw [ Finset.sum_congr rfl fun i hi => hvanish i ( Finset.mem_range.mp hi ), Finset.sum_const_zero, sub_zero ];
  -- By definition of $D$, we know that $‖D‖ ≤ B * (4 / 3) * (1 / 4) ^ j$.
  have hD_norm_le : ‖D‖ ≤ B * (4 / 3) * (1 / 4 : ℝ) ^ j := by
    exact hD_norm.trans ( by rw [ ← Finset.mul_sum _ _ _ ] ; exact le_trans ( mul_le_mul_of_nonneg_left ( geom_sum_quarter_Ico j m ) hB ) ( by ring_nf; norm_num ) );
  linarith [ abs_le.mp ( Complex.abs_re_le_norm D ) ]

/-! ### Per-set construction -/

/-- Block index of the `k`-th smallest element (0-indexed rank `k`): block `j` consists of the
ranks `k` with `4^j ≤ 3k+1 < 4^{j+1}`, so `|block j| = 4^j`. -/
def blk (k : ℕ) : ℕ := Nat.log 4 (3 * k + 1)

theorem blk_mono {a b : ℕ} (h : a ≤ b) : blk a ≤ blk b := by
  classical
  exact Nat.log_mono_right ( by linarith )

theorem pow_blk_le (k : ℕ) : (4 : ℕ) ^ blk k ≤ 3 * k + 1 := by
  classical
  -- By definition of `blk`, we know that `4 ^ blk k ≤ 3 * k + 1`.
  apply Nat.pow_log_le_self 4 (by linarith)

theorem card_block_le (N j : ℕ) :
    (Finset.univ.filter (fun k : Fin N => blk (k : ℕ) = j)).card ≤ 4 ^ j := by
  classical
  refine' le_trans _ ( show 4 ^ j ≥ ( Finset.Ico ( ( 4 ^ j - 1 ) / 3 ) ( ( 4 ^ j - 1 ) / 3 + 4 ^ j ) |> Finset.card ) from _ );
  · -- Let's choose any $k$ such that $blk k = j$.
    have h_filter : ∀ k : Fin N, blk k = j → (k : ℕ) ∈ Finset.Ico ((4^j - 1) / 3) ((4^j - 1) / 3 + 4^j) := by
      intro k hk
      have h_bounds : 4^j ≤ 3 * k.val + 1 ∧ 3 * k.val + 1 < 4^(j+1) := by
        exact ⟨ hk ▸ pow_blk_le _, hk ▸ Nat.lt_pow_succ_log_self ( by decide ) _ ⟩;
      have h_div : 3 ∣ 4^j - 1 := by
        exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div ( 4 ^ j ) 3 ] ; norm_num [ Nat.pow_mod ] );
      grind;
    convert Finset.card_le_card ( show Finset.image ( fun k : Fin N => ( k : ℕ ) ) ( Finset.filter ( fun k : Fin N => blk k = j ) Finset.univ ) ⊆ Finset.Ico ( ( 4 ^ j - 1 ) / 3 ) ( ( 4 ^ j - 1 ) / 3 + 4 ^ j ) from Finset.image_subset_iff.mpr fun k hk => h_filter k <| Finset.mem_filter.mp hk |>.2 ) using 1 <;> try rfl
    rw [ Finset.card_image_of_injective _ fun a b h => by simpa [ Fin.ext_iff ] using h ];
  · norm_num

/-- The set of elements of `A` in block `j` (image of the rank-block under the increasing
enumeration). -/
def blockSet (A : Finset ℤ) (j : ℕ) : Finset ℤ :=
  (Finset.univ.filter (fun k : Fin A.card => blk (k : ℕ) = j)).image (A.orderEmbOfFin rfl)

/-- The trigonometric polynomial `f_j = ∑_{a ∈ S_j} 4^{-j} fourier a`. -/
noncomputable def fpoly (A : Finset ℤ) (j : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑ a ∈ blockSet A j, ((1 / 4 : ℂ) ^ j) * fourier a x

theorem fpoly_continuous (A : Finset ℤ) (j : ℕ) : Continuous (fpoly A j) := by
  classical
  exact continuous_finsetSum _ fun _ _ => Continuous.mul ( continuous_const ) ( by continuity )

theorem card_blockSet_le (A : Finset ℤ) (j : ℕ) : (blockSet A j).card ≤ 4 ^ j := by
  classical
  exact Finset.card_image_le.trans ( card_block_le _ _ )

theorem fpoly_norm_le (A : Finset ℤ) (j : ℕ) (x) : ‖fpoly A j x‖ ≤ 1 := by
  classical
  have h_norm : ‖fpoly A j x‖ ≤ (blockSet A j).card * (1 / 4 : ℝ) ^ j := by
    simpa [fpoly, fourier_apply] using
      norm_sum_le (blockSet A j) (fun a => ((1 / 4 : ℂ) ^ j) * fourier a x)
  exact h_norm.trans ( by have := card_blockSet_le A j; exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr this ) ( by positivity ) ) ( by norm_num [ ← mul_pow ] ) )

theorem fpoly_L2_le (A : Finset ℤ) (j : ℕ) : L2nrm (fpoly A j) ≤ (1 / 2 : ℝ) ^ j := by
  classical
  refine' Real.sqrt_le_iff.mpr ⟨ by positivity, _ ⟩;
  -- By parseval_trigpoly, the integral of the squared norm is equal to the sum of the squared norms of the coefficients.
  have h_parseval : ∫ x, ‖fpoly A j x‖ ^ 2 ∂AddCircle.haarAddCircle = ∑ a ∈ blockSet A j, ‖((1 / 4 : ℂ) ^ j)‖ ^ 2 := by
    exact parseval_trigpoly (blockSet A j) (fun _ => (1 / 4 : ℂ) ^ j)
  norm_num [ h_parseval ];
  exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( card_blockSet_le A j ) ) ( by positivity ) ) ( by norm_num [ sq, ← mul_pow ] )

theorem fpoly_coeff (A : Finset ℤ) (j : ℕ) (n : ℤ) :
    fourierCoeff (fpoly A j) n = if n ∈ blockSet A j then (1 / 4 : ℂ) ^ j else 0 := by
  classical
  unfold fourierCoeff;
  unfold fpoly; simp +decide [ Finset.mul_sum _ _ _ ] ;
  rw [ MeasureTheory.integral_finsetSum ];
  · -- Evaluate the integral $\int_{\mathbb{T}} \overline{e^{2\pi i n x}} e^{2\pi i i x} \, dx$.
    have h_integral : ∀ n i : ℤ, ∫ x : AddCircle (1 : ℝ), (starRingEnd ℂ) (fourier n x) * (fourier i x) ∂AddCircle.haarAddCircle = if n = i then 1 else 0 := by
      intro n i; split_ifs with h; simp_all +decide [] ;
      · simp +decide [ mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      · convert integral_fourier ( i - n ) using 1;
        · simp +decide [ fourier, sub_eq_add_neg ];
          ac_rfl;
        · rw [ if_neg ( sub_ne_zero_of_ne <| Ne.symm h ) ];
    simp_all +decide [ mul_assoc, mul_comm, MeasureTheory.integral_const_mul ];
  · intro i hi; exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
      rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ] ) ;

/-
An element `e k` lies in `blockSet A i` iff `i` is its block index.
-/
theorem mem_blockSet_iff (A : Finset ℤ) (k : Fin A.card) (i : ℕ) :
    (A.orderEmbOfFin rfl) k ∈ blockSet A i ↔ blk (k : ℕ) = i := by
  classical
  unfold blockSet; aesop;

/-
Elements of earlier blocks are strictly smaller.
-/
theorem blockSet_lt (A : Finset ℤ) (k : Fin A.card) {i : ℕ} (hik : i < blk (k : ℕ))
    {a : ℤ} (ha : a ∈ blockSet A i) : a < (A.orderEmbOfFin rfl) k := by
  classical
  obtain ⟨ k', hk', rfl ⟩ := Finset.mem_image.mp ha;
  contrapose! hik; simp_all +decide [ Finset.mem_filter ] ;
  exact hk'.symm ▸ blk_mono hik

/-
For a co-analytic `G`, `G - 1` has vanishing positive Fourier coefficients.
-/
theorem coAnalytic_sub_one {G : AddCircle (1 : ℝ) → ℂ} (hGc : Continuous G) (hG : CoAnalytic G)
    {p : ℤ} (hp : 0 < p) : fourierCoeff (fun x => G x - 1) p = 0 := by
  classical
  unfold fourierCoeff at *; simp_all +decide [  ] ;
  convert hG p hp using 1 ; ring;
  convert integral_add _ _ using 1;
  · rw [ MeasureTheory.integral_neg, show ( ∫ a : AddCircle 1, ( starRingEnd ℂ ) ↑ ( p • a ).toCircle ∂AddCircle.haarAddCircle ) = 0 from ?_ ] ; norm_num [ fourierCoeff ];
    convert integral_fourier ( -p ) using 1 ; norm_num [ hp.ne' ];
    lia;
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · fun_prop (disch := norm_num);
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ];
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · fun_prop (disch := norm_num);
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq, Filter.Eventually ]

/-
Vanishing of the off-diagonal coefficient contributions.
-/
theorem fpoly_mul_prodexp_sub_one_vanish (A : Finset ℤ) {h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hhc : ∀ l, Continuous (h l)) (hhT : ∀ l, TrigPolyNeg (h l)) (i m : ℕ) (k : Fin A.card)
    (hik : i < blk (k : ℕ)) :
    fourierCoeff (fun x => fpoly A i x * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) = 0 := by
  classical
  -- By additivity and `fourierCoeff.const_mul` (each summand `fun x => (1/4:ℂ)^i * (fourier a x * Gm1 x)` is integrable: continuous on the compact probability space),
  have h_fourier_sum : fourierCoeff (fun x => (fpoly A i x) * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) = ∑ a ∈ blockSet A i, (1 / 4 : ℂ) ^ i * fourierCoeff (fun x => fourier a x * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) := by
    unfold fourierCoeff;
    simp +decide [ fpoly, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, ← MeasureTheory.integral_const_mul ];
    rw [ ← MeasureTheory.integral_finsetSum ];
    · simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
    · intro a ha; apply_rules [ Continuous.integrable_of_hasCompactSupport ] ;
      · apply_rules [ Continuous.mul, Continuous.sub, continuous_const, continuous_id ];
        · fun_prop;
        · fun_prop (disch := norm_num);
        · exact prodexp_continuous hhc i m;
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  -- By the shift formula `fourierCoeff_fourier_mul` (with `Gm1` continuous), `fourierCoeff (fun x => fourier a x * Gm1 x) n = fourierCoeff Gm1 (n - a)`.
  have h_shift : ∀ a ∈ blockSet A i, fourierCoeff (fun x => fourier a x * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) = fourierCoeff (fun x => prodexp h i m x - 1) ((A.orderEmbOfFin rfl) k - a) := by
    intros a ha
    exact fourierCoeff_fourier_mul a ((A.orderEmbOfFin rfl) k);
  -- By `coAnalytic_sub_one`, `fourierCoeff Gm1 p = 0` for all `p > 0`.
  have h_coAnalytic : ∀ p : ℤ, 0 < p → fourierCoeff (fun x => prodexp h i m x - 1) p = 0 := by
    apply coAnalytic_sub_one;
    · exact prodexp_continuous hhc i m;
    · exact prodexp_coAnalytic hhT i m;
  exact h_fourier_sum.trans ( Finset.sum_eq_zero fun a ha => by rw [ h_shift a ha, h_coAnalytic _ ( sub_pos.mpr ( blockSet_lt A k hik ha ) ) ] ; ring )

/-
Sum over `A` rewritten as a sum over ranks.
-/
theorem sum_eq_sum_enum (A : Finset ℤ) (g : ℤ → ℝ) :
    ∑ n ∈ A, g n = ∑ k : Fin A.card, g ((A.orderEmbOfFin rfl) k) := by
  classical
  convert Finset.sum_image ?_;
  · exact Eq.symm (Finset.image_orderEmbOfFin_univ A rfl);
  · exact fun x _ y _ hxy => by simpa [ Fin.ext_iff ] using hxy;

/-
**Lower bound for the coefficient sum** of the constructed function.
-/
theorem construction_sum_bound (A : Finset ℤ) {h : ℕ → AddCircle (1 : ℝ) → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hBle : 4 * B ≤ 3)
    (hhc : ∀ l, Continuous (h l)) (hhT : ∀ l, TrigPolyNeg (h l))
    (hhre : ∀ l x, 0 ≤ (h l x).re) (hh2 : ∀ l, L2nrm (h l) ≤ B * (1 / 2 : ℝ) ^ l) :
    (1 - 4 * B / 3) / 15 * harmonic A.card
      ≤ ∑ n ∈ A, (fourierCoeff (Frec (1 / 5 : ℂ) (fpoly A) h (blk (A.card - 1))) n).re := by
  classical
  rw [ sum_eq_sum_enum, harmonic ];
  -- By `Finset.sum_le_sum`, it suffices to prove for each `k : Fin N`:
  suffices h_per_k : ∀ k : Fin A.card, ((1 - 4 * B / 3) / 15) * (1 / (k + 1 : ℝ)) ≤ (fourierCoeff (Frec (1 / 5) (fpoly A) h (blk (A.card - 1))) ((A.orderEmbOfFin rfl) k)).re by
    simpa only [ Finset.mul_sum _ _ _, Finset.sum_range ] using Finset.sum_le_sum fun i _ => h_per_k i;
  intro k;
  have := @re_coeff_ge ( fpoly A ) h B hB ( blk ( A.card - 1 ) );
  refine' le_trans _ ( this ( fun i => fpoly_continuous A i ) hhc hhre ( fun i => fpoly_L2_le A i ) hh2 ( show blk ( k : ℕ ) ≤ blk ( A.card - 1 ) from _ ) _ _ );
  · -- By simplifying, we can see that the inequality holds.
    have h_simp : (1 / 4 : ℝ) ^ blk (k : ℕ) ≥ 1 / (3 * (k + 1)) := by
      have := pow_blk_le k;
      rw [ one_div, inv_pow ];
      rw [ ge_iff_le, inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast at * <;> linarith [ pow_pos ( by decide : 0 < 4 ) ( blk k ) ];
    norm_num at * ; nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ) ];
  · exact blk_mono ( Nat.le_sub_one_of_lt k.2 );
  · rw [ Finset.sum_eq_single ( blk k ) ] <;> norm_num [ fpoly_coeff ];
    · exact fun h => False.elim <| h <| mem_blockSet_iff A k _ |>.2 rfl;
    · intro b hb hb'; rw [ mem_blockSet_iff ] ; aesop;
    · exact fun h => False.elim <| h.not_ge <| blk_mono <| Nat.le_sub_one_of_lt <| Fin.is_lt k;
  · exact fun i hi => fpoly_mul_prodexp_sub_one_vanish A hhc hhT i ( blk ( A.card - 1 ) ) k hi

/-
**The dual construction** (refactored with an existential absolute constant).
-/
theorem exists_good_F : ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ,
    ∃ F : AddCircle (1 : ℝ) → ℂ, Continuous F ∧ (∀ x, ‖F x‖ ≤ 1) ∧
      c * harmonic A.card ≤ ∑ n ∈ A, (fourierCoeff F n).re := by
  classical
  refine' ⟨ ( 2 - Real.sqrt 2 ) / 45, by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ], _ ⟩;
  intro A
  obtain ⟨h, hhT, hhc, hhre, hh2⟩ : ∃ h : ℕ → AddCircle (1 : ℝ) → ℂ,
    (∀ l, TrigPolyNeg (h l)) ∧
    (∀ l, Continuous (h l)) ∧
    (∀ l x, 0 ≤ (h l x).re) ∧
    (∀ l, L2nrm (h l) ≤ ((Real.sqrt 2 + 1) / 4) * (1 / 2 : ℝ) ^ l) ∧
    (∀ l x, (1 / 4 : ℝ) * ‖fpoly A l x‖ ≤ (h l x).re) := by
      have h_majorant : ∀ l, ∃ φ : AddCircle (1 : ℝ) → ℂ, TrigPolyNeg φ ∧ (∀ x, (1 / 4 : ℝ) * ‖fpoly A l x‖ ≤ (φ x).re) ∧ L2nrm φ ≤ (Real.sqrt 2 + 1) / 4 * (1 / 2 : ℝ) ^ l := by
        intro l
        set g : AddCircle (1 : ℝ) → ℝ := fun x => (1 / 4 : ℝ) * ‖fpoly A l x‖
        have hg_cont : Continuous g := by
          exact Continuous.mul continuous_const <| Continuous.norm <| fpoly_continuous A l
        have hg_nonneg : ∀ x, 0 ≤ g x := by
          exact fun x => mul_nonneg ( by norm_num ) ( norm_nonneg _ )
        have hg_L2 : L2nrm (fun x => ((g x : ℝ) : ℂ)) ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ l := by
          have hg_L2 : L2nrm (fun x => ((g x : ℝ) : ℂ)) = (1 / 4 : ℝ) * L2nrm (fpoly A l) := by
            unfold L2nrm;
            norm_num [ g, mul_pow, MeasureTheory.integral_const_mul ];
          exact hg_L2.symm ▸ mul_le_mul_of_nonneg_left ( fpoly_L2_le A l ) ( by norm_num );
        have := exists_majorant hg_cont ( show 0 < ( 1 / 4 : ℝ ) * ( 1 / 2 ) ^ l by positivity );
        exact this.imp fun φ hφ => ⟨ hφ.1, hφ.2.1, by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) l ] ⟩;
      choose φ hφ₁ hφ₂ hφ₃ using h_majorant;
      exact ⟨ φ, hφ₁, fun l => TrigPolyNeg.continuous ( hφ₁ l ), fun l x => le_trans ( by positivity ) ( hφ₂ l x ), hφ₃, hφ₂ ⟩;
  refine' ⟨ Frec ( 1 / 5 : ℂ ) ( fpoly A ) h ( blk ( A.card - 1 ) ), _, _, _ ⟩;
  · exact Frec_continuous _ ( fun l => fpoly_continuous _ _ ) hhc _;
  · apply Frec_norm_le;
    · grind +suggestions;
    · exact hh2.2;
  · convert construction_sum_bound A ( show 0 ≤ ( Real.sqrt 2 + 1 ) / 4 by positivity ) ( show 4 * ( ( Real.sqrt 2 + 1 ) / 4 ) ≤ 3 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ) hhc hhT hhre hh2.1 using 1;
    ring

end Erdos512
