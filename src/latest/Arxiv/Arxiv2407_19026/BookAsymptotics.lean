import Arxiv.Arxiv2407_19026.BookMain
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Uniform asymptotic estimates for the book induction

This file makes the “choose `L₀` sufficiently large” part of
`t:bookmain` explicit.
-/

noncomputable section

namespace Arxiv2407_19026

/-- A point strictly below a point of the closed Ramsey region already
satisfies the defining eventual Ramsey estimate. -/
lemma eventuallyRamseyBound_of_lt_mem_ramseyRegion
    {x y x' y' : ℝ} (h : (x, y) ∈ ramseyRegion)
    (hx' : 0 < x') (hxx : x' < x)
    (hy' : 0 < y') (hyy : y' < y) :
    EventuallyRamseyBound x' y' := by
  rw [ramseyRegion] at h
  let U : Set (ℝ × ℝ) := Set.Ioi x' ×ˢ Set.Ioi y'
  have hUopen : IsOpen U := isOpen_Ioi.prod isOpen_Ioi
  have hxyU : (x, y) ∈ U := ⟨hxx, hyy⟩
  obtain ⟨z, hzU, hzcore⟩ :=
    (mem_closure_iff_nhds.1 h U (hUopen.mem_nhds hxyU))
  exact eventuallyRamseyBound_mono hx'.le hzU.1.le
    hy'.le hzU.2.le hzcore.2.2.2.2

/-- The standard binomial Ramsey bound, oriented so that the smaller
second parameter appears in the exponent. -/
lemma ramseyNumber_le_add_pow {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ramseyNumber k m ≤ (k + m) ^ m := by
  have hR := Erdos1014.ramseyNumber_le_choose (k - 1) m
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at hR
  have htop :
      k - 1 + m - 1 = (k - 1) + (m - 1) := by omega
  rw [htop, Nat.choose_symm_add] at hR
  calc
    ramseyNumber k m ≤ ((k - 1) + (m - 1)).choose (m - 1) := hR
    _ ≤ ((k - 1) + (m - 1)) ^ (m - 1) :=
      Nat.choose_le_pow _ _
    _ ≤ (k + m) ^ (m - 1) := by
      exact Nat.pow_le_pow_left
        (show (k - 1) + (m - 1) ≤ k + m by omega) (m - 1)
    _ ≤ (k + m) ^ m := by
      exact Nat.pow_le_pow_right (by omega) (by omega)

/-- An explicit real upper bound for the logarithmic spine size. -/
lemma bookSpineSize_lt_log_bound {ε : ℝ} {r n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    (bookSpineSize ε r n : ℝ) <
      Real.log (bookAmplificationTarget ε r n) /
          Real.log (1 + ε) + 1 := by
  apply Nat.ceil_lt_add_one
  exact div_nonneg
    (Real.log_nonneg
      (bookAmplificationTarget_gt_one hε hε1 hn).le)
    (Real.log_nonneg (by linarith))

/-- A constant controlling the logarithmic spine size. -/
def bookSpineCoeff (ε : ℝ) (r : ℕ) : ℝ :=
  (Real.log 2 - r * Real.log ε + 2 * r) / Real.log (1 + ε) + 1

lemma bookSpineCoeff_pos {ε : ℝ} {r : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < bookSpineCoeff ε r := by
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hnum :
      0 < Real.log 2 - (r : ℝ) * Real.log ε + 2 * r := by
    have : (r : ℝ) * Real.log ε ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogε
    nlinarith
  dsimp [bookSpineCoeff]
  exact add_pos_of_pos_of_nonneg (div_pos hnum hden) zero_le_one

lemma one_lt_log_natCast {n : ℕ} (hn : 3 ≤ n) :
    1 < Real.log (n : ℝ) := by
  have hlog3 : 1 < Real.log 3 := by
    exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
      Real.log_three_gt_d9
  have h3n : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact hlog3.trans_le
    (Real.strictMonoOn_log.monotoneOn
      (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (n : ℝ) ∈ Set.Ioi 0 by exact hnR)
      h3n)

/-- The spine size is at most a constant times `log n`, uniformly for
`n ≥ 3`. -/
lemma bookSpineSize_lt_coeff_mul_log {ε : ℝ} {r n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 3 ≤ n) :
    (bookSpineSize ε r n : ℝ) <
      bookSpineCoeff ε r * Real.log n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hlogn : 1 < Real.log (n : ℝ) := one_lt_log_natCast hn
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hden : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have htargetLog :
      Real.log (bookAmplificationTarget ε r n) =
        Real.log 2 + (r : ℝ) *
          (2 * Real.log n - Real.log ε) := by
    dsimp [bookAmplificationTarget]
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_div (by positivity) hε.ne',
      Real.log_pow]
    push_cast
    ring
  have hraw := bookSpineSize_lt_log_bound
    (r := r) hε hε1 hn1
  rw [htargetLog] at hraw
  calc
    (bookSpineSize ε r n : ℝ) <
        (Real.log 2 + (r : ℝ) *
            (2 * Real.log n - Real.log ε)) /
              Real.log (1 + ε) + 1 := hraw
    _ ≤ bookSpineCoeff ε r * Real.log n := by
      dsimp [bookSpineCoeff]
      have hconst :
          0 ≤ Real.log 2 - (r : ℝ) * Real.log ε := by
        have : (r : ℝ) * Real.log ε ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogε
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have hprod :
          0 ≤ (Real.log 2 - (r : ℝ) * Real.log ε +
              Real.log (1 + ε)) *
            (Real.log n - 1) :=
        mul_nonneg (by linarith) (by linarith)
      rw [show
          (Real.log 2 + (r : ℝ) *
                (2 * Real.log n - Real.log ε)) / Real.log (1 + ε) + 1 =
            (Real.log 2 + (r : ℝ) *
                (2 * Real.log n - Real.log ε) + Real.log (1 + ε)) /
                  Real.log (1 + ε) by
              field_simp,
        show
          ((Real.log 2 - (r : ℝ) * Real.log ε + 2 * r) /
                Real.log (1 + ε) + 1) *
              Real.log n =
            ((Real.log 2 - (r : ℝ) * Real.log ε + 2 * r +
                Real.log (1 + ε)) * Real.log n) /
                  Real.log (1 + ε) by field_simp]
      apply (div_le_div_iff₀ hden hden).2
      nlinarith

/-- A constant controlling the auxiliary blue-clique parameter. -/
def bookCliqueCoeff (μ ε : ℝ) (r : ℕ) : ℝ :=
  5 * (μ + ε)⁻¹ * (bookSpineCoeff ε r) ^ 2 + 1

lemma bookCliqueCoeff_pos {μ ε : ℝ} {r : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < bookCliqueCoeff μ ε r := by
  have hC := bookSpineCoeff_pos (r := r) hε hε1
  dsimp [bookCliqueCoeff]
  positivity

/-- The auxiliary clique parameter is at most a constant times
`(log n)²`. -/
lemma bookCliqueSize_lt_coeff_mul_log_sq {μ ε : ℝ} {r n : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 3 ≤ n) :
    (bookCliqueSize μ ε r n : ℝ) <
      bookCliqueCoeff μ ε r * (Real.log n) ^ 2 := by
  have hlogn : 1 < Real.log (n : ℝ) := one_lt_log_natCast hn
  have hC : 0 < bookSpineCoeff ε r :=
    bookSpineCoeff_pos hε hε1
  have hb :
      (bookSpineSize ε r n : ℝ) <
        bookSpineCoeff ε r * Real.log n :=
    bookSpineSize_lt_coeff_mul_log hε hε1 hn
  have hb0 : 0 ≤ (bookSpineSize ε r n : ℝ) := by positivity
  have hbsq :
      (bookSpineSize ε r n : ℝ) ^ 2 <
        (bookSpineCoeff ε r) ^ 2 * (Real.log n) ^ 2 := by
    nlinarith [sq_nonneg
      (bookSpineCoeff ε r * Real.log n -
        (bookSpineSize ε r n : ℝ))]
  have hraw :
      (bookCliqueSize μ ε r n : ℝ) <
        5 * (μ + ε)⁻¹ * (bookSpineSize ε r n : ℝ) ^ 2 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  calc
    (bookCliqueSize μ ε r n : ℝ) <
        5 * (μ + ε)⁻¹ *
            (bookSpineSize ε r n : ℝ) ^ 2 + 1 := hraw
    _ < 5 * (μ + ε)⁻¹ *
            ((bookSpineCoeff ε r) ^ 2 * (Real.log n) ^ 2) + 1 := by
      gcongr
    _ ≤ bookCliqueCoeff μ ε r * (Real.log n) ^ 2 := by
      dsimp [bookCliqueCoeff]
      have hlogsq : 1 ≤ (Real.log n) ^ 2 := by nlinarith
      nlinarith [mul_nonneg
        (by positivity :
          0 ≤ 5 * (μ + ε)⁻¹ * (bookSpineCoeff ε r) ^ 2)
        (sub_nonneg.mpr hlogsq)]

/-- Any fixed multiple of `(log z)²` is eventually at most `z`. -/
lemma eventually_const_mul_log_sq_le_self {C : ℝ} (hC : 0 < C) :
    ∀ᶠ z : ℝ in Filter.atTop, C * (Real.log z) ^ 2 ≤ z := by
  have hlittle :
      (fun z : ℝ ↦ Real.log z ^ 2) =o[Filter.atTop]
        (fun z : ℝ ↦ z) :=
    Real.isLittleO_pow_log_id_atTop
  have hbound :=
    (Asymptotics.isLittleO_iff.1 hlittle (inv_pos.mpr hC))
  filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ)] with z hz hz1
  have hlog0 : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have hz0 : 0 ≤ z := zero_le_one.trans hz1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg hz0] at hz
  have hscaled := mul_le_mul_of_nonneg_left hz hC.le
  field_simp at hscaled
  simpa [mul_assoc] using hscaled

/-- Every fixed power of the logarithm is sublinear. -/
lemma eventually_const_mul_log_pow_le_self {C : ℝ} {d : ℕ}
    (hC : 0 < C) :
    ∀ᶠ z : ℝ in Filter.atTop, C * (Real.log z) ^ d ≤ z := by
  have hlittle :
      (fun z : ℝ ↦ Real.log z ^ d) =o[Filter.atTop]
        (fun z : ℝ ↦ z) :=
    Real.isLittleO_pow_log_id_atTop
  have hbound :=
    (Asymptotics.isLittleO_iff.1 hlittle (inv_pos.mpr hC))
  filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ)] with z hz hz1
  have hlog0 : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have hz0 : 0 ≤ z := zero_le_one.trans hz1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
    Real.norm_eq_abs, abs_of_nonneg hz0] at hz
  have hscaled := mul_le_mul_of_nonneg_left hz hC.le
  field_simp at hscaled
  simpa [mul_assoc] using hscaled

/-- A fixed multiple of `log³ n` is eventually below
`n log b` for every `b > 1`. -/
lemma eventually_const_mul_log_cube_le_nat_mul_log {D b : ℝ}
    (hD : 0 < D) (hb : 1 < b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      D * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) * Real.log b := by
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hevent :
      ∀ᶠ z : ℝ in Filter.atTop,
        (D / Real.log b) * (Real.log z) ^ 3 ≤ z :=
    eventually_const_mul_log_pow_le_self (div_pos hD hlogb)
  filter_upwards [hevent.natCast_atTop] with n hn
  have hscaled :=
    mul_le_mul_of_nonneg_right hn hlogb.le
  field_simp at hscaled
  nlinarith

/-- Eventually the auxiliary clique parameter is no larger than `n`. -/
lemma eventually_bookCliqueSize_le_self {μ ε : ℝ} {r : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → bookCliqueSize μ ε r n ≤ n := by
  let C := bookCliqueCoeff μ ε r
  have hC : 0 < C := bookCliqueCoeff_pos hμ hε hε1
  obtain ⟨z₀, hz₀⟩ :=
    (Filter.eventually_atTop.1 (eventually_const_mul_log_sq_le_self hC))
  let N := max 3 ⌈max z₀ 0⌉₊
  refine ⟨N, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := (le_max_left 3 _).trans hn
  have hnz : z₀ ≤ (n : ℝ) := by
    have hceil : max z₀ 0 ≤ (⌈max z₀ 0⌉₊ : ℝ) := Nat.le_ceil _
    have hNceil : ⌈max z₀ 0⌉₊ ≤ N := le_max_right _ _
    exact (le_max_left _ _).trans
      (hceil.trans (by exact_mod_cast hNceil.trans hn))
  have hlog := hz₀ (n : ℝ) hnz
  have hm := bookCliqueSize_lt_coeff_mul_log_sq
    (r := r) hμ hε hε1 hn3
  have hmR : (bookCliqueSize μ ε r n : ℝ) < n :=
    hm.trans_le (by simpa [C] using hlog)
  exact_mod_cast hmR.le

lemma bookCliqueSize_pos {μ ε : ℝ} {r n : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    0 < bookCliqueSize μ ε r n := by
  apply Nat.ceil_pos.mpr
  have hb : 0 < bookSpineSize ε r n :=
    bookSpineSize_pos hε hε1 hn
  positivity

/-- An eventual exponential estimate can be made uniform after
increasing it by one fixed multiplicative constant. -/
lemma exists_uniform_pow_bound {f : ℕ → ℝ} {b : ℝ}
    (hb : 1 < b) (hf : ∀ n, 0 ≤ f n)
    (hev : ∀ᶠ n : ℕ in Filter.atTop, f n ≤ b ^ n) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, f n ≤ M * b ^ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  let M : ℝ := 1 + ∑ i ∈ Finset.range N, f i / b ^ i
  have hb0 : 0 < b := by linarith
  have hsum0 :
      0 ≤ ∑ i ∈ Finset.range N, f i / b ^ i := by
    exact Finset.sum_nonneg fun i _ ↦ div_nonneg (hf i) (by positivity)
  have hM1 : 1 ≤ M := by
    dsimp [M]
    linarith
  refine ⟨M, zero_lt_one.trans_le hM1, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hM1 (by positivity : 0 ≤ b ^ n))
  · have hnmem : n ∈ Finset.range N := Finset.mem_range.2 (by omega)
    have hterm :
        f n / b ^ n ≤ ∑ i ∈ Finset.range N, f i / b ^ i := by
      exact Finset.single_le_sum
        (fun i hi ↦ div_nonneg (hf i) (by positivity)) hnmem
    have hratio : f n / b ^ n ≤ M := hterm.trans (by
      dsimp [M]
      linarith)
    exact (div_le_iff₀ (by positivity : 0 < b ^ n)).1 hratio

/-- A uniform bound `f n ≤ M bⁿ` can absorb its constant into a
sufficiently large additional exponent. -/
lemma uniform_pow_bound_of_eventually {f : ℕ → ℝ} {b A : ℝ}
    (hb : 1 < b) (hA : 0 < A) (hf : ∀ n, 0 ≤ f n)
    (hev : ∀ᶠ n : ℕ in Filter.atTop, f n ≤ b ^ n) :
    ∃ L : ℕ, ∀ n l : ℕ, L ≤ l → f n ≤ A * b ^ (n + l) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_pow_bound hb hf hev
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt hb).eventually
      (Filter.eventually_ge_atTop (M / A)))
  refine ⟨L, ?_⟩
  intro n l hl
  have hpow : M / A ≤ b ^ l := hL l hl
  have hMA : M ≤ A * b ^ l := by
    simpa [mul_comm] using (div_le_iff₀ hA).1 hpow
  calc
    f n ≤ M * b ^ n := hbound n
    _ ≤ (A * b ^ l) * b ^ n := by gcongr
    _ = A * b ^ (n + l) := by rw [pow_add]; ring

/-- A fixed multiple of a polynomial is eventually bounded by any
exponential with base greater than one. -/
lemma eventually_const_mul_nat_pow_le_pow {C b : ℝ} {d : ℕ}
    (hC : 0 < C) (hb : 1 < b) :
    ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ d ≤ b ^ n := by
  have hlittle :
      (fun n : ℕ ↦ (n : ℝ) ^ d) =o[Filter.atTop]
        (fun n ↦ b ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt d hb
  have hbound :=
    (Asymptotics.isLittleO_iff.1 hlittle (inv_pos.mpr hC))
  filter_upwards [hbound] with n hn
  have hnpow : 0 ≤ (n : ℝ) ^ d := by positivity
  have hbpow : 0 ≤ b ^ n := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnpow,
    Real.norm_eq_abs, abs_of_nonneg hbpow] at hn
  have hscaled := mul_le_mul_of_nonneg_left hn hC.le
  field_simp at hscaled
  simpa [mul_assoc] using hscaled

/-- The polynomial factor in `e:moment0` is uniformly absorbed by the
additional `l` exponent. -/
lemma exists_initial_domination {ε : ℝ} {r : ℕ}
    (hε : 0 < ε) :
    ∃ L : ℕ, ∀ n l : ℕ, 2 ≤ n → L ≤ l →
      1 ≤ (ε / (n : ℝ)) ^ r * (1 + ε) ^ (n + l) := by
  let f : ℕ → ℝ := fun n ↦ (ε⁻¹) ^ r * (n : ℝ) ^ r
  have hb : 1 < 1 + ε := by linarith
  have hC : 0 < (ε⁻¹) ^ r := by positivity
  have hf : ∀ n, 0 ≤ f n := fun n ↦ by
    dsimp [f]
    positivity
  obtain ⟨L, hL⟩ := uniform_pow_bound_of_eventually
    (f := f) (b := 1 + ε) (A := 1) hb zero_lt_one hf
    (eventually_const_mul_nat_pow_le_pow hC hb)
  refine ⟨L, ?_⟩
  intro n l hn hl
  have hn0 : (0 : ℝ) < n := by positivity
  have hbound := hL n l hl
  dsimp [f] at hbound
  have hεn : 0 < ε / (n : ℝ) := div_pos hε hn0
  calc
    1 = (ε / (n : ℝ)) ^ r *
        ((ε⁻¹) ^ r * (n : ℝ) ^ r) := by
      have hbase :
          ε / (n : ℝ) * ε⁻¹ * (n : ℝ) = 1 := by
        field_simp [hε.ne', ne_of_gt hn0]
      symm
      calc
        (ε / (n : ℝ)) ^ r *
            ((ε⁻¹) ^ r * (n : ℝ) ^ r) =
            (ε / (n : ℝ) * ε⁻¹ * (n : ℝ)) ^ r := by
              rw [mul_pow, mul_pow]
              ring
        _ = 1 := by rw [hbase, one_pow]
    _ ≤ (ε / (n : ℝ)) ^ r * (1 + ε) ^ (n + l) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using hbound)
        (pow_nonneg hεn.le _)

/-- The logarithmic blue-book size is uniformly absorbed by the
exponential lower bound for `|X|`. -/
lemma exists_book_size_bound {μ ε : ℝ} {r : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ L : ℕ, ∀ n l : ℕ, 4 ≤ n → L ≤ l →
      5 * (bookCliqueSize μ ε r n : ℝ) ^ 2 ≤
        (1 + ε) ^ (n + l) := by
  have hb : 1 < 1 + ε := by linarith
  obtain ⟨N, hN⟩ :=
    eventually_bookCliqueSize_le_self (r := r) hμ hε hε1
  have hpoly :
      ∀ᶠ n : ℕ in Filter.atTop,
        5 * (n : ℝ) ^ 2 ≤ (1 + ε) ^ n :=
    eventually_const_mul_nat_pow_le_pow (by norm_num) hb
  have hm :
      ∀ᶠ n : ℕ in Filter.atTop,
        5 * (bookCliqueSize μ ε r n : ℝ) ^ 2 ≤
          (1 + ε) ^ n := by
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩, hpoly] with n hn hp
    have hmcast : (bookCliqueSize μ ε r n : ℝ) ≤ n := by
      exact_mod_cast hn
    calc
      5 * (bookCliqueSize μ ε r n : ℝ) ^ 2 ≤
          5 * (n : ℝ) ^ 2 := by gcongr
      _ ≤ (1 + ε) ^ n := hp
  obtain ⟨L, hL⟩ := uniform_pow_bound_of_eventually
    (f := fun n ↦ 5 * (bookCliqueSize μ ε r n : ℝ) ^ 2)
    (b := 1 + ε) (A := 1) hb zero_lt_one
    (fun n ↦ by positivity) hm
  refine ⟨L, ?_⟩
  intro n l _ hl
  simpa using hL n l hl

/-- The terminal error term is uniformly absorbed by the exponential
lower bound for `|X|`. -/
lemma exists_terminal_error_bound {p ε : ℝ} {r : ℕ}
    (hε : 0 < ε) (hεp : ε < p) :
    ∃ L : ℕ, ∀ n l : ℕ, 4 ≤ n → L ≤ l →
      (p - ε) ^ ((r : ℝ)⁻¹) * (n : ℝ) ^ 2 /
          (ε * (1 + ε) ^ (n + l)) ≤ ε := by
  have hb : 1 < 1 + ε := by linarith
  have hq : 0 < p - ε := sub_pos.mpr hεp
  let C := (p - ε) ^ ((r : ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos hq _
  have hf : ∀ n : ℕ, 0 ≤ C * (n : ℝ) ^ 2 :=
    fun n ↦ by positivity
  obtain ⟨L, hL⟩ := uniform_pow_bound_of_eventually
    (f := fun n ↦ C * (n : ℝ) ^ 2)
    (b := 1 + ε) (A := ε ^ 2) hb (sq_pos_of_pos hε) hf
    (eventually_const_mul_nat_pow_le_pow hC hb)
  refine ⟨L, ?_⟩
  intro n l _ hl
  have hbound := hL n l hl
  have hden : 0 < ε * (1 + ε) ^ (n + l) := by positivity
  apply (div_le_iff₀ hden).2
  dsimp [C] at hbound
  nlinarith

/-- The Ramsey number occurring in the exceptional set is
subexponential in `n = k + t`, uniformly for `k ≤ n`. -/
lemma eventually_exceptional_envelope {μ ε : ℝ} {r : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 3 *
          ((n + bookCliqueSize μ ε r n : ℕ) : ℝ) ^
            bookCliqueSize μ ε r n ≤
        (1 + ε) ^ n ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
        (n : ℝ) ^ 3 *
            (ramseyNumber k (bookCliqueSize μ ε r n) : ℝ) ≤
          (1 + ε) ^ n := by
  let C := bookCliqueCoeff μ ε r
  let D := 2 * C + 3
  have hC : 0 < C := bookCliqueCoeff_pos hμ hε hε1
  have hD : 0 < D := by dsimp [D]; linarith
  have hb : 1 < 1 + ε := by linarith
  obtain ⟨N, hN⟩ :=
    eventually_bookCliqueSize_le_self (r := r) hμ hε hε1
  have hcube :
      ∀ᶠ n : ℕ in Filter.atTop,
        D * (Real.log (n : ℝ)) ^ 3 ≤
          (n : ℝ) * Real.log (1 + ε) :=
    eventually_const_mul_log_cube_le_nat_mul_log hD hb
  filter_upwards [Filter.eventually_ge_atTop (max N 3), hcube]
    with n hn hcubeN
  let m := bookCliqueSize μ ε r n
  have hnN : N ≤ n := (le_max_left N 3).trans hn
  have hn3 : 3 ≤ n := (le_max_right N 3).trans hn
  have hn1 : 1 ≤ n := by omega
  have hmN : m ≤ n := hN n hnN
  have hm1 : 1 ≤ m := bookCliqueSize_pos hμ hε hε1 hn1
  have hnR : (0 : ℝ) < n := by positivity
  have hbase : 0 < 2 * (n : ℝ) := by positivity
  have hlogn : 1 < Real.log (n : ℝ) :=
    one_lt_log_natCast hn3
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := hlogn.le.trans' zero_le_one
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogbase0 : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by nlinarith [hnR1])
  have hbaseSq : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith
  have hlogbase :
      Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log (2 * (n : ℝ)) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.strictMonoOn_log.monotoneOn
          (show 2 * (n : ℝ) ∈ Set.Ioi 0 by exact hbase)
          (show (n : ℝ) ^ 2 ∈ Set.Ioi 0 by
            exact sq_pos_of_pos hnR)
          hbaseSq
      _ = 2 * Real.log (n : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hmC :
      (m : ℝ) ≤ C * (Real.log (n : ℝ)) ^ 2 :=
    (bookCliqueSize_lt_coeff_mul_log_sq
      (r := r) hμ hε hε1 hn3).le
  have hmLog :
      (m : ℝ) * Real.log (2 * (n : ℝ)) ≤
        2 * C * (Real.log (n : ℝ)) ^ 3 := by
    calc
      (m : ℝ) * Real.log (2 * (n : ℝ)) ≤
          (C * (Real.log (n : ℝ)) ^ 2) *
            Real.log (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hmC hlogbase0
      _ ≤ (C * (Real.log (n : ℝ)) ^ 2) *
            (2 * Real.log (n : ℝ)) := by
        gcongr
      _ = 2 * C * (Real.log (n : ℝ)) ^ 3 := by ring
  have hlogCube :
      Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
    nlinarith [sq_nonneg (Real.log (n : ℝ)),
      mul_nonneg hlogn0
        (mul_nonneg (sub_nonneg.mpr hlogn.le)
          (add_nonneg hlogn0 zero_le_one))]
  have hexponent :
      3 * Real.log (n : ℝ) +
          (m : ℝ) * Real.log (2 * (n : ℝ)) ≤
        D * (Real.log (n : ℝ)) ^ 3 := by
    dsimp [D]
    nlinarith
  have hnExp :
      (n : ℝ) ^ 3 =
        Real.exp (3 * Real.log (n : ℝ)) := by
    calc
      (n : ℝ) ^ 3 =
          (Real.exp (Real.log (n : ℝ))) ^ 3 := by
            rw [Real.exp_log hnR]
      _ = Real.exp ((3 : ℕ) * Real.log (n : ℝ)) :=
        (Real.exp_nat_mul _ 3).symm
      _ = Real.exp (3 * Real.log (n : ℝ)) := by norm_num
  have hmExp :
      (2 * (n : ℝ)) ^ m =
        Real.exp ((m : ℝ) * Real.log (2 * (n : ℝ))) := by
    calc
      (2 * (n : ℝ)) ^ m =
          (Real.exp (Real.log (2 * (n : ℝ)))) ^ m := by
            rw [Real.exp_log hbase]
      _ = Real.exp ((m : ℝ) * Real.log (2 * (n : ℝ))) :=
        (Real.exp_nat_mul _ m).symm
  have henvelope :
      (n : ℝ) ^ 3 * (2 * (n : ℝ)) ^ m ≤
        (1 + ε) ^ n := by
    calc
      (n : ℝ) ^ 3 * (2 * (n : ℝ)) ^ m =
          Real.exp (3 * Real.log (n : ℝ) +
            (m : ℝ) * Real.log (2 * (n : ℝ))) := by
              rw [hnExp, hmExp, Real.exp_add]
      _ ≤ Real.exp (D * (Real.log (n : ℝ)) ^ 3) := by
        exact Real.exp_le_exp.mpr hexponent
      _ ≤ Real.exp ((n : ℝ) * Real.log (1 + ε)) := by
        exact Real.exp_le_exp.mpr hcubeN
      _ = (1 + ε) ^ n := by
        calc
          Real.exp ((n : ℝ) * Real.log (1 + ε)) =
              (Real.exp (Real.log (1 + ε))) ^ n :=
            Real.exp_nat_mul _ n
          _ = (1 + ε) ^ n := by
            rw [Real.exp_log (by positivity)]
  have hsumCast : ((n + m : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + m ≤ 2 * n by omega)
  refine ⟨?_, ?_⟩
  · calc
      (n : ℝ) ^ 3 * ((n + m : ℕ) : ℝ) ^ m ≤
          (n : ℝ) ^ 3 * (2 * (n : ℝ)) ^ m := by
        gcongr
      _ ≤ (1 + ε) ^ n := henvelope
  intro k hk hkn
  have hRnat : ramseyNumber k m ≤ (k + m) ^ m :=
    ramseyNumber_le_add_pow hk hm1
  have hsum : k + m ≤ 2 * n := by omega
  have hRcast :
      (ramseyNumber k m : ℝ) ≤ (2 * (n : ℝ)) ^ m := by
    calc
      (ramseyNumber k m : ℝ) ≤ ((k + m) ^ m : ℕ) := by
        exact_mod_cast hRnat
      _ ≤ ((2 * n) ^ m : ℕ) := by
        exact_mod_cast Nat.pow_le_pow_left hsum m
      _ = (2 * (n : ℝ)) ^ m := by norm_num
  exact (mul_le_mul_of_nonneg_left hRcast (by positivity)).trans henvelope

lemma ramseyNumber_zero_left (m : ℕ) : ramseyNumber 0 m = 0 := by
  apply le_antisymm
  · apply Erdos1014.ramseyNumber_le_of_property
    intro G hbad
    have hnil : G.IsNClique 0 (∅ : Finset (Fin 0)) := by
      simp [SimpleGraph.isNClique_iff]
    exact hbad.1 _ hnil
  · exact Nat.zero_le _

/-- The exceptional Ramsey set is uniformly absorbed by the extra
`l` exponent in `e:x2`. -/
lemma exists_exceptional_size_bound {μ p ε : ℝ} {r : ℕ}
    (hμ : 0 < μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεp : ε < p) :
    ∃ L : ℕ, ∀ n l k : ℕ, 4 ≤ n → L ≤ l → k ≤ n →
      (ramseyNumber k (bookCliqueSize μ ε r n) : ℝ) ≤
        ε * (p - ε) / (n : ℝ) ^ 3 * (1 + ε) ^ (n + l) := by
  let f : ℕ → ℝ := fun n ↦
    (n : ℝ) ^ 3 *
      ((n + bookCliqueSize μ ε r n : ℕ) : ℝ) ^
        bookCliqueSize μ ε r n
  have hb : 1 < 1 + ε := by linarith
  have hA : 0 < ε * (p - ε) :=
    mul_pos hε (sub_pos.mpr hεp)
  have hf : ∀ n, 0 ≤ f n := fun n ↦ by
    dsimp [f]
    positivity
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop, f n ≤ (1 + ε) ^ n :=
    (eventually_exceptional_envelope
      (r := r) hμ hε hε1).mono fun n hn ↦ by
        simpa [f] using hn.1
  obtain ⟨L, hL⟩ := uniform_pow_bound_of_eventually
    (f := f) (b := 1 + ε) (A := ε * (p - ε))
    hb hA hf hev
  refine ⟨L, ?_⟩
  intro n l k hn4 hl hkn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  by_cases hk0 : k = 0
  · subst k
    rw [ramseyNumber_zero_left]
    have hn3nonneg : 0 ≤ (n : ℝ) ^ 3 := by positivity
    have hpowNonneg : 0 ≤ (1 + ε) ^ (n + l) := by positivity
    simpa using
      (mul_nonneg
        (div_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hεp.le))
          hn3nonneg)
        hpowNonneg)
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  let m := bookCliqueSize μ ε r n
  have hm1 : 1 ≤ m := bookCliqueSize_pos hμ hε hε1 hn1
  have hRnat : ramseyNumber k m ≤ (k + m) ^ m :=
    ramseyNumber_le_add_pow hk1 hm1
  have hRcast :
      (ramseyNumber k m : ℝ) ≤ ((n + m : ℕ) : ℝ) ^ m := by
    calc
      (ramseyNumber k m : ℝ) ≤ ((k + m) ^ m : ℕ) := by
        exact_mod_cast hRnat
      _ ≤ ((n + m) ^ m : ℕ) := by
        exact_mod_cast Nat.pow_le_pow_left
          (show k + m ≤ n + m by omega) m
      _ = ((n + m : ℕ) : ℝ) ^ m := by norm_num
  have hbound := hL n l hl
  have hpow3 : 0 < (n : ℝ) ^ 3 := by positivity
  have henvelope :
      ((n + m : ℕ) : ℝ) ^ m ≤
        ε * (p - ε) / (n : ℝ) ^ 3 *
          (1 + ε) ^ (n + l) := by
    calc
      ((n + m : ℕ) : ℝ) ^ m ≤
          (ε * (p - ε) * (1 + ε) ^ (n + l)) /
            (n : ℝ) ^ 3 := by
        apply (le_div_iff₀ hpow3).2
        simpa [f, m, mul_assoc, mul_left_comm, mul_comm] using hbound
      _ = ε * (p - ε) / (n : ℝ) ^ 3 *
            (1 + ε) ^ (n + l) := by
        field_simp
  simpa [m] using hRcast.trans henvelope

/-- All four occurrences of “take `L₀` sufficiently large” in the
book induction can be satisfied simultaneously. -/
theorem exists_bookInductionBounds
    {x y μ p ε : ℝ} {r : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hεp : ε < p) (h2εp : 2 * ε ≤ p)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hμscale : (1 + ε) * μ ≤ 1)
    (hμε1 : μ + ε < 1)
    (hcritical : μ + ε ≤ μ / (μ + x))
    (hterminalBase :
      0 < (p - ε) ^ ((r : ℝ)⁻¹) - μ - 2 * ε)
    (hterminal :
      x ≤ ((p - ε) ^ ((r : ℝ)⁻¹) - μ - 2 * ε) ^
          (r : ℝ) * (1 - μ) ^ (1 - (r : ℝ)))
    (hRamsey : EventuallyRamseyBound (x + ε) (y + ε)) :
    ∃ L₀ : ℕ, BookInductionBounds x y μ p ε r L₀ := by
  obtain ⟨Li, hLi⟩ := exists_initial_domination (r := r) hε
  obtain ⟨Lb, hLb⟩ :=
    exists_book_size_bound (r := r) hμ hε hε1
  obtain ⟨Le, hLe⟩ :=
    exists_exceptional_size_bound (r := r) hμ hε hε1 hεp
  obtain ⟨Lt, hLt⟩ :=
    exists_terminal_error_bound (r := r) hε hεp
  let L₀ := hRamsey.choose + Li + Lb + Le + Lt
  refine ⟨L₀, {
    eps_le_one := hε1
    eps_lt_p := hεp
    two_eps_le_p := h2εp
    x_le_one := hx1
    y_le_one := hy1
    mu_scale := hμscale
    mu_eps_lt_one := hμε1
    critical := hcritical
    terminal_base := hterminalBase
    terminal_parameter := hterminal
    ramsey := hRamsey
    ramsey_start := by dsimp [L₀]; omega
    initial_domination := ?_
    book_size := ?_
    exceptional_size := ?_
    terminal_error := ?_
  }⟩
  · intro n l hn hl
    exact hLi n l hn (by dsimp [L₀] at hl ⊢; omega)
  · intro n l hn hl
    exact hLb n l hn (by dsimp [L₀] at hl ⊢; omega)
  · intro n l k hn hl hk
    exact hLe n l k hn (by dsimp [L₀] at hl ⊢; omega) hk
  · intro n l hn hl
    exact hLt n l hn (by dsimp [L₀] at hl ⊢; omega)

/-- A concrete choice of the perturbation and the moment exponent used
in the proof of `t:bookmain`. -/
structure BookParameterChoice
    (x₀ y₀ μ₀ p : ℝ) where
  ε : ℝ
  r : ℕ
  eps_pos : 0 < ε
  eps_le_one : ε ≤ 1
  eps_lt_p : ε < p
  two_eps_le_p : 2 * ε ≤ p
  r_two : 2 ≤ r
  x_le_one : x₀ + ε ≤ 1
  y_le_one : y₀ + ε ≤ 1
  mu_scale : (1 + ε) * (μ₀ + ε) ≤ 1
  mu_eps_lt_one : μ₀ + 2 * ε < 1
  critical :
    μ₀ + 2 * ε ≤ (μ₀ + ε) / (μ₀ + x₀ + 2 * ε)
  terminal_base :
    0 < (p - ε) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * ε
  terminal_parameter :
    x₀ + ε ≤
      ((p - ε) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * ε) ^ (r : ℝ) *
        (1 - μ₀ - ε) ^ (1 - (r : ℝ))
  ramsey :
    EventuallyRamseyBound (x₀ + 2 * ε) (y₀ + 2 * ε)
  x_scale : x₀ ≤ (x₀ + ε) / (1 + ε)
  y_scale : y₀ ≤ (y₀ + ε) / (1 + ε)
  mu_scale_initial : μ₀ ≤ (μ₀ + ε) / (1 + ε)

/-- Strict room in the limiting inequality and in `𝓡_*` supplies all
parameters required by the book induction. -/
theorem exists_bookParameterChoice
    {x₀ y₀ μ₀ p : ℝ}
    (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1)
    (hy₀ : 0 < y₀) (hy₀1 : y₀ < 1)
    (hμ₀ : 0 < μ₀) (hμ₀1 : μ₀ < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hlimit :
      x₀ < p ^ ((1 : ℝ) / (1 - μ₀)) * (1 - μ₀))
    (hregion : (x₀, y₀) ∈ ramseyRegionInterior) :
    Nonempty (BookParameterChoice x₀ y₀ μ₀ p) := by
  have honeμ : 0 < 1 - μ₀ := sub_pos.mpr hμ₀1
  have hexponent : 0 < (1 : ℝ) / (1 - μ₀) :=
    div_pos zero_lt_one honeμ
  have hpPow : p ^ ((1 : ℝ) / (1 - μ₀)) < 1 :=
    Real.rpow_lt_one hp.le hp1 hexponent
  have hsum : x₀ + μ₀ < 1 := by
    have hprod :
        p ^ ((1 : ℝ) / (1 - μ₀)) * (1 - μ₀) <
          1 - μ₀ := by
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right hpPow honeμ
    linarith
  have hroot :
      Filter.Tendsto (fun z : ℝ ↦ p ^ z⁻¹)
        Filter.atTop (nhds 1) := by
    have hinv :
        Filter.Tendsto (fun z : ℝ ↦ z⁻¹)
          Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left
    have h :=
      (Real.continuousAt_const_rpow hp.ne').tendsto.comp hinv
    change Filter.Tendsto (fun z : ℝ ↦ p ^ z⁻¹)
      Filter.atTop (nhds (p ^ (0 : ℝ))) at h
    simpa only [Real.rpow_zero] using h
  have hrEvent :
      ∀ᶠ z : ℝ in Filter.atTop,
        x₀ <
            (p ^ z⁻¹ - μ₀) ^ z *
              (1 - μ₀) ^ (1 - z) ∧
          μ₀ < p ^ z⁻¹ := by
    filter_upwards [
      (book_limit hp hμ₀1).eventually (Ioi_mem_nhds hlimit),
      hroot.eventually (Ioi_mem_nhds hμ₀1)] with z hz hzr
    exact ⟨hz, hzr⟩
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hrEvent
  obtain ⟨r, hr⟩ := exists_nat_ge (max a 2)
  have har : a ≤ (r : ℝ) :=
    (le_max_left a 2).trans hr
  have hr2R : (2 : ℝ) ≤ r :=
    (le_max_right a 2).trans hr
  have hr2 : 2 ≤ r := by exact_mod_cast hr2R
  have hrFacts := ha (r : ℝ) har
  have hfixed :
      x₀ <
        (p ^ ((r : ℝ)⁻¹) - μ₀) ^ (r : ℝ) *
          (1 - μ₀) ^ (1 - (r : ℝ)) := by
    simpa using hrFacts.1
  have hbase0 : 0 < p ^ ((r : ℝ)⁻¹) - μ₀ := by
    linarith [hrFacts.2]
  let base : ℝ → ℝ := fun e ↦
    (p - e) ^ ((r : ℝ)⁻¹) - μ₀ - 3 * e
  let target : ℝ → ℝ := fun e ↦
    base e ^ (r : ℝ) *
      (1 - μ₀ - e) ^ (1 - (r : ℝ))
  have hsnonneg : 0 ≤ ((r : ℝ)⁻¹) := by positivity
  have hbaseCont : ContinuousAt base 0 := by
    dsimp [base]
    exact (((continuousAt_const.sub continuousAt_id).rpow_const
      (.inr hsnonneg)).sub continuousAt_const).sub
        (continuousAt_const.mul continuousAt_id)
  have htargetCont : ContinuousAt target 0 := by
    dsimp [target]
    apply ContinuousAt.mul
    · exact hbaseCont.rpow_const (.inr (by positivity))
    · exact ((continuousAt_const.sub continuousAt_const).sub
          continuousAt_id).rpow_const
        (.inl (by simpa using ne_of_gt honeμ))
  have htarget0 : x₀ < target 0 := by
    simpa [target, base] using hfixed
  have hbaseAt0 : 0 < base 0 := by
    simpa [base] using hbase0
  have hshiftCont :
      ContinuousAt
        (fun e : ℝ ↦ (x₀ + 3 * e, y₀ + 3 * e)) 0 := by
    fun_prop
  have hregionEvent :
      ∀ᶠ e : ℝ in nhds 0,
        (x₀ + 3 * e, y₀ + 3 * e) ∈
          ramseyRegionInterior := by
    have hopen : IsOpen ramseyRegionInterior := by
      exact isOpen_interior
    have hnhds :
        ramseyRegionInterior ∈
          nhds (x₀ + 3 * (0 : ℝ), y₀ + 3 * (0 : ℝ)) := by
      simpa only [mul_zero, add_zero] using hopen.mem_nhds hregion
    exact hshiftCont.eventually hnhds
  have hall :
      ∀ᶠ e : ℝ in nhds 0,
        e < 1 ∧
        2 * e < p ∧
        x₀ + e < 1 ∧
        y₀ + e < 1 ∧
        (1 + e) * (μ₀ + e) < 1 ∧
        μ₀ + 2 * e < 1 ∧
        (μ₀ + 2 * e) * (μ₀ + x₀ + 2 * e) < μ₀ + e ∧
        0 < base e ∧
        x₀ + e < target e ∧
        (x₀ + 3 * e, y₀ + 3 * e) ∈
          ramseyRegionInterior := by
    have he1 :
        ∀ᶠ e : ℝ in nhds 0, e < 1 :=
      continuousAt_id.eventually_lt continuousAt_const (by norm_num)
    have h2ep :
        ∀ᶠ e : ℝ in nhds 0, 2 * e < p :=
      (continuousAt_const.mul continuousAt_id).eventually_lt
        continuousAt_const (by simpa using hp)
    have hx1e :
        ∀ᶠ e : ℝ in nhds 0, x₀ + e < 1 :=
      (continuousAt_const.add continuousAt_id).eventually_lt
        continuousAt_const (by simpa using hx₀1)
    have hy1e :
        ∀ᶠ e : ℝ in nhds 0, y₀ + e < 1 :=
      (continuousAt_const.add continuousAt_id).eventually_lt
        continuousAt_const (by simpa using hy₀1)
    have hμscale :
        ∀ᶠ e : ℝ in nhds 0,
          (1 + e) * (μ₀ + e) < 1 :=
      ((continuousAt_const.add continuousAt_id).mul
        (continuousAt_const.add continuousAt_id)).eventually_lt
          continuousAt_const (by simpa using hμ₀1)
    have hμeps :
        ∀ᶠ e : ℝ in nhds 0, μ₀ + 2 * e < 1 :=
      (continuousAt_const.add
        (continuousAt_const.mul continuousAt_id)).eventually_lt
          continuousAt_const (by simpa using hμ₀1)
    have hcrit0 : μ₀ * (μ₀ + x₀) < μ₀ := by
      nlinarith [mul_pos hμ₀ (sub_pos.mpr hsum)]
    have hcrit :
        ∀ᶠ e : ℝ in nhds 0,
          (μ₀ + 2 * e) * (μ₀ + x₀ + 2 * e) < μ₀ + e :=
      ((continuousAt_const.add
          (continuousAt_const.mul continuousAt_id)).mul
        ((continuousAt_const.add continuousAt_const).add
          (continuousAt_const.mul continuousAt_id))).eventually_lt
        (continuousAt_const.add continuousAt_id)
        (by simpa using hcrit0)
    have hbasePos :
        ∀ᶠ e : ℝ in nhds 0, 0 < base e :=
      continuousAt_const.eventually_lt hbaseCont
        (by simpa using hbaseAt0)
    have htarget :
        ∀ᶠ e : ℝ in nhds 0, x₀ + e < target e :=
      (continuousAt_const.add continuousAt_id).eventually_lt
        htargetCont (by simpa using htarget0)
    filter_upwards [he1, h2ep, hx1e, hy1e, hμscale, hμeps,
      hcrit, hbasePos, htarget, hregionEvent] with
      e he1 h2ep hx1e hy1e hμscale hμeps hcrit hbasePos
        htarget hreg
    exact ⟨he1, h2ep, hx1e, hy1e, hμscale, hμeps,
      hcrit, hbasePos, htarget, hreg⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hall
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [ε]
    rw [abs_of_pos (by linarith)]
    linarith
  have H := hball hεball
  have hden : 0 < μ₀ + x₀ + 2 * ε := by positivity
  have hcritical :
      μ₀ + 2 * ε ≤ (μ₀ + ε) / (μ₀ + x₀ + 2 * ε) := by
    apply (le_div_iff₀ hden).2
    exact H.2.2.2.2.2.2.1.le
  have hRamsey :
      EventuallyRamseyBound (x₀ + 2 * ε) (y₀ + 2 * ε) := by
    exact eventuallyRamseyBound_of_lt_mem_ramseyRegion
      (interior_subset H.2.2.2.2.2.2.2.2.2)
      (by positivity) (by linarith)
      (by positivity) (by linarith)
  have hscale (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
      z ≤ (z + ε) / (1 + ε) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + ε)).2
    nlinarith
  refine ⟨{
    ε := ε
    r := r
    eps_pos := hε
    eps_le_one := H.1.le
    eps_lt_p := by linarith [H.2.1]
    two_eps_le_p := H.2.1.le
    r_two := hr2
    x_le_one := H.2.2.1.le
    y_le_one := H.2.2.2.1.le
    mu_scale := H.2.2.2.2.1.le
    mu_eps_lt_one := H.2.2.2.2.2.1
    critical := hcritical
    terminal_base := H.2.2.2.2.2.2.2.1
    terminal_parameter := H.2.2.2.2.2.2.2.2.1.le
    ramsey := hRamsey
    x_scale := hscale x₀ hx₀ hx₀1
    y_scale := hscale y₀ hy₀ hy₀1
    mu_scale_initial := hscale μ₀ hμ₀ hμ₀1
  }⟩

/-- Lemma `t:bookmain`: the optimized book induction, including the
parameter choice and every uniform large-`l` estimate. -/
theorem candidate_good_bookMain
    {x₀ y₀ μ₀ p : ℝ}
    (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1)
    (hy₀ : 0 < y₀) (hy₀1 : y₀ < 1)
    (hμ₀ : 0 < μ₀) (hμ₀1 : μ₀ < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hlimit :
      x₀ < p ^ ((1 : ℝ) / (1 - μ₀)) * (1 - μ₀))
    (hregion : (x₀, y₀) ∈ ramseyRegionInterior) :
    ∃ L₀ : ℕ,
      ∀ (V : Type*) (G : SimpleGraph V) (k l t : ℕ)
        (C : Candidate G),
        1 ≤ k → 1 ≤ l → 1 ≤ t → L₀ ≤ l →
        p ≤ C.density →
        bookWeight x₀ y₀ μ₀ k l t ≤
          (C.X.card : ℝ) * C.Y.card →
        C.Good k l t := by
  let ⟨P⟩ := exists_bookParameterChoice
    hx₀ hx₀1 hy₀ hy₀1 hμ₀ hμ₀1 hp hp1 hlimit hregion
  let x := x₀ + P.ε
  let y := y₀ + P.ε
  let μ := μ₀ + P.ε
  have hx : 0 < x := by dsimp [x]; linarith [hx₀, P.eps_pos]
  have hy : 0 < y := by dsimp [y]; linarith [hy₀, P.eps_pos]
  have hμ : 0 < μ := by dsimp [μ]; linarith [hμ₀, P.eps_pos]
  have hcritical : μ + P.ε ≤ μ / (μ + x) := by
    dsimp [μ, x]
    convert P.critical using 1 <;> ring
  have hterminalBase :
      0 < (p - P.ε) ^ ((P.r : ℝ)⁻¹) - μ - 2 * P.ε := by
    dsimp [μ]
    convert P.terminal_base using 1 <;> ring
  have hterminal :
      x ≤
        ((p - P.ε) ^ ((P.r : ℝ)⁻¹) - μ - 2 * P.ε) ^
            (P.r : ℝ) *
          (1 - μ) ^ (1 - (P.r : ℝ)) := by
    dsimp [x, μ]
    convert P.terminal_parameter using 1 <;> ring
  have hRamsey :
      EventuallyRamseyBound (x + P.ε) (y + P.ε) := by
    dsimp [x, y]
    convert P.ramsey using 1 <;> ring
  obtain ⟨L₀, B⟩ := exists_bookInductionBounds
    hx hy hμ P.eps_pos P.eps_le_one P.eps_lt_p
    P.two_eps_le_p P.x_le_one P.y_le_one
    (by simpa [μ] using P.mu_scale)
    (by
      dsimp [μ]
      convert P.mu_eps_lt_one using 1 <;> ring)
    hcritical hterminalBase hterminal hRamsey
  refine ⟨L₀, ?_⟩
  intro V G k l t C hk hl ht hl₀ hdensity hsize
  exact candidate_good_of_bookBounds
    x₀ y₀ μ₀ x y μ p P.ε P.r L₀
    hx₀ hy₀ hμ₀ hx hy hμ P.eps_pos P.r_two B
    (by simpa [x] using P.x_scale)
    (by simpa [y] using P.y_scale)
    (by simpa [μ] using P.mu_scale_initial)
    hk hl ht hl₀ C hdensity hsize

end Arxiv2407_19026
