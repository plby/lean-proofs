import ErdosProblems.Erdos394.GeometricSpecialization
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Square-root geometric parameters and their asymptotic inequalities
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- Natural square root tends to infinity. -/
theorem tendsto_natSqrt_atTop :
    Tendsto Nat.sqrt atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

/-- Iterated natural square root also tends to infinity. -/
theorem tendsto_natSqrt_natSqrt_atTop :
    Tendsto (fun n : ℕ ↦ n.sqrt.sqrt) atTop atTop :=
  tendsto_natSqrt_atTop.comp tendsto_natSqrt_atTop

/-- Elementary bound `n≤2^n`. -/
theorem self_le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ]
      have ih := self_le_two_pow n
      have h_one : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega

/-- The fourth power of `n` is at most `16^n`. -/
theorem pow_four_le_sixteen_pow (n : ℕ) : n ^ 4 ≤ 16 ^ n := by
  have h := Nat.pow_le_pow_left (self_le_two_pow n) 4
  calc
    n ^ 4 ≤ (2 ^ n) ^ 4 := h
    _ = 2 ^ (n * 4) := by rw [pow_mul]
    _ = 2 ^ (4 * n) := by rw [mul_comm]
    _ = (2 ^ 4) ^ n := by rw [pow_mul]
    _ = 16 ^ n := by norm_num

/-- A number is at most 27 times the fourth power of its iterated square
root. -/
theorem le_twentyseven_mul_iteratedSqrt_pow_four {N : ℕ} (hN : 1 ≤ N) :
    N ≤ 27 * (N.sqrt.sqrt) ^ 4 := by
  let u := N.sqrt
  let l := u.sqrt
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact Nat.le_sqrt.mpr (by simpa using hN)
  have hl1 : 1 ≤ l := by
    dsimp [l]
    exact Nat.le_sqrt.mpr (by simpa [u] using hu1)
  have hNu : N ≤ 3 * u ^ 2 := by
    have h := Nat.sqrt_le_add N
    dsimp [u]
    nlinarith [Nat.mul_le_mul_left u hu1]
  have hul : u ≤ 3 * l ^ 2 := by
    have h := Nat.sqrt_le_add u
    dsimp [l]
    nlinarith [Nat.mul_le_mul_left l hl1]
  have hu2 : u ^ 2 ≤ 9 * l ^ 4 := by
    nlinarith [sq_nonneg (3 * (l : ℤ) ^ 2 - (u : ℤ))]
  nlinarith

/-- Consequently `N≤27·16^(sqrt(sqrt N))`. -/
theorem le_twentyseven_mul_sixteen_iteratedSqrt {N : ℕ} (hN : 1 ≤ N) :
    N ≤ 27 * 16 ^ N.sqrt.sqrt :=
  (le_twentyseven_mul_iteratedSqrt_pow_four hN).trans
    (Nat.mul_le_mul_left 27 (pow_four_le_sixteen_pow N.sqrt.sqrt))

/-- The explicit Brun order is eventually at most one hundredth of its
argument (in the denominator-free form used later). -/
theorem eventually_hundred_mul_geometricBrunOrder_add_one_le :
    ∀ᶠ J : ℕ in atTop, 100 * (geometricBrunOrder J + 1) ≤ J := by
  have hsmallR := Real.isLittleO_log_id_atTop.bound
    (by norm_num : (0 : ℝ) < 1 / 40000)
  have hsmall := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallR
  filter_upwards [eventually_ge_atTop 100000, hsmall] with J hJ hlog
  have hJpos : (0 : ℝ) < J := by positivity
  have hlog0 : 0 ≤ Real.log J := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ J))
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hJpos.le,
    abs_of_nonneg hlog0] at hlog
  have harg0 : 0 ≤ 100 * (1 + Real.log J) := by positivity
  have hceil := Nat.ceil_lt_add_one harg0
  have hRcast : (geometricBrunOrder J : ℝ) <
      200 * (1 + Real.log J) + 2 := by
    unfold geometricBrunOrder
    push_cast
    nlinarith
  have hJR : (100000 : ℝ) ≤ J := by exact_mod_cast hJ
  have hfinal : (100 : ℝ) * (geometricBrunOrder J + 1) ≤ J := by
    push_cast
    norm_num at hlog
    nlinarith
  exact_mod_cast hfinal

/-- With square-root upper endpoint, the Brun exponent (including a small
coefficient allowance) is eventually at most `N/2`. -/
theorem eventually_geometricBrun_exponent_le_half :
    ∀ᶠ N : ℕ in atTop,
      1 + N.sqrt + 3 * (N.sqrt * geometricBrunOrder N.sqrt) ≤ N / 2 := by
  have horder := tendsto_natSqrt_atTop.eventually
    eventually_hundred_mul_geometricBrunOrder_add_one_le
  have husize := tendsto_natSqrt_atTop.eventually (eventually_ge_atTop 100)
  filter_upwards [horder, husize] with N hR hu
  let u := N.sqrt
  let R := geometricBrunOrder u
  have hu2 : u * u ≤ N := Nat.sqrt_le N
  have h100R : 100 * R ≤ u := by
    dsimp [R, u] at hR ⊢
    omega
  have h100u : 100 * u ≤ N := by
    apply (Nat.mul_le_mul_right u hu).trans
    exact hu2
  have h100uR : 100 * (u * R) ≤ N := by
    calc
      100 * (u * R) = u * (100 * R) := by ring
      _ ≤ u * u := Nat.mul_le_mul_left u h100R
      _ ≤ N := hu2
  have h100 : 100 ≤ N := by omega
  change 1 + u + 3 * (u * R) ≤ N / 2
  omega

/-- The full natural Brun remainder coefficient is eventually bounded by
`16^(N/2)`. -/
theorem eventually_geometricBrun_coefficient_le :
    ∀ᶠ N : ℕ in atTop,
      4 * (geometricBrunOrder N.sqrt + 1) *
          (((16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt) ^ 3) ≤
        16 ^ (N / 2) := by
  have horder := tendsto_natSqrt_atTop.eventually
    eventually_hundred_mul_geometricBrunOrder_add_one_le
  filter_upwards [horder, eventually_geometricBrun_exponent_le_half] with N hR hexp
  let u := N.sqrt
  let R := geometricBrunOrder u
  have hRu : R + 1 ≤ u := by
    dsimp [R, u] at hR ⊢
    omega
  have hu16 : u ≤ 16 ^ u :=
    (self_le_two_pow u).trans (Nat.pow_le_pow_left (by norm_num : 2 ≤ 16) u)
  have hcoef : 4 * (R + 1) ≤ 16 ^ (1 + u) := by
    calc
      4 * (R + 1) ≤ 16 * (16 ^ u) :=
        Nat.mul_le_mul (by norm_num) (hRu.trans hu16)
      _ = 16 ^ (1 + u) := by rw [pow_add]; norm_num
  have hcube : (((16 ^ u) ^ R) ^ 3) = 16 ^ (3 * (u * R)) := by
    calc
      (((16 ^ u) ^ R) ^ 3) = (16 ^ (u * R)) ^ 3 := by
        rw [pow_mul]
      _ = 16 ^ ((u * R) * 3) := (pow_mul 16 (u * R) 3).symm
      _ = 16 ^ (3 * (u * R)) := by rw [mul_comm]
  have hpre : 4 * (R + 1) * (((16 ^ u) ^ R) ^ 3) ≤
      16 ^ (1 + u + 3 * (u * R)) := by
    rw [hcube, pow_add]
    exact Nat.mul_le_mul_right _ hcoef
  have hpow : 16 ^ (1 + u + 3 * (u * R)) ≤ 16 ^ (N / 2) :=
    Nat.pow_le_pow_right (by norm_num) (by simpa [u, R] using hexp)
  exact hpre.trans hpow

/-- The exact remainder from F-025 is eventually at most
`16^N·16^(N/2)`. -/
theorem eventually_geometricBrun_remainder_le :
    ∀ᶠ N : ℕ in atTop,
      2 * (16 ^ N : ℝ) *
          (((geometricBrunOrder N.sqrt + 1) *
            (16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt : ℕ) : ℝ) *
          ((((16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt : ℕ) : ℝ) *
            ((((16 ^ N.sqrt) ^ geometricBrunOrder N.sqrt + 1 : ℕ) : ℝ))) ≤
        (16 ^ N : ℝ) * (16 ^ (N / 2) : ℕ) := by
  filter_upwards [eventually_geometricBrun_coefficient_le] with N hcoef
  let R := geometricBrunOrder N.sqrt
  let Q := (16 ^ N.sqrt) ^ R
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.one_le_pow R (16 ^ N.sqrt) (by positivity)
  have hQsucc : Q + 1 ≤ 2 * Q := by omega
  have hnat : 2 * 16 ^ N * ((R + 1) * Q) * (Q * (Q + 1)) ≤
      16 ^ N * 16 ^ (N / 2) := by
    let A : ℕ := 2 * 16 ^ N * (R + 1) * Q ^ 2
    calc
      2 * 16 ^ N * ((R + 1) * Q) * (Q * (Q + 1)) =
          A * (Q + 1) := by dsimp [A]; ring
      _ ≤ A * (2 * Q) := Nat.mul_le_mul_left A hQsucc
      _ = 4 * 16 ^ N * (R + 1) * Q ^ 3 := by dsimp [A]; ring
      _ = 16 ^ N * (4 * (R + 1) * Q ^ 3) := by ring
      _ ≤ 16 ^ N * 16 ^ (N / 2) :=
        Nat.mul_le_mul_left _ (by simpa [R, Q] using hcoef)
  exact_mod_cast hnat

/-- For `N≥2`, the residual half-exponential beats one factor of `N`. -/
theorem sixteen_pow_half_mul_le {N : ℕ} (hN : 2 ≤ N) :
    16 ^ (N / 2) * N ≤ 16 ^ N := by
  have hexp : N ≤ 4 * (N / 2) := by omega
  have hNpow : N ≤ 16 ^ (N / 2) := by
    apply (self_le_two_pow N).trans
    calc
      2 ^ N ≤ 2 ^ (4 * (N / 2)) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = 16 ^ (N / 2) := by
        rw [pow_mul]
        norm_num
  calc
    16 ^ (N / 2) * N ≤ 16 ^ (N / 2) * 16 ^ (N / 2) :=
      Nat.mul_le_mul_left _ hNpow
    _ = 16 ^ (2 * (N / 2)) := by rw [← pow_add]; congr 1 <;> omega
    _ ≤ 16 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The logarithmic decay exponent produced by the moving interval
`(16^sqrt(sqrt N),16^sqrt N]` eventually dominates `log N / 8`. -/
theorem eventually_log_sqrt_gap :
    ∀ᶠ N : ℕ in atTop,
      Real.log N / 8 ≤
        Real.log N.sqrt - (1 + Real.log N.sqrt.sqrt) := by
  have hlogtop := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (2 * Real.log 3 + 8)
  filter_upwards [eventually_ge_atTop 1, hlogtop] with N hN hlogN
  let u := N.sqrt
  let l := u.sqrt
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact Nat.le_sqrt.mpr (by simpa using hN)
  have hl1 : 1 ≤ l := by
    dsimp [l]
    exact Nat.le_sqrt.mpr (by simpa [u] using hu1)
  have hNu : N ≤ 3 * u ^ 2 := by
    have h := Nat.sqrt_le_add N
    dsimp [u]
    nlinarith [Nat.mul_le_mul_left u hu1]
  have hlu : l ^ 2 ≤ u := by
    simpa [l, pow_two] using Nat.sqrt_le u
  have hlogN_u : Real.log N ≤ Real.log 3 + 2 * Real.log u := by
    have hposN : (0 : ℝ) < N := by positivity
    have hposR : (0 : ℝ) < 3 * u ^ 2 := by positivity
    have hNuR : (N : ℝ) ≤ 3 * (u : ℝ) ^ 2 := by exact_mod_cast hNu
    have hlogle := Real.log_le_log hposN hNuR
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity : (u : ℝ) ^ 2 ≠ 0),
      Real.log_pow] at hlogle
    norm_num at hlogle
    exact hlogle
  have hlogl_u : 2 * Real.log l ≤ Real.log u := by
    have hposl2 : (0 : ℝ) < (l : ℝ) ^ 2 := by positivity
    have hluR : ((l : ℝ) ^ 2) ≤ (u : ℝ) := by exact_mod_cast hlu
    have hlogle := Real.log_le_log hposl2 hluR
    rw [Real.log_pow] at hlogle
    norm_num at hlogle
    exact hlogle
  dsimp [u, l] at *
  nlinarith

/-- Saving factor used on the geometric grid `X=16^N`. -/
noncomputable def gridSaving (N : ℕ) : ℝ :=
  Real.exp (-Real.log N / 1024)

/-- On the power-of-16 grid, the first target sum has a fixed power saving in
`N` (equivalently, a fixed log-power saving in `X`). -/
theorem eventually_sum_t_two_pow_sixteen_le :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 (16 ^ N), (t 2 n : ℝ)) ≤
        30 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
  obtain ⟨Jmin, hJmin, hgeom⟩ := exists_geometric_finite_medium_bound
  have hmin := tendsto_natSqrt_natSqrt_atTop.eventually
    (eventually_ge_atTop Jmin)
  filter_upwards [eventually_ge_atTop 2, hmin, eventually_log_sqrt_gap,
    eventually_geometricBrun_remainder_le] with N hN hJ hgap hrem
  let u := N.sqrt
  let l := u.sqrt
  have hlu : l ≤ u := Nat.sqrt_le_self u
  have hbase := hgeom l u (16 ^ N) hJ hlu
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hinvSaving : 1 / (N : ℝ) ≤ gridSaving N := by
    calc
      1 / (N : ℝ) = Real.exp (-Real.log N) := by
        rw [Real.exp_neg, Real.exp_log hNpos]
        simp [one_div]
      _ ≤ Real.exp (-Real.log N / 1024) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = gridSaving N := rfl
  have hNz : N ≤ 27 * 16 ^ l := by
    exact le_twentyseven_mul_sixteen_iteratedSqrt (by omega : 1 ≤ N)
  have hzpos : (0 : ℝ) < (16 ^ l : ℕ) := by positivity
  have hfracZ : 1 / ((16 ^ l : ℕ) : ℝ) ≤ 27 / (N : ℝ) := by
    have hNzR : (N : ℝ) ≤ 27 * ((16 ^ l : ℕ) : ℝ) := by exact_mod_cast hNz
    rw [div_le_div_iff₀ hzpos hNpos]
    nlinarith
  have hzterm : ((16 ^ N : ℕ) : ℝ) ^ 2 / ((16 ^ l : ℕ) : ℝ) ≤
      27 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
    have hinvSaving' : (N : ℝ)⁻¹ ≤ gridSaving N := by
      simpa [one_div] using hinvSaving
    have h := hfracZ.trans (mul_le_mul_of_nonneg_left hinvSaving'
      (by norm_num : (0 : ℝ) ≤ 27))
    calc
      ((16 ^ N : ℕ) : ℝ) ^ 2 / ((16 ^ l : ℕ) : ℝ) =
          ((16 ^ N : ℕ) : ℝ) ^ 2 * (1 / ((16 ^ l : ℕ) : ℝ)) := by ring
      _ ≤ ((16 ^ N : ℕ) : ℝ) ^ 2 * (27 * gridSaving N) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = 27 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by ring
  have hdecay :
      Real.exp (-((Real.log u - (1 + Real.log l)) / 128)) ≤ gridSaving N := by
    unfold gridSaving
    apply Real.exp_le_exp.mpr
    dsimp [u, l] at hgap ⊢
    nlinarith
  have hmain : 2 * ((16 ^ N : ℕ) : ℝ) ^ 2 *
      Real.exp (-((Real.log u - (1 + Real.log l)) / 128)) ≤
      2 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N :=
    mul_le_mul_of_nonneg_left hdecay (by positivity)
  have hhalfNat := sixteen_pow_half_mul_le hN
  have hhalf : ((16 ^ (N / 2) : ℕ) : ℝ) ≤
      ((16 ^ N : ℕ) : ℝ) / (N : ℝ) := by
    apply (le_div_iff₀ hNpos).2
    exact_mod_cast hhalfNat
  have hremSaving : ((16 ^ N : ℕ) : ℝ) * ((16 ^ (N / 2) : ℕ) : ℝ) ≤
      ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
    calc
      ((16 ^ N : ℕ) : ℝ) * ((16 ^ (N / 2) : ℕ) : ℝ) ≤
          ((16 ^ N : ℕ) : ℝ) * (((16 ^ N : ℕ) : ℝ) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = ((16 ^ N : ℕ) : ℝ) ^ 2 * (1 / (N : ℝ)) := by ring
      _ ≤ ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N :=
        mul_le_mul_of_nonneg_left hinvSaving (by positivity)
  have hrem' :
      2 * ((16 ^ N : ℕ) : ℝ) *
          (((geometricBrunOrder u + 1) *
            (16 ^ u) ^ geometricBrunOrder u : ℕ) : ℝ) *
          ((((16 ^ u) ^ geometricBrunOrder u : ℕ) : ℝ) *
            ((((16 ^ u) ^ geometricBrunOrder u + 1 : ℕ) : ℝ))) ≤
      ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := by
    apply (show _ ≤ ((16 ^ N : ℕ) : ℝ) * ((16 ^ (N / 2) : ℕ) : ℝ) by
      simpa [u] using hrem).trans
    exact hremSaving
  dsimp [u, l] at hbase hmain hrem' hzterm
  linarith

end Erdos394
