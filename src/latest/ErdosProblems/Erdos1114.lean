/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1114.
https://www.erdosproblems.com/forum/thread/1114

Informal authors:
- Elemér Bálint

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1114.md
-/
import Mathlib

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Erdős Problem 1114

The complete mathematical proof and the indexing correction are in
`tex/1114.tex`.  The development below proves the gap theorem for the
non-vacuous reading: a degree `N + 1` polynomial has the `N + 1` simple
arithmetic-progression roots indexed by `0, ..., N`.
-/

open scoped BigOperators Topology
open Filter Set

namespace Erdos1114

/-- The derivative gaps indexed from the midpoint towards the right endpoint
are nondecreasing.  The two inequalities on `i` say that the three terms
exist and that the first gap is on (or straddles) the right half. -/
def RightGapMonotone (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i + 2 < N → N ≤ 2 * (i + 1) →
    b (i + 1) - b i ≤ b (i + 2) - b (i + 1)

/-- Reflection symmetry of the consecutive gaps. -/
def GapSymmetric (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i + 1 < N →
    b (i + 1) - b i = b (N - 1 - i) - b (N - 2 - i)

/-- The rational kernel in the cubic series estimate. -/
noncomputable def kernel (p q : ℝ) (m : ℕ) : ℝ :=
  1 / (((m : ℝ) + p) * ((m : ℝ) + q))

noncomputable def kernelPotential (p q : ℝ) (m : ℕ) : ℝ :=
  1 / Real.sqrt (((m : ℝ) + p) * ((m : ℝ) + q)) +
    2 / (3 * (((m : ℝ) + p) * ((m : ℝ) + q)))

/-- The purely algebraic form of the one-step potential estimate. -/
lemma potential_drop_of_one_le {X Y : ℝ} (hX : 1 ≤ X) (hXY : X + 1 ≤ Y) :
    1 / X ^ 2 ≤
      (1 / X + 2 / (3 * X ^ 2)) - (1 / Y + 2 / (3 * Y ^ 2)) := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hYp : 0 < Y := lt_of_lt_of_le hXp (le_trans (le_add_of_nonneg_right zero_le_one) hXY)
  have hd : 1 ≤ Y - X := by linarith
  have haux : 0 ≤ 3 * X * Y * (Y - X) - Y ^ 2 - 2 * X ^ 2 := by
    have h₁ : 0 ≤ 3 * X ^ 2 * ((Y - X) - 1) := by positivity
    have h₂ : 0 ≤ (Y - X) * (3 * X * (Y - X) - 2 * X - (Y - X)) := by
      have : 0 ≤ 3 * X * (Y - X) - 2 * X - (Y - X) := by nlinarith
      positivity
    nlinarith
  field_simp
  nlinarith

lemma sqrt_product_succ {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Real.sqrt (x * y) + 1 ≤ Real.sqrt ((x + 1) * (y + 1)) := by
  have hxy : 0 ≤ x * y := mul_nonneg (zero_le_one.trans hx) (zero_le_one.trans hy)
  have hxy' : 0 ≤ (x + 1) * (y + 1) := by positivity
  have hs₀ : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
  have ht₀ : 0 ≤ Real.sqrt ((x + 1) * (y + 1)) := Real.sqrt_nonneg _
  have hs_sq : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt hxy
  have ht_sq : Real.sqrt ((x + 1) * (y + 1)) ^ 2 = (x + 1) * (y + 1) :=
    Real.sq_sqrt hxy'
  have ham : 2 * Real.sqrt (x * y) ≤ x + y := by
    nlinarith [sq_nonneg (x - y)]
  nlinarith

/-- For the rational kernel, the potential loses at least the current term. -/
lemma kernel_le_potential_sub_succ {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    kernel p q m ≤ kernelPotential p q m - kernelPotential p q (m + 1) := by
  let x : ℝ := (m : ℝ) + p
  let y : ℝ := (m : ℝ) + q
  let X := Real.sqrt (x * y)
  let Y := Real.sqrt ((x + 1) * (y + 1))
  have hx : 1 ≤ x := by
    dsimp [x]
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have hy : 1 ≤ y := by
    dsimp [y]
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have hxy : 0 < x * y := mul_pos (zero_lt_one.trans_le hx) (zero_lt_one.trans_le hy)
  have hX₀ : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = x * y := Real.sq_sqrt hxy.le
  have hX : 1 ≤ X := by
    nlinarith
  have hXY : X + 1 ≤ Y := sqrt_product_succ hx hy
  have hbase := potential_drop_of_one_le hX hXY
  have hYsq : Y ^ 2 = (x + 1) * (y + 1) := Real.sq_sqrt (by positivity)
  dsimp [kernel, kernelPotential, x, y, X, Y] at hbase hXsq hYsq ⊢
  norm_num [Nat.cast_add, hXsq, hYsq] at hbase ⊢
  ring_nf at hbase ⊢
  exact hbase

lemma kernel_nonneg {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    0 ≤ kernel p q m := by
  unfold kernel
  positivity

lemma kernel_pos {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    0 < kernel p q m := by
  unfold kernel
  positivity

lemma kernelPotential_nonneg {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    0 ≤ kernelPotential p q m := by
  unfold kernelPotential
  positivity

/-- Finite telescoping form of the potential bound. -/
lemma sum_range_kernel_le_potential_sub {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (m n : ℕ) :
    (∑ i ∈ Finset.range n, kernel p q (m + i)) ≤
      kernelPotential p q m - kernelPotential p q (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hdrop := kernel_le_potential_sub_succ hp hq (m + n)
      have hm : m + n + 1 = m + (n + 1) := by omega
      rw [hm] at hdrop
      nlinarith

/-- Every tail of the kernel series is bounded by its first potential. -/
lemma tsum_kernel_tail_le_potential {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    (∑' i : ℕ, kernel p q (m + i)) ≤ kernelPotential p q m := by
  apply Real.tsum_le_of_sum_range_le (c := kernelPotential p q m)
  · exact fun i ↦ kernel_nonneg hp hq _
  · intro n
    exact (sum_range_kernel_le_potential_sub hp hq m n).trans <| by
      have := kernelPotential_nonneg hp hq (m + n)
      linarith

lemma summable_kernel_tail {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    Summable fun i : ℕ ↦ kernel p q (m + i) := by
  apply summable_of_sum_range_le (c := kernelPotential p q m)
    (fun i ↦ kernel_nonneg hp hq _)
  intro n
  exact (sum_range_kernel_le_potential_sub hp hq m n).trans <| by
    have := kernelPotential_nonneg hp hq (m + n)
    linarith

lemma summable_kernel {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Summable (kernel p q) := by
  simpa using summable_kernel_tail hp hq 0

lemma kernelPotential_eq {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    kernelPotential p q m = Real.sqrt (kernel p q m) + 2 * kernel p q m / 3 := by
  have hd : 0 < ((m : ℝ) + p) * ((m : ℝ) + q) := by positivity
  unfold kernel kernelPotential
  simp only [div_eq_mul_inv, one_mul, Real.sqrt_inv]
  field_simp [hd.ne']

lemma kernel_le_half {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 3 ≤ p + q) (m : ℕ) : kernel p q m ≤ 1 / 2 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hp' : 0 < (m : ℝ) + p := by positivity
  have hq' : 0 < (m : ℝ) + q := by positivity
  have hpqprod : 2 ≤ ((m : ℝ) + p) * ((m : ℝ) + q) := by
    have hbase : 0 ≤ (p - 1) * (q - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  unfold kernel
  exact one_div_le_one_div_of_le (by norm_num) hpqprod

/-- Cubing a tail costs at most four times the square of its first term. -/
lemma cube_add_sub_cube_le_four_sq {C R : ℝ} (hC : 0 ≤ C) (hChalf : C ≤ 1 / 2)
    (hR : 0 ≤ R) (hbound : C + R ≤ Real.sqrt C + 2 * C / 3) :
    (C + R) ^ 3 - R ^ 3 ≤ 4 * C ^ 2 := by
  let w := Real.sqrt C
  let S := C + R
  let U := w + 2 * C / 3
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hw_sq : w ^ 2 = C := Real.sq_sqrt hC
  have hw_le : w ≤ 3 / 4 := by nlinarith
  have hCU : 3 * w + C ≤ 3 := by nlinarith
  have hpolyU : 3 * U ^ 2 - 3 * C * U + C ^ 2 ≤ 4 * C := by
    dsimp [U]
    nlinarith
  have hCS : C ≤ S := by dsimp [S]; linarith
  have hSU : S ≤ U := hbound
  have hmono :
      3 * S ^ 2 - 3 * C * S + C ^ 2 ≤ 3 * U ^ 2 - 3 * C * U + C ^ 2 := by
    have hfactor : 0 ≤ (U - S) * (3 * (U + S) - 3 * C) := by
      apply mul_nonneg (sub_nonneg.mpr hSU)
      nlinarith
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hmono.trans hpolyU) hC
  dsimp [S] at hmul ⊢
  nlinarith

noncomputable def kernelTail (p q : ℝ) (m : ℕ) : ℝ :=
  ∑' i : ℕ, kernel p q (i + m)

lemma kernelTail_nonneg {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    0 ≤ kernelTail p q m := by
  apply tsum_nonneg
  exact fun i ↦ kernel_nonneg hp hq _

lemma kernelTail_le_potential {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    kernelTail p q m ≤ kernelPotential p q m := by
  unfold kernelTail
  convert tsum_kernel_tail_le_potential hp hq m using 1
  apply tsum_congr
  intro i
  rw [Nat.add_comm]

lemma kernelTail_eq_add_succ {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    kernelTail p q m = kernel p q m + kernelTail p q (m + 1) := by
  have hsum := (summable_kernel_tail hp hq m).tsum_eq_zero_add
  unfold kernelTail
  rw [show (∑' i : ℕ, kernel p q (i + m)) =
      ∑' i : ℕ, kernel p q (m + i) by
    apply tsum_congr
    intro i
    rw [Nat.add_comm]]
  rw [hsum]
  congr 1
  apply tsum_congr
  intro i
  congr 1
  omega

/-- The cubic moment estimate for the Bálint kernel. -/
lemma kernel_tsum_cube_le_four_tsum_sq {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 3 ≤ p + q) :
    (∑' m : ℕ, kernel p q m) ^ 3 ≤ 4 * ∑' m : ℕ, (kernel p q m) ^ 2 := by
  have hc₀ : ∀ m, 0 ≤ kernel p q m := fun m ↦ kernel_nonneg hp hq m
  have hc_half : ∀ m, kernel p q m ≤ 1 / 2 := fun m ↦ kernel_le_half hp hq hpq m
  have hsq : Summable fun m : ℕ ↦ (kernel p q m) ^ 2 := by
    apply Summable.of_nonneg_of_le (fun m ↦ sq_nonneg (kernel p q m))
      (fun m ↦ ?_) (summable_kernel hp hq)
    have := hc_half m
    nlinarith [hc₀ m]
  have hstep : ∀ m,
      kernelTail p q m ^ 3 - kernelTail p q (m + 1) ^ 3 ≤
        4 * kernel p q m ^ 2 := by
    intro m
    rw [kernelTail_eq_add_succ hp hq m]
    apply cube_add_sub_cube_le_four_sq (hc₀ m) (hc_half m)
      (kernelTail_nonneg hp hq (m + 1))
    rw [← kernelPotential_eq hp hq m]
    simpa only [kernelTail_eq_add_succ hp hq m] using kernelTail_le_potential hp hq m
  have hfinite : ∀ n,
      kernelTail p q 0 ^ 3 - kernelTail p q n ^ 3 ≤
        4 * ∑ m ∈ Finset.range n, kernel p q m ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hs := hstep n
        nlinarith
  have htail : Tendsto (kernelTail p q) atTop (𝓝 0) := by
    exact tendsto_sum_nat_add (kernel p q)
  have hleft : Tendsto
      (fun n ↦ kernelTail p q 0 ^ 3 - kernelTail p q n ^ 3)
      atTop (𝓝 (kernelTail p q 0 ^ 3)) := by
    simpa using tendsto_const_nhds.sub (htail.pow 3)
  have hright : Tendsto
      (fun n ↦ 4 * ∑ m ∈ Finset.range n, kernel p q m ^ 2)
      atTop (𝓝 (4 * ∑' m : ℕ, kernel p q m ^ 2)) := by
    exact tendsto_const_nhds.mul hsq.hasSum.tendsto_sum_nat
  have hlim := le_of_tendsto_of_tendsto' hleft hright hfinite
  simpa [kernelTail, Nat.add_zero] using hlim

/-- Cauchy--Schwarz for the first three moments of the kernel series. -/
lemma kernel_tsum_sq_sq_le_tsum_mul_tsum_cube {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 3 ≤ p + q) :
    (∑' m : ℕ, (kernel p q m) ^ 2) ^ 2 ≤
      (∑' m : ℕ, kernel p q m) * ∑' m : ℕ, (kernel p q m) ^ 3 := by
  have hc₀ : ∀ m, 0 ≤ kernel p q m := fun m ↦ kernel_nonneg hp hq m
  have hc_half : ∀ m, kernel p q m ≤ 1 / 2 := fun m ↦ kernel_le_half hp hq hpq m
  have hsquare : Summable fun m : ℕ ↦ (kernel p q m) ^ 2 := by
    apply Summable.of_nonneg_of_le (fun m ↦ sq_nonneg (kernel p q m))
      (fun m ↦ ?_) (summable_kernel hp hq)
    nlinarith [hc₀ m, hc_half m]
  have hcube : Summable fun m : ℕ ↦ (kernel p q m) ^ 3 := by
    apply Summable.of_nonneg_of_le (fun m ↦ pow_nonneg (hc₀ m) 3)
      (fun m ↦ ?_) (summable_kernel hp hq)
    have hc1 : kernel p q m ≤ 1 := by linarith [hc_half m]
    have hprod : 0 ≤ kernel p q m * (1 - kernel p q m) * (1 + kernel p q m) := by
      exact mul_nonneg (mul_nonneg (hc₀ m) (sub_nonneg.mpr hc1)) (by nlinarith [hc₀ m])
    nlinarith
  have hfinite : ∀ n,
      (∑ m ∈ Finset.range n, kernel p q m ^ 2) ^ 2 ≤
        (∑ m ∈ Finset.range n, kernel p q m) *
          ∑ m ∈ Finset.range n, kernel p q m ^ 3 := by
    intro n
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.range n)
      (r := fun m ↦ kernel p q m ^ 2)
      (f := kernel p q) (g := fun m ↦ kernel p q m ^ 3)
    · exact fun m _ ↦ hc₀ m
    · exact fun m _ ↦ pow_nonneg (hc₀ m) 3
    · intro m _
      ring_nf
      exact le_rfl
  exact le_of_tendsto_of_tendsto'
    (hsquare.hasSum.tendsto_sum_nat.pow 2)
    ((summable_kernel hp hq).hasSum.tendsto_sum_nat.mul hcube.hasSum.tendsto_sum_nat)
    hfinite

noncomputable def radius (N : ℕ) : ℝ := (N : ℝ) / 2

noncomputable def shift (N : ℕ) : ℝ := radius N + 1

noncomputable def phaseKernel (N : ℕ) (m : ℕ) (u : ℝ) : ℝ :=
  kernel (shift N - u) (shift N + u) m

noncomputable def moment (r N : ℕ) (u : ℝ) : ℝ :=
  ∑' m : ℕ, phaseKernel N m u ^ r

noncomputable def phaseRemainder (N : ℕ) (u : ℝ) : ℝ :=
  2 * u * moment 1 N u

lemma phaseKernel_eq (N m : ℕ) (u : ℝ) :
    phaseKernel N m u =
      1 / (((m : ℝ) + shift N) ^ 2 - u ^ 2) := by
  unfold phaseKernel kernel
  congr 1
  ring

lemma phaseKernel_hasDerivAt {N m : ℕ} {u : ℝ}
    (hu : |u| < (m : ℝ) + shift N) :
    HasDerivAt (phaseKernel N m) (2 * u * phaseKernel N m u ^ 2) u := by
  have hfun : phaseKernel N m =
      fun x ↦ 1 / (((m : ℝ) + shift N) ^ 2 - x ^ 2) := by
    funext x
    exact phaseKernel_eq N m x
  rw [hfun]
  have hne : ((m : ℝ) + shift N) ^ 2 - u ^ 2 ≠ 0 := by
    have hm : 0 ≤ (m : ℝ) + shift N := by unfold shift radius; positivity
    have hu' : u ^ 2 < ((m : ℝ) + shift N) ^ 2 := by
      simpa [sq_abs] using (sq_lt_sq₀ (abs_nonneg u) hm).2 hu
    nlinarith
  let d : ℝ → ℝ := (fun _ : ℝ ↦ (m : ℝ) + shift N) ^ 2 - id ^ 2
  have hd : HasDerivAt d (-2 * u) u :=
    ((((hasDerivAt_const u ((m : ℝ) + shift N)).pow 2).sub
      ((hasDerivAt_id u).pow 2))).congr_deriv (by norm_num)
  have hdu : d u ≠ 0 := by simpa [d] using hne
  have hi := hd.inv hdu
  have hfd : (fun x : ℝ ↦ 1 / (((m : ℝ) + shift N) ^ 2 - x ^ 2)) = d⁻¹ := by
    funext x
    simp [d, one_div]
  rw [hfd]
  exact hi.congr_deriv (by
    simp only [Pi.inv_apply]
    field_simp [hdu])

lemma phaseKernel_sq_hasDerivAt {N m : ℕ} {u : ℝ}
    (hu : |u| < (m : ℝ) + shift N) :
    HasDerivAt ((phaseKernel N m) ^ 2)
      (4 * u * phaseKernel N m u ^ 3) u := by
  exact ((phaseKernel_hasDerivAt (N := N) (m := m) hu).pow 2).congr_deriv (by ring)

lemma kernel_le_one {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) :
    kernel p q m ≤ 1 := by
  have hd : 1 ≤ ((m : ℝ) + p) * ((m : ℝ) + q) := by
    have hmp : 1 ≤ (m : ℝ) + p := by nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
    have hmq : 1 ≤ (m : ℝ) + q := by nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmp) (sub_nonneg.mpr hmq)]
  unfold kernel
  simpa using one_div_le_one_div_of_le (zero_lt_one : (0 : ℝ) < 1) hd

lemma kernel_mono {p q p' q' : ℝ} (hp' : 1 ≤ p') (hq' : 1 ≤ q')
    (hpp : p' ≤ p) (hqq : q' ≤ q) (m : ℕ) : kernel p q m ≤ kernel p' q' m := by
  have hmp' : 0 < (m : ℝ) + p' := by positivity
  have hmq' : 0 < (m : ℝ) + q' := by positivity
  have hmp : 0 ≤ (m : ℝ) + p := by nlinarith
  have hmq : 0 ≤ (m : ℝ) + q := by nlinarith
  have hprod : ((m : ℝ) + p') * ((m : ℝ) + q') ≤
      ((m : ℝ) + p) * ((m : ℝ) + q) := by
    gcongr
  unfold kernel
  exact one_div_le_one_div_of_le (mul_pos hmp' hmq') hprod

lemma phase_parameters_of_mem_Icc {N : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (-radius N) (radius N)) :
    1 ≤ shift N - u ∧ 1 ≤ shift N + u := by
  rcases hu with ⟨hu₀, hu₁⟩
  unfold shift
  constructor <;> linarith

lemma phaseKernel_nonneg_of_mem_Icc {N m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (-radius N) (radius N)) : 0 ≤ phaseKernel N m u := by
  rcases phase_parameters_of_mem_Icc hu with ⟨hp, hq⟩
  exact kernel_nonneg hp hq m

lemma phaseKernel_le_base {N m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (-radius N) (radius N)) :
    phaseKernel N m u ≤ kernel 1 1 m := by
  rcases phase_parameters_of_mem_Icc hu with ⟨hp, hq⟩
  exact kernel_mono (by norm_num) (by norm_num) hp hq m

lemma summable_kernel_one_pow_two : Summable fun m : ℕ ↦ kernel 1 1 m ^ 2 := by
  refine Summable.of_nonneg_of_le (fun m ↦ sq_nonneg (kernel 1 1 m))
    (fun m ↦ ?_) (summable_kernel (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num))
  have h₀ := kernel_nonneg (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num) m
  have h₁ := kernel_le_one (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num) m
  nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]

lemma summable_phaseKernel_zero (N : ℕ) : Summable fun m ↦ phaseKernel N m 0 := by
  have hs : 1 ≤ shift N := by
    unfold shift radius
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity]
  simpa [phaseKernel] using summable_kernel hs hs

lemma phaseKernel_pow_two_le_base {N m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (-radius N) (radius N)) :
    phaseKernel N m u ^ 2 ≤ kernel 1 1 m := by
  have hc₀ := phaseKernel_nonneg_of_mem_Icc (m := m) hu
  have hcb := phaseKernel_le_base (m := m) hu
  have hb₁ := kernel_le_one (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num) m
  have hc₁ : phaseKernel N m u ≤ 1 := hcb.trans hb₁
  nlinarith [mul_nonneg hc₀ (sub_nonneg.mpr hc₁)]

lemma phaseKernel_pow_three_le_base {N m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (-radius N) (radius N)) :
    phaseKernel N m u ^ 3 ≤ kernel 1 1 m := by
  have hc₀ := phaseKernel_nonneg_of_mem_Icc (m := m) hu
  have hcb := phaseKernel_le_base (m := m) hu
  have hb₁ := kernel_le_one (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num) m
  have hc₁ : phaseKernel N m u ≤ 1 := hcb.trans hb₁
  have hprod : 0 ≤ phaseKernel N m u * (1 - phaseKernel N m u) *
      (1 + phaseKernel N m u) := by
    exact mul_nonneg (mul_nonneg hc₀ (sub_nonneg.mpr hc₁)) (by nlinarith)
  nlinarith

lemma phaseKernel_deriv_bound {N m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    ‖2 * u * phaseKernel N m u ^ 2‖ ≤ (N : ℝ) * kernel 1 1 m := by
  have hucc : u ∈ Set.Icc (-radius N) (radius N) := ⟨hu.1.le, hu.2.le⟩
  have hc₀ := phaseKernel_nonneg_of_mem_Icc (m := m) hucc
  have hc₂ := phaseKernel_pow_two_le_base (m := m) hucc
  have hb₀ := kernel_nonneg (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num) m
  have hx : 2 * |u| ≤ (N : ℝ) := by
    have habs : |u| < radius N := (abs_lt).2 hu
    unfold radius at habs
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_pow, abs_of_nonneg hc₀]
  exact mul_le_mul hx hc₂ (sq_nonneg _) (by positivity)

lemma phaseKernel_sq_deriv_bound {N m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    ‖4 * u * phaseKernel N m u ^ 3‖ ≤ 2 * (N : ℝ) * kernel 1 1 m := by
  have hucc : u ∈ Set.Icc (-radius N) (radius N) := ⟨hu.1.le, hu.2.le⟩
  have hc₀ := phaseKernel_nonneg_of_mem_Icc (m := m) hucc
  have hc₃ := phaseKernel_pow_three_le_base (m := m) hucc
  have hb₀ := kernel_nonneg (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num) m
  have hx : 4 * |u| ≤ 2 * (N : ℝ) := by
    have habs : |u| < radius N := (abs_lt).2 hu
    unfold radius at habs
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_pow, abs_of_nonneg hc₀]
  exact mul_le_mul hx hc₃ (pow_nonneg hc₀ 3) (by positivity)

lemma moment_one_hasDerivAt {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    HasDerivAt (moment 1 N) (2 * u * moment 2 N u) u := by
  have hbound : Summable fun m : ℕ ↦ (N : ℝ) * kernel 1 1 m :=
    (summable_kernel (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num)).mul_left _
  have hseries := hasDerivAt_tsum_of_isPreconnected hbound isOpen_Ioo
    isPreconnected_Ioo
    (fun m x hx ↦ phaseKernel_hasDerivAt (by
      have : |x| < radius N := (abs_lt).2 hx
      unfold shift
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]))
    (fun m x hx ↦ phaseKernel_deriv_bound hx)
    (show (0 : ℝ) ∈ Set.Ioo (-radius N) (radius N) by
      have hr : 0 < radius N := by
        unfold radius
        exact div_pos (Nat.cast_pos.mpr hN) (by norm_num)
      exact ⟨by linarith, hr⟩)
    (summable_phaseKernel_zero N) hu
  have hcoef : (∑' n : ℕ, 2 * u * phaseKernel N n u ^ 2) =
      2 * u * ∑' n : ℕ, phaseKernel N n u ^ 2 := by
    rw [← tsum_mul_left]
  unfold moment
  simpa only [pow_one] using hseries.congr_deriv hcoef

lemma summable_phaseKernel_zero_pow_two (N : ℕ) :
    Summable fun m : ℕ ↦ phaseKernel N m 0 ^ 2 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (-radius N) (radius N) := by
    have hr : 0 ≤ radius N := by unfold radius; positivity
    exact ⟨by linarith, hr⟩
  apply Summable.of_nonneg_of_le (fun m ↦ sq_nonneg (phaseKernel N m 0))
    (fun m ↦ phaseKernel_pow_two_le_base (m := m) hzero)
    (summable_kernel (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num))

lemma moment_two_hasDerivAt {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    HasDerivAt (moment 2 N) (4 * u * moment 3 N u) u := by
  have hbound : Summable fun m : ℕ ↦ 2 * (N : ℝ) * kernel 1 1 m :=
    (summable_kernel (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num)).mul_left _
  have hseries := hasDerivAt_tsum_of_isPreconnected
    (g := fun m ↦ (phaseKernel N m) ^ 2)
    (g' := fun m x ↦ 4 * x * phaseKernel N m x ^ 3)
    hbound isOpen_Ioo isPreconnected_Ioo
    (fun m x hx ↦ phaseKernel_sq_hasDerivAt (by
      have : |x| < radius N := (abs_lt).2 hx
      unfold shift
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]))
    (fun m x hx ↦ phaseKernel_sq_deriv_bound hx)
    (show (0 : ℝ) ∈ Set.Ioo (-radius N) (radius N) by
      have hr : 0 < radius N := by
        unfold radius
        exact div_pos (Nat.cast_pos.mpr hN) (by norm_num)
      exact ⟨by linarith, hr⟩)
    (by simpa only [Pi.pow_apply] using summable_phaseKernel_zero_pow_two N) hu
  have hcoef : (∑' n : ℕ, 4 * u * phaseKernel N n u ^ 3) =
      4 * u * ∑' n : ℕ, phaseKernel N n u ^ 3 := by
    rw [← tsum_mul_left]
  unfold moment
  simpa only [Pi.pow_apply] using hseries.congr_deriv hcoef

lemma moment_one_continuousOn (N : ℕ) :
    ContinuousOn (moment 1 N) (Set.Icc (-radius N) (radius N)) := by
  have hcont : ∀ m : ℕ, ContinuousOn (phaseKernel N m)
      (Set.Icc (-radius N) (radius N)) := by
    intro m u hu
    apply (phaseKernel_hasDerivAt (N := N) (m := m) ?_).continuousAt.continuousWithinAt
    have habs : |u| ≤ radius N := (abs_le).2 hu
    unfold shift
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have hsum := continuousOn_tsum hcont
    (summable_kernel (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num))
    (fun m u hu ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (phaseKernel_nonneg_of_mem_Icc (m := m) hu)]
      exact phaseKernel_le_base (m := m) hu)
  unfold moment
  simpa only [pow_one] using hsum

lemma moment_two_continuousOn (N : ℕ) :
    ContinuousOn (moment 2 N) (Set.Icc (-radius N) (radius N)) := by
  have hcont : ∀ m : ℕ, ContinuousOn ((phaseKernel N m) ^ 2)
      (Set.Icc (-radius N) (radius N)) := by
    intro m u hu
    apply ((phaseKernel_hasDerivAt (N := N) (m := m) ?_).continuousAt.pow 2).continuousWithinAt
    have habs : |u| ≤ radius N := (abs_le).2 hu
    unfold shift
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have hsum := continuousOn_tsum hcont
    (summable_kernel (p := (1 : ℝ)) (q := 1) (by norm_num) (by norm_num))
    (fun m u hu ↦ by
      rw [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (phaseKernel N m u))]
      exact phaseKernel_pow_two_le_base (m := m) hu)
  unfold moment
  simpa only [Pi.pow_apply] using hsum

noncomputable def phaseRemainderDeriv (N : ℕ) (u : ℝ) : ℝ :=
  2 * (moment 1 N u + 2 * u ^ 2 * moment 2 N u)

noncomputable def phaseRemainderDeriv2 (N : ℕ) (u : ℝ) : ℝ :=
  4 * u * (3 * moment 2 N u + 4 * u ^ 2 * moment 3 N u)

lemma phaseRemainder_hasDerivAt {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    HasDerivAt (phaseRemainder N) (phaseRemainderDeriv N u) u := by
  have h := (hasDerivAt_id u).mul (moment_one_hasDerivAt hN hu)
  have hcoef : 2 * (1 * moment 1 N u + id u * (2 * u * moment 2 N u)) =
      phaseRemainderDeriv N u := by
    unfold phaseRemainderDeriv
    simp only [id_eq]
    ring
  have hh := (h.const_mul 2).congr_deriv hcoef
  unfold phaseRemainder
  exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ by
    simp only [Pi.mul_apply, id_eq]
    ring)

lemma phaseRemainderDeriv_hasDerivAt {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    HasDerivAt (phaseRemainderDeriv N) (phaseRemainderDeriv2 N u) u := by
  have h₁ := moment_one_hasDerivAt hN hu
  have h₂ := (((hasDerivAt_id u).pow 2).mul (moment_two_hasDerivAt hN hu)).const_mul 2
  have hh := (h₁.add h₂).const_mul 2
  have hcoef :
      2 * (2 * u * moment 2 N u +
        2 * ((2 : ℝ) * u ^ (2 - 1) * 1 * moment 2 N u +
          u ^ 2 * (4 * u * moment 3 N u))) = phaseRemainderDeriv2 N u := by
    unfold phaseRemainderDeriv2
    norm_num
    ring
  unfold phaseRemainderDeriv
  exact (hh.congr_deriv hcoef).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring)

lemma phase_moment_cubic {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (radius N)) : moment 1 N u ^ 3 ≤ 4 * moment 2 N u := by
  have hu' : u ∈ Set.Icc (-radius N) (radius N) := by
    have hr : 0 ≤ radius N := by unfold radius; positivity
    exact ⟨by linarith [hu.1], hu.2⟩
  rcases phase_parameters_of_mem_Icc hu' with ⟨hp, hq⟩
  have hpq : 3 ≤ (shift N - u) + (shift N + u) := by
    have hcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    unfold shift radius
    nlinarith
  simpa only [moment, pow_one, phaseKernel] using
    kernel_tsum_cube_le_four_tsum_sq hp hq hpq

lemma phase_moment_cauchy {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (radius N)) :
    moment 2 N u ^ 2 ≤ moment 1 N u * moment 3 N u := by
  have hu' : u ∈ Set.Icc (-radius N) (radius N) := by
    have hr : 0 ≤ radius N := by unfold radius; positivity
    exact ⟨by linarith [hu.1], hu.2⟩
  rcases phase_parameters_of_mem_Icc hu' with ⟨hp, hq⟩
  have hpq : 3 ≤ (shift N - u) + (shift N + u) := by
    have hcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    unfold shift radius
    nlinarith
  simpa only [moment, pow_one, phaseKernel] using
    kernel_tsum_sq_sq_le_tsum_mul_tsum_cube hp hq hpq

lemma moment_one_pos {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (radius N)) : 0 < moment 1 N u := by
  have hu' : u ∈ Set.Icc (-radius N) (radius N) := by
    have hr : 0 ≤ radius N := by unfold radius; positivity
    exact ⟨by linarith [hu.1], hu.2⟩
  rcases phase_parameters_of_mem_Icc hu' with ⟨hp, hq⟩
  unfold moment phaseKernel
  simpa only [pow_one] using
    (summable_kernel hp hq).tsum_pos (fun m ↦ kernel_nonneg hp hq m) 0 (kernel_pos hp hq 0)

lemma moment_two_nonneg {N : ℕ} (u : ℝ) : 0 ≤ moment 2 N u := by
  unfold moment
  exact tsum_nonneg fun m ↦ sq_nonneg _

/-- The elementary ordered-field calculation at the heart of phase convexity.
All analytic work is encapsulated in the two moment inequalities. -/
lemma phase_convexity_certificate
    {u z s t v : ℝ}
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hs : 0 < s) (ht : 0 ≤ t)
    (hmoment : t ^ 2 ≤ s * v) (hcubic : s ^ 3 ≤ 4 * t) :
    0 ≤ 4 * u *
      ((3 * t + 4 * z * v) * (Real.pi ^ 2 + 4 * z * s ^ 2) -
        4 * s * (s + 2 * z * t) ^ 2) := by
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hv : 0 ≤ v := by
    nlinarith [sq_nonneg t, hs]
  have hst : 0 ≤ s * t := mul_nonneg hs.le ht
  have hzt2 : 0 ≤ z * t ^ 2 := mul_nonneg hz (sq_nonneg t)
  have h₁ : 4 * s ^ 4 ≤ 16 * s * t := by
    nlinarith [mul_le_mul_of_nonneg_left hcubic
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs.le)]
  have h₂ : 4 * z * s ^ 3 * t ≤ 16 * z * t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcubic
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hz) ht)]
  have hmoment' : 4 * z * t ^ 2 ≤ 4 * z * s * v := by
    nlinarith [mul_le_mul_of_nonneg_left hmoment
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hz)]
  have hmoment₂ : 16 * z ^ 2 * s ^ 2 * t ^ 2 ≤
      16 * z ^ 2 * s ^ 3 * v := by
    nlinarith [mul_le_mul_of_nonneg_left hmoment
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg z))
        (sq_nonneg s))]
  have hD : 0 ≤ s *
      ((3 * t + 4 * z * v) * (Real.pi ^ 2 + 4 * z * s ^ 2) -
        4 * s * (s + 2 * z * t) ^ 2) := by
    nlinarith [h₁, h₂, hmoment', hmoment₂, hst, hzt2]
  have hD' : 0 ≤
      ((3 * t + 4 * z * v) * (Real.pi ^ 2 + 4 * z * s ^ 2) -
        4 * s * (s + 2 * z * t) ^ 2) := by
    by_contra hn
    have hneg :
        ((3 * t + 4 * z * v) * (Real.pi ^ 2 + 4 * z * s ^ 2) -
          4 * s * (s + 2 * z * t) ^ 2) < 0 := lt_of_not_ge hn
    exact (not_lt_of_ge hD) (mul_neg_of_pos_of_neg hs hneg)
  positivity

lemma phase_numerator_nonneg {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (radius N)) :
    0 ≤ phaseRemainderDeriv2 N u * (Real.pi ^ 2 + phaseRemainder N u ^ 2) -
      2 * phaseRemainder N u * phaseRemainderDeriv N u ^ 2 := by
  have hcert := phase_convexity_certificate hu.1 (sq_nonneg u)
    (moment_one_pos hN hu) (moment_two_nonneg (N := N) u)
    (phase_moment_cauchy hN hu) (phase_moment_cubic hN hu)
  unfold phaseRemainder phaseRemainderDeriv phaseRemainderDeriv2
  nlinarith

noncomputable def phase (N : ℕ) (u : ℝ) : ℝ :=
  Real.arctan (phaseRemainder N u / Real.pi) / Real.pi

noncomputable def phaseDeriv (N : ℕ) (u : ℝ) : ℝ :=
  phaseRemainderDeriv N u / (Real.pi ^ 2 + phaseRemainder N u ^ 2)

noncomputable def phaseDeriv2 (N : ℕ) (u : ℝ) : ℝ :=
  (phaseRemainderDeriv2 N u * (Real.pi ^ 2 + phaseRemainder N u ^ 2) -
    2 * phaseRemainder N u * phaseRemainderDeriv N u ^ 2) /
      (Real.pi ^ 2 + phaseRemainder N u ^ 2) ^ 2

lemma phase_hasDerivAt {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    HasDerivAt (phase N) (phaseDeriv N u) u := by
  have hg := phaseRemainder_hasDerivAt hN hu
  have h := ((hg.div_const Real.pi).arctan).div_const Real.pi
  have hcoef :
      (1 / (1 + (phaseRemainder N u / Real.pi) ^ 2) *
        (phaseRemainderDeriv N u / Real.pi)) / Real.pi = phaseDeriv N u := by
    unfold phaseDeriv
    field_simp [Real.pi_ne_zero]
  have hh := h.congr_deriv hcoef
  unfold phase
  exact hh

lemma phaseDeriv_hasDerivAt {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Ioo (-radius N) (radius N)) :
    HasDerivAt (phaseDeriv N) (phaseDeriv2 N u) u := by
  have hg := phaseRemainder_hasDerivAt hN hu
  have hgp := phaseRemainderDeriv_hasDerivAt hN hu
  have hden : HasDerivAt
      (fun x ↦ Real.pi ^ 2 + phaseRemainder N x ^ 2)
      (2 * phaseRemainder N u * phaseRemainderDeriv N u) u := by
    have hraw := (hasDerivAt_const u (Real.pi ^ 2)).add (hg.pow 2)
    exact hraw.congr_deriv (by ring)
  have hne : Real.pi ^ 2 + phaseRemainder N u ^ 2 ≠ 0 := by
    have : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    nlinarith [sq_nonneg (phaseRemainder N u)]
  have h := hgp.div hden hne
  have hcoef :
      (phaseRemainderDeriv2 N u *
          (Real.pi ^ 2 + phaseRemainder N u ^ 2) -
        phaseRemainderDeriv N u *
          (2 * phaseRemainder N u * phaseRemainderDeriv N u)) /
        (Real.pi ^ 2 + phaseRemainder N u ^ 2) ^ 2 = phaseDeriv2 N u := by
    unfold phaseDeriv2
    ring
  have hh := h.congr_deriv hcoef
  unfold phaseDeriv
  exact hh

lemma phaseDeriv2_nonneg {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (radius N)) : 0 ≤ phaseDeriv2 N u := by
  unfold phaseDeriv2
  exact div_nonneg (phase_numerator_nonneg hN hu) (sq_nonneg _)

lemma phase_continuousOn (N : ℕ) :
    ContinuousOn (phase N) (Set.Icc 0 (radius N)) := by
  have hsub : Set.Icc (0 : ℝ) (radius N) ⊆ Set.Icc (-radius N) (radius N) := by
    intro x hx
    have hr : 0 ≤ radius N := by unfold radius; positivity
    exact ⟨by linarith [hx.1], hx.2⟩
  have hm : ContinuousOn (moment 1 N) (Set.Icc 0 (radius N)) :=
    (moment_one_continuousOn N).mono hsub
  have hg : ContinuousOn (phaseRemainder N) (Set.Icc 0 (radius N)) := by
    unfold phaseRemainder
    fun_prop
  unfold phase
  fun_prop

lemma phase_convexOn {N : ℕ} (hN : 0 < N) :
    ConvexOn ℝ (Set.Icc 0 (radius N)) (phase N) := by
  have hr : 0 < radius N := by
    unfold radius
    exact div_pos (Nat.cast_pos.mpr hN) (by norm_num)
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (D := Set.Icc 0 (radius N)) (f := phase N)
    (f' := phaseDeriv N) (f'' := phaseDeriv2 N)
    (convex_Icc 0 (radius N)) (phase_continuousOn N)
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (radius N) := by simpa [interior_Icc, hr.ne'] using hx
    exact (phase_hasDerivAt hN ⟨by linarith [hx'.1], hx'.2⟩).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (radius N) := by simpa [interior_Icc, hr.ne'] using hx
    exact (phaseDeriv_hasDerivAt hN ⟨by linarith [hx'.1], hx'.2⟩).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (radius N) := by simpa [interior_Icc, hr.ne'] using hx
    exact phaseDeriv2_nonneg hN ⟨hx'.1.le, hx'.2.le⟩

noncomputable def realCotTerm (x : ℝ) (n : ℕ) : ℝ :=
  1 / (x - (n + 1)) + 1 / (x + (n + 1))

noncomputable def negTerm (x : ℝ) (n : ℕ) : ℝ := 1 / (x - (n + 1))

noncomputable def posTerm (x : ℝ) (n : ℕ) : ℝ := 1 / (x + (n + 1))

lemma realCotTerm_eq (x : ℝ) (n : ℕ) :
    realCotTerm x n = negTerm x n + posTerm x n := rfl

lemma tendsto_negTerm_atTop (x : ℝ) : Tendsto (negTerm x) atTop (𝓝 0) := by
  have h := (tendsto_mul_add_inv_atTop_nhds_zero (-1) (x - 1) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  ext n
  unfold negTerm
  norm_num
  ring_nf

/-- Splitting an absolutely convergent paired series after unequal numbers of
negative and positive terms.  The proof uses partial sums; it never separates
the two divergent one-sided harmonic series. -/
lemma paired_tsum_split {a b : ℕ → ℝ} {L d : ℕ}
    (hab : Summable fun n ↦ a n + b n)
    (htail : Summable fun n ↦ a (L + n) + b (L + d + n))
    (ha0 : Tendsto a atTop (𝓝 0)) :
    (∑' n : ℕ, (a n + b n)) =
      (∑ n ∈ Finset.range L, a n) +
        (∑ n ∈ Finset.range (L + d), b n) +
          ∑' n : ℕ, (a (L + n) + b (L + d + n)) := by
  have hpartial (n : ℕ) :
      (∑ i ∈ Finset.range L, a i) +
          (∑ i ∈ Finset.range (L + d), b i) +
            (∑ i ∈ Finset.range n, (a (L + i) + b (L + d + i))) =
        (∑ i ∈ Finset.range (L + n), a i) +
          ∑ i ∈ Finset.range (L + d + n), b i := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show L + (n + 1) = (L + n) + 1 by omega,
          show L + d + (n + 1) = (L + d + n) + 1 by omega]
        rw [Finset.sum_range_succ
            (f := fun i ↦ a (L + i) + b (L + d + i)),
          Finset.sum_range_succ (f := a), Finset.sum_range_succ (f := b)]
        linear_combination ih
  have hblock : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range d, a (n + (L + j))) atTop (𝓝 0) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      tendsto_finsetSum (Finset.range d)
        (fun j _ ↦ ha0.comp (tendsto_add_atTop_nat (L + j)))
  have hpaired : Tendsto
      (fun n : ℕ ↦ ∑ i ∈ Finset.range (L + d + n), (a i + b i))
      atTop (𝓝 (∑' i : ℕ, (a i + b i))) := by
    have hc := hab.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat (L + d))
    refine hc.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    simp only [Function.comp_apply]
    rw [show n + (L + d) = L + d + n by omega]
  have hright : Tendsto
      (fun n : ℕ ↦ (∑ i ∈ Finset.range (L + n), a i) +
        ∑ i ∈ Finset.range (L + d + n), b i)
      atTop (𝓝 (∑' i : ℕ, (a i + b i))) := by
    have hident (n : ℕ) :
        (∑ i ∈ Finset.range (L + n), a i) +
            (∑ i ∈ Finset.range (L + d + n), b i) =
          (∑ i ∈ Finset.range (L + d + n), (a i + b i)) -
            ∑ j ∈ Finset.range d, a (n + (L + j)) := by
      rw [Finset.sum_add_distrib]
      have had : L + d + n = (L + n) + d := by omega
      have haSplit :
          (∑ i ∈ Finset.range ((L + n) + d), a i) =
            (∑ i ∈ Finset.range (L + n), a i) +
              ∑ j ∈ Finset.range d, a ((L + n) + j) := by
        rw [Finset.sum_range_add]
      rw [had, haSplit]
      simp only [show ∀ j : ℕ, (L + n) + j = n + (L + j) by omega]
      ring
    simpa only [sub_zero] using (hpaired.sub hblock).congr (fun n ↦ (hident n).symm)
  have hleft : Tendsto
      (fun n : ℕ ↦ (∑ i ∈ Finset.range L, a i) +
          (∑ i ∈ Finset.range (L + d), b i) +
            ∑ i ∈ Finset.range n, (a (L + i) + b (L + d + i)))
      atTop (𝓝 ((∑ i ∈ Finset.range L, a i) +
          (∑ i ∈ Finset.range (L + d), b i) +
            ∑' i : ℕ, (a (L + i) + b (L + d + i)))) :=
    (tendsto_const_nhds.add tendsto_const_nhds).add htail.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique (hleft.congr fun n ↦ hpartial n) hright |>.symm

lemma real_cot_series_rep' {x : ℝ} (hx : ∀ z : ℤ, x ≠ (z : ℝ)) :
    Real.pi * Real.cot (Real.pi * x) - 1 / x = ∑' n : ℕ, realCotTerm x n := by
  have hz : (x : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨z, hz⟩
    have hre := congrArg Complex.re hz
    simp only [Complex.intCast_re, Complex.ofReal_re] at hre
    exact hx z hre.symm
  have h := cot_series_rep' hz
  have hs := summable_cotTerm hz
  have hcot : Complex.cot ((Real.pi * x : ℝ) : ℂ) =
      (Real.cot (Real.pi * x) : ℂ) := by
    exact (Complex.ofReal_cot _).symm
  calc
    Real.pi * Real.cot (Real.pi * x) - 1 / x =
        ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (x : ℂ)) - 1 / (x : ℂ)).re := by
          have harg : (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) := by
            norm_num
          have hcplx :
              (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (x : ℂ)) - 1 / (x : ℂ) =
                ((Real.pi * Real.cot (Real.pi * x) - 1 / x : ℝ) : ℂ) := by
            rw [harg, hcot]
            norm_num
          exact (congrArg Complex.re hcplx).symm
    _ = (∑' n : ℕ, cotTerm (x : ℂ) n).re := congrArg Complex.re h
    _ = ∑' n : ℕ, (cotTerm (x : ℂ) n).re := Complex.re_tsum hs
    _ = ∑' n : ℕ, realCotTerm x n := by
      apply tsum_congr
      intro n
      have hc : cotTerm (x : ℂ) n = (realCotTerm x n : ℂ) := by
        norm_num [realCotTerm, cotTerm]
      exact congrArg Complex.re hc

lemma summable_realCotTerm {x : ℝ} (hx : ∀ z : ℤ, x ≠ (z : ℝ)) :
    Summable (realCotTerm x) := by
  have hz : (x : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨z, hz⟩
    have hre := congrArg Complex.re hz
    simp only [Complex.intCast_re, Complex.ofReal_re] at hre
    exact hx z hre.symm
  have hs := summable_cotTerm hz
  have hsc : Summable fun n : ℕ ↦ (realCotTerm x n : ℂ) := by
    apply hs.congr
    intro n
    norm_num [realCotTerm, cotTerm]
  exact Complex.summable_ofReal.mp hsc

lemma not_int_of_mem_Ioo_zero_one {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ z : ℤ, x ≠ (z : ℝ) := by
  intro z hz
  have hz0 : (0 : ℤ) < z := by
    exact_mod_cast (hz ▸ hx.1)
  have hz1 : z < (1 : ℤ) := by
    exact_mod_cast (hz ▸ hx.2)
  omega

lemma cot_eq_one_div_add_tsum {x : ℝ} (hx : ∀ z : ℤ, x ≠ (z : ℝ)) :
    Real.pi * Real.cot (Real.pi * x) = 1 / x + ∑' n : ℕ, realCotTerm x n := by
  linarith [real_cot_series_rep' hx]

/-- The unequal paired tail is exactly the rational phase remainder term. -/
lemma unequal_tail_eq_phaseKernel {N k m : ℕ} {τ : ℝ}
    (hk : k < N) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    negTerm τ (N - k + m) + posTerm τ (k + m) =
      -2 * ((k : ℝ) + τ - radius N) *
        phaseKernel N m ((k : ℝ) + τ - radius N) := by
  let A : ℝ := ((N - k + m : ℕ) : ℝ) + 1 - τ
  let B : ℝ := ((k + m : ℕ) : ℝ) + 1 + τ
  have hA : A ≠ 0 := by
    have hnm : (0 : ℝ) ≤ ((N - k + m : ℕ) : ℝ) := by positivity
    dsimp [A]
    linarith [hτ.2]
  have hB : B ≠ 0 := by
    have hkm : (0 : ℝ) ≤ ((k + m : ℕ) : ℝ) := by positivity
    dsimp [B]
    linarith [hτ.1]
  have hden :
      (((m : ℝ) + shift N) ^ 2 - ((k : ℝ) + τ - radius N) ^ 2) = A * B := by
    dsimp [A, B, shift, radius]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hk.le]
    ring
  rw [phaseKernel_eq]
  rw [hden]
  unfold negTerm posTerm
  have hnegA : τ - (((N - k + m : ℕ) : ℝ) + 1) = -A := by
    dsimp [A]
    ring
  have hposB : τ + (((k + m : ℕ) : ℝ) + 1) = B := by
    dsimp [B]
    ring
  rw [hnegA, hposB]
  field_simp [hA, hB]
  dsimp [A, B, radius]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hk.le]
  ring

lemma summable_unequal_tail {N k : ℕ} {τ : ℝ}
    (hk : k < N) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    Summable fun m : ℕ ↦ negTerm τ (N - k + m) + posTerm τ (k + m) := by
  let u : ℝ := (k : ℝ) + τ - radius N
  have hu : u ∈ Set.Icc (-radius N) (radius N) := by
    dsimp [u, radius]
    constructor
    · have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith [hτ.1]
    · have hkc : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk.le
      have hk1 : k + 1 ≤ N := hk
      have hk1c : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk1
      linarith [hτ.2]
  rcases phase_parameters_of_mem_Icc hu with ⟨hp, hq⟩
  have hs : Summable fun m : ℕ ↦ phaseKernel N m u := by
    simpa [phaseKernel] using summable_kernel hp hq
  have hmul : Summable fun m : ℕ ↦ -2 * u * phaseKernel N m u :=
    hs.mul_left (-2 * u)
  apply hmul.congr
  intro m
  dsimp [u]
  exact (unequal_tail_eq_phaseKernel hk hτ).symm

/-- Mittag--Leffler decomposition of the finite logarithmic derivative on the
right half. -/
lemma finite_logarithmic_sum_eq_cot_add_phase {N k : ℕ} {τ : ℝ}
    (hk : k < N) (hhalf : N ≤ 2 * k) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    1 / τ + (∑ n ∈ Finset.range (N - k), negTerm τ n) +
        (∑ n ∈ Finset.range k, posTerm τ n) =
      Real.pi * Real.cot (Real.pi * τ) +
        phaseRemainder N ((k : ℝ) + τ - radius N) := by
  let L := N - k
  let d := 2 * k - N
  have hLd : L + d = k := by dsimp [L, d]; omega
  have hsplit := paired_tsum_split
    (a := negTerm τ) (b := posTerm τ) (L := L) (d := d)
    (by
      simpa only [← realCotTerm_eq] using
        summable_realCotTerm (not_int_of_mem_Ioo_zero_one hτ))
    (by
      simpa only [hLd] using
        summable_unequal_tail (N := N) (k := k) hk hτ)
    (tendsto_negTerm_atTop τ)
  have hcot := cot_eq_one_div_add_tsum (not_int_of_mem_Ioo_zero_one hτ)
  have htail :
      (∑' n : ℕ, (negTerm τ (L + n) + posTerm τ (L + d + n))) =
        -phaseRemainder N ((k : ℝ) + τ - radius N) := by
    rw [hLd]
    rw [show L = N - k by rfl]
    calc
      (∑' n : ℕ, (negTerm τ (N - k + n) + posTerm τ (k + n))) =
          ∑' n : ℕ, (-2 * ((k : ℝ) + τ - radius N) *
            phaseKernel N n ((k : ℝ) + τ - radius N)) := by
              apply tsum_congr
              intro n
              exact unequal_tail_eq_phaseKernel hk hτ
      _ = -2 * ((k : ℝ) + τ - radius N) *
          ∑' n : ℕ, phaseKernel N n ((k : ℝ) + τ - radius N) := by
            rw [← tsum_mul_left]
      _ = -phaseRemainder N ((k : ℝ) + τ - radius N) := by
            unfold phaseRemainder moment
            simp only [pow_one]
            ring
  rw [hLd] at hsplit
  have htail' :
      (∑' n : ℕ, (negTerm τ (L + n) + posTerm τ (k + n))) =
        -phaseRemainder N ((k : ℝ) + τ - radius N) := by
    simpa only [hLd] using htail
  rw [htail'] at hsplit
  rw [show (∑' n : ℕ, realCotTerm τ n) =
      ∑' n : ℕ, (negTerm τ n + posTerm τ n) by
        apply tsum_congr
        exact realCotTerm_eq τ] at hcot
  rw [hsplit] at hcot
  dsimp [L] at hcot ⊢
  linarith

lemma neg_cot_eq_tan_sub_pi_div_two (x : ℝ) :
    -Real.cot x = Real.tan (x - Real.pi / 2) := by
  rw [show x - Real.pi / 2 = -(Real.pi / 2 - x) by ring]
  rw [Real.tan_neg, Real.tan_pi_div_two_sub, Real.tan_inv_eq_cot]

/-- At a zero of the finite logarithmic derivative, the phase is the
fractional displacement from the midpoint of the unit interval. -/
lemma phase_eq_sub_half_of_critical {N k : ℕ} {τ : ℝ}
    (hk : k < N) (hhalf : N ≤ 2 * k) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (hcrit : 1 / τ + (∑ n ∈ Finset.range (N - k), negTerm τ n) +
      (∑ n ∈ Finset.range k, posTerm τ n) = 0) :
    phase N ((k : ℝ) + τ - radius N) = τ - 1 / 2 := by
  have hdecomp := finite_logarithmic_sum_eq_cot_add_phase hk hhalf hτ
  have hg : phaseRemainder N ((k : ℝ) + τ - radius N) =
      -Real.pi * Real.cot (Real.pi * τ) := by
    linarith
  have hratio : phaseRemainder N ((k : ℝ) + τ - radius N) / Real.pi =
      -Real.cot (Real.pi * τ) := by
    rw [hg]
    field_simp [Real.pi_ne_zero]
  let y : ℝ := Real.pi * τ - Real.pi / 2
  have hy₁ : -(Real.pi / 2) < y := by
    dsimp [y]
    nlinarith [Real.pi_pos, hτ.1]
  have hy₂ : y < Real.pi / 2 := by
    dsimp [y]
    nlinarith [Real.pi_pos, hτ.2]
  unfold phase
  rw [hratio, neg_cot_eq_tan_sub_pi_div_two,
    Real.arctan_tan hy₁ hy₂]
  dsimp [y]
  field_simp [Real.pi_ne_zero]

lemma phase_zero (N : ℕ) : phase N 0 = 0 := by
  unfold phase phaseRemainder
  simp

noncomputable def centered (N : ℕ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  b k - radius N

/-- Phase equation stated directly for an indexed critical point. -/
lemma phase_centered_eq {N k : ℕ} {b : ℕ → ℝ}
    (hk : k < N) (hhalf : N ≤ 2 * k)
    (hb : b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hcrit : 1 / (b k - k) +
      (∑ n ∈ Finset.range (N - k), negTerm (b k - k) n) +
      (∑ n ∈ Finset.range k, posTerm (b k - k) n) = 0) :
    phase N (centered N b k) = b k - k - 1 / 2 := by
  have hτ : b k - (k : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hb.1, hb.2]
  have h := phase_eq_sub_half_of_critical hk hhalf hτ hcrit
  unfold centered at h ⊢
  ring_nf at h ⊢
  exact h

lemma indexed_points_strictMono {N : ℕ} {b : ℕ → ℝ}
    (hb : ∀ k, k < N → b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    {i j : ℕ} (hj : j < N) (hij : i < j) : b i < b j := by
  have hi : i < N := hij.trans hj
  have hbi := hb i hi
  have hbj := hb j hj
  have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
  linarith [hbi.2, hbj.1]

lemma centered_nonneg_of_right {N : ℕ} {b : ℕ → ℝ}
    (hb : ∀ k, k < N → b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hsymm : ∀ k, k < N → b (N - 1 - k) = (N : ℝ) - b k)
    {k : ℕ} (hk : k < N) (hright : N ≤ 2 * k + 1) :
    0 ≤ centered N b k := by
  let j := N - 1 - k
  have hj : j < N := by dsimp [j]; omega
  have hjk : j ≤ k := by dsimp [j]; omega
  have horder : b j ≤ b k := by
    by_cases heq : j = k
    · rw [heq]
    · exact (indexed_points_strictMono hb hk (lt_of_le_of_ne hjk heq)).le
  have hs := hsymm k hk
  change b j = (N : ℝ) - b k at hs
  unfold centered radius
  linarith

lemma centered_le_radius {N : ℕ} {b : ℕ → ℝ}
    (hb : ∀ k, k < N → b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    {k : ℕ} (hk : k < N) : centered N b k ≤ radius N := by
  have hbk := hb k hk
  have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
  unfold centered radius
  linarith [hbk.2]

lemma phase_centered_eq_of_right_or_center {N k : ℕ} {b : ℕ → ℝ}
    (hk : k < N) (hright : N ≤ 2 * k + 1)
    (hb : ∀ j, j < N → b j ∈ Set.Ioo (j : ℝ) ((j : ℝ) + 1))
    (hcrit : ∀ j, j < N →
      1 / (b j - j) +
        (∑ n ∈ Finset.range (N - j), negTerm (b j - j) n) +
        (∑ n ∈ Finset.range j, posTerm (b j - j) n) = 0)
    (hsymm : ∀ j, j < N → b (N - 1 - j) = (N : ℝ) - b j) :
    phase N (centered N b k) = b k - k - 1 / 2 := by
  by_cases hhalf : N ≤ 2 * k
  · exact phase_centered_eq hk hhalf (hb k hk) (hcrit k hk)
  · have hodd : N = 2 * k + 1 := by omega
    have hs := hsymm k hk
    have hindex : N - 1 - k = k := by omega
    rw [hindex] at hs
    have hcenter : centered N b k = 0 := by
      unfold centered radius
      rw [hodd] at hs ⊢
      norm_num at hs ⊢
      linarith
    rw [hcenter, phase_zero]
    rw [hodd] at hs
    norm_num at hs ⊢
    linarith

/-- Analytic gap theorem for the canonical equally spaced zero set.  The
hypotheses are precisely the interval location, logarithmic-derivative
equation, and reflection identity that will be derived from the polynomial. -/
theorem canonical_gap_theorem {N : ℕ} (hN : 0 < N) {b : ℕ → ℝ}
    (hb : ∀ k, k < N → b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hcrit : ∀ k, k < N →
      1 / (b k - k) +
        (∑ n ∈ Finset.range (N - k), negTerm (b k - k) n) +
        (∑ n ∈ Finset.range k, posTerm (b k - k) n) = 0)
    (hsymm : ∀ k, k < N → b (N - 1 - k) = (N : ℝ) - b k) :
    RightGapMonotone N b := by
  intro i hi hright
  have hi0 : i < N := by omega
  have hi1 : i + 1 < N := by omega
  have hi2 : i + 2 < N := hi
  have h01 : centered N b i < centered N b (i + 1) := by
    unfold centered
    linarith [indexed_points_strictMono hb hi1 (by omega : i < i + 1)]
  have h12 : centered N b (i + 1) < centered N b (i + 2) := by
    unfold centered
    linarith [indexed_points_strictMono hb hi2 (by omega : i + 1 < i + 2)]
  have hphase1 := phase_centered_eq_of_right_or_center hi1
    (by omega : N ≤ 2 * (i + 1) + 1) hb hcrit hsymm
  have hphase2 := phase_centered_eq_of_right_or_center hi2
    (by omega : N ≤ 2 * (i + 2) + 1) hb hcrit hsymm
  by_cases heven : N = 2 * (i + 1)
  · have hy0 : 0 < centered N b (i + 1) := by
      have hbi := (hb (i + 1) hi1).1
      unfold centered radius
      rw [heven]
      norm_num [Nat.cast_add] at hbi ⊢
      exact hbi
    have hzmem : centered N b (i + 2) ∈ Set.Icc 0 (radius N) :=
      ⟨centered_nonneg_of_right hb hsymm hi2 (by omega), centered_le_radius hb hi2⟩
    have hslope := (phase_convexOn hN).slope_mono_adjacent
      (show (0 : ℝ) ∈ Set.Icc 0 (radius N) by
        constructor
        · exact le_rfl
        · unfold radius; positivity)
      hzmem hy0 h12
    have hphase0 := phase_zero N
    have hgap1 : b (i + 1) - b i = 2 * centered N b (i + 1) := by
      have hs := hsymm (i + 1) hi1
      have hindex : N - 1 - (i + 1) = i := by omega
      rw [hindex, heven] at hs
      unfold centered radius
      rw [heven]
      norm_num at hs ⊢
      linarith
    have hgap2pos : 0 < b (i + 2) - b (i + 1) :=
      sub_pos.mpr (indexed_points_strictMono hb hi2 (by omega))
    rw [hphase0, hphase1, hphase2] at hslope
    have hden2 : centered N b (i + 2) - centered N b (i + 1) =
        b (i + 2) - b (i + 1) := by unfold centered; ring
    rw [hden2] at hslope
    have hyEq : centered N b (i + 1) = b (i + 1) - (i + 1) := by
      unfold centered radius
      rw [heven]
      norm_num
    rw [hyEq] at hslope
    have hden1 : 0 < b (i + 1) - (i + 1) := by linarith [hy0]
    norm_num [Nat.cast_add] at hslope
    rw [div_le_div_iff₀ hden1 hgap2pos] at hslope
    rw [hgap1]
    nlinarith
  · have hNi : N ≤ 2 * i + 1 := by omega
    have hxmem : centered N b i ∈ Set.Icc 0 (radius N) :=
      ⟨centered_nonneg_of_right hb hsymm hi0 hNi, centered_le_radius hb hi0⟩
    have hzmem : centered N b (i + 2) ∈ Set.Icc 0 (radius N) :=
      ⟨centered_nonneg_of_right hb hsymm hi2 (by omega), centered_le_radius hb hi2⟩
    have hphase0 := phase_centered_eq_of_right_or_center hi0 hNi hb hcrit hsymm
    have hslope := (phase_convexOn hN).slope_mono_adjacent hxmem hzmem h01 h12
    rw [hphase0, hphase1, hphase2] at hslope
    have hden1 : centered N b (i + 1) - centered N b i =
        b (i + 1) - b i := by unfold centered; ring
    have hden2 : centered N b (i + 2) - centered N b (i + 1) =
        b (i + 2) - b (i + 1) := by unfold centered; ring
    rw [hden1, hden2] at hslope
    have hgap1pos : 0 < b (i + 1) - b i :=
      sub_pos.mpr (indexed_points_strictMono hb hi1 (by omega))
    have hgap2pos : 0 < b (i + 2) - b (i + 1) :=
      sub_pos.mpr (indexed_points_strictMono hb hi2 (by omega))
    rw [div_le_div_iff₀ hgap1pos hgap2pos] at hslope
    norm_num [Nat.cast_add] at hslope
    nlinarith

noncomputable def reciprocalSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), 1 / (x - j)

lemma reciprocal_term_strictAnti {k j : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hy : y ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1)) (hxy : x < y) :
    1 / (y - j) < 1 / (x - j) := by
  have hxne : x - (j : ℝ) ≠ 0 := by
    rcases le_or_gt j k with hjk | hkj
    · have hc : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      linarith [hx.1]
    · have hc : (k : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkj)
      linarith [hx.2]
  have hyne : y - (j : ℝ) ≠ 0 := by
    rcases le_or_gt j k with hjk | hkj
    · have hc : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      linarith [hy.1]
    · have hc : (k : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkj)
      linarith [hy.2]
  have hprod : 0 < (x - (j : ℝ)) * (y - (j : ℝ)) := by
    rcases le_or_gt j k with hjk | hkj
    · have hc : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      exact mul_pos (by linarith [hx.1]) (by linarith [hy.1])
    · have hc : (k : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkj)
      exact mul_pos_of_neg_of_neg (by linarith [hx.2]) (by linarith [hy.2])
  rw [← sub_pos]
  have hid : 1 / (x - (j : ℝ)) - 1 / (y - (j : ℝ)) =
      (y - x) / ((x - (j : ℝ)) * (y - (j : ℝ))) := by
    field_simp [hxne, hyne]
    ring
  rw [hid]
  exact div_pos (sub_pos.mpr hxy) hprod

lemma reciprocalSum_strictAnti_on_interval {N k : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hy : y ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1)) (hxy : x < y) :
    reciprocalSum N y < reciprocalSum N x := by
  unfold reciprocalSum
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  · intro j hj
    exact reciprocal_term_strictAnti hx hy hxy

lemma reciprocalSum_injective_on_interval {N k : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hy : y ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hs : reciprocalSum N x = reciprocalSum N y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := reciprocalSum_strictAnti_on_interval (N := N) hx hy hxy
    linarith
  · exact hxy
  · have := reciprocalSum_strictAnti_on_interval (N := N) hy hx hxy
    linarith

lemma reciprocalSum_reflect (N : ℕ) (x : ℝ) :
    reciprocalSum N ((N : ℝ) - x) = -reciprocalSum N x := by
  unfold reciprocalSum
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_range_reflect (fun j : ℕ ↦ 1 / ((N : ℝ) - x - j)) (N + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := by simpa [Finset.mem_range] using hj
  have hcast : (((N + 1 - 1 - j : ℕ) : ℝ)) = (N : ℝ) - (j : ℝ) := by
    norm_num
    rw [Nat.cast_sub hjN]
  rw [hcast]
  have hden : (N : ℝ) - x - ((N : ℝ) - (j : ℝ)) = (j : ℝ) - x := by ring
  rw [hden]
  simp only [one_div]
  rw [show (j : ℝ) - x = -(x - (j : ℝ)) by ring, inv_neg]

lemma sum_range_left_part (k : ℕ) (τ : ℝ) :
    (∑ j ∈ Finset.range (k + 1), 1 / ((k : ℝ) + τ - j)) =
      1 / τ + ∑ n ∈ Finset.range k, posTerm τ n := by
  rw [Finset.sum_range_succ]
  rw [add_comm]
  congr 1
  · norm_num
  · rw [← Finset.sum_range_reflect
      (fun j : ℕ ↦ 1 / ((k : ℝ) + τ - j)) k]
    apply Finset.sum_congr rfl
    intro n hn
    have hnk : n < k := Finset.mem_range.mp hn
    unfold posTerm
    congr 1
    rw [Nat.cast_sub (by omega : n ≤ k - 1)]
    have hkcast : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    linarith

/-- Reindex the finite reciprocal sum around the interval `(k,k+1)`. -/
lemma reciprocalSum_eq_decomposed {N k : ℕ} (hk : k < N) (τ : ℝ) :
    reciprocalSum N ((k : ℝ) + τ) =
      1 / τ + (∑ n ∈ Finset.range (N - k), negTerm τ n) +
        ∑ n ∈ Finset.range k, posTerm τ n := by
  unfold reciprocalSum
  have hsize : N + 1 = (k + 1) + (N - k) := by omega
  rw [hsize, Finset.sum_range_add]
  have hleft := sum_range_left_part k τ
  rw [hleft]
  have hright :
      (∑ n ∈ Finset.range (N - k),
        1 / ((k : ℝ) + τ - (((k + 1) + n : ℕ) : ℝ))) =
        ∑ n ∈ Finset.range (N - k), negTerm τ n := by
    apply Finset.sum_congr rfl
    intro n hn
    unfold negTerm
    congr 1
    push_cast
    ring
  rw [hright]
  ring

lemma canonical_symmetry_of_reciprocal_zeros {N : ℕ} {b : ℕ → ℝ}
    (hb : ∀ k, k < N → b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1))
    (hzero : ∀ k, k < N → reciprocalSum N (b k) = 0) :
    ∀ k, k < N → b (N - 1 - k) = (N : ℝ) - b k := by
  intro k hk
  let j := N - 1 - k
  have hj : j < N := by dsimp [j]; omega
  have hjinterval := hb j hj
  have hrefinterval : (N : ℝ) - b k ∈
      Set.Ioo (j : ℝ) ((j : ℝ) + 1) := by
    have hbk := hb k hk
    have hcastj : (j : ℝ) = (N : ℝ) - 1 - (k : ℝ) := by
      dsimp [j]
      rw [Nat.cast_sub (by omega : k ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N)]
      norm_num
    rw [hcastj]
    constructor <;> linarith [hbk.1, hbk.2]
  apply reciprocalSum_injective_on_interval hjinterval hrefinterval
  rw [hzero j hj, reciprocalSum_reflect, hzero k hk]
  simp

open Polynomial

/-- Product polynomial with a prescribed finite list of roots. -/
noncomputable def rootPolynomial (r : ℕ → ℝ) (s : Finset ℕ) : ℝ[X] :=
  ∏ j ∈ s, (X - C (r j))

/-- Logarithmic derivative identity for a finite product, away from its roots. -/
lemma eval_rootPolynomial_derivative {r : ℕ → ℝ} {s : Finset ℕ} {x : ℝ}
    (hx : ∀ j ∈ s, x ≠ r j) :
    eval x (rootPolynomial r s).derivative =
      eval x (rootPolynomial r s) * ∑ j ∈ s, 1 / (x - r j) := by
  classical
  unfold rootPolynomial
  rw [derivative_prod_finset]
  simp only [eval_finsetSum, derivative_X_sub_C, mul_one,
    eval_prod, eval_sub, eval_X, eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hne : x - r j ≠ 0 := sub_ne_zero.mpr (hx j hj)
  have hprod := Finset.prod_erase_mul s (fun t ↦ x - r t) hj
  calc
    ∏ t ∈ s.erase j, (x - r t) =
        ((∏ t ∈ s.erase j, (x - r t)) * (x - r j)) * (1 / (x - r j)) := by
          field_simp [hne]
    _ = (∏ t ∈ s, (x - r t)) * (1 / (x - r j)) := by rw [hprod]

noncomputable def arithmeticProgressionPolynomial
    (N : ℕ) (a d : ℝ) : ℝ[X] :=
  rootPolynomial (fun j ↦ a + d * j) (Finset.range (N + 1))

noncomputable def normalizePoint (a d : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  (b k - a) / d

lemma normalizePoint_mem_interval {k : ℕ} {a d : ℝ} {b : ℕ → ℝ}
    (hd : 0 < d) (hb : b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1))) :
    normalizePoint a d b k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) := by
  unfold normalizePoint
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith [hb.1]
  · rw [div_lt_iff₀ hd]
    nlinarith [hb.2]

lemma point_ne_progression_root {k j : ℕ} {a d x : ℝ}
    (hd : 0 < d)
    (hx : x ∈ Set.Ioo (a + d * k) (a + d * (k + 1))) :
    x ≠ a + d * j := by
  rcases le_or_gt j k with hjk | hkj
  · have hjkc : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    intro heq
    rw [heq] at hx
    have hle : a + d * (j : ℝ) ≤ a + d * (k : ℝ) := by gcongr
    exact (not_lt_of_ge hle) hx.1
  · have hjkc : (k : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hkj)
    intro heq
    rw [heq] at hx
    have hle : a + d * ((k : ℝ) + 1) ≤ a + d * (j : ℝ) := by gcongr
    exact (not_lt_of_ge hle) hx.2

/-- A derivative zero of the factored arithmetic-progression polynomial gives
the normalized reciprocal equation used in the analytic theorem. -/
lemma normalized_reciprocalSum_eq_zero {N k : ℕ} {a d c : ℝ}
    (hd : 0 < d) (hc : c ≠ 0)
    {f : ℝ[X]} {b : ℕ → ℝ}
    (hf : f = C c * arithmeticProgressionPolynomial N a d)
    (hb : b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : eval (b k) f.derivative = 0) :
    reciprocalSum N (normalizePoint a d b k) = 0 := by
  let r : ℕ → ℝ := fun j ↦ a + d * j
  have hne : ∀ j ∈ Finset.range (N + 1), b k ≠ r j := by
    intro j hj
    exact point_ne_progression_root hd hb
  have hlog := eval_rootPolynomial_derivative (r := r) (x := b k) hne
  have hfroot : arithmeticProgressionPolynomial N a d =
      rootPolynomial r (Finset.range (N + 1)) := by rfl
  have hPderiv : eval (b k) (arithmeticProgressionPolynomial N a d).derivative = 0 := by
    rw [hf] at hderiv
    have hcder : c * eval (b k) (arithmeticProgressionPolynomial N a d).derivative = 0 := by
      simpa [derivative_mul] using hderiv
    exact (mul_eq_zero.mp hcder).resolve_left hc
  rw [hfroot] at hPderiv
  rw [hlog] at hPderiv
  have hPeval : eval (b k) (rootPolynomial r (Finset.range (N + 1))) ≠ 0 := by
    unfold rootPolynomial
    simp only [eval_prod, eval_sub, eval_X, eval_C, Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.mpr (hne j hj)
  have hsum : (∑ j ∈ Finset.range (N + 1), 1 / (b k - r j)) = 0 :=
    (mul_eq_zero.mp hPderiv).resolve_left hPeval
  have hscale :
      (∑ j ∈ Finset.range (N + 1), 1 / (b k - r j)) =
        (1 / d) * reciprocalSum N (normalizePoint a d b k) := by
    unfold reciprocalSum normalizePoint
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [r]
    have hd0 : d ≠ 0 := hd.ne'
    field_simp [hd0]
    ring
  rw [hscale] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (one_div_ne_zero hd.ne')

/-- A degree `N+1` nonzero polynomial vanishing at all `N+1` distinct
progression points is its leading coefficient times the progression product. -/
lemma eq_progression_factorization {N : ℕ} {a d : ℝ} (hd : 0 < d)
    {f : ℝ[X]} (hf0 : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j, j ≤ N → eval (a + d * j) f = 0) :
    f = C f.leadingCoeff * arithmeticProgressionPolynomial N a d := by
  classical
  let r : ℕ → ℝ := fun j ↦ a + d * j
  let S : Multiset ℝ := (Finset.range (N + 1)).1.map r
  have hrinj : Function.Injective r := by
    intro i j hij
    dsimp [r] at hij
    have hmul : d * (i : ℝ) = d * (j : ℝ) := by linarith
    have hc : (i : ℝ) = (j : ℝ) := mul_left_cancel₀ hd.ne' hmul
    exact_mod_cast hc
  have hSnodup : S.Nodup := by
    dsimp [S]
    exact (Finset.range (N + 1)).2.map hrinj
  have hSle : S ≤ f.roots := by
    rw [Multiset.le_iff_subset hSnodup]
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨j, hj, rfl⟩
    rw [mem_roots hf0]
    apply hroots j
    have hj' : j = N ∨ j < N := by simpa using hj
    omega
  have hdvdS := (Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 S).2 hSle
  have hdvd : arithmeticProgressionPolynomial N a d ∣ f := by
    have heq : (S.map fun x ↦ X - C x).prod =
        rootPolynomial r (Finset.range (N + 1)) := by
      dsimp [S, rootPolynomial]
      rw [Multiset.map_map]
      rfl
    rw [heq] at hdvdS
    simpa [arithmeticProgressionPolynomial, r] using hdvdS
  have hmonic : (arithmeticProgressionPolynomial N a d).Monic := by
    unfold arithmeticProgressionPolynomial rootPolynomial
    exact monic_prod_X_sub_C _ _
  have hpdeg : (arithmeticProgressionPolynomial N a d).natDegree = N + 1 := by
    simpa [arithmeticProgressionPolynomial, rootPolynomial] using
      (natDegree_finsetProd_X_sub_C_eq_card
        (R := ℝ) (Finset.range (N + 1)) (fun j : ℕ ↦ a + d * j))
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmonic hdvd
  rw [hdegree, hpdeg]

/-- Full affine form of Erdős Problem 1114.  The factorization hypothesis is
the exact algebraic formulation of a nonzero polynomial whose `N+1` simple
zeros are the arithmetic progression `a + d*j`, `0 ≤ j ≤ N`.  The family `b`
lists the derivative zero in each consecutive root interval. -/
theorem erdos_1114_full {N : ℕ} (hN : 0 < N) {a d c : ℝ}
    (hd : 0 < d) (hc : c ≠ 0) {f : ℝ[X]} {b : ℕ → ℝ}
    (hf : f = C c * arithmeticProgressionPolynomial N a d)
    (hb : ∀ k, k < N →
      b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : ∀ k, k < N → eval (b k) f.derivative = 0) :
    RightGapMonotone N b ∧ GapSymmetric N b := by
  let β : ℕ → ℝ := normalizePoint a d b
  have hβinterval : ∀ k, k < N →
      β k ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) := by
    intro k hk
    exact normalizePoint_mem_interval hd (hb k hk)
  have hβzero : ∀ k, k < N → reciprocalSum N (β k) = 0 := by
    intro k hk
    exact normalized_reciprocalSum_eq_zero hd hc hf (hb k hk) (hderiv k hk)
  have hβsymm : ∀ k, k < N → β (N - 1 - k) = (N : ℝ) - β k :=
    canonical_symmetry_of_reciprocal_zeros hβinterval hβzero
  have hβcrit : ∀ k, k < N →
      1 / (β k - k) +
        (∑ n ∈ Finset.range (N - k), negTerm (β k - k) n) +
        (∑ n ∈ Finset.range k, posTerm (β k - k) n) = 0 := by
    intro k hk
    have hz := hβzero k hk
    rw [show β k = (k : ℝ) + (β k - k) by ring] at hz
    rw [reciprocalSum_eq_decomposed hk] at hz
    exact hz
  have hβgap := canonical_gap_theorem hN hβinterval hβcrit hβsymm
  constructor
  · intro i hi hright
    have hg := hβgap i hi hright
    have hleft : β (i + 1) - β i = (b (i + 1) - b i) / d := by
      dsimp [β, normalizePoint]
      ring
    have hright' : β (i + 2) - β (i + 1) =
        (b (i + 2) - b (i + 1)) / d := by
      dsimp [β, normalizePoint]
      ring
    rw [hleft, hright', div_le_div_iff_of_pos_right hd] at hg
    exact hg
  · intro i hi
    have hi0 : i < N := by omega
    have hi1 : i + 1 < N := hi
    have hs0 := hβsymm i hi0
    have hs1 := hβsymm (i + 1) hi1
    have hindex : N - 1 - (i + 1) = N - 2 - i := by omega
    rw [hindex] at hs1
    have hβgaps : β (i + 1) - β i =
        β (N - 1 - i) - β (N - 2 - i) := by linarith
    dsimp [β, normalizePoint] at hβgaps
    have hd0 : d ≠ 0 := hd.ne'
    field_simp [hd0] at hβgaps
    linarith

/-- Erdős Problem 1114: consecutive derivative gaps, read from the midpoint
towards the right endpoint, are nondecreasing.  Reflection (the second
component of `erdos_1114_full`) gives the identical assertion on the left. -/
theorem erdos_1114_of_factorization {N : ℕ} (hN : 0 < N) {a d c : ℝ}
    (hd : 0 < d) (hc : c ≠ 0) {f : ℝ[X]} {b : ℕ → ℝ}
    (hf : f = C c * arithmeticProgressionPolynomial N a d)
    (hb : ∀ k, k < N →
      b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : ∀ k, k < N → eval (b k) f.derivative = 0) :
    RightGapMonotone N b :=
  (erdos_1114_full hN hd hc hf hb hderiv).1

/-- Erdős Problem 1114 in the literal roots-and-degree formulation. -/
theorem erdos_1114 {N : ℕ} (hN : 0 < N) {a d : ℝ}
    (hd : 0 < d) {f : ℝ[X]} {b : ℕ → ℝ}
    (hf0 : f ≠ 0) (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j, j ≤ N → eval (a + d * j) f = 0)
    (hb : ∀ k, k < N →
      b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : ∀ k, k < N → eval (b k) f.derivative = 0) :
    RightGapMonotone N b ∧ GapSymmetric N b := by
  have hfactor := eq_progression_factorization hd hf0 hdegree hroots
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  exact erdos_1114_full hN hd hlc hfactor hb hderiv

#print axioms erdos_1114

end Erdos1114
