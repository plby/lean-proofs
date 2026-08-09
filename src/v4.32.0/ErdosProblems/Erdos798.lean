/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 798.
https://www.erdosproblems.com/forum/thread/798

Informal authors:
- Noga Alon

Formal authors:
- Aristotle
- Parcly Taxel

URLs:
- https://www.erdosproblems.com/forum/thread/798#post-6329
- https://gist.githubusercontent.com/Parcly-Taxel/757ca8323d74784da1a776795b9c90a9/raw/3a9724b1f6cd2504b809cf3c66f843b89d375e8b/Erdos798.lean
-/
import Mathlib

namespace Erdos798


noncomputable section

open Finset Int Real Filter Topology

variable {d : ℕ} [d.AtLeastTwo] {v : Fin d → ℤ}

-- Lattice points are represented as vectors `Fin d → ℤ`.

/-- The side-`n` cube from which we may take points. -/
def cube (d n : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ ↦ Icc 1 n

section MaxAbs

variable (v) in
/-- An index for which the given tuple of integers attains a maximal absolute value. -/
def maxAbsIdx : Fin d :=
  (Finset.univ.exists_maximalFor (fun i ↦ (v i).natAbs) (by simp)).choose

variable (v) in
/-- The maximum absolute value of a tuple of integers. -/
def maxAbs : ℕ :=
  Finset.univ.sup fun i ↦ (v i).natAbs

/-- Proved by Aristotle -/
lemma natAbs_maxAbsIdx : (v (maxAbsIdx v)).natAbs = maxAbs v := by
  apply le_antisymm
  · exact le_sup (f := fun i ↦ (v i).natAbs) (mem_univ _)
  · refine Finset.sup_le fun i _ ↦ ?_
    have : MaximalFor _ _ (maxAbsIdx v) := (Finset.univ.exists_maximalFor _ (by simp)).choose_spec
    replace this := this.2
    grind

omit [d.AtLeastTwo] in
/-- Proved by Aristotle -/
lemma maxAbs_eq_zero_iff_eq_zero : maxAbs v = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> simp_all [funext_iff, maxAbs]

end MaxAbs

/-- A fraction that frequently appears in the proof. -/
def K (d : ℕ) : ℝ := (d - 1) / (2 * d - 1)

variable (d) in
lemma K_pos : 0 < K d := by
  apply div_pos <;> norm_cast <;> grind [‹d.AtLeastTwo›.one_lt]

variable (d) in
lemma K_lt_half : K d < 2⁻¹ := by
  have hd := ‹d.AtLeastTwo›.one_lt
  apply lt_inv_of_lt_inv₀ zero_lt_two
  rw [K, inv_div, lt_div_iff₀ (by simpa)]
  linarith

variable (d) in
lemma K_lt_one : K d < 1 := by linarith [K_lt_half d]

/-! ### Lemma 3.1 -/

variable (v) in
/-- The collection of variables and properties guaranteed by Lemma 3.1. -/
structure ShortApprox (n : ℕ) where
  /-- A vector `p` of integers -/
  p : Fin d → ℤ
  /-- A real number `z` -/
  z : ℝ
  /-- The special index `j` -/
  j : Fin d
  /-- `p`'s maximum absolute value is in `[1, n^K(d)]`, i.e. `p` is "short" -/
  maxAbs_p_mem_Icc : ↑(maxAbs p) ∈ Set.Icc 1 (n ^ K d : ℝ)
  /-- `p * z` approximates `v` well -/
  abs_sub_le (i) : |v i - p i * z| ≤ 2 * n ^ (2 * K d) / maxAbs p
  /-- `p` equals its maximum absolute value at index `j` -/
  p_j : p j = maxAbs p
  /-- The approximation `p * z` is exact at index `j` -/
  exact_j : v j = p j * z

variable (v) in
/-- `α_i` in the paper. -/
def mults (i : Fin d) : ℝ := v i / v (maxAbsIdx v)

/-- Proved by Aristotle -/
lemma abs_mults_le {i : Fin d} : |mults v i| ≤ 1 := by
  unfold mults
  norm_num [abs_div]
  refine div_le_one_of_le₀ ?_ (abs_nonneg _)
  have h_abs_ge (i) : (v i).natAbs ≤ (v (maxAbsIdx v)).natAbs := by
    rw [natAbs_maxAbsIdx]
    exact le_sup (f := fun i ↦ (v i).natAbs) (mem_univ _)
  exact_mod_cast Int.le_of_lt_add_one (by grind)

lemma mults_maxAbsIdx_eq_one (hv : v ≠ 0) : mults v (maxAbsIdx v) = 1 := by
  apply div_self
  rw [cast_ne_zero, ← natAbs_ne_zero, natAbs_maxAbsIdx]
  simpa [maxAbs_eq_zero_iff_eq_zero]

lemma floor_mul_sub_floor_mul {x y : ℕ} {a : ℝ} (hxy : x ≤ y) (ha : |a| ≤ 1) :
    (⌊a * y⌋ - ⌊a * x⌋).natAbs ≤ y - x := by
  obtain nn | nn := le_total 0 a
  · have : 0 ≤ ⌊a * y⌋ - ⌊a * x⌋ :=
      sub_nonneg_of_le <| Int.floor_mono <| mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hxy) nn
    rw [← ofNat_le, ofNat_natAbs_of_nonneg this, Nat.cast_sub hxy, sub_le_iff_le_add']
    apply le_of_lt_add_one
    simp_rw [floor_lt, cast_add, cast_one, cast_sub, cast_natCast]
    have l₁ := lt_floor_add_one (a * x)
    have l₂ := abs_le.mp ha
    nlinarith [show (x : ℝ) ≤ y by norm_cast]
  · have : ⌊a * y⌋ - ⌊a * x⌋ ≤ 0 :=
      sub_nonpos_of_le <| Int.floor_mono <| mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hxy) nn
    rw [← ofNat_le, ofNat_natAbs_of_nonpos this, Nat.cast_sub hxy]
    apply le_of_lt_add_one
    simp_rw [← cast_lt (R := ℝ), cast_neg, cast_add, cast_sub, cast_one, cast_natCast]
    have l₁ := lt_floor_add_one (a * x)
    have l₂ := abs_le.mp ha
    have l₃ := lt_floor_add_one (a * y)
    have l₄ := floor_le (a * x)
    nlinarith [(show (x : ℝ) ≤ y by norm_cast)]

theorem dirichlet_argument {n : ℕ} (hv : v ≠ 0) (n_pos : 0 < n) :
    ∃ p : Fin d → ℤ, ∃ q : ℕ,
      1 ≤ q ∧ q ≤ n ^ (d - 1) ∧ q = p (maxAbsIdx v) ∧
      ∀ i, (p i).natAbs ≤ q ∧ |q * mults v i - p i| < 1 / n := by
  let f (m : ℕ) (i : Fin d) : ℤ := ⌊fract (mults v i * m) * n⌋
  have hn : 0 < (n : ℝ) := mod_cast n_pos
  have hfu (m i) : fract (mults v i * m) * n < n := mul_lt_of_lt_one_left hn (fract_lt_one _)
  conv in |_| < _ => rw [mul_comm, lt_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Finset.range (n ^ (d - 1) + 1)
  have hwd (m) (_ : m ∈ D) :
      f m ∈ Fintype.piFinset fun j ↦ if j = maxAbsIdx v then {0} else Ico (0 : ℤ) n := by
    simp_rw [Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · simp [hi, f, mults_maxAbsIdx_eq_one hv]
    · refine mem_Ico.mpr ⟨?_, ?_⟩
      · exact floor_nonneg.mpr (mul_nonneg (fract_nonneg _) hn.le)
      · exact_mod_cast (floor_le _).trans_lt (hfu ..)
  have hD : #(Fintype.piFinset fun j ↦ if j = maxAbsIdx v then {0} else Ico (0 : ℤ) n) < #D := by
    simp_rw [Fintype.card_piFinset, apply_ite, card_singleton, card_Ico, sub_zero, toNat_natCast]
    rw [prod_ite, prod_const_one, prod_const, one_mul, filter_ne', card_erase_of_mem (mem_univ _),
      card_fin]
    simp [D]
  obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ f x = f y := by
    obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
    obtain h | rfl | h := lt_trichotomy x y
    exacts [⟨x, hx, y, hy, h, hxy⟩, by contradiction, ⟨y, hy, x, hx, h, hxy.symm⟩]
  refine ⟨fun i ↦ ⌊mults v i * y⌋ - ⌊mults v i * x⌋, y - x, by lia, ?_, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · have hy_le : y ≤ n ^ (d - 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    exact (Nat.sub_le y x).trans hy_le
  · simp [mults_maxAbsIdx_eq_one hv, Nat.cast_sub x_lt_y.le]
  · exact floor_mul_sub_floor_mul x_lt_y.le abs_mults_le
  rw [cast_sub, Nat.cast_sub x_lt_y.le]
  have h_abs :
      |(mults v i * ((y : ℝ) - x) -
            ((⌊mults v i * (y : ℝ)⌋ : ℝ) - (⌊mults v i * (x : ℝ)⌋ : ℝ))) *
          (n : ℝ)| =
        |fract (mults v i * (y : ℝ)) * (n : ℝ) -
          fract (mults v i * (x : ℝ)) * (n : ℝ)| := by
    rw [← self_sub_floor (mults v i * y), ← self_sub_floor (mults v i * x)]
    ring_nf
  rw [h_abs]
  exact abs_sub_lt_one_of_floor_eq_floor congr($hxy i).symm

lemma eventually_half_le_floor : ∀ᶠ (x : ℝ) in atTop, x / 2 ≤ ⌊x⌋₊ := by
  rw [eventually_atTop]
  exact ⟨2, fun x hx ↦ by linarith [Nat.sub_one_lt_floor x]⟩

variable (d) in
lemma eventually_half_pow_le_floor :
    ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ (2 * d - 1 : ℝ)⁻¹ / 2 ≤ ⌊(n : ℝ) ^ (2 * d - 1 : ℝ)⁻¹⌋₊ := by
  refine (tendsto_rpow_atTop ?_).comp tendsto_natCast_atTop_atTop
    |>.eventually eventually_half_le_floor
  rw [inv_pos, sub_pos]
  norm_cast
  grind [‹d.AtLeastTwo›.one_lt]

variable (d) in
/-- Lemma 3.1. -/
theorem nonempty_shortApprox :
    ∀ᶠ n in atTop, ∀ v : Fin d → ℤ, (∀ i, (v i).natAbs ≤ n) → Nonempty (ShortApprox v n) := by
  have hd := ‹d.AtLeastTwo›.one_lt
  filter_upwards [eventually_half_pow_le_floor d, eventually_ge_atTop 1] with n hn npos v hv
  by_cases hxy : v = 0 -- trivial case
  · refine ⟨⟨1, 0, 0, ?_, ?_, ?_, ?_⟩⟩ <;> subst hxy
    · simp_rw [maxAbs, Pi.one_apply, natAbs_one]
      rw [sup_const (by simp), Nat.cast_one]
      exact ⟨le_rfl,
        one_le_rpow (by simp [npos]) (div_nonneg (by norm_cast; lia) (by norm_cast; lia))⟩
    · simp_rw [Pi.zero_apply, mul_zero, sub_zero, Int.cast_zero, abs_zero]
      intro; positivity
    · simp [maxAbs, Finset.sup_const]
    · simp
  set Q : ℕ := ⌊(n : ℝ) ^ (2 * d - 1 : ℝ)⁻¹⌋₊ -- nontrivial case
  have Qpos : 0 < Q := by
    contrapose! hn
    rw [Nat.le_zero] at hn
    rw [hn, CharP.cast_eq_zero]
    positivity
  obtain ⟨p, q, lbq, ubq, pmax, hp⟩ := dirichlet_argument hxy Qpos
  have qnz : q ≠ 0 := Nat.ne_zero_of_lt lbq
  have qma : q = maxAbs p := by
    refine le_antisymm ?_ (Finset.sup_le fun i _ ↦ (hp i).1)
    have : (p (maxAbsIdx v)).natAbs ≤ maxAbs p := le_sup (f := fun i ↦ (p i).natAbs) (mem_univ _)
    rwa [← pmax, natAbs_natCast] at this
  refine ⟨⟨p, v (maxAbsIdx v) / q, maxAbsIdx v, ?_, fun i ↦ ?_, ?_, ?_⟩⟩
  · rw [← qma]
    constructor
    · simp [lbq]
    · calc
        _ ≤ (Q : ℝ) ^ (d - 1) := by norm_cast
        _ ≤ ((n : ℝ) ^ (2 * d - 1 : ℝ)⁻¹) ^ (d - 1) :=
          pow_le_pow_left₀ (Nat.cast_pos'.mpr Qpos).le (Nat.floor_le (by positivity)) _
        _ = _ := by
          rw [← rpow_natCast, ← rpow_mul (by simp), ← div_eq_inv_mul, K, Nat.cast_pred (by lia)]
  · have nn : 0 ≤ |(v (maxAbsIdx v) : ℝ) / q| := abs_nonneg _
    have key := mul_le_mul_of_nonneg_right (hp i).2.le nn
    have vmax : v (maxAbsIdx v) ≠ 0 := by
      rw [← natAbs_ne_zero, natAbs_maxAbsIdx]
      simpa [maxAbs_eq_zero_iff_eq_zero]
    rw [← abs_mul, sub_mul, mults, mul_div_left_comm (q : ℝ), mul_assoc, ← mul_div_assoc,
      div_mul_cancel₀ _ (by simp [vmax]), div_self (by simp [qnz]), mul_one] at key
    apply key.trans
    rw [← qma, abs_div, Nat.abs_cast, ← Int.cast_abs, Int.abs_eq_natAbs, cast_natCast]
    calc
      _ ≤ 1 / (n ^ (2 * d - 1 : ℝ)⁻¹ / 2 : ℝ) * (n / q) := by gcongr; exact hv _
      _ = _ := by
        rw [one_div_div, div_mul_div_comm, ← div_div, mul_div_assoc]
        nth_rw 1 [← rpow_one n, ← rpow_sub (by simpa)]
        congr
        nth_rw 1 [K, ← one_div, ← div_self (show (2 * d - 1 : ℝ) ≠ 0 by norm_cast; lia)]
        ring
  · rw [← qma, pmax]
  · rw [← pmax, cast_natCast, mul_div_cancel₀ _ (by rwa [Nat.cast_ne_zero])]

/-! ### Lemma 3.2 -/

/-- The constant `c₄` in Lemma 3.2. -/
def C4 (d : ℕ) : ℕ := 10 * d * 15 ^ (d - 1)

variable (d) in
lemma C4_pos : 0 < C4 d := by
  unfold C4
  positivity [‹d.AtLeastTwo›.one_lt]

/-- The set of points satisfying Equation (5). -/
def cubeInterior (d n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ ↦ Icc ⌈(C4 d + 3) * (n : ℝ) ^ K d⌉ (n - ⌈(C4 d + 3) * (n : ℝ) ^ K d⌉)

omit [d.AtLeastTwo] in
lemma cubeInterior_subset_cube {n : ℕ} (hn : 1 ≤ n) : cubeInterior d n ⊆ cube d n := fun v mv ↦ by
  rw [cubeInterior, cube, Fintype.mem_piFinset] at *
  set l := ⌈(C4 d + 3) * (n : ℝ) ^ K d⌉
  suffices 1 ≤ l by exact forall_imp (fun i ↦ mem_of_subset (Icc_subset_Icc (by lia) (by lia))) mv
  simp_rw [l, one_le_ceil_iff]
  positivity

/-- A predicate saying that `v = x - a` satisfies Equations (6) and (7). -/
def HasShortApprox (v : Fin d → ℤ) (n : ℕ) : Prop :=
  ∃ p : Fin d → ℤ, ∃ z : ℝ, ∀ i, (p i).natAbs ≤ (n ^ K d : ℝ) ∧ |v i - p i * z| ≤ C4 d * n ^ K d

variable (d) in
/-- Proved by Aristotle -/
lemma eventually_card_cubeInterior_ge :
    ∀ᶠ (n : ℕ) in atTop, 3 * n ^ d / 4 + 1 ≤ #(cubeInterior d n) := by
  let P (n : ℝ) := (C4 d + 3) * (n ^ K d : ℝ)
  have cZ : Tendsto (fun n : ℝ ↦ (C4 d + 3) * n ^ (K d - 1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (sub_pos.mpr (K_lt_one d)))
  replace cZ : Tendsto (fun n : ℝ ↦ (C4 d + 3) * n ^ K d / n) atTop (𝓝 0) := by
    apply cZ.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [rpow_sub_one hn.ne']
    ring
  replace cZ : ∀ᶠ n in atTop, ⌈P n⌉ ≤ n - ⌈P n⌉ := by
    have := cZ.eventually (gt_mem_nhds <| show 0 < 1 / 4 by norm_num)
    filter_upwards [this, eventually_gt_atTop 4] with n hn₁ hn₂
    rw [div_lt_iff₀ (by linarith)] at hn₁
    linarith [ceil_lt_add_one (P n)]
  replace cZ : ∀ᶠ n in atTop, #(cubeInterior d n) = (n - 2 * ⌈P n⌉ + 1) ^ d := by
    filter_upwards [cZ.natCast_atTop, eventually_ge_atTop 1] with n hn hn'
    norm_cast at hn
    rw [cubeInterior, Fintype.card_piFinset_const, card_Icc, Nat.cast_pow,
      toNat_of_nonneg (by linarith), add_sub_right_comm, sub_sub, ← two_mul]
  have ll {n : ℕ} (hn : 1 ≤ n) : (⌈P n⌉ / n : ℝ) ≤ (C4 d + 3) * n ^ (K d - 1) + 1 / n := by
    rw [rpow_sub_one (by positivity)]
    simp_rw [P, ← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right ((ceil_lt_add_one _).le) (by simp)
  replace ll : Tendsto (fun n : ℕ ↦ (⌈P n⌉ / n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ ↦ (C4 d + 3) * (n : ℝ) ^ (K d - 1) + 1 / n)
    · rw [eventually_atTop]
      refine ⟨1, fun n hn ↦ ?_⟩
      rw [norm_of_nonneg (by positivity)]
      exact ll hn
    · rw [show (0 : ℝ) = (C4 d + 3) * 0 + 0 by simp]
      simp_rw [one_div, ← neg_sub _ (K d)]
      refine (tendsto_const_nhds.mul ?_).add tendsto_inv_atTop_nhds_zero_nat
      exact (tendsto_rpow_neg_atTop (sub_pos.mpr (K_lt_one d))).comp tendsto_natCast_atTop_atTop
  replace ll : Tendsto (fun n : ℕ ↦ (n - 2 * ⌈P n⌉ + 1 : ℝ) / n) atTop (𝓝 1) := by
    nth_rw 2 [show (1 : ℝ) = 1 - 2 * 0 + 0 by simp]
    simp_rw [add_div, one_div, sub_div, mul_div_assoc]
    refine (Tendsto.sub ?_ (ll.const_mul 2)).add tendsto_inv_atTop_nhds_zero_nat
    exact tendsto_const_nhds.congr' (by filter_upwards [eventually_ne_atTop 0] with n hn; simp_all)
  replace ll := ll.pow d
  simp only [div_pow, one_pow] at ll
  replace ll := ll.eventually (lt_mem_nhds <| show 1 > 3 / 4 by norm_num)
  filter_upwards [ll, cZ, eventually_gt_atTop 0] with n hn hn' hn''
  rw [div_lt_div_iff₀ zero_lt_four (by positivity)] at hn
  norm_cast at hn
  have hn'_real :
      ((cubeInterior d n).card : ℝ) =
        ((n : ℝ) - 2 * ↑⌈P (n : ℝ)⌉ + 1) ^ d := by
    exact_mod_cast hn'
  have hn_real :
      3 * (n : ℝ) ^ d < (((n : ℝ) - 2 * ↑⌈P (n : ℝ)⌉ + 1) ^ d) * 4 := by
    exact_mod_cast hn
  have h_cast_main : ((3 * n ^ d : ℕ) : ℝ) = 3 * (n : ℝ) ^ d := by
    norm_num [Nat.cast_mul, Nat.cast_pow]
  have h_lower4 : 3 * (n : ℝ) ^ d < 4 * ((cubeInterior d n).card : ℝ) := by
    rw [hn'_real]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hn_real
  have h_lower : (3 * n ^ d : ℝ) / 4 < ((cubeInterior d n).card : ℝ) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_lower4
  have h_div_lt_card : 3 * n ^ d / 4 < (cubeInterior d n).card := by
    have h_cast_div :
        ((3 * n ^ d / 4 : ℕ) : ℝ) ≤ (3 * n ^ d : ℝ) / 4 := by
      refine
        (Nat.cast_div_le (m := 3 * n ^ d) (n := 4) :
          ((3 * n ^ d / 4 : ℕ) : ℝ) ≤ ((3 * n ^ d : ℕ) : ℝ) / (4 : ℝ)).trans_eq ?_
      norm_num [Nat.cast_mul, Nat.cast_pow]
    exact Nat.cast_lt.mp
      (h_cast_div.trans_lt h_lower)
  exact Nat.succ_le_of_lt h_div_lt_card

/-- Proved by Aristotle -/
lemma exists_bound_of_abs_sub_le (x : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    ∃ s, #s ≤ 2 * b + 1 ∧ ∀ a : ℤ, |a - x| ≤ b → a ∈ s := by
  refine ⟨Icc ⌈x - b⌉ ⌊x + b⌋, ?_, fun a ha ↦ ?_⟩
  · rw [card_Icc]
    calc
      _ = (⌊x + b⌋ + 1 - ⌈x - b⌉ : ℝ) := by
        norm_cast
        apply toNat_of_nonneg
        rw [sub_nonneg, ← sub_le_iff_le_add, le_floor, cast_sub, cast_one]
        linarith [ceil_lt_add_one (x - b)]
      _ ≤ _ := by linarith [floor_le (x + b), le_ceil (x - b)]
  · rw [abs_le, sub_le_iff_le_add', le_sub_iff_add_le', ← sub_eq_add_neg] at ha
    rwa [mem_Icc, ceil_le, le_floor]

lemma estimation_chain1 {n q : ℕ} (x : Fin d → ℤ) (j i : Fin d) (M p : ℤ) (hn : q ^ 2 ≤ n)
    (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) :
    ∃ s, #s ≤ (5 * n ^ (2 * K d) / q : ℝ) ∧
    ∀ a, maxAbs (f a).p = q → (f a).j = j → a.1 j = M → (f a).p i = p → a.1 i ∈ s := by
  obtain rfl | hq := q.eq_zero_or_pos
  · simp_rw [Nat.cast_zero, div_zero, Nat.cast_nonpos, card_eq_zero, exists_eq_left]
    intro a ctr
    have olp := (f a).maxAbs_p_mem_Icc.1
    rw [ctr, CharP.cast_eq_zero] at olp
    linarith [zero_lt_one' ℝ]
  have z_fix {a} (hq' : maxAbs (f a).p = q) (hj : (f a).j = j) (hM : a.1 j = M) :
      (x j - M) / q = (f a).z := by
    have ex := (f a).exact_j
    rwa [Pi.sub_apply, (f a).p_j, hj, cast_sub, cast_natCast,
      ← inv_mul_eq_iff_eq_mul₀ (by simp [hq', hq.ne']), ← div_eq_inv_mul, hq', hM] at ex
  obtain ⟨s, hs₁, hs₂⟩ := exists_bound_of_abs_sub_le (x i - p * ((x j - M) / q))
    (show (0 : ℝ) ≤ 2 * n ^ (2 * K d) / q by positivity)
  refine ⟨s, ?_, fun a hq' hj hM hp ↦ ?_⟩
  · apply hs₁.trans
    calc
      2 * (2 * n ^ (2 * K d) / q : ℝ) + 1 = 4 * (n ^ (2 * K d) / q) + 1 := by ring
      _ ≤ 5 * (n ^ (2 * K d) / q) := by
        suffices (1 : ℝ) ≤ n ^ (2 * K d) / q by nlinarith
        rw [one_le_div (mod_cast hq)]
        calc
          _ ≤ (q ^ 2 : ℝ) ^ (2 * K d) := by
            have hd := ‹d.AtLeastTwo›.one_lt
            nth_rw 1 [← rpow_one q, ← rpow_natCast, ← rpow_mul (by positivity)]
            apply rpow_le_rpow_of_exponent_le (by norm_cast)
            rw [K, ← mul_assoc, ← mul_div_assoc, one_le_div (by norm_cast; lia), Nat.cast_two]
            suffices 3 ≤ (2 * d : ℝ) by linarith
            norm_cast
            lia
          _ ≤ _ := rpow_le_rpow (by positivity) (mod_cast hn) (by positivity [K_pos d])
      _ = 5 * n ^ (2 * K d) / q := by ring
  have key := (f a).abs_sub_le i
  rw [Pi.sub_apply, cast_sub, ← abs_neg,
    show -(x i - a.1 i - (f a).p i * (f a).z) = a.1 i - (x i - (f a).p i * (f a).z) by ring,
    ← z_fix hq' hj hM, hq', hp] at key
  exact hs₂ _ key

lemma estimation_chain2 {n q : ℕ} (x : Fin d → ℤ) (j i : Fin d) (M : ℤ) (hn : q ^ 2 ≤ n)
    (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) :
    ∃ s, #s ≤ (15 * n ^ (2 * K d) : ℝ) ∧
    ∀ a, maxAbs (f a).p = q → (f a).j = j → a.1 j = M → a.1 i ∈ s := by
  obtain rfl | hq := q.eq_zero_or_pos
  · refine ⟨∅, by rw [card_empty, Nat.cast_zero]; positivity, fun a ctr ↦ ?_⟩
    have olp := (f a).maxAbs_p_mem_Icc.1
    rw [ctr, CharP.cast_eq_zero] at olp
    linarith [zero_lt_one' ℝ]
  refine ⟨(Icc (-q : ℤ) q).biUnion fun p ↦ (estimation_chain1 x j i M p hn f).choose,
    ?_, fun a hq' hj hM ↦ ?_⟩
  · calc
      _ ≤ ∑ p ∈ Icc (-q : ℤ) q, (#(estimation_chain1 x j i M p hn f).choose : ℝ) := by
        rw [← Nat.cast_sum, Nat.cast_le]
        exact card_biUnion_le
      _ ≤ ∑ p ∈ Icc (-q : ℤ) q, (5 * n ^ (2 * K d) / q : ℝ) :=
        sum_le_sum fun p _ ↦ (estimation_chain1 x j i M p hn f).choose_spec.1
      _ ≤ 3 * q * (5 * n ^ (2 * K d) / q : ℝ) := by
        rw [sum_const, card_Icc, show (q + 1 - -q : ℤ).toNat = 2 * q + 1 by lia, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        norm_cast
        lia
      _ = _ := by field
  · rw [mem_biUnion]
    refine ⟨(f a).p i, ?_, ?_⟩
    · rw [mem_Icc, ← abs_le, abs_eq_natAbs, Nat.cast_le, ← hq']
      exact le_sup (f := fun i ↦ ((f a).p i).natAbs) (mem_univ _)
    · exact (estimation_chain1 x j i M ((f a).p i) hn f).choose_spec.2 a hq' hj hM rfl

lemma estimation_chain3 {n q : ℕ} (x : Fin d → ℤ) (j : Fin d) (M : ℤ) (hn : q ^ 2 ≤ n)
    (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) :
    ∃ S, #S ≤ (15 * n ^ (2 * K d) : ℝ) ^ (d - 1) ∧
    ∀ a, maxAbs (f a).p = q → (f a).j = j → a.1 j = M → a.1 ∈ S := by
  refine ⟨Fintype.piFinset fun i ↦ if i = j then {M} else (estimation_chain2 x j i M hn f).choose,
    ?_, fun a hq' hj hM ↦ ?_⟩
  · simp_rw [Fintype.card_piFinset, apply_ite, card_singleton]
    rw [prod_ite, prod_const_one, one_mul, filter_ne', Nat.cast_prod]
    calc
      _ ≤ ∏ i ∈ univ.erase j, (15 * n ^ (2 * K d) : ℝ) :=
        prod_le_prod (fun _ _ ↦ by simp) fun i mi ↦ (estimation_chain2 x j i M hn f).choose_spec.1
      _ = _ := by rw [prod_const, card_erase_of_mem (mem_univ _), card_fin]
  · rw [Fintype.mem_piFinset]
    intro i
    have h := (estimation_chain2 x j i M hn f).choose_spec.2
    split_ifs with hij
    · rwa [mem_singleton, hij]
    · exact h a hq' hj hM

lemma estimation_chain4 {n q : ℕ} (x : Fin d → ℤ) (j : Fin d) (hn : q ^ 2 ≤ n) (hn' : 1 ≤ n)
    (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) :
    ∃ S, #S ≤ n * (15 * n ^ (2 * K d) : ℝ) ^ (d - 1) ∧
    ∀ a, maxAbs (f a).p = q → (f a).j = j → a.1 ∈ S := by
  refine ⟨(Icc (1 : ℤ) n).biUnion fun M ↦ (estimation_chain3 x j M hn f).choose,
    ?_, fun a hq' hj ↦ ?_⟩
  · calc
      _ ≤ ∑ M ∈ Icc (1 : ℤ) n, (#(estimation_chain3 x j M hn f).choose : ℝ) := by
        rw [← Nat.cast_sum, Nat.cast_le]
        exact card_biUnion_le
      _ ≤ ∑ p ∈ Icc (1 : ℤ) n, (15 * n ^ (2 * K d) : ℝ) ^ (d - 1) :=
        sum_le_sum fun M _ ↦ (estimation_chain3 x j M hn f).choose_spec.1
      _ = _ := by rw [sum_const, card_Icc, add_sub_cancel_right, toNat_natCast, nsmul_eq_mul]
  · rw [mem_biUnion]
    refine ⟨a.1 j, ?_, ?_⟩
    · obtain ⟨a, ma⟩ := a
      replace ma := cubeInterior_subset_cube hn' ma
      rw [cube, Fintype.mem_piFinset] at ma
      exact ma j
    · exact (estimation_chain3 x j (a.1 j) hn f).choose_spec.2 a hq' hj rfl

lemma estimation_chain5 {n q : ℕ} (x : Fin d → ℤ) (hn : q ^ 2 ≤ n) (hn' : 1 ≤ n)
    (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) :
    ∃ S, #S ≤ d * n * (15 * n ^ (2 * K d) : ℝ) ^ (d - 1) ∧
    ∀ a, maxAbs (f a).p = q → a.1 ∈ S := by
  refine ⟨univ.biUnion fun j ↦ (estimation_chain4 x j hn hn' f).choose,
    ?_, fun a hq' ↦ ?_⟩
  · calc
      _ ≤ ∑ j, (#(estimation_chain4 x j hn hn' f).choose : ℝ) := by
        rw [← Nat.cast_sum, Nat.cast_le]
        exact card_biUnion_le
      _ ≤ ∑ j, n * (15 * n ^ (2 * K d) : ℝ) ^ (d - 1) :=
        sum_le_sum fun j _ ↦ (estimation_chain4 x j hn hn' f).choose_spec.1
      _ = _ := by rw [sum_const, card_fin, nsmul_eq_mul, mul_assoc]
  · rw [mem_biUnion]
    exact ⟨(f a).j, mem_univ _, (estimation_chain4 x (f a).j hn hn' f).choose_spec.2 a hq' rfl⟩

lemma n_power_bound {n : ℕ} (hn : 4 ^ (2 * d - 1) ≤ n) :
    1 ≤ n ∧ ∀ q : Icc 1 ⌊(2 * n ^ K d : ℝ) / C4 d⌋₊, q.1 ^ 2 ≤ n := by
  have hd := ‹d.AtLeastTwo›.one_lt
  have hn' : 1 ≤ n := by
    by_contra! h
    rw [Nat.lt_one_iff] at h
    rw [h, Nat.le_zero, Nat.pow_eq_zero] at hn
    lia
  refine ⟨hn', fun ⟨q, hq⟩ ↦ ?_⟩
  rw [mem_Icc, Nat.le_floor_iff (by positivity)] at hq
  replace hq : q ≤ (2 * n ^ K d : ℝ) := by
    refine hq.2.trans (div_le_self (by positivity) ?_)
    rw [Nat.one_le_cast]
    exact C4_pos d
  rify at hn ⊢
  apply (pow_le_pow_left₀ (by simp) hq _).trans
  have hden : 0 < (2 * d - 1 : ℝ) := by norm_cast; lia
  nth_rw 1 [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← le_div_iff₀ (by positivity),
    ← rpow_natCast, ← rpow_mul (by simp), ← rpow_one n, ← rpow_sub (by simpa), K,
    ← mul_div_right_comm, one_sub_div hden.ne', Nat.cast_two,
    show (2 * d - 1 - (d - 1) * 2 : ℝ) = 1 by ring,
    ← rpow_le_rpow_iff zero_le_four (by positivity) hden, ← rpow_mul (by simp),
    div_mul_cancel₀ _ hden.ne', rpow_one]
  rw [← rpow_natCast, Nat.cast_sub (by lia)] at hn
  simpa using hn

lemma n_d_rearrange {n : ℕ} (hn : 4 ^ (2 * d - 1) ≤ n) :
    2 * n ^ K d / C4 d * (d * n * (15 * n ^ (2 * K d) : ℝ) ^ (d - 1)) ≤ (n ^ d / 4 : ℕ) := by
  have hd := ‹d.AtLeastTwo›.one_lt
  have lbn : 64 ≤ n :=
    calc
      _ = 4 ^ 3 := by decide
      _ ≤ 4 ^ (2 * d - 1) := pow_le_pow_right₀ (by decide) (by lia)
      _ ≤ _ := hn
  have npos : 0 < n := by lia
  calc
    _ = 2 * d * 15 ^ (d - 1) / C4 d * ((n ^ K d : ℝ) * (n ^ (2 * K d)) ^ (d - 1) * n) := by ring
    _ = n ^ K d * (n ^ (2 * K d)) ^ (d - 1) * n / 5 := by
      simp_rw [C4, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        show 10 * (d : ℝ) * 15 ^ (d - 1) = 2 * d * 15 ^ (d - 1) * 5 by ring]
      rw [div_mul_cancel_left₀ (by positivity), ← div_eq_inv_mul]
    _ = (n ^ (1 : ℝ)) ^ (d - 1) * n / 5 := by
      rw [K]
      nth_rw 1 [div_eq_mul_inv (d - 1 : ℝ), mul_comm (d - 1 : ℝ), rpow_mul (by simp),
        ← Nat.cast_pred (by lia), rpow_natCast, ← mul_pow, ← rpow_add (by simp [npos])]
      congr
      rw [← mul_div_assoc, div_eq_mul_inv, ← one_add_mul,
        show 1 + 2 * (d - 1 : ℝ) = 2 * d - 1 by ring]
      exact mul_inv_cancel₀ (by norm_cast; lia)
    _ = n ^ d / 5 := by rw [rpow_one, ← pow_succ, show d - 1 + 1 = d by lia]
    _ ≤ _ := by
      apply div_le_of_le_mul₀ (by simp) (by positivity)
      rw [← Nat.cast_pow]
      norm_cast
      suffices 64 ^ 1 ≤ n ^ d by lia
      calc
        _ ≤ 64 ^ d := pow_le_pow_right₀ (by decide) hd.le
        _ ≤ _ := pow_le_pow_left₀ (by decide) lbn d

lemma estimation_chain6 {n : ℕ} (x : Fin d → ℤ) (hn : 4 ^ (2 * d - 1) ≤ n)
    (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) :
    ∃ S, #S ≤ n ^ d / 4 ∧ ∀ a, maxAbs (f a).p < (2 * n ^ K d : ℝ) / C4 d → a.1 ∈ S := by
  obtain ⟨hn', hq⟩ := n_power_bound hn
  refine ⟨(Icc 1 ⌊(2 * n ^ K d : ℝ) / C4 d⌋₊).attach.biUnion
    fun q ↦ (estimation_chain5 x (hq q) hn' f).choose, ?_, fun a hq' ↦ ?_⟩
  · rw [← Nat.cast_le (α := ℝ)]
    calc
      _ ≤ ∑ q, (#(estimation_chain5 x (hq q) hn' f).choose : ℝ) := by
        rw [← Nat.cast_sum, Nat.cast_le]
        exact card_biUnion_le
      _ ≤ ∑ q, d * n * (15 * n ^ (2 * K d) : ℝ) ^ (d - 1) :=
        sum_le_sum fun q _ ↦ (estimation_chain5 x (hq q) hn' f).choose_spec.1
      _ ≤ 2 * n ^ K d / C4 d * (d * n * (15 * n ^ (2 * K d) : ℝ) ^ (d - 1)) := by
        rw [sum_const, card_univ, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
      _ ≤ _ := n_d_rearrange hn
  · simp_rw [mem_biUnion, mem_attach, true_and]
    have lb := (f a).maxAbs_p_mem_Icc.1
    rw [Nat.one_le_cast] at lb
    let q : Icc 1 ⌊(2 * n ^ K d : ℝ) / C4 d⌋₊ :=
      ⟨maxAbs (f a).p, mem_Icc.mpr ⟨lb, (Nat.le_floor hq'.le)⟩⟩
    exact ⟨q, (estimation_chain5 x (hq q) hn' f).choose_spec.2 a rfl⟩

variable (d) in
lemma estimation_chain7 :
    ∀ᶠ n in atTop, ∀ x : Fin d → ℤ, (f : (a : cubeInterior d n) → ShortApprox (x - a.1) n) →
    #{a | maxAbs (f a).p < (2 * n ^ K d : ℝ) / C4 d} ≤ n ^ d / 4 := by
  rw [eventually_atTop]
  refine ⟨4 ^ (2 * d - 1), fun n hn x f ↦ ?_⟩
  obtain ⟨S, hS₁, hS₂⟩ := estimation_chain6 x hn f
  calc
    _ ≤ #{a : cubeInterior d n | a.1 ∈ S} := by
      refine card_le_card fun a ma ↦ ?_
      rw [mem_filter_univ] at ma ⊢
      exact hS₂ a ma
    _ ≤ #S := by
      rw [univ_eq_attach, filter_attach (· ∈ S), card_map, card_attach, filter_mem_eq_inter]
      exact card_le_card inter_subset_right
    _ ≤ _ := hS₁

variable (d) in
open scoped Classical in
/-- Lemma 3.2. -/
theorem card_hasShortApprox_lt : ∀ᶠ n in atTop, ∀ x ∈ cube d n,
    n ^ d / 2 < #{a ∈ cubeInterior d n | HasShortApprox (x - a) n} := by
  filter_upwards [eventually_card_cubeInterior_ge d, nonempty_shortApprox d,
    eventually_ge_atTop 1, estimation_chain7 d] with n hci hv hn hec x mx
  rw [← card_filter_add_card_filter_not (p := fun a ↦ HasShortApprox (x - a) n)] at hci
  suffices #({a ∈ cubeInterior d n | ¬HasShortApprox (x - a) n}) ≤ n ^ d / 4 by lia
  -- Define a function sending a point `a ∈ cubeInterior d n` to _some_ `ShortApprox (x - a) n`
  have md (a : cubeInterior d n) (i) : ((x - a.1) i).natAbs ≤ n := by
    obtain ⟨a, ma⟩ := a
    simp only [Pi.sub_apply]
    replace ma := cubeInterior_subset_cube hn ma
    rw [cube, Fintype.mem_piFinset] at mx ma
    specialize mx i
    specialize ma i
    rw [mem_Icc] at mx ma
    lia
  let f (a : cubeInterior d n) : ShortApprox (x - a.1) n := (hv (x - a.1) (md a)).some
  have crw : #{a ∈ cubeInterior d n | ¬HasShortApprox (x - a) n} =
      #{a : cubeInterior d n | ¬HasShortApprox (x - a.1) n} := by
    rw [univ_eq_attach, filter_attach fun a ↦ ¬HasShortApprox (x - a) n, card_map, card_attach]
  rw [crw]
  have hsa (a) (ha : (2 * n ^ K d : ℝ) / C4 d ≤ maxAbs (f a).p) : HasShortApprox (x - a.1) n := by
    refine ⟨(f a).p, (f a).z, fun i ↦ ⟨?_, ?_⟩⟩
    · apply ((f a).maxAbs_p_mem_Icc.2).trans'
      rw [Nat.cast_le]
      exact le_sup (f := fun i ↦ ((f a).p i).natAbs) (mem_univ _)
    · calc
        _ ≤ _ := (f a).abs_sub_le i
        _ ≤ 2 * n ^ (2 * K d) / (2 * n ^ K d / C4 d) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity [C4_pos d]) ha
        _ = _ := by
          rw [← div_mul, two_mul (K d), rpow_add (by simp [Nat.zero_lt_of_lt hn]), ← mul_assoc,
            mul_div_cancel_left₀ _ (by positivity), mul_comm]
  suffices #{a | maxAbs (f a).p < (2 * n ^ K d : ℝ) / C4 d} ≤ n ^ d / 4 by
    refine (card_le_card fun a ma ↦ ?_).trans this
    rw [mem_filter_univ] at ma ⊢
    contrapose! ma
    exact hsa a ma
  exact hec x f

/-! ### Lemma 3.3 -/

/-- The line determined by `a,b` covers `c` if `c` can be written as a
linear combination of `a,b`. -/
def Covers (a b c : Fin d → ℤ) : Prop :=
  ∃ t q : ℤ, q ≠ 0 ∧ (q - t) • a + t • b = q • c

/-- The set `B(a)` defined in the paper. -/
def cubeAround (a : Fin d → ℤ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i ↦ Icc (a i - ⌊(C4 d + 2) * (n : ℝ) ^ K d⌋)
    (a i + ⌊(C4 d + 2) * (n : ℝ) ^ K d⌋)

variable (d) in
lemma cubeAround_cubeInterior_subset_cube :
    ∀ᶠ n in atTop, ∀ a, a ∈ cubeInterior d n → cubeAround a n ⊆ cube d n := by
  filter_upwards [eventually_ge_atTop 1] with n hn a ma v mv
  rw [cubeInterior, cubeAround, cube, Fintype.mem_piFinset] at *
  intro i
  specialize ma i
  specialize mv i
  rw [mem_Icc] at *
  have key : ⌊(C4 d + 2) * (n ^ K d : ℝ)⌋ + 1 ≤ ⌈(C4 d + 3) * (n ^ K d : ℝ)⌉ := by
    rw [← floor_add_one]
    calc
      _ ≤ ⌊(C4 d + 3) * (n ^ K d : ℝ)⌋ := by
        rw [show (C4 d + 3) * (n ^ K d : ℝ) = (C4 d + 2) * (n ^ K d) + n ^ K d by ring]
        refine floor_mono (add_le_add_right ?_ _)
        exact one_le_rpow (by norm_cast) (K_pos d).le
      _ ≤ _ := floor_le_ceil _
  constructor <;> linarith

/-- Lemma 3.3. -/
theorem exists_covers {n : ℕ} {x a : Fin d → ℤ}
    (mx : x ∈ cube d n) (ma : a ∈ cubeInterior d n) (hsa : HasShortApprox (x - a) n) :
    ∃ y z, y ∈ cubeAround a n ∧ z ∈ cubeAround a n ∧ Covers y z x := by
  obtain ⟨p, z, h⟩ := hsa
  have ltf : (C4 d + 1) * (n ^ K d : ℝ) ≤ ⌊(C4 d + 2) * (n ^ K d : ℝ)⌋ := by
    obtain rfl | hn := n.eq_zero_or_pos
    · simp [zero_rpow (K_pos d).ne']
    apply (lt_floor_add_one _).le.trans
    rw [← cast_one, ← cast_add, ← floor_add_one, cast_one,
      show (C4 d + 2 : ℝ) * n ^ K d = (C4 d + 1) * n ^ K d + n ^ K d by ring]
    refine cast_mono (floor_mono (add_le_add_right ?_ _))
    exact one_le_rpow (by norm_cast) (K_pos d).le
  refine ⟨x - ⌊z⌋ • p, x - (⌊z⌋ + 1) • p, ?_, ?_, ?_⟩
  on_goal 3 => exact ⟨-⌊z⌋, 1, one_ne_zero, by ring⟩
  all_goals
    rw [cubeAround, Fintype.mem_piFinset]
    intro i
    specialize h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cast_sub] at h ⊢
    rw [Nat.cast_natAbs, cast_abs] at h
    rw [mem_Icc, sub_eq_neg_add, ← le_sub_iff_add_le, ← sub_le_iff_le_add', ← abs_le]
    rify
  · calc
      _ = |x i - a i - p i * z + (p i * (z - ⌊z⌋))| := by congr; ring
      _ ≤ _ := abs_add_le ..
      _ ≤ (C4 d + 1) * n ^ K d := by
        rw [add_one_mul]
        apply add_le_add h.2
        rw [abs_mul, self_sub_floor, abs_fract, ← mul_one (_ ^ _)]
        exact mul_le_mul h.1 (fract_lt_one _).le (fract_nonneg _) (by positivity)
      _ ≤ _ := ltf
  · calc
      _ = |x i - a i - p i * z + (p i * (z - ⌊z⌋ - 1))| := by congr; ring
      _ ≤ _ := abs_add_le ..
      _ ≤ (C4 d + 1) * n ^ K d := by
        rw [add_one_mul]
        apply add_le_add h.2
        rw [abs_mul, self_sub_floor, ← mul_one (_ ^ _)]
        refine mul_le_mul h.1 ?_ (abs_nonneg _) (by positivity)
        rw [abs_le, le_sub_iff_add_le, neg_add_cancel]
        exact ⟨fract_nonneg z, by linarith [fract_lt_one z]⟩
      _ ≤ _ := ltf

/-! ### The dénouement -/

/-- A predicate stating that `B(a)` covers `x`. -/
def CAC (n : ℕ) (a x : Fin d → ℤ) : Prop :=
  ∃ y z, y ∈ cubeAround a n ∧ z ∈ cubeAround a n ∧ Covers y z x

variable (d) in
open scoped Classical BigOperators in
lemma expect_cubeInterior_lt_half : ∀ᶠ n in atTop, ∀ x ∈ cube d n,
    (𝔼 a ∈ cubeInterior d n, if ¬CAC n a x then (1 : ℝ) else 0) < 2⁻¹ := by
  filter_upwards [card_hasShortApprox_lt d, eventually_ge_atTop 1] with n hn lbn x mx
  specialize hn x mx
  replace hn : n ^ d / 2 < #{a ∈ cubeInterior d n | CAC n a x} := by
    refine hn.trans_le (card_le_card fun a ma ↦ ?_)
    rw [mem_filter] at ma ⊢
    exact ⟨ma.1, exists_covers mx ma.1 ma.2⟩
  have hn' : #{a ∈ cubeInterior d n | ¬CAC n a x} ≤ n ^ d / 2 := by
    have key := card_le_card (cubeInterior_subset_cube (d := d) lbn)
    rw [cube, Fintype.card_piFinset_const, card_Icc, add_sub_cancel_right, toNat_natCast,
      ← card_filter_add_card_filter_not (CAC n · x)] at key
    lia
  rw [expect_eq_sum_div_card, sum_boole, ← one_div]
  obtain hc | hc := (#(cubeInterior d n)).eq_zero_or_pos
  · simp [hc]
  rw [div_lt_div_iff₀ (by simp [hc]) zero_lt_two, one_mul]
  norm_cast
  rw [mul_two]
  conv_rhs => rw [← card_filter_add_card_filter_not (CAC n · x)]
  lia

variable (d) in
open scoped Classical BigOperators in
lemma expect_cubeInterior_lt_one : ∀ᶠ n : ℕ in atTop,
    (𝔼 s ∈ Fintype.piFinset fun _ : Fin (⌈d * logb 2 n⌉₊ + 1) ↦ cubeInterior d n,
      (#{x ∈ cube d n | ∀ i, ¬CAC n (s i) x} : ℝ)) < 1 := by
  filter_upwards [expect_cubeInterior_lt_half d, eventually_gt_atTop 0] with n hn lbn
  simp_rw [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, expect_sum_comm]
  have ccube : #(cube d n) = n ^ d := by
    rw [cube, Fintype.card_piFinset_const, card_Icc, add_sub_cancel_right, toNat_natCast]
  suffices ∀ x ∈ cube d n,
      (𝔼 s ∈ Fintype.piFinset fun _ : Fin (⌈d * logb 2 n⌉₊ + 1) ↦ cubeInterior d n,
      if ∀ i, ¬CAC n (s i) x then (1 : ℝ) else 0) < (n ^ d : ℝ)⁻¹ by
    calc
      _ < ∑ x ∈ cube d n, (n ^ d : ℝ)⁻¹ := by
        refine sum_lt_sum_of_nonempty ?_ this
        rw [← card_ne_zero, ccube]
        exact pow_ne_zero _ lbn.ne'
      _ ≤ _ := by
        rw [sum_const, ccube, nsmul_eq_mul, Nat.cast_pow]
        exact mul_inv_le_one
  intro x mx
  specialize hn x mx
  have con (s) (hs : s ∈ Fintype.piFinset fun i : Fin (⌈d * logb 2 n⌉₊ + 1) ↦ cubeInterior d n) :
      (if ∀ i, ¬CAC n (s i) x then (1 : ℝ) else 0) =
      ∏ i, if ¬CAC n (s i) x then (1 : ℝ) else 0 := by
    split_ifs with h
    · exact (prod_eq_one fun i _ ↦ by simp [h i]).symm
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [prod_eq_zero (mem_univ i) (by simp [hi])]
  rw [expect_congr rfl con, ← expect_pow _ fun a ↦ if ¬CAC n a x then 1 else 0]
  calc
    _ < (2 : ℝ)⁻¹ ^ (⌈d * logb 2 n⌉₊ + 1) := pow_lt_pow_left₀ hn (by positivity) (by positivity)
    _ < 2⁻¹ ^ (d * logb 2 n) := by
      rw [← rpow_natCast, rpow_lt_rpow_left_iff_of_base_lt_one (by positivity) (by norm_num),
        Nat.cast_add_one]
      exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    _ = _ := by
      rw [mul_comm, rpow_mul (by positivity), inv_rpow zero_le_two,
        rpow_logb zero_lt_two (by norm_num) (by simpa), rpow_natCast, inv_pow]

/-- A predicate saying that (1) `S` is contained in `cube d n` and (2) the lines determined
by all pairs of points in `S` cover `cube d n`. -/
def IsCubeCover (n : ℕ) (S : Finset (Fin d → ℤ)) : Prop :=
  S ⊆ cube d n ∧ ∀ x ∈ cube d n, ∃ y z, y ∈ S ∧ z ∈ S ∧ Covers y z x

/-- The constant `c₆` in the upper bound proof. -/
def C6 (d : ℕ) : ℕ := 2 * d * (2 * C4 d + 5) ^ d

lemma ceil_le_two_mul_logb {n : ℕ} (hn : 2 ≤ n) : ⌈d * logb 2 n⌉₊ + 1 ≤ 2 * d * logb 2 n := by
  rw [mul_assoc]
  set x : ℝ := d * logb 2 n
  suffices 2 ≤ x by linarith [Nat.ceil_lt_add_one (zero_le_two.trans this)]
  unfold x
  nth_rw 1 [← mul_one 2]
  refine mul_le_mul ?_ ?_ zero_le_one (Nat.cast_nonneg' d)
  · exact_mod_cast Nat.succ_le_of_lt ‹d.AtLeastTwo›.one_lt
  · rw [le_logb_iff_rpow_le one_lt_two (by norm_cast; lia)]
    simpa

variable (d) in
theorem exists_isCubeCover_of_card_le : ∀ᶠ n : ℕ in atTop,
    ∃ S : Finset (Fin d → ℤ), #S ≤ C6 d * n ^ (d * K d) * logb 2 n ∧ IsCubeCover n S := by
  filter_upwards [expect_cubeInterior_lt_one d, eventually_card_cubeInterior_ge d,
    cubeAround_cubeInterior_subset_cube d, eventually_ge_atTop 2] with n hn cci cacis lbn
  have nem : (Fintype.piFinset fun i : Fin (⌈d * logb 2 n⌉₊ + 1) ↦ cubeInterior d n).Nonempty := by
    rw [Fintype.piFinset_nonempty, forall_const, ← card_pos]
    lia
  obtain ⟨S, mS, hS⟩ := exists_lt_of_expect_lt nem hn
  simp_rw [Nat.cast_lt_one, card_eq_zero, filter_eq_empty_iff, not_forall, not_not] at hS
  refine ⟨univ.biUnion fun i ↦ cubeAround (S i) n, ?_, ?_, fun x mx ↦ ?_⟩
  · calc
      _ ≤ (∑ i, #(cubeAround (S i) n) : ℝ) := mod_cast card_biUnion_le
      _ ≤ ∑ i : Fin (⌈d * logb 2 n⌉₊ + 1), ((2 * C4 d + 5) * (n ^ K d : ℝ)) ^ d := by
        refine sum_le_sum fun i _ ↦ ?_
        simp_rw [cubeAround, Fintype.card_piFinset, card_Icc, add_assoc, add_sub_sub_cancel]
        rw [prod_const, card_fin, ← add_rotate, ← two_mul, Nat.cast_pow]
        apply pow_le_pow_left₀ (by simp)
        rw [← cast_natCast, toNat_of_nonneg (by positivity),
          show (2 * C4 d + 5) * (n ^ K d : ℝ) = 2 * ((C4 d + 2) * (n ^ K d : ℝ)) + n ^ K d by ring]
        push_cast
        apply add_le_add (mul_le_mul_of_nonneg_left (floor_le _) zero_le_two)
        exact one_le_rpow (by norm_cast; lia) (K_pos d).le
      _ = (⌈d * logb 2 n⌉₊ + 1) * (2 * C4 d + 5) ^ d * n ^ (d * K d) := by
        rw [sum_const, card_fin, nsmul_eq_mul, mul_pow, ← mul_assoc, Nat.cast_add_one]
        congr 1
        rw [← rpow_natCast, ← rpow_mul (by simp), mul_comm]
      _ ≤ (2 * d * logb 2 n) * (2 * C4 d + 5) ^ d * n ^ (d * K d) := by
        gcongr
        exact ceil_le_two_mul_logb lbn
      _ = _ := by unfold C6; push_cast; ring
  · simp_rw [biUnion_subset_iff_forall_subset, mem_univ, forall_const]
    rw [Fintype.mem_piFinset] at mS
    exact fun i ↦ cacis _ (mS i)
  · obtain ⟨i, y, z, h⟩ := hS mx
    refine ⟨y, z, ?_⟩
    simp_rw [mem_biUnion, mem_univ, true_and]
    exact ⟨⟨i, h.1⟩, ⟨i, h.2.1⟩, h.2.2⟩

variable (d) in
open scoped Classical in
/-- The minimum number of points needed to cover `cube d n` with determined lines. -/
def minCoverSize (n : ℕ) : ℕ :=
  {c ∈ Finset.range (n ^ d + 1) | ∃ S : Finset (Fin d → ℤ), #S = c ∧ IsCubeCover n S}.min'
  ⟨n ^ d, by
    simp_rw [mem_filter, mem_range_succ_iff, le_rfl, true_and]
    exact ⟨cube d n, by simp [cube], subset_rfl,
      fun a ma ↦ ⟨_, _, ma, ma, ⟨0, 1, by simp, by simp⟩⟩⟩⟩

theorem isBigO_minCoverSize :
    (fun n ↦ (minCoverSize d n : ℝ)) =O[atTop] fun n ↦ n ^ (d * K d) * log n := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨C6 d / log 2, ?_⟩
  filter_upwards [exists_isCubeCover_of_card_le d] with n eS
  obtain ⟨S, cardS, covS⟩ := eS
  rw [RCLike.norm_natCast, norm_of_nonneg (by positivity)]
  calc
    _ ≤ (#S : ℝ) := by
      norm_cast
      apply min'_le
      classical rw [mem_filter, mem_range_succ_iff]
      refine ⟨(card_le_card covS.1).trans_eq ?_, ⟨S, rfl, covS⟩⟩
      simp [cube]
    _ ≤ _ := cardS
    _ = _ := by rw [logb]; ring

theorem erdos798 : (fun n ↦ (minCoverSize 2 n : ℝ)) =O[atTop] fun n ↦ n ^ (2 / 3 : ℝ) * log n := by
  convert isBigO_minCoverSize using 4
  · norm_num [K]
  · infer_instance

end

#print axioms erdos798
-- 'Erdos798.erdos798' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos798
