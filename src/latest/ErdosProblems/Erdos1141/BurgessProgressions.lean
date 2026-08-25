import ErdosProblems.Erdos1141.BurgessLongIntervals
import ErdosProblems.Erdos1141.QuadraticRealCharacter

/-!
# The short two-adic factor and arithmetic progressions
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem sum_range_mul_eq_progressions (f : ℕ → ℝ) (h t M : ℕ) :
    (∑ i ∈ Finset.range (t * h), f (M + i)) =
      ∑ a ∈ Finset.range h, ∑ j ∈ Finset.range t, f (M + a + h * j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ac_rfl

theorem abs_sum_range_le_progressions (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {h : ℕ} (hh : 0 < h) (M H : ℕ) {B : ℝ}
    (hbound : ∀ a ∈ Finset.range h,
      |∑ j ∈ Finset.range (H / h), f (M + a + h * j)| ≤ B) :
    |∑ i ∈ Finset.range H, f (M + i)| ≤ (h : ℝ) * B + h := by
  have hdecomp : H = (H / h) * h + H % h := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod H h).symm
  have heq : (∑ i ∈ Finset.range H, f (M + i)) =
      (∑ a ∈ Finset.range h, ∑ j ∈ Finset.range (H / h), f (M + a + h * j)) +
        ∑ i ∈ Finset.range (H % h), f (M + ((H / h) * h + i)) := by
    calc
      _ = ∑ i ∈ Finset.range ((H / h) * h + H % h), f (M + i) := by rw [← hdecomp]
      _ = _ := by rw [Finset.sum_range_add, sum_range_mul_eq_progressions]
  have hmain : |∑ a ∈ Finset.range h,
      ∑ j ∈ Finset.range (H / h), f (M + a + h * j)| ≤ (h : ℝ) * B := by
    calc
      _ ≤ ∑ a ∈ Finset.range h, |∑ j ∈ Finset.range (H / h), f (M + a + h * j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ Finset.range h, B := Finset.sum_le_sum hbound
      _ = _ := by simp
  have htail : |∑ i ∈ Finset.range (H % h), f (M + ((H / h) * h + i))| ≤ h := by
    calc
      _ ≤ ∑ i ∈ Finset.range (H % h), |f (M + ((H / h) * h + i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (H % h), (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = (H % h : ℕ) := by simp
      _ ≤ (h : ℝ) := by exact_mod_cast (Nat.mod_lt H hh).le
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain htail)

theorem abs_twisted_progression_sum_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {h : ℕ} (hcop : h.Coprime (primeModulus s))
    (θ : DirichletCharacter ℝ h) (hθ : θ.IsQuadratic) (a L : ℕ) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ M : ℕ, |∑ j ∈ Finset.range L,
      productChar s hs (M + j : ℕ)| ≤ B) :
    |∑ j ∈ Finset.range L,
      θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ)| ≤ B := by
  let q := primeModulus s
  let t : ℕ := ((h : ZMod q)⁻¹ * a).val
  have halg (j : ℕ) : ((a + h * j : ℕ) : ZMod q) =
      (h : ZMod q) * (t + j : ℕ) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul]
    dsimp only [t]
    rw [ZMod.natCast_zmod_val, mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one h hcop, one_mul]
  have hterm (j : ℕ) : θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ) =
      (θ (a : ZMod h) * productChar s hs (h : ZMod q)) * productChar s hs (t + j : ℕ) := by
    have hθval : θ (a + h * j : ℕ) = θ (a : ZMod h) := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hθval, halg, productChar_mul]
    ring
  have hθabs : |θ (a : ZMod h)| ≤ 1 := by
    rcases hθ (a : ZMod h) with hz | hz | hz <;> norm_num [hz]
  have hcoeff : |θ (a : ZMod h) * productChar s hs (h : ZMod q)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hθabs (abs_productChar_le_one s hs _) (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  simp_rw [hterm]
  rw [← Finset.mul_sum, abs_mul]
  exact (mul_le_mul hcoeff (hbound t) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem div_small_modulus_ge_scale {H h : ℕ} (hh : 0 < h) (hh8 : h ≤ 8)
    {Q : ℝ} (hQ : 1 ≤ Q) (hH : 16 * Q ≤ H) : Q ≤ ((H / h : ℕ) : ℝ) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh8' : (h : ℝ) ≤ 8 := by exact_mod_cast hh8
  have hdiv : (H : ℝ) / h < ((H / h : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using Nat.lt_floor_add_one ((H : ℝ) / h)
  have hHlt := (div_lt_iff₀ hh0).mp hdiv
  have hmul := mul_le_mul_of_nonneg_left hh8'
    (by positivity : (0 : ℝ) ≤ ((H / h : ℕ) : ℝ) + 1)
  linarith only [hQ, hH, hHlt, hmul]

theorem eventually_twisted_squarefree_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q →
        ∀ h : ℕ, 0 < h → h ≤ 8 → h.Coprime q →
          ∀ θ : DirichletCharacter ℝ h, θ.IsQuadratic →
            ∀ M H : ℕ, (q : ℝ) ^ d ≤ H →
              |∑ i ∈ Finset.range H, θ (M + i : ℕ) * productChar s hs (M + i : ℕ)| ≤
                (H : ℝ) * (q : ℝ) ^ (-σ) := by
  let c : ℝ := (d + 1 / 4) / 2
  have hc : 1 / 4 < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c]; linarith
  have hd0 : 0 < d := by linarith
  obtain ⟨η, hη, hburgess⟩ := eventually_squarefree_burgess hc
  let σ : ℝ := min η d / 2
  have hσ : 0 < σ := half_pos (lt_min hη hd0)
  have hση : σ < η := by have h := min_le_left η d; dsimp [σ]; linarith
  have hσd : σ < d := by have h := min_le_right η d; dsimp [σ]; linarith
  have hscale := eventually_const_mul_rpow_le (C := 16) (d := 1) (by norm_num) hcd
  have hmain := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := -η) (b := -σ) (by norm_num) (by linarith)
  have htail := eventually_const_mul_rpow_le (C := 8) (d := 1 / 2)
    (a := 0) (b := d - σ) (by norm_num) (by linarith)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hburgess, hscale, hmain, htail, eventually_ge_atTop 1]
    with q hburgessq hscaleq hmainq htailq hq1
  intro s hs hsq h hh hh8 hcop θ hθ M H hH
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  have hcop' : h.Coprime (primeModulus s) := by simpa only [hsq] using hcop
  have hscale' : 16 * (q : ℝ) ^ c ≤ (q : ℝ) ^ d := by simpa only [one_mul] using hscaleq
  have hHscale : 16 * (q : ℝ) ^ c ≤ H := hscale'.trans hH
  have hN : (q : ℝ) ^ c ≤ ((H / h : ℕ) : ℝ) :=
    div_small_modulus_ge_scale hh hh8
      (Real.one_le_rpow (by exact_mod_cast hq1) (by linarith)) hHscale
  have hB : 0 ≤ ((H / h : ℕ) : ℝ) * (q : ℝ) ^ (-η) := by positivity
  have hθabs (n : ℕ) : |θ (n : ZMod h)| ≤ 1 := by
    rcases hθ (n : ZMod h) with hz | hz | hz <;> norm_num [hz]
  have hf (n : ℕ) : |θ (n : ZMod h) * productChar s hs (n : ℕ)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hθabs n) (abs_productChar_le_one s hs _) (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  have hprog (a : ℕ) : |∑ j ∈ Finset.range (H / h),
      θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ)| ≤
      ((H / h : ℕ) : ℝ) * (q : ℝ) ^ (-η) :=
    abs_twisted_progression_sum_le s hs hcop' θ hθ a (H / h) hB
      (fun K => hburgessq s hs hsq K (H / h) hN)
  have hsum := abs_sum_range_le_progressions
    (fun n => θ (n : ZMod h) * productChar s hs (n : ℕ)) hf hh M H
    (fun a _ => by simpa only [Nat.add_assoc] using hprog (M + a))
  have hcount : (h : ℝ) * ((H / h : ℕ) : ℝ) ≤ H := by
    exact_mod_cast Nat.mul_div_le H h
  have hraw : |∑ i ∈ Finset.range H, θ (M + i : ℕ) * productChar s hs (M + i : ℕ)| ≤
      (H : ℝ) * (q : ℝ) ^ (-η) + 8 := by
    refine hsum.trans ?_
    have hm := mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hq0.le (-η))
    have hh8' : (h : ℝ) ≤ 8 := by exact_mod_cast hh8
    nlinarith only [hm, hh8']
  have hfirst : (H : ℝ) * (q : ℝ) ^ (-η) ≤
      (1 / 2 : ℝ) * ((H : ℝ) * (q : ℝ) ^ (-σ)) := by
    have hm := mul_le_mul_of_nonneg_left hmainq (Nat.cast_nonneg H)
    nlinarith only [hm]
  have hsecond : (8 : ℝ) ≤ (1 / 2 : ℝ) * ((H : ℝ) * (q : ℝ) ^ (-σ)) := by
    have ht : (8 : ℝ) ≤ (1 / 2 : ℝ) * ((q : ℝ) ^ d * (q : ℝ) ^ (-σ)) := by
      simpa only [Real.rpow_zero, mul_one, sub_eq_add_neg, Real.rpow_add hq0] using htailq
    exact ht.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hq0.le _)) (by norm_num))
  nlinarith only [hraw, hfirst, hsecond]

end Pollack17.Burgess
