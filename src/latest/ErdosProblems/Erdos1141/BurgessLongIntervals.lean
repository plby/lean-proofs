import ErdosProblems.Erdos1141.BurgessQuarter

/-!
# Extending fixed-block cancellation to every longer interval
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem abs_sum_range_multiple_le (f : ℕ → ℝ) (H : ℕ) {B : ℝ}
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range H, f (M + i)| ≤ B) (t M : ℕ) :
    |∑ i ∈ Finset.range (t * H), f (M + i)| ≤ (t : ℝ) * B := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range H, f (M + (t * H + i))) =
        ∑ i ∈ Finset.range H, f (M + t * H + i) := by
      simp only [Nat.add_assoc]
    rw [htail]
    have htri := (abs_add_le _ _).trans (add_le_add ih (hblock (M + t * H)))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using htri

theorem abs_sum_range_le_blocks (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {H : ℕ} (hH : 0 < H) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range H, f (M + i)| ≤ B) (M L : ℕ) :
    |∑ i ∈ Finset.range L, f (M + i)| ≤ (L : ℝ) * (B / H) + H := by
  have hdecomp : L = (L / H) * H + L % H := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod L H).symm
  have heq : (∑ i ∈ Finset.range L, f (M + i)) =
      (∑ i ∈ Finset.range ((L / H) * H), f (M + i)) +
        ∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i)) := by
    calc
      _ = ∑ i ∈ Finset.range ((L / H) * H + L % H), f (M + i) := by rw [← hdecomp]
      _ = _ := Finset.sum_range_add _ _ _
  have htail : |∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i))| ≤ H := by
    calc
      _ ≤ ∑ i ∈ Finset.range (L % H), |f (M + ((L / H) * H + i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (L % H), (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = (L % H : ℕ) := by simp
      _ ≤ (H : ℝ) := by exact_mod_cast (Nat.mod_lt L hH).le
  rw [heq]
  calc
    _ ≤ |∑ i ∈ Finset.range ((L / H) * H), f (M + i)| +
        |∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i))| := abs_add_le _ _
    _ ≤ ((L / H : ℕ) : ℝ) * B + H :=
      add_le_add (abs_sum_range_multiple_le f H hblock (L / H) M) htail
    _ ≤ ((L : ℝ) / H) * B + H :=
      add_le_add (mul_le_mul_of_nonneg_right Nat.cast_div_le hB) le_rfl
    _ = _ := by ring

theorem block_bound_implies_long_bound {q : ℕ} (hq : 0 < q) {c η : ℝ}
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hfloor : (q : ℝ) ^ c / 2 ≤ (⌊(q : ℝ) ^ c⌋₊ : ℝ))
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, f (M + i)| ≤
      (q : ℝ) ^ (c - η)) (M L : ℕ) :
    |∑ i ∈ Finset.range L, f (M + i)| ≤
      2 * (L : ℝ) * (q : ℝ) ^ (-η) + (q : ℝ) ^ c := by
  let H := ⌊(q : ℝ) ^ c⌋₊
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hfloor
  have hHpos : 0 < H := by exact_mod_cast hH0
  have hratio : (q : ℝ) ^ (c - η) / H ≤ 2 * (q : ℝ) ^ (-η) := by
    apply (div_le_iff₀ hH0).mpr
    calc
      _ = (2 * (q : ℝ) ^ (-η)) * ((q : ℝ) ^ c / 2) := by
        rw [show c - η = -η + c by ring, Real.rpow_add hq0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)
  have h := abs_sum_range_le_blocks f hf hHpos (Real.rpow_nonneg hq0.le _) hblock M L
  calc
    _ ≤ (L : ℝ) * ((q : ℝ) ^ (c - η) / H) + H := h
    _ ≤ (L : ℝ) * (2 * (q : ℝ) ^ (-η)) + (q : ℝ) ^ c :=
      add_le_add (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg L))
        (Nat.floor_le (Real.rpow_nonneg hq0.le c))
    _ = _ := by ring

theorem eventually_squarefree_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q →
        ∀ M L : ℕ, (q : ℝ) ^ d ≤ L →
          |∑ i ∈ Finset.range L, productChar s hs (M + i : ℕ)| ≤
            (L : ℝ) * (q : ℝ) ^ (-σ) := by
  let c : ℝ := min ((d + 1 / 4) / 2) (3 / 8)
  have hc : 1 / 4 < c := lt_min (by linarith) (by norm_num)
  have hc' : c < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hcd : c < d := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨η, hη, hblock⟩ := eventually_quarter_block_cancellation hc hc'
  let σ : ℝ := min η (d - c) / 2
  have hσ : 0 < σ := half_pos (lt_min hη (sub_pos.mpr hcd))
  have hση : σ < η := by
    have h := min_le_left η (d - c)
    dsimp [σ]
    linarith
  have hσd : σ < d - c := by
    have h := min_le_right η (d - c)
    dsimp [σ]
    linarith
  have hmain := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := -η) (b := -σ) (by norm_num) (by linarith)
  have hrem := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := c) (b := d - σ) (by norm_num) (by linarith)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hblock, hmain, hrem, eventually_floor_rpow_bounds (by linarith : 0 < c),
    eventually_ge_atTop 1] with q hblockq hmainq hremq hfloor hq1
  intro s hs hsq M L hL
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hb := block_bound_implies_long_bound (by omega : 0 < q)
    (fun n => productChar s hs (n : ℕ))
    (fun n => abs_productChar_le_one s hs _) hfloor.1 (hblockq s hs hsq) M L
  have hfirst : 2 * (L : ℝ) * (q : ℝ) ^ (-η) ≤
      (1 / 2 : ℝ) * ((L : ℝ) * (q : ℝ) ^ (-σ)) := by
    have h := mul_le_mul_of_nonneg_left hmainq (Nat.cast_nonneg L)
    nlinarith only [h]
  have hsecond : (q : ℝ) ^ c ≤ (1 / 2 : ℝ) * ((L : ℝ) * (q : ℝ) ^ (-σ)) := by
    have hrem' : (q : ℝ) ^ c ≤ (1 / 2 : ℝ) * ((q : ℝ) ^ d * (q : ℝ) ^ (-σ)) := by
      simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hq0] using hremq
    exact hrem'.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hq0.le _)) (by norm_num))
  nlinarith only [hb, hfirst, hsecond]

end Pollack17.Burgess
