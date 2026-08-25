import ErdosProblems.Erdos1141.BurgessEnergy
import ErdosProblems.Erdos1141.BurgessHolder

/-!
# Interval averaging for real multiplicative characters

The boundary estimates are extracted from `Erdos587.NVDevelopment`.
The amplification below allows any finite family of coprime denominators.
-/

namespace Pollack17.Burgess

open scoped BigOperators

lemma abs_sum_range_shift_sub_le (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (M H h : ℕ) (hh : h ≤ H) :
    |(∑ i ∈ Finset.range H, f (M + i)) -
      ∑ i ∈ Finset.range H, f (M + h + i)| ≤ 2 * h := by
  have hH₁ : h + (H - h) = H := Nat.add_sub_of_le hh
  have hH₂ : (H - h) + h = H := Nat.sub_add_cancel hh
  have hdecomp :
      (∑ i ∈ Finset.range H, f (M + i)) -
          ∑ i ∈ Finset.range H, f (M + h + i) =
        (∑ i ∈ Finset.range h, f (M + i)) -
          ∑ i ∈ Finset.range h, f (M + H + i) := by
    have hleft := Finset.sum_range_add (fun i ↦ f (M + i)) h (H - h)
    have hright := Finset.sum_range_add
      (fun i ↦ f (M + h + i)) (H - h) h
    rw [hH₁] at hleft
    rw [hH₂] at hright
    rw [hleft, hright]
    have hmiddle :
        (∑ x ∈ Finset.range (H - h), f (M + (h + x))) =
          ∑ x ∈ Finset.range (H - h), f (M + h + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    have hsuffix :
        (∑ x ∈ Finset.range h, f (M + h + ((H - h) + x))) =
          ∑ x ∈ Finset.range h, f (M + H + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hmiddle, hsuffix]
    ring
  rw [hdecomp]
  calc
    |(∑ i ∈ Finset.range h, f (M + i)) -
        ∑ i ∈ Finset.range h, f (M + H + i)| ≤
        |∑ i ∈ Finset.range h, f (M + i)| +
          |∑ i ∈ Finset.range h, f (M + H + i)| := abs_sub _ _
    _ ≤ (∑ i ∈ Finset.range h, |f (M + i)|) +
        ∑ i ∈ Finset.range h, |f (M + H + i)| := by
      gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i ∈ Finset.range h, (1 : ℝ)) +
        ∑ _i ∈ Finset.range h, (1 : ℝ) := by
      gcongr <;> exact hf _
    _ = 2 * h := by simp; ring

lemma abs_burgess_shift_average_sub_le
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (M H : ℕ) (U V : Finset ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ u ∈ U, ∀ v ∈ V, g u v ≤ H) :
    |((U.card * V.card : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, f (M + i)) -
      ∑ u ∈ U, ∑ v ∈ V,
        ∑ i ∈ Finset.range H, f (M + g u v + i)| ≤
      ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
  let S : ℕ → ℝ := fun h ↦ ∑ i ∈ Finset.range H, f (M + h + i)
  have hS0 : S 0 = ∑ i ∈ Finset.range H, f (M + i) := by
    simp [S]
  have heq :
      ((U.card * V.card : ℕ) : ℝ) * S 0 -
          ∑ u ∈ U, ∑ v ∈ V, S (g u v) =
        ∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v)) := by
    simp only [Finset.sum_sub_distrib]
    simp
    ring
  rw [← hS0, heq]
  calc
    |∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v))| ≤
        ∑ u ∈ U, |∑ v ∈ V, (S 0 - S (g u v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, |S 0 - S (g u v)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simpa [S] using
        abs_sum_range_shift_sub_le f hf M H (g u v) (hg u hu v hv)

lemma abs_burgess_shifted_triple_sum_le_finset
    (f : ℕ → ℝ) (M H : ℕ) (U V : Finset ℕ) (shift : ℕ → ℕ → ℕ) :
    |∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
        f (M + shift u v + i)| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
  have hreorder :
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + i + shift u v) := by
    calc
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ u ∈ U, ∑ i ∈ Finset.range H,
          ∑ v ∈ V, f (M + shift u v + i) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + shift u v + i) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ U,
        ∑ v ∈ V, f (M + i + shift u v)| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ U, ∑ v ∈ V, f (M + i + shift u v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

noncomputable def naturalShiftSum {q : ℕ} (f : ZMod q → ℝ) (V : ℕ) (x : ZMod q) : ℝ :=
  ∑ v ∈ Finset.Icc 1 V, f (x + v)

noncomputable def amplifierNumerator {q : ℕ} [NeZero q] (f : ZMod q → ℝ)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * |naturalShiftSum f V x|

theorem amplifierNumerator_nonneg {q : ℕ} [NeZero q] (f : ZMod q → ℝ)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ) : 0 ≤ amplifierNumerator f M H D V :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

theorem abs_natural_dilated_sum {q : ℕ} (f : ZMod q → ℝ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (M i u V : ℕ)
    (hu : u.Coprime q) (hfu : |f u| = 1) :
    |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| =
      |naturalShiftSum f V ((u : ZMod q)⁻¹ * (M + i : ℕ))| := by
  have halg (v : ℕ) : ((M + i + u * v : ℕ) : ZMod q) =
      u * ((u : ZMod q)⁻¹ * (M + i : ℕ) + v) := by
    rw [mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one u hu, one_mul]
    push_cast
    ring
  simp_rw [halg, hmul]
  rw [← Finset.mul_sum, abs_mul, hfu, one_mul]
  rfl

theorem amplifierNumerator_eq_natural {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) (hfD : ∀ u ∈ D, |f u| = 1) :
    amplifierNumerator f M H D V =
      ∑ i ∈ Finset.range H, ∑ u ∈ D,
        |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| := by
  rw [amplifierNumerator, sum_naturalRatioWeight_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u hu
  exact (abs_natural_dilated_sum f hmul M i u V (hD u hu) (hfD u hu)).symm

theorem amplified_abs_le {q M H U V : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hf : ∀ x, |f x| ≤ 1) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hfD : ∀ u ∈ D, |f u| = 1) (hUV : U * V ≤ H) :
    (D.card : ℝ) * V * |∑ i ∈ Finset.range H, f (M + i : ℕ)| ≤
      amplifierNumerator f M H D V + 2 * (D.card : ℝ) * V * (U * V) := by
  let S := ∑ i ∈ Finset.range H, f (M + i : ℕ)
  let T := ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V,
    ∑ i ∈ Finset.range H, f (M + u * v + i : ℕ)
  have havg := abs_burgess_shift_average_sub_le (fun n => f (n : ZMod q))
    (fun n => hf _) M H D (Finset.Icc 1 V) (fun u v => u * v) (by
      intro u hu v hv
      exact (Nat.mul_le_mul (Finset.mem_Icc.mp (hD hu)).2
        (Finset.mem_Icc.mp hv).2).trans hUV)
  have herror : |(D.card : ℝ) * V * S - T| ≤
      2 * (D.card : ℝ) * V * (U * V) := by
    have havg' : |(D.card : ℝ) * V * S - T| ≤
        ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V, ((2 * (u * v) : ℕ) : ℝ) := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul] using havg
    refine havg'.trans ?_
    calc
      _ ≤ ∑ _u ∈ D, ∑ _v ∈ Finset.Icc 1 V, ((2 * (U * V) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast Nat.mul_le_mul_left 2 (Nat.mul_le_mul
          (Finset.mem_Icc.mp (hD hu)).2 (Finset.mem_Icc.mp hv).2)
      _ = _ := by simp; ring
  have hT : |T| ≤ amplifierNumerator f M H D V := by
    rw [amplifierNumerator_eq_natural f hmul M H D V hcop hfD]
    exact abs_burgess_shifted_triple_sum_le_finset
      (fun n => f (n : ZMod q)) M H D (Finset.Icc 1 V) (fun u v => u * v)
  have htri : |(D.card : ℝ) * V * S| ≤ |(D.card : ℝ) * V * S - T| + |T| := by
    simpa only [sub_add_cancel] using abs_add_le ((D.card : ℝ) * V * S - T) T
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at htri
  exact htri.trans ((add_le_add herror hT).trans_eq (add_comm _ _))

theorem amplifierNumerator_even_power_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (M H : ℕ) (D : Finset ℕ) (V k : ℕ) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := by
  have hh := weighted_even_power_sum_le (Finset.univ : Finset (ZMod q))
    (fun x => (naturalRatioWeight q M H D x : ℝ))
    (fun x => |naturalShiftSum f V x|)
    (fun x _ => Nat.cast_nonneg _) (fun x _ => abs_nonneg _) k
  have hsum : (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ)) =
      (H : ℝ) * D.card := by exact_mod_cast sum_naturalRatioWeight q M H D
  have habs (x : ZMod q) : |naturalShiftSum f V x| ^ (2 * (k + 1)) =
      naturalShiftSum f V x ^ (2 * (k + 1)) := (even_two_mul _).pow_abs _
  simpa only [hsum, habs, amplifierNumerator, naturalRatioEnergy] using hh

end Pollack17.Burgess
