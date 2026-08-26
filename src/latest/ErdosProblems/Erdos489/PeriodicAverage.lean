import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- Sum over an integral number of periods. -/
theorem sum_range_mul_periodic
    (f : ℕ → ℕ) (P : ℕ) (hf : Function.Periodic f P) (q : ℕ) :
    ∑ n ∈ Finset.range (q * P), f n =
      q * ∑ n ∈ Finset.range P, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa [Nat.add_comm, Nat.mul_comm] using (hf.nat_mul q n)

/-- Quotient/remainder decomposition of a periodic partial sum. -/
theorem sum_range_periodic_div_mod
    (f : ℕ → ℕ) (P x : ℕ) (hf : Function.Periodic f P) :
    ∑ n ∈ Finset.range x, f n =
      (x / P) * (∑ n ∈ Finset.range P, f n) +
        ∑ n ∈ Finset.range (x % P), f n := by
  by_cases hP : P = 0
  · subst P
    simp
  · have hx : x = (x / P) * P + x % P := by
      simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div x P).symm
    conv_lhs => rw [hx]
    rw [Finset.sum_range_add, sum_range_mul_periodic f P hf]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa [Nat.mul_comm, Nat.add_comm] using (hf.nat_mul (x / P) n)

/-- The real quotient `(x/P)/x` tends to `1/P`. -/
theorem tendsto_nat_div_cast_div (P : ℕ) (hP : 0 < P) :
    Tendsto (fun x : ℕ => ((x / P : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 (1 / (P : ℝ))) := by
  have hm := tendsto_mod_div_atTop_nhds_zero_nat hP
  have hbase : Tendsto (fun x : ℕ =>
      (1 - (((x % P : ℕ) : ℝ) / (x : ℝ))) / (P : ℝ))
      atTop (𝓝 ((1 - 0) / (P : ℝ))) :=
    (tendsto_const_nhds.sub hm).div_const (P : ℝ)
  have hbase' : Tendsto (fun x : ℕ =>
      (1 - (((x % P : ℕ) : ℝ) / (x : ℝ))) / (P : ℝ))
      atTop (𝓝 (1 / (P : ℝ))) := by simpa using hbase
  apply hbase'.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdecomp := Nat.mod_add_div x P
  have hdecompR : ((x % P : ℕ) : ℝ) +
      (P : ℝ) * ((x / P : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast hdecomp
  field_simp
  nlinarith

/-- Every nonnegative natural-valued periodic sequence has a Cesàro limit,
equal to its one-period mean. -/
theorem tendsto_periodic_nat_average
    (f : ℕ → ℕ) (P : ℕ) (hP : 0 < P)
    (hf : Function.Periodic f P) :
    Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f n : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 (((∑ n ∈ Finset.range P, f n : ℕ) : ℝ) / (P : ℝ))) := by
  let S : ℕ := ∑ n ∈ Finset.range P, f n
  let rem : ℕ → ℕ := fun x => ∑ n ∈ Finset.range (x % P), f n
  have hrem0 : ∀ x, 0 ≤ rem x := fun _ => Nat.zero_le _
  have hremS : ∀ x, rem x ≤ S := by
    intro x
    dsimp [rem, S]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.mod_lt x hP).le
    · intro i hiP hir
      exact Nat.zero_le _
  have hremT : Tendsto (fun x : ℕ => (rem x : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := (0 : ℝ)) (B := (S : ℝ))
    · exact Filter.Eventually.of_forall (fun x => by exact_mod_cast hrem0 x)
    · exact Filter.Eventually.of_forall (fun x => by exact_mod_cast hremS x)
    · exact tendsto_natCast_atTop_atTop
  have hq := (tendsto_nat_div_cast_div P hP).mul_const (S : ℝ)
  have hsum := hq.add hremT
  have hlim : (1 / (P : ℝ)) * (S : ℝ) + 0 = (S : ℝ) / (P : ℝ) := by ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdecomp := sum_range_periodic_div_mod f P x hf
  dsimp [S, rem] at hdecomp ⊢
  rw [hdecomp]
  norm_num only [Nat.cast_add, Nat.cast_mul]
  field_simp

end Erdos489
