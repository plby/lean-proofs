import ErdosProblems.Erdos245.Inverse

open Filter Set
open scoped Pointwise Topology

namespace Erdos245Scratch

open Erdos899

lemma countIn_inter_Ici_one (A : Set ℕ) (N : ℕ) :
    countIn (A ∩ Ici 1) N = countIn A N := by
  rw [countIn_eq_ncard, countIn_eq_ncard]
  congr 1
  ext n
  simp only [mem_inter_iff, mem_Ici, mem_Icc]
  tauto

/-- The affirmative resolution of Erdős Problem 245. -/
theorem erdos_245 :
    ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (nhds 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
          (A ∩ Icc 1 ⌊N⌋₊).ncard := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _htrue A hA hdenReal
    let S := A ∩ Ici 1
    have hS : S.Infinite := by
      have hdiff : (A \ {0}).Infinite := hA.sdiff (Set.finite_singleton 0)
      have heq : A \ {0} = S := by
        ext n
        simp [S, Nat.one_le_iff_ne_zero]
      rwa [heq] at hdiff
    have hpos : S ⊆ Ici 1 := inter_subset_right
    have hcount (N : ℕ) : countIn S N = countIn A N := by
      simpa [S] using countIn_inter_Ici_one A N
    have hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N)
        atTop (nhds 0) := by
      have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have hcomp := hdenReal.comp hcast
      change Tendsto
        (fun n : ℕ ↦
          (A ∩ Icc 1 ⌊(n : ℝ)⌋₊ |>.ncard : ℝ) / (n : ℝ))
        atTop (nhds 0) at hcomp
      simpa only [Nat.floor_natCast, ← countIn_eq_ncard, hcount] using hcomp
    let ratio : ℝ → EReal := fun N ↦
      ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
        (A ∩ Icc 1 ⌊N⌋₊).ncard
    change 3 ≤ atTop.limsup ratio
    by_contra hnot
    have hlim : atTop.limsup ratio < (3 : EReal) := lt_of_not_ge hnot
    obtain ⟨c, hlimc, hc3E⟩ := EReal.lt_iff_exists_real_btwn.mp hlim
    have hc3 : c < 3 := by
      change (c : EReal) < ((3 : ℝ) : EReal) at hc3E
      exact EReal.coe_lt_coe_iff.mp hc3E
    obtain ⟨m, hm, hminv⟩ :=
      Real.exists_nat_pos_inv_lt (sub_pos.mpr hc3)
    have hcb : c < 3 - (m : ℝ)⁻¹ := by linarith
    have hlimb : atTop.limsup ratio <
        (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) :=
      hlimc.trans (EReal.coe_lt_coe hcb)
    have hratioReal : ∀ᶠ N in atTop,
        ratio N < (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt hlimb
    have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hratioNat : ∀ᶠ n : ℕ in atTop,
        (countIn (A + A) n : EReal) / countIn A n <
          (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) := by
      have hcomp := hcast.eventually hratioReal
      simpa only [ratio, Nat.floor_natCast, ← countIn_eq_ncard] using hcomp
    have hSS : S + S ⊆ A + A :=
      Set.add_subset_add inter_subset_left inter_subset_left
    have hpositive : ∀ᶠ n in atTop, 0 < countIn S n :=
      eventually_countIn_pos hS hpos
    have hscaled : ∀ᶠ n in atTop,
        m * countIn (S + S) n < (3 * m - 1) * countIn S n := by
      filter_upwards [hratioNat, hpositive] with n hratio hnpos
      have hratio' :
          (((countIn (A + A) n : ℝ) : EReal) /
              ((countIn A n : ℝ) : EReal)) <
            (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) := by
        simpa only [EReal.coe_coe_eq_natCast] using hratio
      have hratioℝ :
          (countIn (A + A) n : ℝ) / (countIn A n : ℝ) <
            3 - (m : ℝ)⁻¹ := by
        rw [← EReal.coe_div, EReal.coe_lt_coe_iff] at hratio'
        exact hratio'
      have hApos : 0 < (countIn A n : ℝ) := by
        rw [← hcount]
        exact_mod_cast hnpos
      have hcross : (countIn (A + A) n : ℝ) <
          (3 - (m : ℝ)⁻¹) * countIn A n :=
        (div_lt_iff₀ hApos).mp hratioℝ
      have hsubcount : countIn (S + S) n ≤ countIn (A + A) n :=
        countIn_mono_set hSS n
      have hmℝ : 0 < (m : ℝ) := by exact_mod_cast hm
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmℝ
      have hid :
          (m : ℝ) * (3 - (m : ℝ)⁻¹) = ((3 * m - 1 : ℕ) : ℝ) := by
        rw [mul_sub, mul_inv_cancel₀ hmne]
        rw [Nat.cast_sub (by omega : 1 ≤ 3 * m), Nat.cast_mul]
        norm_num
        ring
      have hscaledℝ :
          (m : ℝ) * countIn (S + S) n <
            ((3 * m - 1 : ℕ) : ℝ) * countIn S n := by
        calc
          (m : ℝ) * countIn (S + S) n ≤
              (m : ℝ) * countIn (A + A) n := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsubcount) hmℝ.le
          _ < (m : ℝ) *
              ((3 - (m : ℝ)⁻¹) * countIn A n) :=
            mul_lt_mul_of_pos_left hcross hmℝ
          _ = ((3 * m - 1 : ℕ) : ℝ) * countIn S n := by
            rw [← mul_assoc, hid, hcount]
      exact_mod_cast hscaledℝ
    exact (not_eventually_scaled_sum_lt_three hS hpos hden m hm hscaled).elim
  · intro _h
    trivial

#print axioms Erdos245Scratch.erdos_245

end Erdos245Scratch
