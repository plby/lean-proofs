import ErdosProblems.Erdos421.DivisibilityWindows
import ErdosProblems.Erdos421.OneSidedSchwartzWindow

/-! # The Poisson lattice window counts positive multiples in a finite interval -/

namespace Erdos421

noncomputable def additiveIntegerWeight (Y x : ℝ) (n : ℕ) : ℂ :=
  (Y⁻¹ : ℝ) • oneSidedSchwartzWindow ((x - n) / Y)

theorem additiveIntegerWeight_nonzero {Y x : ℝ} (hY : 0 < Y) {n : ℕ}
    (hn : additiveIntegerWeight Y x n ≠ 0) : x < n ∧ (n : ℝ) < x + Y := by
  have hφ : oneSidedSchwartzWindow ((x - n) / Y) ≠ 0 := by
    intro h
    apply hn
    simp only [additiveIntegerWeight, h, smul_zero]
  obtain ⟨hlo, hhi⟩ := oneSidedSchwartzWindow_nonzero hφ
  have hlow := (lt_div_iff₀ hY).mp hlo
  have hhigh := (div_lt_iff₀ hY).mp hhi
  constructor <;> linarith

theorem sum_positive_multiples {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {m : ℕ} (hm : 0 < m) (B : ℕ) :
    (∑ k ∈ Finset.Icc 1 (B / m), f (m * k)) =
      ∑ n ∈ Finset.Icc 1 B, if m ∣ n then f n else 0 := by
  classical
  have hset : (Finset.Icc 1 (B / m)).image (fun k ↦ m * k) =
      (Finset.Icc 1 B).filter (fun n ↦ m ∣ n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hk1, hkB⟩ := Finset.mem_Icc.mp hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hm hk1, ?_⟩,
        dvd_mul_right m k⟩
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hm).mp hkB
    · intro hn
      obtain ⟨hn, hmn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnB⟩ := Finset.mem_Icc.mp hn
      refine Finset.mem_image.mpr ⟨n / m, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnB⟩,
        Nat.mul_div_cancel' hmn⟩
      exact Nat.div_pos (Nat.le_of_dvd hn1 hmn) hm
  rw [← Finset.sum_filter, ← hset, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left hm hab

theorem additiveDivisorWindow_positive_sum {Y x : ℝ} (hY : 0 < Y) (hx : 0 ≤ x)
    {m : ℕ} (hm : 0 < m) {B : ℕ} (hB : x + Y ≤ B) :
    additiveDivisorWindow oneSidedSchwartzWindow Y x m =
      ∑ n ∈ Finset.Icc 1 B, if m ∣ n then additiveIntegerWeight Y x n else 0 := by
  classical
  let S := (Finset.Icc 1 (B / m)).image (fun k : ℕ ↦ -(k : ℤ))
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hsupport (j : ℤ) (hj : j ∉ S) :
      (Y⁻¹ : ℝ) • oneSidedSchwartzWindow ((x + (m : ℝ) * j) / Y) = 0 := by
    by_contra hne
    have hφ : oneSidedSchwartzWindow ((x + (m : ℝ) * j) / Y) ≠ 0 := by
      intro h
      apply hne
      rw [h, smul_zero]
    obtain ⟨hlo, hhi⟩ := oneSidedSchwartzWindow_nonzero hφ
    have hlow := (lt_div_iff₀ hY).mp hlo
    have hhigh := (div_lt_iff₀ hY).mp hhi
    have hjneg : j < 0 := by
      have hjR : (j : ℝ) < 0 := by nlinarith
      exact_mod_cast hjR
    let k := (-j).toNat
    have hkcast : (k : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    have hkpos : 0 < k := by omega
    have hkR : (k : ℝ) = -(j : ℝ) := by exact_mod_cast hkcast
    have hmk : m * k ≤ B := by
      have hmkR : (m : ℝ) * k ≤ B := by rw [hkR]; nlinarith
      exact_mod_cast hmkR
    apply hj
    refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hkpos, ?_⟩, ?_⟩
    · exact (Nat.le_div_iff_mul_le hm).mpr (by simpa only [mul_comm] using hmk)
    · omega
  rw [additiveDivisorWindow, tsum_eq_sum hsupport]
  change (∑ j ∈ (Finset.Icc 1 (B / m)).image (fun k : ℕ ↦ -(k : ℤ)), _) = _
  rw [Finset.sum_image]
  · rw [← sum_positive_multiples (additiveIntegerWeight Y x) hm B]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [additiveIntegerWeight, Nat.cast_mul, Int.cast_neg, Int.cast_natCast,
      mul_neg, sub_eq_add_neg]
  · intro a ha b hb hab
    exact_mod_cast neg_injective hab

end Erdos421
