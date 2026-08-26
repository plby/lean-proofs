import ErdosProblems.Erdos421.PrimeLongIntervals
import ErdosProblems.Erdos421.WeightedBuchstab

/-! # Exact rough-number intervals and their Buchstab decomposition -/

namespace Erdos421

noncomputable def roughInRealInterval (a b : ℝ) (z : ℕ) : Finset ℕ :=
  sifted (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) z

theorem mem_integer_real_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ↔ a < n ∧ (n : ℝ) ≤ b := by
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨hnlo, hnhi⟩
    exact ⟨(Nat.floor_lt ha).mp hnlo, (Nat.cast_le.mpr hnhi).trans (Nat.floor_le (ha.trans hab))⟩
  · rintro ⟨hnlo, hnhi⟩
    exact ⟨(Nat.floor_lt ha).mpr hnlo, (Nat.le_floor_iff (ha.trans hab)).mpr hnhi⟩

theorem mem_roughInRealInterval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n z : ℕ) :
    n ∈ roughInRealInterval a b z ↔ a < n ∧ (n : ℝ) ≤ b ∧ RoughAt n z := by
  simp only [roughInRealInterval, sifted, Finset.mem_filter, mem_integer_real_interval ha hab]
  tauto

theorem sieveCofactors_real_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {p : ℕ} (hp : 0 < p) :
    sieveCofactors (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) p =
      Finset.Ioc ⌊a / (p : ℝ)⌋₊ ⌊b / (p : ℝ)⌋₊ := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  ext n
  rw [mem_sieveCofactors hp, mem_integer_real_interval ha hab,
    mem_integer_real_interval (div_nonneg ha hpr.le) (div_le_div_of_nonneg_right hab hpr.le)]
  push_cast
  rw [div_lt_iff₀ hpr, le_div_iff₀ hpr]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> nlinarith

theorem roughInRealInterval_buchstab {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {w z : ℕ} (hwz : w ≤ z) :
    (roughInRealInterval a b w).card = (roughInRealInterval a b z).card +
      ∑ p ∈ sievePrimes w z, (roughInRealInterval (a / p) (b / p) p).card := by
  have h := buchstab_identity (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) hwz
  change (roughInRealInterval a b w).card = (roughInRealInterval a b z).card + _ at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2
  rw [sieveCofactors_real_interval ha hab hpp.pos]
  rfl

end Erdos421
