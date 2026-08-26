import ErdosProblems.Erdos4.FiberAsymptotic
import BoundedGaps.Maynard.ImprovedGPY.CongruenceCount

/-!
# A residue-class count with a fixed coprimality condition

For coprime moduli `W` and `d`, a residue class modulo `d` meets each
permitted residue modulo `W` in exactly one CRT class. The total endpoint
error is at most `totient W`, independent of `d` and of the interval length.
-/

open scoped BigOperators

namespace Erdos4.CoprimeResidueCount

noncomputable def residueCount (Y d a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, if n ≡ a [MOD d] then 1 else 0

noncomputable def coprimeCount (Y W d a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, if n.Coprime W ∧ n ≡ a [MOD d] then 1 else 0

theorem residueCount_eq_card (Y d a : ℕ) : residueCount Y d a =
    (((Finset.Icc 1 Y).filter (fun n => n ≡ a [MOD d])).card : ℝ) := by
  classical
  unfold residueCount
  rw [← Finset.sum_filter]
  simp

theorem residueCount_error_le (Y d a : ℕ) (hd : 0 < d) :
    |residueCount Y d a - (Y : ℝ) / d| ≤ 1 := by
  have hh := BoundedGaps.Maynard.intervalModEqCardError_abs_le_one 1 (Y + 1) d a (by omega) hd
  have hI : Finset.Ico 1 (Y + 1) = Finset.Icc 1 Y := by ext n; simp
  rw [residueCount_eq_card]
  simpa only [BoundedGaps.Maynard.intervalModEqCardError, hI,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hh

theorem coprime_mod (n W : ℕ) : (n % W).Coprime W ↔ n.Coprime W := by
  change (n % W).gcd W = 1 ↔ n.gcd W = 1
  rw [Nat.gcd_comm n W, Nat.gcd_rec W n]

theorem sum_coprime_residues (W : ℕ) :
    (∑ v ∈ Finset.range W, if v.Coprime W then (1 : ℝ) else 0) = Nat.totient W := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Nat.totient_eq_card_coprime]
  congr 1
  congr 1
  ext v
  simp only [Finset.mem_filter, Nat.coprime_comm]

theorem crt_iff {W d : ℕ} (hWd : W.Coprime d) (v a n : ℕ) :
    n ≡ (Nat.chineseRemainder hWd v a : ℕ) [MOD W * d] ↔
      n ≡ v [MOD W] ∧ n ≡ a [MOD d] := by
  constructor
  · intro hn
    have hh := (Nat.modEq_and_modEq_iff_modEq_mul hWd).mpr hn
    exact ⟨hh.1.trans (Nat.chineseRemainder hWd v a).property.1,
      hh.2.trans (Nat.chineseRemainder hWd v a).property.2⟩
  · intro hn
    exact Nat.chineseRemainder_modEq_unique hWd hn.1 hn.2

theorem coprimeCount_split (Y W d a : ℕ) (hW : 0 < W) (hWd : W.Coprime d) :
    coprimeCount Y W d a = ∑ v ∈ Finset.range W,
      if v.Coprime W then residueCount Y (W * d) (Nat.chineseRemainder hWd v a) else 0 := by
  classical
  have hpoint : ∀ n : ℕ, (if n.Coprime W ∧ n ≡ a [MOD d] then (1 : ℝ) else 0) =
      ∑ v ∈ Finset.range W, if v.Coprime W then
        (if n ≡ (Nat.chineseRemainder hWd v a : ℕ) [MOD W * d] then 1 else 0) else 0 := by
    intro n
    symm
    calc
      _ = ∑ v ∈ Finset.range W, if v = n % W then
          (if n.Coprime W ∧ n ≡ a [MOD d] then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvW := Finset.mem_range.mp hv
        have hmod : n ≡ v [MOD W] ↔ v = n % W := by
          change n % W = v % W ↔ v = n % W
          rw [Nat.mod_eq_of_lt hvW]
          exact eq_comm
        simp only [crt_iff hWd, hmod]
        by_cases hvn : v = n % W
        · subst v
          by_cases hc : n.Coprime W <;> by_cases ha : n ≡ a [MOD d] <;>
            simp [coprime_mod, hc, ha]
        · simp [hvn]
      _ = _ := by simp [Nat.mod_lt n hW]
  unfold coprimeCount
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hv : v.Coprime W
  · simp only [if_pos hv, residueCount]
  · simp only [if_neg hv, Finset.sum_const_zero]

theorem coprimeCount_error_le (Y W d a : ℕ) (hW : 0 < W) (hd : 0 < d)
    (hWd : W.Coprime d) :
    |coprimeCount Y W d a -
      (Nat.totient W : ℝ) * ((Y : ℝ) / (W * d : ℕ))| ≤ Nat.totient W := by
  classical
  have hmain : (Nat.totient W : ℝ) * ((Y : ℝ) / (W * d : ℕ)) =
      ∑ v ∈ Finset.range W, if v.Coprime W then (Y : ℝ) / (W * d : ℕ) else 0 := by
    rw [← sum_coprime_residues, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _hv
    split_ifs <;> simp
  rw [coprimeCount_split Y W d a hW hWd, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ v ∈ Finset.range W,
        |(if v.Coprime W then residueCount Y (W * d) (Nat.chineseRemainder hWd v a) else 0) -
          (if v.Coprime W then (Y : ℝ) / (W * d : ℕ) else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ Finset.range W, if v.Coprime W then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro v _hv
      by_cases hv : v.Coprime W
      · simp only [if_pos hv]
        exact residueCount_error_le Y (W * d) (Nat.chineseRemainder hWd v a) (Nat.mul_pos hW hd)
      · simp [hv]
    _ = Nat.totient W := sum_coprime_residues W

theorem density_error_le (Y W d a : ℕ) (hW : 0 < W) (hd : 0 < d)
    (hWd : W.Coprime d) :
    |coprimeCount Y W d a -
      BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / d| ≤ Nat.totient W := by
  have heq : BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / d =
      (Nat.totient W : ℝ) * ((Y : ℝ) / (W * d : ℕ)) := by
    unfold BoundedGaps.Maynard.coprimeHarmonicDensity
    rw [Nat.cast_mul]
    ring
  rw [heq]
  exact coprimeCount_error_le Y W d a hW hd hWd

end Erdos4.CoprimeResidueCount
