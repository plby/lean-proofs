import ErdosProblems.Erdos4.CoprimeResidueCount

/-! CRT counting for an arbitrary set of permitted small-modulus residues. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical CoprimeResidueCount

noncomputable def allowedResidueCount (Y W d a : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, if n % W ∈ S ∧ n ≡ a [MOD d] then 1 else 0

theorem allowedResidueCount_split (Y W d a : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range W) (hWd : W.Coprime d) :
    allowedResidueCount Y W d a S =
      ∑ v ∈ S, residueCount Y (W * d) (Nat.chineseRemainder hWd v a) := by
  have hpoint : ∀ n : ℕ, (if n % W ∈ S ∧ n ≡ a [MOD d] then (1 : ℝ) else 0) =
      ∑ v ∈ S, if n ≡ (Nat.chineseRemainder hWd v a : ℕ) [MOD W * d] then 1 else 0 := by
    intro n
    symm
    calc
      _ = ∑ v ∈ S, if v = n % W then (if n ≡ a [MOD d] then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvW := Finset.mem_range.mp (hS hv)
        have hmod : n ≡ v [MOD W] ↔ v = n % W := by
          change n % W = v % W ↔ v = n % W
          rw [Nat.mod_eq_of_lt hvW]
          exact eq_comm
        simp only [crt_iff hWd, hmod]
        by_cases hvn : v = n % W <;> by_cases ha : n ≡ a [MOD d] <;> simp [hvn, ha]
      _ = _ := by
        by_cases hn : n % W ∈ S <;> by_cases ha : n ≡ a [MOD d] <;> simp [hn, ha]
  unfold allowedResidueCount
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  rfl

theorem allowedResidueCount_error_le (Y W d a : ℕ) (S : Finset ℕ)
    (hW : 0 < W) (hd : 0 < d) (hS : S ⊆ Finset.range W) (hWd : W.Coprime d) :
    |allowedResidueCount Y W d a S - (S.card : ℝ) * ((Y : ℝ) / (W * d : ℕ))| ≤ S.card := by
  have hmain : (S.card : ℝ) * ((Y : ℝ) / (W * d : ℕ)) =
      ∑ _v ∈ S, (Y : ℝ) / (W * d : ℕ) := by simp
  rw [allowedResidueCount_split Y W d a S hS hWd, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ v ∈ S, |residueCount Y (W * d) (Nat.chineseRemainder hWd v a) -
        (Y : ℝ) / (W * d : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, (1 : ℝ) := Finset.sum_le_sum
      (fun v _ => residueCount_error_le Y (W * d) (Nat.chineseRemainder hWd v a)
        (Nat.mul_pos hW hd))
    _ = _ := by simp

theorem allowedResidueCount_density_error (Y W d a : ℕ) (S : Finset ℕ)
    (hW : 0 < W) (hd : 0 < d) (hS : S ⊆ Finset.range W) (hWd : W.Coprime d) :
    |allowedResidueCount Y W d a S - ((S.card : ℝ) / W) * Y / d| ≤ S.card := by
  have heq : ((S.card : ℝ) / W) * Y / d = (S.card : ℝ) * ((Y : ℝ) / (W * d : ℕ)) := by
    rw [Nat.cast_mul]
    ring
  rw [heq]
  exact allowedResidueCount_error_le Y W d a S hW hd hS hWd

end Erdos4.FGKMT
