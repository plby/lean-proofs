import ErdosProblems.Erdos69.IteratedCancellation
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Primorial

/-!
# Pairwise coprime composite dilations

The slopes are explicit rough integers, not conjectural prime patterns.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def roughDilation (P j : ℕ) : ℕ := 1 + primorial P * (1 + j)

theorem roughDilation_pos (P j : ℕ) : 0 < roughDilation P j := by
  simp [roughDilation]

theorem prime_gt_of_dvd_roughDilation {P j p : ℕ} (hp : p.Prime)
    (hd : p ∣ roughDilation P j) : P < p := by
  by_contra! hle
  have hv := hp.dvd_primorial_iff.mpr hle
  have hm : p ∣ primorial P * (1 + j) := dvd_mul_of_dvd_left hv _
  have hone : p ∣ 1 := by
    have h := Nat.dvd_sub hd hm
    simpa [roughDilation] using h
  exact hp.not_dvd_one hone

private theorem roughDilation_sub {j k : ℕ} (P : ℕ) :
    roughDilation P k - roughDilation P j = primorial P * (k - j) := by
  simp [roughDilation, Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]

theorem roughDilation_coprime_of_lt {P j k : ℕ} (hjk : j < k) (hk : k ≤ P) :
    (roughDilation P j).Coprime (roughDilation P k) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpj hpk
  have hgt := prime_gt_of_dvd_roughDilation hp hpj
  have hd : p ∣ primorial P * (k - j) := by
    rw [← roughDilation_sub P]
    exact Nat.dvd_sub hpk hpj
  rcases hp.dvd_mul.mp hd with hv | hdiff
  · have hle := hp.dvd_primorial_iff.mp hv
    omega
  · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hjk) hdiff
    omega

theorem roughDilation_coprime {P j k : ℕ} (hj : j ≤ P) (hk : k ≤ P) (hne : j ≠ k) :
    (roughDilation P j).Coprime (roughDilation P k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact roughDilation_coprime_of_lt h hk
  · exact (roughDilation_coprime_of_lt h hj).symm

def patternDilation (m P : ℕ) (i : PatternLabel m) : ℕ :=
  roughDilation P (patternDigit m i)

def patternOffset (m P : ℕ) (i : PatternLabel m) : ℕ :=
  primorial P * patternIntercept m i

theorem patternDilation_pos (m P : ℕ) (i : PatternLabel m) :
    0 < patternDilation m P i := roughDilation_pos _ _

theorem patternDilation_pairwise (m P : ℕ) (hP : 49 ^ m ≤ P) :
    Pairwise (fun i j : PatternLabel m ↦
      (patternDilation m P i).Coprime (patternDilation m P j)) := by
  intro i j hij
  apply roughDilation_coprime
  · exact (patternDigit_lt m i).le.trans hP
  · exact (patternDigit_lt m j).le.trans hP
  · exact fun h ↦ hij (patternDigit_injective m h)

/-- The congruences needed for every dilation are simultaneously soluble. -/
theorem exists_pattern_residue (m P : ℕ) (hP : 49 ^ m ≤ P) :
    ∃ n : ℕ, ∀ i : PatternLabel m, n ≡ patternOffset m P i [MOD patternDilation m P i] := by
  classical
  let c := Nat.chineseRemainderOfFinset (patternOffset m P) (patternDilation m P)
    Finset.univ
    (fun i _ ↦ (patternDilation_pos m P i).ne')
    (fun i _ j _ hij ↦ patternDilation_pairwise m P hP hij)
  exact ⟨c.val, fun i ↦ c.property i (Finset.mem_univ i)⟩

end Erdos69.Elementary
