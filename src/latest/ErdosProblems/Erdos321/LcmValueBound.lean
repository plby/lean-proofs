import ErdosProblems.Erdos321.SubsetSumCount

namespace Erdos321

/-- LCM of a finite denominator set. -/
def denominatorLCM (A : Finset ℕ) : ℕ := A.lcm id

/-- Integer numerator after clearing all denominators by their LCM. -/
def lcmClearedSubsetSum (A S : Finset ℕ) : ℕ :=
  ∑ n ∈ S, denominatorLCM A / n

/-- Clearing denominators computes the reciprocal sum exactly. -/
theorem reciprocalSubsetSum_eq_lcmCleared
    {A S : Finset ℕ} (hpos : ∀ n ∈ A, 0 < n) (hS : S ⊆ A) :
    reciprocalSubsetSum S =
      (lcmClearedSubsetSum A S : ℚ) / denominatorLCM A := by
  have hL0 : denominatorLCM A ≠ 0 := by
    intro hzero
    rcases Finset.lcm_eq_zero_iff.mp hzero with ⟨n, hn, hn0⟩
    exact (hpos n hn).ne' hn0
  rw [reciprocalSubsetSum, lcmClearedSubsetSum, Nat.cast_sum,
    eq_div_iff (Nat.cast_ne_zero.mpr hL0)]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hnS
  have hnA : n ∈ A := hS hnS
  have hnpos : 0 < n := hpos n hnA
  have hdiv : n ∣ denominatorLCM A := Finset.dvd_lcm hnA
  have hn0q : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  rw [Nat.cast_div hdiv hn0q]
  simp [div_eq_mul_inv, mul_comm]

/-- The cleared numerator is bounded by `|A|` times the LCM. -/
theorem lcmClearedSubsetSum_le
    {A S : Finset ℕ} (hS : S ⊆ A) :
    lcmClearedSubsetSum A S ≤ A.card * denominatorLCM A := by
  calc
    lcmClearedSubsetSum A S ≤ S.card * denominatorLCM A := by
      rw [lcmClearedSubsetSum]
      calc
        (∑ n ∈ S, denominatorLCM A / n) ≤
            ∑ _n ∈ S, denominatorLCM A := by
          apply Finset.sum_le_sum
          intro n hn
          exact Nat.div_le_self _ _
        _ = S.card * denominatorLCM A := by simp
    _ ≤ A.card * denominatorLCM A :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hS)

/-- All reciprocal sums from positive denominators fit in the integer grid of
mesh `1/lcm(A)` and length at most `|A|`. -/
theorem subsetSumCount_le_card_mul_lcm_add_one
    {A : Finset ℕ} (hpos : ∀ n ∈ A, 0 < n) :
    subsetSumCount A ≤ A.card * denominatorLCM A + 1 := by
  let C : Finset ℕ := A.powerset.image (lcmClearedSubsetSum A)
  have hValues : subsetSumValues A =
      C.image (fun k : ℕ => (k : ℚ) / denominatorLCM A) := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨S, hS, rfl⟩
      have hSsub : S ⊆ A := Finset.mem_powerset.mp hS
      rw [reciprocalSubsetSum_eq_lcmCleared hpos hSsub]
      exact Finset.mem_image.mpr
        ⟨lcmClearedSubsetSum A S, Finset.mem_image.mpr ⟨S, hS, rfl⟩, rfl⟩
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
      rcases Finset.mem_image.mp hk with ⟨S, hS, rfl⟩
      have hSsub : S ⊆ A := Finset.mem_powerset.mp hS
      rw [← reciprocalSubsetSum_eq_lcmCleared hpos hSsub]
      exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
  have hCrange : C ⊆ Finset.range (A.card * denominatorLCM A + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨S, hS, rfl⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le
      (lcmClearedSubsetSum_le (Finset.mem_powerset.mp hS))
  rw [subsetSumCount, hValues]
  exact (Finset.card_image_le).trans
    ((Finset.card_le_card hCrange).trans (by simp))

end Erdos321
