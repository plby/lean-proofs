/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.RangeAssembly
import Mathlib.Data.Nat.Log

/-!
# Erdős 730: exact depth partition of the small-prime ledger

For a prime `p ≤ sqrt X`, the paper's unique depth is
`r = floor(log_p X) - 1`; it satisfies
`p^(r+1) ≤ X < p^(r+2)` and `r ≥ 1`.  This file partitions the exact local
small-prime witness finset by that depth and records the corresponding finite
union bound, including the residual depth tail.
-/

namespace Erdos730.SmallPrimeDepth

open BranchEvents RangeAssembly

noncomputable section

/-- The unique digit depth associated with a small prime at height `X`. -/
def smallPrimeDepth (p X : ℕ) : ℕ := Nat.log p X - 1

theorem smallPrimeDepth_spec
    {p X : ℕ} (hp : p.Prime) (hX : 0 < X) (hpSmall : p ≤ Nat.sqrt X) :
    1 ≤ smallPrimeDepth p X ∧
      p ^ (smallPrimeDepth p X + 1) ≤ X ∧
      X < p ^ (smallPrimeDepth p X + 2) := by
  have hp2 : p ^ 2 ≤ X := by
    rw [pow_two]
    exact Nat.le_sqrt.mp hpSmall
  have hlog2 : 2 ≤ Nat.log p X :=
    Nat.le_log_of_pow_le hp.one_lt hp2
  have hpowLow : p ^ Nat.log p X ≤ X :=
    Nat.pow_log_le_self p hX.ne'
  have hpowHigh : X < p ^ (Nat.log p X).succ :=
    Nat.lt_pow_succ_log_self hp.one_lt X
  unfold smallPrimeDepth
  constructor
  · omega
  constructor
  · have hexp : Nat.log p X - 1 + 1 = Nat.log p X := by omega
    rw [hexp]
    exact hpowLow
  · have hexp : Nat.log p X - 1 + 2 = (Nat.log p X).succ := by omega
    rw [hexp]
    exact hpowHigh

theorem smallPrimeDepth_eq_of_power_band
    {p X r : ℕ} (hlow : p ^ (r + 1) ≤ X)
    (hhigh : X < p ^ (r + 2)) :
    smallPrimeDepth p X = r := by
  have hlog : Nat.log p X = r + 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow hlow (by simpa [Nat.add_assoc] using hhigh)
  unfold smallPrimeDepth
  omega

/-- Small-prime witnesses of exact depth `r`. -/
noncomputable def localSmallPrimeDepthWitnessesUpTo (X r : ℕ) :
    Finset LocalBranchWitness :=
  (localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).filter fun w ↦
    smallPrimeDepth (localWitnessPrime w) X = r

/-- Small-prime witnesses whose depth has not yet been included below `R`. -/
noncomputable def localSmallPrimeDepthTailWitnessesUpTo (X R : ℕ) :
    Finset LocalBranchWitness :=
  (localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).filter fun w ↦
    R ≤ smallPrimeDepth (localWitnessPrime w) X

@[simp] theorem mem_localSmallPrimeDepthWitnessesUpTo
    {X r : ℕ} {w : LocalBranchWitness} :
    w ∈ localSmallPrimeDepthWitnessesUpTo X r ↔
      w ∈ localSmallPrimeWitnessesUpTo X (Nat.sqrt X) ∧
        smallPrimeDepth (localWitnessPrime w) X = r := by
  simp [localSmallPrimeDepthWitnessesUpTo]

@[simp] theorem mem_localSmallPrimeDepthTailWitnessesUpTo
    {X R : ℕ} {w : LocalBranchWitness} :
    w ∈ localSmallPrimeDepthTailWitnessesUpTo X R ↔
      w ∈ localSmallPrimeWitnessesUpTo X (Nat.sqrt X) ∧
        R ≤ smallPrimeDepth (localWitnessPrime w) X := by
  simp [localSmallPrimeDepthTailWitnessesUpTo]

/-- Exact finite decomposition into depths below `R` and the remaining tail. -/
theorem localSmallPrimeWitnesses_depth_union_tail (X R : ℕ) :
    localSmallPrimeWitnessesUpTo X (Nat.sqrt X) =
      (Finset.range R).biUnion
          (localSmallPrimeDepthWitnessesUpTo X) ∪
        localSmallPrimeDepthTailWitnessesUpTo X R := by
  classical
  ext w
  constructor
  · intro hw
    by_cases hdepth : smallPrimeDepth (localWitnessPrime w) X < R
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      exact ⟨smallPrimeDepth (localWitnessPrime w) X,
        Finset.mem_range.mpr hdepth,
        mem_localSmallPrimeDepthWitnessesUpTo.mpr ⟨hw, rfl⟩⟩
    · apply Finset.mem_union_right
      exact mem_localSmallPrimeDepthTailWitnessesUpTo.mpr
        ⟨hw, Nat.le_of_not_gt hdepth⟩
  · intro hw
    rcases Finset.mem_union.mp hw with hfinite | htail
    · rcases Finset.mem_biUnion.mp hfinite with ⟨r, _hr, hw⟩
      exact (mem_localSmallPrimeDepthWitnessesUpTo.mp hw).1
    · exact (mem_localSmallPrimeDepthTailWitnessesUpTo.mp htail).1

/-- Cardinal form of the depth decomposition.  Equality is unnecessary for
the density argument; this union bound deliberately avoids relying on
pairwise-disjoint simplification. -/
theorem localSmallPrimeWitnesses_card_le_depth_sum_add_tail (X R : ℕ) :
    (localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card ≤
      (∑ r ∈ Finset.range R,
        (localSmallPrimeDepthWitnessesUpTo X r).card) +
        (localSmallPrimeDepthTailWitnessesUpTo X R).card := by
  rw [localSmallPrimeWitnesses_depth_union_tail X R]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_biUnion_le le_rfl)

/-- Normalized exact-depth witness count. -/
def normalizedSmallPrimeDepthWitnessCount (r X : ℕ) : ℝ :=
  ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ) / (X : ℝ)

/-- Normalized residual depth-tail witness count. -/
def normalizedSmallPrimeDepthTailWitnessCount (R X : ℕ) : ℝ :=
  ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) / (X : ℝ)

theorem normalizedSmallPrimeDepthWitnessCount_nonneg (r X : ℕ) :
    0 ≤ normalizedSmallPrimeDepthWitnessCount r X := by
  unfold normalizedSmallPrimeDepthWitnessCount
  positivity

theorem normalizedSmallPrimeDepthTailWitnessCount_nonneg (R X : ℕ) :
    0 ≤ normalizedSmallPrimeDepthTailWitnessCount R X := by
  unfold normalizedSmallPrimeDepthTailWitnessCount
  positivity

/-- Pointwise normalized decomposition in exactly the form consumed by the
generic finite-depth limsup theorem. -/
theorem normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail (X R : ℕ) :
    normalizedSmallPrimeWitnessCount X ≤
      (∑ r ∈ Finset.range R, normalizedSmallPrimeDepthWitnessCount r X) +
        normalizedSmallPrimeDepthTailWitnessCount R X := by
  have hcard := localSmallPrimeWitnesses_card_le_depth_sum_add_tail X R
  have hcast :
      ((localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card : ℝ) ≤
        (∑ r ∈ Finset.range R,
          ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ)) +
          ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) := by
    exact_mod_cast hcard
  unfold normalizedSmallPrimeWitnessCount
    normalizedSmallPrimeDepthWitnessCount
    normalizedSmallPrimeDepthTailWitnessCount
  rw [← Finset.sum_div]
  simpa only [add_div] using
    (div_le_div_of_nonneg_right hcast (Nat.cast_nonneg X))

#print axioms smallPrimeDepth_spec
#print axioms localSmallPrimeWitnesses_card_le_depth_sum_add_tail
#print axioms normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail

end

end Erdos730.SmallPrimeDepth
