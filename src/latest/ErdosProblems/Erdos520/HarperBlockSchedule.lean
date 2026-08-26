import ErdosProblems.Erdos520.HarperPrimeBlocks
import ErdosProblems.Erdos520.HarperTiltedBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# A natural-number prime-block schedule for the Harper walk

For the fixed `q = 2/3` specialization needed by #520, it is convenient to
use the exact integer scales

`Y_j = 2^(16 * 2^j)`.

Then `Y_{j+1} = Y_j^2`, so every interval `(Y_j,Y_{j+1}]` has constant
logarithmic length.  The initial factor `16` keeps every prime in the walk
well inside the range where the one-prime Taylor and variance estimates are
uniform.  This avoids floors and real exponentiation in the block geometry.
-/

/-- Doubly-exponential integer endpoint for the `j`-th Harper scale. -/
def harperBlockEndpoint (j : ℕ) : ℕ := 2 ^ (16 * 2 ^ j)

theorem harperBlockEndpoint_pos (j : ℕ) :
    0 < harperBlockEndpoint j := by
  exact pow_pos (by norm_num) _

theorem harperBlockEndpoint_ge_sixteen (j : ℕ) :
    16 ≤ harperBlockEndpoint j := by
  have hexp : 4 ≤ 16 * 2 ^ j := by
    have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hmono := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  norm_num at hmono ⊢
  exact hmono

theorem harperBlockEndpoint_succ (j : ℕ) :
    harperBlockEndpoint (j + 1) = harperBlockEndpoint j ^ 2 := by
  unfold harperBlockEndpoint
  rw [show 16 * 2 ^ (j + 1) = (16 * 2 ^ j) * 2 by
    rw [pow_succ]
    ring, pow_mul]

theorem strictMono_harperBlockEndpoint :
    StrictMono harperBlockEndpoint := by
  intro j k hjk
  unfold harperBlockEndpoint
  apply Nat.pow_lt_pow_right (by norm_num)
  have hpow : 2 ^ j < 2 ^ k :=
    Nat.pow_lt_pow_right (by norm_num) hjk
  exact Nat.mul_lt_mul_of_pos_left hpow (by norm_num)

theorem monotone_harperBlockEndpoint :
    Monotone harperBlockEndpoint :=
  strictMono_harperBlockEndpoint.monotone

/-- The `j`-th prime block, as coordinates in the ambient cube through `y`. -/
def harperScheduledPrimeBlock (y j : ℕ) :
    Finset (HarperPrimeIndex y) :=
  harperPrimeInterval y (harperBlockEndpoint j)
    (harperBlockEndpoint (j + 1))

@[simp] theorem mem_harperScheduledPrimeBlock
    {y j : ℕ} (p : HarperPrimeIndex y) :
    p ∈ harperScheduledPrimeBlock y j ↔
      harperBlockEndpoint j < p.1 ∧
        p.1 ≤ harperBlockEndpoint (j + 1) := by
  simp [harperScheduledPrimeBlock]

/-- Every scheduled prime is large enough for the cubic logarithm estimate. -/
theorem four_le_prime_of_mem_harperScheduledPrimeBlock
    {y j : ℕ} {p : HarperPrimeIndex y}
    (hp : p ∈ harperScheduledPrimeBlock y j) :
    4 ≤ p.1 := by
  have hlo := harperBlockEndpoint_ge_sixteen j
  have hp' := (mem_harperScheduledPrimeBlock p).mp hp
  omega

/-- Every scheduled prime is large enough for the uniform lower variance
comparison in `HarperTiltedBounds`. -/
theorem sixteen_le_prime_of_mem_harperScheduledPrimeBlock
    {y j : ℕ} {p : HarperPrimeIndex y}
    (hp : p ∈ harperScheduledPrimeBlock y j) :
    16 ≤ p.1 := by
  have hlo := harperBlockEndpoint_ge_sixteen j
  have hp' := (mem_harperScheduledPrimeBlock p).mp hp
  omega

/-- Distinct scheduled intervals contain disjoint prime-coordinate sets. -/
theorem disjoint_harperScheduledPrimeBlock
    (y : ℕ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (harperScheduledPrimeBlock y j)
      (harperScheduledPrimeBlock y k) := by
  wlog hlt : j < k generalizing j k
  · have hkj : k < j := by omega
    exact (this hkj.ne hkj).symm
  rw [Finset.disjoint_left]
  intro p hpj hpk
  have hj := (mem_harperScheduledPrimeBlock p).mp hpj
  have hk := (mem_harperScheduledPrimeBlock p).mp hpk
  have hjk' : j + 1 ≤ k := by omega
  have hscale : harperBlockEndpoint (j + 1) ≤
      harperBlockEndpoint k := monotone_harperBlockEndpoint hjk'
  omega

/-- Two adjacent scheduled blocks merge to the corresponding two-scale
prime interval. -/
theorem harperScheduledPrimeBlock_union_succ (y j : ℕ) :
    harperScheduledPrimeBlock y j ∪
        harperScheduledPrimeBlock y (j + 1) =
      harperPrimeInterval y (harperBlockEndpoint j)
        (harperBlockEndpoint (j + 2)) := by
  ext p
  simp only [Finset.mem_union, mem_harperScheduledPrimeBlock,
    mem_harperPrimeInterval]
  rw [show j + 1 + 1 = j + 2 by omega]
  have hmono : harperBlockEndpoint j ≤ harperBlockEndpoint (j + 1) :=
    monotone_harperBlockEndpoint (by omega)
  have hmono' : harperBlockEndpoint (j + 1) ≤
      harperBlockEndpoint (j + 2) :=
    monotone_harperBlockEndpoint (by omega)
  omega

/-! ## Consecutive ranges of scheduled blocks -/

/-- Every integer lying between the initial endpoint and the `n`-th
endpoint belongs to a unique consecutive scale interval.  The existence
form is the convenient one for finite unions below. -/
theorem exists_harperBlock_bracket_iff (n m : ℕ) :
    (∃ j < n, harperBlockEndpoint j < m ∧
        m ≤ harperBlockEndpoint (j + 1)) ↔
      harperBlockEndpoint 0 < m ∧ m ≤ harperBlockEndpoint n := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · rintro ⟨j, hj, hjlo, hjhi⟩
        have hzeroj : harperBlockEndpoint 0 ≤ harperBlockEndpoint j :=
          monotone_harperBlockEndpoint (Nat.zero_le j)
        have hjn : j + 1 ≤ n + 1 := by omega
        have hscale : harperBlockEndpoint (j + 1) ≤
            harperBlockEndpoint (n + 1) :=
          monotone_harperBlockEndpoint hjn
        exact ⟨lt_of_le_of_lt hzeroj hjlo, hjhi.trans hscale⟩
      · rintro ⟨hzero, htop⟩
        by_cases hm : m ≤ harperBlockEndpoint n
        · obtain ⟨j, hjn, hjlo, hjhi⟩ := ih.mpr ⟨hzero, hm⟩
          exact ⟨j, by omega, hjlo, hjhi⟩
        · exact ⟨n, by omega, Nat.lt_of_not_ge hm, by simpa using! htop⟩

/-- Union of the first `n` scheduled prime blocks in the ambient cube. -/
def harperScheduledPrimeRange (y n : ℕ) :
    Finset (HarperPrimeIndex y) :=
  (Finset.range n).biUnion (harperScheduledPrimeBlock y)

@[simp] theorem mem_harperScheduledPrimeRange
    {y n : ℕ} (p : HarperPrimeIndex y) :
    p ∈ harperScheduledPrimeRange y n ↔
      harperBlockEndpoint 0 < p.1 ∧
        p.1 ≤ harperBlockEndpoint n := by
  rw [harperScheduledPrimeRange]
  simp only [Finset.mem_biUnion, Finset.mem_range,
    mem_harperScheduledPrimeBlock]
  exact exists_harperBlock_bracket_iff n p.1

/-- The first `n` scheduled blocks are exactly one prime interval. -/
theorem harperScheduledPrimeRange_eq_interval (y n : ℕ) :
    harperScheduledPrimeRange y n =
      harperPrimeInterval y (harperBlockEndpoint 0)
        (harperBlockEndpoint n) := by
  ext p
  simp

end Problem520
end Erdos
