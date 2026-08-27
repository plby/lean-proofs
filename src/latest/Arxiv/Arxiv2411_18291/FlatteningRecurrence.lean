import Arxiv.Arxiv2411_18291.BoundedCliqueGrouping
import Mathlib.Logic.Function.Iterate

/-!
# A conservative recurrence for multiplicity reduction

The numerical recurrence `x ↦ max 16 (2*sqrt(x)+4)` reaches the fixed bound
16 after a number of steps controlled by a doubly exponential capacity.
These are numerical statements only; constructing sparse elimination rounds
that satisfy the recurrence is a separate task.
-/

noncomputable section

namespace Arxiv2411_18291

def flatteningStep (x : ℕ) : ℕ := max 16 (2 * x.sqrt + 4)

def flatteningCapacity (k : ℕ) : ℕ := 16 * 4 ^ (2 ^ k)

theorem flatteningStep_mono : Monotone flatteningStep := by
  intro x y hxy
  exact max_le_max le_rfl (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.sqrt_le_sqrt hxy)) 4)

theorem flatteningStep_of_le_sixteen {x : ℕ} (hx : x ≤ 16) : flatteningStep x = 16 := by
  have h16 : Nat.sqrt 16 = 4 := Nat.sqrt_eq' 4
  have hs : x.sqrt ≤ 4 := (Nat.sqrt_le_sqrt hx).trans_eq h16
  exact max_eq_left (by omega)

theorem flatteningStep_lt {x : ℕ} (hx : 16 < x) : flatteningStep x < x := by
  have hs : 4 ≤ x.sqrt := Nat.le_sqrt.mpr (by omega)
  have hsquare := Nat.sqrt_le x
  exact max_lt hx (by nlinarith only [hs, hsquare])

theorem flatteningStep_capacity (k : ℕ) :
    flatteningStep (flatteningCapacity (k + 1)) ≤ flatteningCapacity k := by
  have hpow : 1 ≤ 4 ^ (2 ^ k) := Nat.one_le_pow _ _ (by decide)
  have heq : flatteningCapacity (k + 1) = (4 * 4 ^ (2 ^ k)) ^ 2 := by
    rw [flatteningCapacity, pow_succ, pow_mul, mul_pow]
    ring
  rw [flatteningStep, heq, Nat.sqrt_eq', flatteningCapacity]
  apply max_le <;> omega

theorem iterate_flatteningStep_le_sixty_four (k x : ℕ) (hx : x ≤ flatteningCapacity k) :
    (flatteningStep^[k]) x ≤ 64 := by
  induction k generalizing x with
  | zero =>
    simpa only [flatteningCapacity, pow_zero, pow_one, Function.iterate_zero_apply] using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ ((flatteningStep_mono hx).trans (flatteningStep_capacity k))

theorem iterate_flatteningStep_le_sixteen (k x : ℕ) (hx : x ≤ flatteningCapacity k) :
    (flatteningStep^[k + 2]) x ≤ 16 := by
  rw [Nat.add_comm k 2, Function.iterate_add_apply]
  have h := (flatteningStep_mono.iterate 2) (iterate_flatteningStep_le_sixty_four k x hx)
  have hs64 : Nat.sqrt 64 = 8 := Nat.sqrt_eq' 8
  have hs20 : Nat.sqrt 20 = 4 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  have h64 : (flatteningStep^[2]) 64 = 16 := by
    norm_num [Function.iterate_succ_apply, flatteningStep, hs64, hs20]
  rw [h64] at h
  exact h

end Arxiv2411_18291
