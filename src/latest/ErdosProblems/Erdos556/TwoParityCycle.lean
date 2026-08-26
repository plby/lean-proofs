import ErdosProblems.Erdos556.TwoThreeCycle

/-! Joining the two parity classes with two specified chords. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

def twoParityCycleIndex (t a k : ℕ) : ℕ :=
  if k < t - 1 then 2 * k + 2 else
    if k - (t - 1) < a then 2 * (a - 1 - (k - (t - 1))) + 1
    else 2 * (a + t - 1 - (k - (t - 1))) + 1

theorem twoParityCycleIndex_lt (t a k : ℕ) (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (hk : k < 2 * t - 1) : twoParityCycleIndex t a k < 2 * t := by
  unfold twoParityCycleIndex
  split_ifs <;> omega

theorem twoParityCycleIndex_injective (t a : ℕ) (ha : 2 ≤ a) (hat : a + 2 ≤ t) :
    Set.InjOn (twoParityCycleIndex t a) (Set.Iio (2 * t - 1)) := by
  intro k hk l hl h
  change k < 2 * t - 1 at hk
  change l < 2 * t - 1 at hl
  unfold twoParityCycleIndex at h
  split_ifs at h <;> omega

theorem twoParityCycleIndex_step (t a k : ℕ) (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (hk : k + 1 < 2 * t - 1) (hcross : k ≠ t - 2) :
    CyclicStep (2 * t) 2 (twoParityCycleIndex t a k) (twoParityCycleIndex t a (k + 1)) := by
  unfold twoParityCycleIndex CyclicStep
  split_ifs <;> first | contradiction | omega

theorem exists_odd_cycle_from_parity_chords {V : Type*} {G : SimpleGraph V}
    (t a : ℕ) [NeZero (2 * t)] (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (f : Fin (2 * t) → V) (hf : Function.Injective f)
    (h2 : ∀ i, G.Adj (f i) (f (i + 2)))
    (hfirst : G.Adj (f 2) (f (↑(2 * a + 1) : Fin (2 * t))))
    (hsecond : G.Adj (f (↑(2 * t - 2) : Fin (2 * t))) (f (↑(2 * a - 1) : Fin (2 * t)))) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 2 * t - 1 := by
  apply exists_cycle_of_indexed_vertices G (2 * t - 1) (by omega)
    (fun k => f (twoParityCycleIndex t a k : Fin (2 * t)))
  · intro k hk l hl h
    have hi := congrArg Fin.val (hf h)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (twoParityCycleIndex_lt t a k ha hat hk),
      Nat.mod_eq_of_lt (twoParityCycleIndex_lt t a l ha hat hl)] at hi
    exact twoParityCycleIndex_injective t a ha hat hk hl hi
  · intro k hk
    by_cases hcross : k = t - 2
    · have h₁ : twoParityCycleIndex t a k = 2 * t - 2 := by
        unfold twoParityCycleIndex
        split_ifs <;> omega
      have h₂ : twoParityCycleIndex t a (k + 1) = 2 * a - 1 := by
        unfold twoParityCycleIndex
        split_ifs <;> omega
      simpa only [h₁, h₂] using hsecond
    · exact adjacency_of_cyclicStep f 2 h2 _ _ (twoParityCycleIndex_step t a k ha hat hk hcross)
  · have hlast : twoParityCycleIndex t a (2 * t - 1 - 1) = 2 * a + 1 := by
      unfold twoParityCycleIndex
      split_ifs <;> omega
    have hzero : twoParityCycleIndex t a 0 = 2 := by
      unfold twoParityCycleIndex
      split_ifs <;> omega
    simpa only [hlast, hzero, Nat.cast_ofNat] using hfirst.symm

#print axioms exists_odd_cycle_from_parity_chords

end Erdos556
