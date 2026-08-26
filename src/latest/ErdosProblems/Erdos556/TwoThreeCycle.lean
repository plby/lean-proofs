import ErdosProblems.Erdos556.ThreeChords

/-! An explicit even cycle using the two- and three-step chords of an odd cycle. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

def CyclicStep (m s a b : ℕ) : Prop :=
  a + s = b ∨ b + s = a ∨ a + s = b + m ∨ b + s = a + m

theorem adjacency_of_cyclicStep {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (f : Fin m → V) (s : ℕ) (hs : ∀ i, G.Adj (f i) (f (i + (s : Fin m))))
    (a b : ℕ) (h : CyclicStep m s a b) : G.Adj (f (a : Fin m)) (f (b : Fin m)) := by
  have hf (a b : ℕ) (hab : a + s = b ∨ a + s = b + m) :
      G.Adj (f (a : Fin m)) (f (b : Fin m)) := by
    have he : (a : Fin m) + (s : Fin m) = (b : Fin m) := by
      rw [← Nat.cast_add]
      rcases hab with h | h
      · rw [h]
      · rw [h, Nat.cast_add, Fin.natCast_self, add_zero]
    simpa only [he] using hs (a : Fin m)
  rcases h with h | h | h | h
  · exact hf a b (Or.inl h)
  · exact (hf b a (Or.inl h)).symm
  · exact hf a b (Or.inr h)
  · exact (hf b a (Or.inr h)).symm

def twoThreeCycleIndex (r k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 3 else if k < r then 2 * k + 2
  else if k = r then 1 else if k < 2 * r - 1 then 4 * r + 1 - 2 * k else 2

theorem twoThreeCycleIndex_lt (r k : ℕ) (hr : 3 ≤ r) (hk : k < 2 * r) :
    twoThreeCycleIndex r k < 2 * r + 1 := by
  unfold twoThreeCycleIndex
  split_ifs <;> omega

theorem twoThreeCycleIndex_injective (r : ℕ) (hr : 3 ≤ r) :
    Set.InjOn (twoThreeCycleIndex r) (Set.Iio (2 * r)) := by
  intro a ha b hb hab
  change a < 2 * r at ha
  change b < 2 * r at hb
  unfold twoThreeCycleIndex at hab
  split_ifs at hab <;> omega

theorem twoThreeCycleIndex_step (r k : ℕ) (hr : 3 ≤ r) (hk : k + 1 < 2 * r) :
    CyclicStep (2 * r + 1) 2 (twoThreeCycleIndex r k) (twoThreeCycleIndex r (k + 1)) ∨
    CyclicStep (2 * r + 1) 3 (twoThreeCycleIndex r k) (twoThreeCycleIndex r (k + 1)) := by
  unfold twoThreeCycleIndex CyclicStep
  split_ifs <;> first | contradiction | omega

theorem exists_even_cycle_of_two_three_steps {V : Type*} {G : SimpleGraph V}
    (r : ℕ) (hr : 3 ≤ r) (f : Fin (2 * r + 1) → V) (hf : Function.Injective f)
    (h2 : ∀ i, G.Adj (f i) (f (i + 2))) (h3 : ∀ i, G.Adj (f i) (f (i + 3))) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 2 * r := by
  apply exists_cycle_of_indexed_vertices G (2 * r) (by omega)
    (fun k => f (twoThreeCycleIndex r k : Fin (2 * r + 1)))
  · intro a ha b hb hab
    have hi := congrArg Fin.val (hf hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (twoThreeCycleIndex_lt r a hr ha),
      Nat.mod_eq_of_lt (twoThreeCycleIndex_lt r b hr hb)] at hi
    exact twoThreeCycleIndex_injective r hr ha hb hi
  · intro k hk
    rcases twoThreeCycleIndex_step r k hr hk with h | h
    · exact adjacency_of_cyclicStep f 2 h2 _ _ h
    · exact adjacency_of_cyclicStep f 3 h3 _ _ h
  · have hlast : twoThreeCycleIndex r (2 * r - 1) = 2 := by
      unfold twoThreeCycleIndex
      split_ifs <;> omega
    have hzero : twoThreeCycleIndex r 0 = 0 := by simp [twoThreeCycleIndex]
    apply adjacency_of_cyclicStep f 2 h2
    rw [hlast, hzero]
    exact Or.inr (Or.inl rfl)

#print axioms exists_even_cycle_of_two_three_steps

end Erdos556
