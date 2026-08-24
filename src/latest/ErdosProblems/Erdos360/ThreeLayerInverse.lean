/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.FiveLayerInverse

/-!
# The three-layer fibre branch

For three occupied first coordinates, one pair on each of the five ordered
antidiagonals gives the sharp weighted Kneser contradiction.  This file
formalizes the support-independent version of that finite argument.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-- Every normalized three-point support admits a sharp pair selection.
The middle pair is chosen between `(0,b)` and `(a,a)` according to which
has larger pair weight. -/
theorem exists_pairWeight_selection_of_three_support
    (A : Finset ℕ) (w : ℕ → ℕ)
    (hzero : 0 ∈ A) (hAcard : A.card = 3) :
    ∃ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P ∧
      5 * (∑ a ∈ A, w a) ≤
        ∑ p ∈ P, pairWeight (w p.1) (w p.2) := by
  classical
  have hRcard : (A.erase 0).card = 2 := by
    rw [Finset.card_erase_of_mem hzero, hAcard]
  obtain ⟨u, v, huv, hR⟩ := Finset.card_eq_two.mp hRcard
  let a := min u v
  let b := max u v
  have hab : a < b := by
    dsimp only [a, b]
    exact min_lt_max.mpr huv
  have haR : a ∈ A.erase 0 := by
    rw [hR]
    rcases le_total u v with huvle | hvule
    · simp [a, min_eq_left huvle]
    · simp [a, min_eq_right hvule]
  have hbR : b ∈ A.erase 0 := by
    rw [hR]
    rcases le_total u v with huvle | hvule
    · simp [b, max_eq_right huvle]
    · simp [b, max_eq_left hvule]
  have haA : a ∈ A := Finset.mem_of_mem_erase haR
  have hbA : b ∈ A := Finset.mem_of_mem_erase hbR
  have ha0 : a ≠ 0 := by
    exact (Finset.mem_erase.mp haR).1
  have hb0 : b ≠ 0 := by
    exact (Finset.mem_erase.mp hbR).1
  have h0a : 0 ≠ a := Ne.symm ha0
  have h0b : 0 ≠ b := Ne.symm hb0
  have hba : b ≠ a := Ne.symm hab.ne
  have hAeq : A = {0, a, b} := by
    rw [← Finset.insert_erase hzero, hR]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    dsimp only [a, b]
    omega
  by_cases hmid : pairWeight (w a) (w a) ≤ pairWeight (w 0) (w b)
  · let P : Finset (ℕ × ℕ) :=
      {(0, 0), (0, a), (0, b), (a, b), (b, b)}
    refine ⟨P, ?_, ?_, ?_⟩
    · intro p hp
      simp [P, ha0, hb0, hab.ne] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        simp [hzero, haA, hbA]
    · intro p hp q hq hpq
      simp [P, ha0, hb0, hab.ne] at hp hq
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        simp only [Prod.fst, Prod.snd, Prod.mk.injEq] at hpq ⊢ <;>
        omega
    · have hthree := three_weight_endpoint_bound (w 0) (w a) (w b)
      rw [max_eq_left hmid] at hthree
      have hsumA : (∑ z ∈ A, w z) = w 0 + w a + w b := by
        rw [hAeq]
        have h0 : 0 ∉ ({a, b} : Finset ℕ) := by simp [h0a, h0b]
        have ha : a ∉ ({b} : Finset ℕ) := by simp [hab.ne]
        rw [Finset.sum_insert h0, Finset.sum_insert ha, Finset.sum_singleton]
        simp only [Nat.add_assoc]
      have hsumP : (∑ p ∈ P, pairWeight (w p.1) (w p.2)) =
          pairWeight (w 0) (w 0) + pairWeight (w 0) (w a) +
            pairWeight (w 0) (w b) + pairWeight (w a) (w b) +
              pairWeight (w b) (w b) := by
        dsimp only [P]
        have h1 : (0, 0) ∉
            ({(0, a), (0, b), (a, b), (b, b)} : Finset (ℕ × ℕ)) := by
          simp [h0a, h0b, ha0, hb0, hab.ne, hba]
        have h2 : (0, a) ∉
            ({(0, b), (a, b), (b, b)} : Finset (ℕ × ℕ)) := by
          simp [h0a, h0b, ha0, hb0, hab.ne, hba]
        have h3 : (0, b) ∉
            ({(a, b), (b, b)} : Finset (ℕ × ℕ)) := by
          simp [h0a, h0b, ha0, hb0, hab.ne, hba]
        have h4 : (a, b) ∉ ({(b, b)} : Finset (ℕ × ℕ)) := by
          simp [hab.ne]
        rw [Finset.sum_insert h1, Finset.sum_insert h2,
          Finset.sum_insert h3, Finset.sum_insert h4, Finset.sum_singleton]
        simp only [Prod.fst, Prod.snd, Nat.add_assoc]
      rw [hsumA, hsumP]
      exact hthree
  · have hmid' : pairWeight (w 0) (w b) < pairWeight (w a) (w a) :=
      Nat.lt_of_not_ge hmid
    let P : Finset (ℕ × ℕ) :=
      {(0, 0), (0, a), (a, a), (a, b), (b, b)}
    refine ⟨P, ?_, ?_, ?_⟩
    · intro p hp
      simp [P, ha0, hb0, hab.ne] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        simp [hzero, haA, hbA]
    · intro p hp q hq hpq
      simp [P, ha0, hb0, hab.ne] at hp hq
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        simp only [Prod.fst, Prod.snd, Prod.mk.injEq] at hpq ⊢ <;>
        omega
    · have hthree := three_weight_endpoint_bound (w 0) (w a) (w b)
      rw [max_eq_right hmid'.le] at hthree
      have hsumA : (∑ z ∈ A, w z) = w 0 + w a + w b := by
        rw [hAeq]
        have h0 : 0 ∉ ({a, b} : Finset ℕ) := by simp [h0a, h0b]
        have ha : a ∉ ({b} : Finset ℕ) := by simp [hab.ne]
        rw [Finset.sum_insert h0, Finset.sum_insert ha, Finset.sum_singleton]
        simp only [Nat.add_assoc]
      have hsumP : (∑ p ∈ P, pairWeight (w p.1) (w p.2)) =
          pairWeight (w 0) (w 0) + pairWeight (w 0) (w a) +
            pairWeight (w a) (w a) + pairWeight (w a) (w b) +
              pairWeight (w b) (w b) := by
        dsimp only [P]
        have h1 : (0, 0) ∉
            ({(0, a), (a, a), (a, b), (b, b)} : Finset (ℕ × ℕ)) := by
          simp [h0a, h0b, ha0, hb0, hab.ne, hba]
        have h2 : (0, a) ∉
            ({(a, a), (a, b), (b, b)} : Finset (ℕ × ℕ)) := by
          simp [h0a, h0b, ha0, hb0, hab.ne, hba]
        have h3 : (a, a) ∉
            ({(a, b), (b, b)} : Finset (ℕ × ℕ)) := by
          simp [hab.ne]
        have h4 : (a, b) ∉ ({(b, b)} : Finset (ℕ × ℕ)) := by
          simp [hab.ne]
        rw [Finset.sum_insert h1, Finset.sum_insert h2,
          Finset.sum_insert h3, Finset.sum_insert h4, Finset.sum_singleton]
        simp only [Prod.fst, Prod.snd, Nat.add_assoc]
      rw [hsumA, hsumP]
      exact hthree

/-- A three-layer product core with doubling below `5/2` has a fibre which
occupies more than two thirds of a subgroup coset. -/
theorem exists_dense_fiber_coset_of_three_layers
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 3)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  let A := firstCoordinateSet X
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  obtain ⟨P, hPmem, hPinj, hPweight⟩ :=
    exists_pairWeight_selection_of_three_support A w
      (by simpa [A] using hzero) (by simpa [A] using hAcard)
  exact exists_dense_fiber_coset_of_pairWeight_selection X P
    (by simpa [A] using hPmem) hPinj
    (by simpa [A, w] using hPweight) hsmall

end Erdos360

#print axioms Erdos360.exists_pairWeight_selection_of_three_support
#print axioms Erdos360.exists_dense_fiber_coset_of_three_layers
