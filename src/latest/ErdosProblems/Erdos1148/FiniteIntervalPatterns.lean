import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

/-! # A finite ordered window has at most n²+1 interval visit patterns -/

namespace Erdos1148.DukeArithmetic

lemma ordConnected_finset_eq_Icc {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (s : Finset α) (hs : Set.OrdConnected (s : Set α)) (hne : s.Nonempty) :
    s = Finset.Icc (s.min' hne) (s.max' hne) := by
  ext x
  rw [Finset.mem_Icc]
  constructor
  · intro hx
    exact ⟨s.min'_le x hx, s.le_max' x hx⟩
  · intro hx
    exact hs.out (s.min'_mem hne) (s.max'_mem hne) hx

def finiteIntervalPatterns (n : ℕ) : Finset (Finset (Fin n)) :=
  insert ∅ (Finset.univ.image (fun p : Fin n × Fin n => Finset.Icc p.1 p.2))

theorem mem_finiteIntervalPatterns_of_ordConnected {n : ℕ} (s : Finset (Fin n))
    (hs : Set.OrdConnected (s : Set (Fin n))) : s ∈ finiteIntervalPatterns n := by
  classical
  by_cases hne : s.Nonempty
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(s.min' hne, s.max' hne), Finset.mem_univ _,
      (ordConnected_finset_eq_Icc s hs hne).symm⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact Finset.mem_insert_self _ _

theorem card_finiteIntervalPatterns_le (n : ℕ) : (finiteIntervalPatterns n).card ≤ n ^ 2 + 1 := by
  calc
    _ ≤ (Finset.univ.image (fun p : Fin n × Fin n => Finset.Icc p.1 p.2)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin n × Fin n)).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = _ := by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]

end Erdos1148.DukeArithmetic
