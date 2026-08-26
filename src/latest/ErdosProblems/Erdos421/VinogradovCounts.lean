import ErdosProblems.Erdos421.DomainTuples
import ErdosProblems.Erdos421.ZeroRepresentation

/-! # Finite counts for the complete power-sum system

Entries of `Fin N` represent the integers `1,...,N` by adding one.
These definitions include empty intervals and zero-dimensional tuples.
-/

namespace Erdos421

def vinogradovSums {s N : ℕ} (k : ℕ) (x : Fin s → Fin N) : Fin k → ℤ :=
  fun j ↦ ∑ i : Fin s, ((x i : ℤ) + 1) ^ ((j : ℕ) + 1)

def vinogradovSolutions (s k N : ℕ) (w : Fin k → ℤ) :
    Finset ((Fin s → Fin N) × (Fin s → Fin N)) :=
  Finset.univ.filter (fun p ↦ vinogradovSums k p.1 - vinogradovSums k p.2 = w)

def vinogradovCount (s k N : ℕ) : ℕ := (vinogradovSolutions s k N 0).card

theorem vinogradovSolutions_card_le_zero (s k N : ℕ) (w : Fin k → ℤ) :
    (vinogradovSolutions s k N w).card ≤ vinogradovCount s k N := by
  simpa only [Finset.univ_product_univ, vinogradovSolutions, vinogradovCount] using
    card_difference_fiber_le_zero (Finset.univ : Finset (Fin s → Fin N))
      (vinogradovSums k) w

theorem vinogradov_power_sums_eq {s k N : ℕ} {x y : Fin s → Fin N}
    (hs : vinogradovSums k x = vinogradovSums k y) {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    (∑ i : Fin s, ((x i : ℤ) + 1) ^ j) = ∑ i : Fin s, ((y i : ℤ) + 1) ^ j := by
  have hi : j - 1 < k := by omega
  have he := congrFun hs ⟨j - 1, hi⟩
  simpa only [vinogradovSums, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj.ne')] using he

theorem vinogradov_tuple_perm {s k N : ℕ} (hsk : s ≤ k) (x y : Fin s → Fin N)
    (hs : vinogradovSums k x = vinogradovSums k y) :
    ∃ e : Equiv.Perm (Fin s), ∀ i : Fin s, x i = y (e i) := by
  have hp : ∀ j : ℕ, 0 < j → j ≤ s →
      (∑ i : Fin s, ((x i : ℚ) + 1) ^ j) = ∑ i : Fin s, ((y i : ℚ) + 1) ^ j := by
    intro j hj hjs
    exact_mod_cast vinogradov_power_sums_eq hs hj (hjs.trans hsk)
  obtain ⟨e, he⟩ := field_tuple_perm_of_power_sums
    (fun i ↦ (x i : ℚ) + 1) (fun i ↦ (y i : ℚ) + 1) hp
  refine ⟨e, fun i ↦ Fin.ext ?_⟩
  exact_mod_cast add_right_cancel (he i)

/-- The diagonal base estimate, including tuples with repeated entries. -/
theorem vinogradovCount_le_factorial {s k N : ℕ} (hsk : s ≤ k) :
    vinogradovCount s k N ≤ s.factorial * N ^ s := by
  classical
  let T : Finset (Equiv.Perm (Fin s) × (Fin s → Fin N)) := Finset.univ
  let f : Equiv.Perm (Fin s) × (Fin s → Fin N) →
      (Fin s → Fin N) × (Fin s → Fin N) := fun q ↦ (fun i ↦ q.2 (q.1 i), q.2)
  have hsub : vinogradovSolutions s k N 0 ⊆ T.image f := by
    intro q hq
    have he : vinogradovSums k q.1 = vinogradovSums k q.2 :=
      sub_eq_zero.mp (Finset.mem_filter.mp hq).2
    obtain ⟨e, he⟩ := vinogradov_tuple_perm hsk q.1 q.2 he
    exact Finset.mem_image.mpr ⟨(e, q.2), Finset.mem_univ _,
      Prod.ext (funext he).symm rfl⟩
  calc
    vinogradovCount s k N ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = s.factorial * N ^ s := by
      simp only [T, Finset.card_univ, Fintype.card_prod, Fintype.card_perm,
        Fintype.card_fun, Fintype.card_fin]

theorem pow_le_vinogradovCount (s k N : ℕ) : N ^ s ≤ vinogradovCount s k N := by
  have hsub : (Finset.univ : Finset (Fin s → Fin N)).diag ⊆
      vinogradovSolutions s k N 0 := by
    intro q hq
    obtain ⟨_, he⟩ := Finset.mem_diag.mp hq
    simp only [vinogradovSolutions, Finset.mem_filter, Finset.mem_univ, true_and, he, sub_self]
  simpa only [Finset.diag_card, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    vinogradovCount] using Finset.card_le_card hsub

end Erdos421
