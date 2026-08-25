import StackExchange.Puzzling139335.FiniteBoundaryPartition.Breakpoints
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Consecutive intervals between ordered breakpoints

The consecutive closed intervals of a monotone finite sequence cover the
interval between its first and last terms.  Distinct consecutive intervals
can meet only at their endpoints.
-/

open Set

namespace Puzzling139335

variable {α : Type*} [LinearOrder α] {n : ℕ} {t : Fin (n + 1) → α}

/-- Consecutive closed intervals cover the interval between the first and
last terms of a nontrivial monotone sequence. -/
theorem iUnion_consecutive_Icc (hn : 0 < n) (ht : Monotone t) :
    (⋃ k : Fin n, Icc (t k.castSucc) (t k.succ)) =
      Icc (t 0) (t (Fin.last n)) := by
  classical
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨(ht (Fin.zero_le k.castSucc)).trans hk.1,
      hk.2.trans (ht k.succ.le_last)⟩
  · intro x hx
    have hex : ∃ j : Fin (n + 1), x ≤ t j := ⟨Fin.last n, hx.2⟩
    let j := Fin.find (fun j : Fin (n + 1) => x ≤ t j) hex
    have hxj : x ≤ t j := Fin.find_spec hex
    by_cases hj0 : j = 0
    · have hx0 : x ≤ t 0 := hj0 ▸ hxj
      exact mem_iUnion.mpr ⟨⟨0, hn⟩, hx.1, hx0.trans (ht (Fin.zero_le _))⟩
    · obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hj0
      have hkj : k.castSucc < j := hk ▸ k.castSucc_lt_succ
      have hkmin : ¬ x ≤ t k.castSucc := Fin.find_min hex hkj
      exact mem_iUnion.mpr ⟨k, (lt_of_not_ge hkmin).le, hk.symm ▸ hxj⟩

/-- Different consecutive closed intervals in a monotone sequence have no
common point except endpoints of both intervals. -/
theorem consecutive_Icc_inter_subset_endpoints (ht : Monotone t)
    {i j : Fin n} (hij : i ≠ j) :
    Icc (t i.castSucc) (t i.succ) ∩ Icc (t j.castSucc) (t j.succ) ⊆
      {t i.castSucc, t i.succ} ∩ {t j.castSucc, t j.succ} := by
  have ordered (i j : Fin n) (hij : i < j) {x : α}
      (hi : x ∈ Icc (t i.castSucc) (t i.succ))
      (hj : x ∈ Icc (t j.castSucc) (t j.succ)) :
      x = t i.succ ∧ x = t j.castSucc := by
    have hidx : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    have hbound := ht hidx
    exact ⟨le_antisymm hi.2 (hbound.trans hj.1),
      le_antisymm (hi.2.trans hbound) hj.1⟩
  intro x hx
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨hi, hj⟩ := ordered i j hij hx.1 hx.2
    exact ⟨Or.inr hi, Or.inl hj⟩
  · obtain ⟨hj, hi⟩ := ordered j i hji hx.2 hx.1
    exact ⟨Or.inl hi, Or.inr hj⟩

/-- The consecutive intervals of normalized breakpoints cover the unit interval. -/
theorem iUnion_consecutive_Icc_eq_unitInterval {t : Fin (n + 1) → ℝ}
    (hn : 0 < n) (ht : Monotone t) (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1) :
    (⋃ k : Fin n, Icc (t k.castSucc) (t k.succ)) = Icc 0 1 := by
  rw [iUnion_consecutive_Icc hn ht, h0, h1]

end Puzzling139335
