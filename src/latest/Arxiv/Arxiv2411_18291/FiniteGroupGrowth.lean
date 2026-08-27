import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Growth of a finite generated subgroup

Every new generator outside the previous subgroup at least doubles its
cardinality. This is the finite-group counting argument in `lem:KSG`.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {A I : Type*} [AddGroup A] [Finite A]

theorem addSubgroup_two_mul_card_le {H K : AddSubgroup A} (hle : H ≤ K) (hne : H ≠ K) :
    2 * Nat.card H ≤ Nat.card K := by
  have hlt : Nat.card H < Nat.card K := lt_of_not_ge fun h =>
    hne (AddSubgroup.eq_of_le_of_card_ge hle h)
  obtain ⟨d, hd⟩ := AddSubgroup.card_dvd_of_le hle
  have hd2 : 2 ≤ d := by
    by_contra h
    have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl <;> simp_all
  calc
    2 * Nat.card H = Nat.card H * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card H * d := Nat.mul_le_mul_left _ hd2
    _ = Nat.card K := hd.symm

def generatedSubgroup (f : I → A) (s : Finset I) : AddSubgroup A :=
  AddSubgroup.closure (f '' (s : Set I))

omit [Finite A] in
theorem generatedSubgroup_mono (f : I → A) {s t : Finset I} (hst : s ⊆ t) :
    generatedSubgroup f s ≤ generatedSubgroup f t :=
  AddSubgroup.closure_mono (Set.image_mono hst)

omit [Finite A] in
theorem mem_generatedSubgroup (f : I → A) {s : Finset I} {i : I} (hi : i ∈ s) :
    f i ∈ generatedSubgroup f s := AddSubgroup.subset_closure ⟨i, hi, rfl⟩

theorem generatedSubgroup_card_insert [DecidableEq I] (f : I → A) (s : Finset I) (i : I)
    (hi : f i ∉ generatedSubgroup f s) :
    2 * Nat.card (generatedSubgroup f s) ≤ Nat.card (generatedSubgroup f (insert i s)) := by
  apply addSubgroup_two_mul_card_le (generatedSubgroup_mono f (subset_insert _ _))
  intro h
  exact hi (h ▸ mem_generatedSubgroup f (mem_insert_self i s))

end Arxiv2411_18291
