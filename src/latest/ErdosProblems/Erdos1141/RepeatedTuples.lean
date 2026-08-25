import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Counting tuples with no singleton entry

An exceptional tuple in a Burgess moment has at most half as many distinct
entries as positions.  Encoding its distinct entries and a map into their
labels gives a bound valid for every moment order.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def RepeatedTuple {α : Type*} {n : ℕ} (v : Fin n → α) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, j ≠ i ∧ v j = v i

theorem repeatedTuple_image_card {α : Type*} [DecidableEq α] {n : ℕ}
    (v : Fin n → α) (hv : RepeatedTuple v) :
    2 * (Finset.univ.image v).card ≤ n := by
  have hfiber (a : α) (ha : a ∈ Finset.univ.image v) :
      2 ≤ (Finset.univ.filter fun i => v i = a).card := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hji, hval⟩ := hv i
    apply Finset.one_lt_card.mpr
    exact ⟨i, by simp, j, by simp [hval], hji.symm⟩
  calc
    2 * (Finset.univ.image v).card = ∑ _a ∈ Finset.univ.image v, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.image v, (Finset.univ.filter fun i => v i = a).card :=
      Finset.sum_le_sum hfiber
    _ = n := by simpa using (Finset.card_eq_sum_card_image v Finset.univ).symm

theorem exists_tuple_factorization {α : Type*} [DecidableEq α] {n r : ℕ}
    (hn : 0 < n) (v : Fin n → α) (hcard : (Finset.univ.image v).card ≤ r) :
    ∃ a : Fin r → α, ∃ b : Fin n → Fin r, v = a ∘ b := by
  classical
  let S := Finset.univ.image v
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let z : Fin n → S := fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let b : Fin n → Fin r := fun i => ⟨(e (z i)).val, (e (z i)).isLt.trans_le hcard⟩
  let a : Fin r → α := fun j =>
    if h : j.val < S.card then (e.symm ⟨j.val, h⟩).val else v ⟨0, hn⟩
  refine ⟨a, b, ?_⟩
  funext i
  dsimp only [Function.comp_apply, a, b]
  rw [dif_pos (e (z i)).isLt]
  exact (congrArg Subtype.val (e.symm_apply_apply (z i))).symm

noncomputable def repeatedTuples (α : Type*) [Fintype α] (n : ℕ) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter RepeatedTuple

theorem repeatedTuples_card_le (α : Type*) [Fintype α] (r : ℕ) :
    (repeatedTuples α (2 * r)).card ≤ (Fintype.card α) ^ r * r ^ (2 * r) := by
  classical
  by_cases hr : r = 0
  · subst r
    simpa [repeatedTuples] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin 0 → α)) RepeatedTuple)
  let T : Finset ((Fin r → α) × (Fin (2 * r) → Fin r)) := Finset.univ
  let compose : ((Fin r → α) × (Fin (2 * r) → Fin r)) → (Fin (2 * r) → α) :=
    fun ab => ab.1 ∘ ab.2
  have hsubset : repeatedTuples α (2 * r) ⊆ T.image compose := by
    intro v hv
    have hrep : RepeatedTuple v := (Finset.mem_filter.mp hv).2
    have htwice := repeatedTuple_image_card v hrep
    have hcard : (Finset.univ.image v).card ≤ r := by omega
    obtain ⟨a, b, hab⟩ := exists_tuple_factorization (by omega : 0 < 2 * r) v hcard
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, hab.symm⟩
  calc
    (repeatedTuples α (2 * r)).card ≤ (T.image compose).card := Finset.card_le_card hsubset
    _ ≤ T.card := Finset.card_image_le
    _ = (Fintype.card α) ^ r * r ^ (2 * r) := by simp [T]

end Pollack17.Burgess
