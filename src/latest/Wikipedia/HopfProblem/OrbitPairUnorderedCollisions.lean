import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Counting unordered collisions and the effect of a cusp

Retain time and quotient each ordered source pair by interchange. Membership
is equivalent to either ordering being an actual double point. Adding one
new unordered collision changes the finite cardinal by exactly one; no
assumption of distinct collision times or absence of triple points is used.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

variable {M N : Type*}

def unorderedProjection (p : ℝ × (M × M)) : ℝ × Sym2 M := (p.1, s(p.2.1, p.2.2))

def unorderedDoublePoints (F : ℝ × M → N) : Set (ℝ × Sym2 M) :=
  unorderedProjection '' doublePoints F

theorem mem_unordered_iff (F : ℝ × M → N) (t : ℝ) (x y : M) :
    (t, s(x, y)) ∈ unorderedDoublePoints F ↔ (t, (x, y)) ∈ doublePoints F := by
  constructor
  · rintro ⟨⟨a, u, v⟩, ⟨hne, heq⟩, hp⟩
    have ht : a = t := congrArg (fun q : ℝ × Sym2 M => q.1) hp
    have hs : s(u, v) = s(x, y) := congrArg (fun q : ℝ × Sym2 M => q.2) hp
    subst a
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, heq⟩
    · exact ⟨hne.symm, heq.symm⟩
  · intro hp
    exact ⟨(t, (x, y)), hp, rfl⟩

theorem finite_unordered {F : ℝ × M → N} (hF : (doublePoints F).Finite) :
    (unorderedDoublePoints F).Finite := hF.image unorderedProjection

theorem unordered_eq_insert_of_one_pair {F G : ℝ × M → N} (t : ℝ) (x y : M)
    (hD : doublePoints G = doublePoints F ∪ {(t, (x, y)), (t, (y, x))}) :
    unorderedDoublePoints G = insert (t, s(x, y)) (unorderedDoublePoints F) := by
  unfold unorderedDoublePoints
  rw [hD, image_union, image_insert_eq, image_singleton]
  change unorderedProjection '' doublePoints F ∪ {(t, s(x, y)), (t, s(y, x))} =
    insert (t, s(x, y)) (unorderedProjection '' doublePoints F)
  have hs : s(y, x) = s(x, y) := Sym2.eq_swap
  rw [hs]
  ext p
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, or_self, or_comm]

theorem unordered_ncard_add_one {F G : ℝ × M → N} (hF : (doublePoints F).Finite)
    (t : ℝ) (x y : M) (hnew : (t, (x, y)) ∉ doublePoints F)
    (hD : doublePoints G = doublePoints F ∪ {(t, (x, y)), (t, (y, x))}) :
    (unorderedDoublePoints G).ncard = (unorderedDoublePoints F).ncard + 1 := by
  rw [unordered_eq_insert_of_one_pair t x y hD]
  have hnot : (t, s(x, y)) ∉ unorderedDoublePoints F := fun h =>
    hnew ((mem_unordered_iff F t x y).mp h)
  exact ncard_insert_of_notMem hnot (finite_unordered hF)

theorem even_unordered_of_not_even_after_one_pair {F G : ℝ × M → N}
    (hF : (doublePoints F).Finite) (t : ℝ) (x y : M)
    (hnew : (t, (x, y)) ∉ doublePoints F)
    (hD : doublePoints G = doublePoints F ∪ {(t, (x, y)), (t, (y, x))})
    (hodd : ¬ Even (unorderedDoublePoints F).ncard) :
    Even (unorderedDoublePoints G).ncard := by
  rw [unordered_ncard_add_one hF t x y hnew hD, Nat.even_add_one]
  exact hodd

/-- A finite even collision set can be partitioned into two-slot blocks.
This is a pairing of unordered source pairs, not yet a choice of geometric
Whitney disks or compatible intersection signs. -/
theorem exists_unordered_pair_enumeration {F : ℝ × M → N}
    (hF : (doublePoints F).Finite) (heven : Even (unorderedDoublePoints F).ncard) :
    ∃ k : ℕ, Nonempty ((Fin k × Fin 2) ≃ unorderedDoublePoints F) := by
  obtain ⟨k, hk⟩ := heven
  letI : Fintype (unorderedDoublePoints F) := (finite_unordered hF).fintype
  have hcard : Fintype.card (Fin k × Fin 2) = Fintype.card (unorderedDoublePoints F) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, fintypeCard_eq_ncard, hk]
    omega
  exact ⟨k, ⟨Fintype.equivOfCardEq hcard⟩⟩

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints
