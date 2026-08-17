/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.Stationary

/-!
# Club ladders and the countable-cell lemma

This file turns each club supplied by club guessing into a chosen increasing
`kappa`-sequence and proves the countable partition argument used in the
diagonal coloring contradiction.
-/

noncomputable section

open Cardinal Set Order

namespace Erdos110
namespace Height

open Ordinal

local instance ladderOrdinalLT : LT Ordinal := Ordinal.partialOrder.toLT
local instance ladderOrdinalLE : LE Ordinal := Ordinal.partialOrder.toLE

private def nextInClub {a : Ordinal} (C : Ordinal.Club a) (p : Set.Iio a) :
    Set.Iio a :=
  ⟨Classical.choose (C.isClub.forall_lt p.1 p.2),
    (Classical.choose_spec (C.isClub.forall_lt p.1 p.2)).2.2⟩

private theorem nextInClub_mem {a : Ordinal} (C : Ordinal.Club a)
    (p : Set.Iio a) : (nextInClub C p).1 ∈ C :=
  (Classical.choose_spec (C.isClub.forall_lt p.1 p.2)).1

private theorem nextInClub_above {a : Ordinal} (C : Ordinal.Club a)
    (p : Set.Iio a) : p.1 < (nextInClub C p).1 :=
  (Classical.choose_spec (C.isClub.forall_lt p.1 p.2)).2.1

/-- A chosen increasing cofinal-length sequence through the club at `a`. -/
def ladder (C : (a : S) → Ordinal.Club a.1) (a : S) :
    Set.Iio kappa.ord → Set.Iio a.1 := by
  refine @Ordinal.boundedRec kappa.ord (fun _ ↦ Set.Iio a.1) (fun i ih ↦ ?_)
  let p : Ordinal := ⨆ j, (ih j).1
  have hp : p < a.1 := by
    apply Ordinal.iSup_lt_ord_lift'
      (ι := Set.Iio i) (f := fun j ↦ (ih j).1)
    · rw [Ordinal.mk_Iio_subtype, Cardinal.mk_Iio_ordinal,
        Cardinal.lift_lift, a.2.2, Cardinal.lift_lt]
      exact Cardinal.lt_ord.mp i.2
    · exact fun j ↦ (ih j).2
  exact nextInClub (C a) ⟨p, hp⟩

theorem ladder_mem (C : (a : S) → Ordinal.Club a.1) (a : S)
    (i : Set.Iio kappa.ord) : (ladder C a i).1 ∈ C a := by
  rw [ladder, Ordinal.boundedRec_eq]
  exact nextInClub_mem (C a) _

theorem ladder_above (C : (a : S) → Ordinal.Club a.1) (a : S)
    (i : Set.Iio kappa.ord) :
    (⨆ j : Set.Iio i, (ladder C a j).1) < (ladder C a i).1 := by
  rw [ladder, Ordinal.boundedRec_eq]
  exact nextInClub_above (C a) _

theorem ladder_strictMono (C : (a : S) → Ordinal.Club a.1) (a : S) :
    StrictMono (fun i ↦ (ladder C a i).1) := by
  intro i j hij
  refine lt_of_le_of_lt ?_ (ladder_above C a j)
  exact le_ciSup (f := fun x : Set.Iio j ↦ (ladder C a x).1)
    bddAbove_of_small ⟨i, hij⟩

/-- Every natural number is an index below `kappa = aleph_1`. -/
def natIndex (n : ℕ) : Set.Iio kappa.ord := ⟨n, by
  change (n : Ordinal) < kappa.ord
  rw [Cardinal.lt_ord]
  rw [Ordinal.card_nat]
  exact (Cardinal.nat_lt_aleph0 n).trans aleph0_lt_kappa⟩

/-- The `n`-th selected point of the club ladder at `a`. -/
def point (C : (a : S) → Ordinal.Club a.1) (a : S) (n : ℕ) : Ordinal :=
  (ladder C a (natIndex n)).1

theorem point_lt_height (C : (a : S) → Ordinal.Club a.1) (a : S) (n : ℕ) :
    point C a n < a.1 :=
  (ladder C a (natIndex n)).2

theorem point_mem (C : (a : S) → Ordinal.Club a.1) (a : S) (n : ℕ) :
    point C a n ∈ C a :=
  ladder_mem C a (natIndex n)

theorem point_strictMono (C : (a : S) → Ordinal.Club a.1) (a : S) :
    StrictMono (point C a) := by
  intro m n hmn
  apply ladder_strictMono C a
  change (m : Ordinal) < (n : Ordinal)
  exact_mod_cast hmn

/-- Some cell of every countable partition retains the club-guessing
property. -/
theorem exists_guessing_color
    (C : (a : S) → Ordinal.Club a.1)
    (hC : Ordinal.IsClubGuessing C lambda.ord) (color : S → ℕ) :
    ∃ k : ℕ, ∀ D : Ordinal.Club lambda.ord,
      ∃ a : S, color a = k ∧ (C a).carrier ⊆ D.carrier := by
  by_contra! h
  choose D hD using h
  let E : Ordinal.Club lambda.ord :=
    ⟨⋂ k : ℕ, (D k).carrier, by
      apply Ordinal.IsClub.iInter_lift
        (by rw [regular_lambda.cof_ord]; exact aleph0_lt_kappa.trans kappa_lt_lambda)
        (fun k ↦ (D k).isClub)
      simpa only [Cardinal.mk_nat, regular_lambda.cof_ord,
        Cardinal.lift_id] using aleph0_lt_kappa.trans kappa_lt_lambda⟩
  obtain ⟨a, ha⟩ := hC E
  exact hD (color a) a rfl (ha.trans (Set.iInter_subset (fun k ↦ (D k).carrier) (color a)))

end Height
end Erdos110
