/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.PCF.ClubGuessing

/-!
# A stationary cofinality slice for Erdős Problem 110

The club-guessing theorem imported above is formulated for uncountable
cofinality.  We therefore use the harmless variant of Lambie-Hanson's
construction with heights in `S^λ_κ`, where `κ = ℵ₁` and
`λ = κ⁺⁺ = ℵ₃`.
-/

noncomputable section

open Cardinal Set Order

namespace Erdos110
namespace Height

open Ordinal

-- Match the order projections used by the ordinal club API.
local instance stationaryOrdinalLT : LT Ordinal := Ordinal.partialOrder.toLT
local instance stationaryOrdinalLE : LE Ordinal := Ordinal.partialOrder.toLE

/-- The common cofinality of the height ordinals. -/
abbrev kappa : Cardinal.{0} := succ ℵ₀

/-- The ambient regular cardinal.  There is one full cardinal between `kappa`
and `lambda`, as required by Shelah's club-guessing theorem. -/
abbrev lambda : Cardinal.{0} := succ (succ kappa)

/-- Ordinals below `lambda` having cofinality `kappa`. -/
def S : Set Ordinal.{0} := {a | a < lambda.ord ∧ a.cof = kappa}

theorem regular_kappa : kappa.IsRegular :=
  isRegular_succ le_rfl

theorem aleph0_lt_kappa : ℵ₀ < kappa := lt_succ _

theorem regular_lambda : lambda.IsRegular :=
  isRegular_succ
    (regular_kappa.aleph0_le.trans (le_succ kappa))

theorem kappa_lt_lambda : kappa < lambda :=
  (lt_succ _).trans (lt_succ _)

theorem succ_kappa_lt_cof_lambda : succ kappa < lambda.ord.cof := by
  rw [regular_lambda.cof_ord]
  exact lt_succ _

/-- The first chosen point of `C` strictly above `p`. -/
private def clubNext (C : Ordinal.Club lambda.ord) (p : Set.Iio lambda.ord) :
    Set.Iio lambda.ord :=
  ⟨Classical.choose (C.isClub.forall_lt p.1 p.2),
    (Classical.choose_spec (C.isClub.forall_lt p.1 p.2)).2.2⟩

private theorem clubNext_mem (C : Ordinal.Club lambda.ord)
    (p : Set.Iio lambda.ord) : (clubNext C p).1 ∈ C :=
  (Classical.choose_spec (C.isClub.forall_lt p.1 p.2)).1

private theorem clubNext_above (C : Ordinal.Club lambda.ord)
    (p : Set.Iio lambda.ord) : p.1 < (clubNext C p).1 :=
  (Classical.choose_spec (C.isClub.forall_lt p.1 p.2)).2.1

/-- Recursively choose points of a club, always above all earlier chosen
points. -/
private def clubSeq (C : Ordinal.Club lambda.ord) :
    Set.Iio kappa.ord → Set.Iio lambda.ord := by
  refine @Ordinal.boundedRec kappa.ord (fun _ ↦ Set.Iio lambda.ord) (fun i ih ↦ ?_)
  let p : Ordinal := ⨆ j, (ih j).1
  have hp : p < lambda.ord := by
    apply Ordinal.iSup_lt_ord_lift'
      (ι := Set.Iio i) (f := fun j ↦ (ih j).1)
    · rw [Ordinal.mk_Iio_subtype, Cardinal.mk_Iio_ordinal,
        Cardinal.lift_lift, regular_lambda.cof_ord, Cardinal.lift_lt]
      exact (Cardinal.lt_ord.mp i.2).trans kappa_lt_lambda
    · exact fun j ↦ (ih j).2
  exact clubNext C ⟨p, hp⟩

private theorem clubSeq_mem (C : Ordinal.Club lambda.ord) (i : Set.Iio kappa.ord) :
    (clubSeq C i).1 ∈ C := by
  rw [clubSeq, Ordinal.boundedRec_eq]
  exact clubNext_mem C _

private theorem clubSeq_above (C : Ordinal.Club lambda.ord) (i : Set.Iio kappa.ord) :
    (⨆ j : Set.Iio i, (clubSeq C j).1) < (clubSeq C i).1 := by
  rw [clubSeq, Ordinal.boundedRec_eq]
  exact clubNext_above C _

private theorem clubSeq_strictMono (C : Ordinal.Club lambda.ord) :
    StrictMono (fun i ↦ (clubSeq C i).1) := by
  intro i j hij
  refine lt_of_le_of_lt ?_ (clubSeq_above C j)
  exact le_ciSup (f := fun x : Set.Iio j ↦ (clubSeq C x).1)
    bddAbove_of_small ⟨i, hij⟩

private theorem clubSeq_sup_lt (C : Ordinal.Club lambda.ord) :
    (⨆ i, (clubSeq C i).1) < lambda.ord := by
  apply Ordinal.iSup_lt_ord_lift'
    (ι := Set.Iio kappa.ord) (f := fun i ↦ (clubSeq C i).1)
  · rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.card_ord,
      regular_lambda.cof_ord, Cardinal.lift_lt]
    exact kappa_lt_lambda
  · exact fun i ↦ (clubSeq C i).2

private theorem clubSeq_sup_cof (C : Ordinal.Club lambda.ord) :
    (⨆ i, (clubSeq C i).1).cof = kappa := by
  simpa only [regular_kappa.cof_ord] using
    Ordinal.cof_iSup_Iio (clubSeq_strictMono C)
      (Cardinal.isSuccLimit_ord regular_kappa.aleph0_le).isSuccPrelimit

private theorem clubSeq_sup_mem (C : Ordinal.Club lambda.ord) :
    (⨆ i, (clubSeq C i).1) ∈ C := by
  apply C.isClub.mem_of_isAcc (clubSeq_sup_lt C)
  let z : Set.Iio kappa.ord := ⟨0, regular_kappa.ord_pos⟩
  apply Ordinal.isAcc_iSup (o := kappa.ord) (α := z)
    (Cardinal.isSuccLimit_ord regular_kappa.aleph0_le)
    (fun i ↦ (clubSeq C i).1)
  · exact fun i j hij ↦ clubSeq_strictMono C hij
  · exact fun i _ ↦ clubSeq_mem C i

/-- The standard cofinality slice `S^λ_κ` is stationary. -/
theorem stationary : Ordinal.IsStationary S lambda.ord := by
  intro C hC
  let D : Ordinal.Club lambda.ord := ⟨C, hC⟩
  refine ⟨⨆ i, (clubSeq D i).1, ?_, clubSeq_sup_mem D⟩
  exact ⟨clubSeq_sup_lt D, clubSeq_sup_cof D⟩

/-- A club-guessing sequence on the height set used by the construction. -/
theorem exists_clubGuessing :
    ∃ C : (a : S) → Ordinal.Club a.1,
      Ordinal.IsClubGuessing C lambda.ord :=
  Ordinal.exists_isClubGuessing_of_cof_uncountable aleph0_lt_kappa
    succ_kappa_lt_cof_lambda stationary (fun _ ha ↦ ha.2)

end Height
end Erdos110
