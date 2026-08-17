import ErdosProblems.Erdos110.PCF.Background.Club

/-!
Adapted from Y. Paz, `PCF-Theory` (Apache 2.0), and ported to Mathlib v4.33.0.
-/

/-
This file formalizes `theorem 2.17` in the chapter "Cardinal Arithmetic" in the "Handbook
of set theory."

For `δ` an ordinal, let `S ⊆ δ`, and `f : (α : S) → Club α` a function assigning a club
to each element of `S`.
Then `f` is said to be "club guessing" if for every club of `δ`, `C : Club δ`, there is some
`α ∈ S` such that `f α ⊆ C`. That is, `f` guesses `C` at `α`.

There are many existence results on club guessing sequences. The one we need is `theorem 2.17`:
  Let `Ϟ` be an ordinal and let `S` be a stationary set below `Ϟ`, such that every
  element of `S` has the same cofinality `κ`. Further assume `succ κ < Ϟ.cof`.
  Then there exists a club guessing sequence on `S`.

## definitions

* `IsClubGuessing {S} f γ` says `f : (α : S) → Club α` is a club guessing sequence for `γ`.
  Unlike in the typical definition, we don't assume `S ⊆ Iio γ`. This makes no mathematical
  difference but allows us to have `IsClubGuessing f γ` for many different `γ`.

## theorems

* `exists_isClubGuessing_of_cof_uncountable`: Let `Ϟ` be an ordinal and `S` stationary below
  `Ϟ`, such that `∀ α ∈ S, α.cof = κ`, for a constant `κ` satisfying `succ κ < Ϟ.cof`.
  Assume also that `ℵ₀ < κ`. Then there exists `f : (α : S) → Club α` that is club guessing
  below `Ϟ`.


The countable-cofinality version is separate and is not needed for the
uncountable-cofinality specialization used here.
-/

noncomputable section
open Classical

open Cardinal Order Set

universe u

namespace Ordinal

-- Match the order projections used by the legacy ordinal club API.
local instance clubGuessingOrdinalLT : LT Ordinal := Ordinal.partialOrder.toLT
local instance clubGuessingOrdinalLE : LE Ordinal := Ordinal.partialOrder.toLE

def IsClubGuessing {S : Set Ordinal} (f : (α : S) → Club α) (γ : Ordinal) : Prop :=
  ∀ C : Club γ, ∃ δ, (f δ).carrier ⊆ C.carrier

theorem exists_club_of_not_isClubGuessing {S : Set Ordinal} {γ : Ordinal} (f : (α : S) → Club α)
    (h : ¬ IsClubGuessing f γ) : ∃ C : Club γ, ∀ δ, ¬ (f δ).carrier ⊆ C := by
  dsimp [IsClubGuessing] at h
  push_neg at h
  exact h

section ClubGuessing
namespace ClubGuessing

/- The assumptions of the theorem and `hCont`, which says the result is false. -/
class Assumptions where
  Ϟ : Ordinal.{u}
  κ : Cardinal.{u}
  hκ : ℵ₀ < κ
  hcof : succ κ < Ϟ.cof
  S : Set Ordinal.{u}
  hStat : IsStationary S Ϟ
  hSub : S ⊆ Iio Ϟ
  hS : ∀ α ∈ S, α.cof = κ
  hCont : ∀ f : (α : S) → Club.{u} α, ¬ IsClubGuessing f Ϟ

namespace Assumptions
variable [assumptions : Assumptions.{u}]

instance : Nonempty (Iio (succ κ).ord) := ⟨0,
  ord_zero ▸ (ord_lt_ord.mpr <| (aleph0_pos.trans hκ).trans (lt_succ κ))⟩

theorem isLimit_of_mem_S {α : S} : IsSuccLimit α.1 :=
  aleph0_le_cof.mp (hS α α.2 ▸ hκ).le

theorem aleph0_lt_cof_Ϟ : ℵ₀ < Ϟ.cof := by
    calc
      ℵ₀ < κ := hκ
      _ < succ κ := lt_succ _
      _ < Ϟ.cof := hcof

/- We start by picking an arbitrary club of cardinality `κ` below each element of `S`. This
is out first attempt at a club guessing sequence. -/
def f : (α : S) → Club α := fun _ ↦ Classical.choose <| exists_club_card isLimit_of_mem_S

/- If `E` is a club that is not guessed by `f`, we can "force" `f` to guess `E` at every
point in `S` that is an accumulation point of `E`, by intersecting every `f α` with `E`.
This is the "restriction" of `f` to `E`. -/
def restrict (E : Club Ϟ) : (α : S) → Club α := fun α ↦ if h : IsAcc α.1 E then
  ⟨(f α).1 ∩ E, IsClub.inter (hS α α.2 ▸ hκ) (f α).2 <| IsClub.isClub_of_isAcc (hSub α.2) E.2 h⟩
  else univ_club isLimit_of_mem_S

/- We assume there is no club guessing sequence, so `f ↾ E₀` is not club guessing. We choose
a club `E₁` that `f ↾ E₀` doesn't guess, and look at `f ↾ (E₀ ∩ E₁)`. Let `E₂` be a club this
function doesn't guess. Using `succ κ < Ϟ.cof`, we can do this `succ κ` many times. -/
def F : Iio (succ κ).ord → Club Ϟ := by
  refine @boundedRec (succ κ).ord (fun _ ↦ Club Ϟ) fun o ih ↦
    Classical.choose <| exists_club_of_not_isClubGuessing _
      ((hCont <| restrict ⟨⋂ α, ih α, ?_⟩))
  apply IsClub.iInter_Iio aleph0_lt_cof_Ϟ
  · exact (lt_ord.mp o.2).trans hcof
  · exact fun x ↦ (ih x).isClub

/- Prefix intersections of `F` for convenience. -/
def F' : Iio (succ κ).ord → Club Ϟ := fun δ ↦ ⟨⋂ α : Iio δ, F α,
  IsClub.iInter_Iio aleph0_lt_cof_Ϟ ((lt_ord.mp δ.2).trans hcof) fun x ↦ (F x).2⟩

/- Using `succ κ < Ϟ.cof` we can intersect all `E_α` for `α < succ κ`. -/
def E : Club Ϟ := ⟨⋂ α : Iio (succ κ).ord, F α, by
  apply IsClub.iInter_lift aleph0_lt_cof_Ϟ fun i ↦ (F i).2
  rw [mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt, card_ord]
  exact hcof⟩

/- E is a club and `S` is stationary, so there is some `α ∈ S ∩ E'`. -/
def α : S := by
  have : Set.Nonempty _ := hStat.inter_isClub (E.2.derivedSet aleph0_lt_cof_Ϟ)
  exact ⟨Classical.choose this, (Classical.choose_spec this).1.1⟩

theorem isAcc_α : IsAcc α E := by
  unfold α
  generalize_proofs pf
  exact (Classical.choose_spec pf).1.2

theorem isAcc_α_F' (β : Iio (succ κ).ord) : IsAcc α (F' β) :=
  isAcc_α.mono (by exact fun x hx y ⟨z, hz⟩ ↦ hx y ⟨z, hz⟩)

theorem restrict_subset_α (β : Iio (succ κ).ord) : restrict (F' β) α ⊆ f α := by
  rw [restrict, dif_pos (isAcc_α_F' _)]
  exact inter_subset_left

theorem restrict_subset_restrict {C D : Club Ϟ} (h : C ⊆ D) (ha : IsAcc α C) :
    restrict C α ⊆ restrict D α := by
  unfold restrict
  rw [dif_pos ha, dif_pos (by exact ha.mono h)]
  exact inter_subset_inter (fun _ H ↦ H) h

theorem restrict_not_subset (β : Iio (succ κ).ord) :
    ¬ (restrict (F' β) α).carrier ⊆ (F β).carrier := by
  rw [F, boundedRec_eq]
  generalize_proofs _ _ _ pf
  exact choose_spec pf α

theorem restrict_subset {β γ : Iio (succ κ).ord} (h : β < γ) :
    (restrict (F' γ) α).carrier ⊆ (F β).carrier := by
  rw [restrict, dif_pos (isAcc_α_F' γ)]
  refine inter_subset_right.trans ?_
  intro x xmem
  exact xmem (F β).carrier ⟨⟨β, h⟩, rfl⟩

/- At each of the `succ κ` steps, when we chose a club `C` that is not guessed so far,
we shrunk the club we started with below `α`, `f α`.
In fact we shrunk the club below every element of `S ∩ C'`, because no club guessed `C`.
 -/
theorem restrict_ssubset_restrict {β γ : Iio (succ κ).ord} (h : β < γ) :
    restrict (F' γ) α ⊂ restrict (F' β) α := by
  change (restrict (F' γ) α).carrier ⊂ (restrict (F' β) α).carrier
  rw [ssubset_iff_subset_ne]
  constructor
  · apply restrict_subset_restrict
    · exact fun x hx s ⟨z, hz⟩ ↦ hx s ⟨⟨z.1, z.2.trans h⟩, hz⟩
    · exact isAcc_α_F' _
  · exact fun heq ↦ restrict_not_subset β (heq ▸ (restrict_subset h))

/- `f α` has cardinality `κ`, but we removed elements from it `succ κ` many times. -/
theorem contradiction : False := by
  have : Cardinal.lift.{u, u + 1} #(f α).carrier
      < Cardinal.lift.{u + 1, u} (succ κ).ord.card := by
    have : #↑(f α).carrier = Cardinal.lift.{u + 1, u} κ := by
      calc
        #↑(f α).carrier = Cardinal.lift.{u + 1, u} α.1.cof := by
          change #(f α) = Cardinal.lift.{u + 1, u} α.1.cof
          simpa only [f] using
            (Classical.choose_spec (exists_club_card (isLimit_of_mem_S (α := α))))
        _ = Cardinal.lift.{u + 1, u} κ :=
          congrArg (Cardinal.lift.{u + 1, u}) (hS α α.2)
    rw [card_ord, this, Cardinal.lift_lift, Cardinal.lift_lt]
    exact lt_succ κ
  apply not_exists_ssubset_chain_lift (isSuccLimit_ord (hκ.trans (lt_succ κ)).le) this
  use fun x ↦ restrict (F' x) α
  constructor
  · exact restrict_subset_α
  · exact fun β γ ↦ restrict_ssubset_restrict

end Assumptions
end ClubGuessing

/-- Club guessing when the common cofinality is uncountable. -/
theorem exists_isClubGuessing_of_cof_uncountable {Ϟ : Ordinal} {κ : Cardinal} (hκ : ℵ₀ < κ)
    (hcof : succ κ < Ϟ.cof) {S : Set Ordinal} (hStat : IsStationary S Ϟ)
    (hS : ∀ α ∈ S, α.cof = κ) : ∃ f : (α : S) → Club α, IsClubGuessing f Ϟ := by
  by_contra! h
  have : ClubGuessing.Assumptions := ⟨Ϟ, κ, hκ, hcof, S ∩ Iio Ϟ, hStat.inter_Iio,
    inter_subset_right, (fun _ ⟨h, _⟩ ↦ hS _ h), ?_⟩
  exact ClubGuessing.Assumptions.contradiction
  · intro f hf
    let g : (α : S) → (Club α) := fun α ↦ if hα : α.1 ∈ (Iio Ϟ) then (f ⟨α.1, ⟨α.2, hα⟩⟩) else
      univ_club (aleph0_le_cof.mp (hS α α.2 ▸ hκ).le)
    refine h g fun C ↦ ?_
    obtain ⟨δ, hδ⟩ := hf ⟨C.1 ∩ Iio Ϟ, C.2.inter_Iio⟩
    use ⟨δ.1, δ.2.1⟩
    unfold g
    rw [dif_pos δ.2.2]
    exact hδ.trans inter_subset_left

end ClubGuessing
