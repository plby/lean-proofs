import ErdosProblems.Erdos19.QuotaGreedy
import Mathlib.Data.Set.Card

/-! # Balanced assignments for vertex-color requests

Requests sharing either a vertex or a color receive distinct partners.
Every partner also obeys the prescribed global quota.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

abbrev ActiveRequest {I J : Type*} (active : I → Finset J) :=
  {p : I × J // p.2 ∈ active p.1}

theorem exists_balanced_request_assignment {I J Y : Type*}
    [Fintype I] [Fintype J] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (active : I → Finset J) (lists : ActiveRequest active → Finset Y)
    (q : ℕ) (hq : 0 < q)
    (hroom : ∀ e, (active e.1.1).card + Fintype.card I +
      (Fintype.card I * Fintype.card J) / q < (lists e).card) :
    ∃ partner : ActiveRequest active → Y,
      (∀ e, partner e ∈ lists e) ∧
      (∀ e f, e ≠ f → (e.1.1 = f.1.1 ∨ e.1.2 = f.1.2) → partner e ≠ partner f) ∧
      (∀ y, ((univ : Finset (ActiveRequest active)).filter fun e ↦ partner e = y).card ≤ q) := by
  classical
  let E := ActiveRequest active
  let G : _root_.SimpleGraph E :=
    { Adj e f := e ≠ f ∧ (e.1.1 = f.1.1 ∨ e.1.2 = f.1.2)
      symm.symm := fun _ _ h ↦ ⟨Ne.symm h.1, h.2.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)⟩
      loopless.irrefl := fun _ h ↦ h.1 rfl }
  have hrow : ∀ i : I, ({e : E | e.1.1 = i} : Set E).ncard ≤ (active i).card := by
    intro i
    let code : {e : E // e.1.1 = i} → active i := fun e ↦
      ⟨e.1.1.2, by have h := e.1.2; rw [e.2] at h; exact h⟩
    have hinj : Function.Injective code := by
      intro e f h
      have hcol : e.1.1.2 = f.1.1.2 := congrArg Subtype.val h
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (e.2.trans f.2.symm) hcol
    have hcard := Fintype.card_le_of_injective code hinj
    have hcount : Fintype.card {e : E // e.1.1 = i} = ({e : E | e.1.1 = i} : Set E).ncard :=
      Set.fintypeCard_eq_ncard _
    simpa only [hcount, Fintype.card_coe] using hcard
  have hcol : ∀ j : J, ({e : E | e.1.2 = j} : Set E).ncard ≤ Fintype.card I := by
    intro j
    let code : {e : E // e.1.2 = j} → I := fun e ↦ e.1.1.1
    have hinj : Function.Injective code := by
      intro e f h
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext h (e.2.trans f.2.symm)
    have hcount : Fintype.card {e : E // e.1.2 = j} = ({e : E | e.1.2 = j} : Set E).ncard :=
      Set.fintypeCard_eq_ncard _
    simpa only [hcount] using Fintype.card_le_of_injective code hinj
  have hdegree : ∀ e : E, (G.neighborSet e).ncard ≤ (active e.1.1).card + Fintype.card I := by
    intro e
    have hsub : G.neighborSet e ⊆ {f : E | f.1.1 = e.1.1} ∪ {f : E | f.1.2 = e.1.2} := by
      intro f hf
      exact hf.2.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
    exact ((Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)).trans
      (Nat.add_le_add (hrow _) (hcol _))
  have hEcard : Fintype.card E ≤ Fintype.card I * Fintype.card J := by
    have h := Fintype.card_le_of_injective (Subtype.val : E → I × J) Subtype.val_injective
    simpa only [Fintype.card_prod] using h
  have hroom' : ∀ e : E, (univ.filter (G.Adj e)).card + Fintype.card E / q < (lists e).card := by
    intro e
    have hd : (univ.filter (G.Adj e)).card ≤ (active e.1.1).card + Fintype.card I := by
      simpa only [← G.neighborFinset_eq_filter, card_neighborFinset_eq_degree,
        ← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdegree e
    have hquot := Nat.div_le_div_right hEcard (c := q)
    exact (Nat.add_le_add hd hquot).trans_lt (hroom e)
  obtain ⟨color, hlist, hquota⟩ := exists_list_coloring_with_quota G lists q hq hroom'
  exact ⟨color, hlist, fun e f hef hsame ↦ color.valid ⟨hef, hsame⟩, hquota⟩

#print axioms exists_balanced_request_assignment

end Erdos19
