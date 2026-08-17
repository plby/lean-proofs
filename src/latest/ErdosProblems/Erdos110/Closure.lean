/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.SetTheory.Cardinal.Arithmetic
import ErdosProblems.Erdos110.Ladder

/-!
# Clubs closed under countably many finite-arity Skolem functions

The elementary-submodel argument in Lambie-Hanson's type-realization lemma
only uses closure under countably many explicitly selected witnesses.  This
file proves the precise closure-club statement directly.
-/

noncomputable section

open Cardinal Set Order

namespace Erdos110
namespace Height

open Ordinal

local instance closureOrdinalLT : LT Ordinal := Ordinal.partialOrder.toLT
local instance closureOrdinalLE : LE Ordinal := Ordinal.partialOrder.toLE

/-- Regard a finite list below `b` as a list below the ambient `lambda`. -/
private def liftList (b : Set.Iio lambda.ord) (xs : List (Set.Iio b.1)) :
    List (Set.Iio lambda.ord) :=
  xs.map fun x ↦ ⟨x.1, Set.mem_Iio.mpr (x.2.trans b.2)⟩

/-- Lower a list whose entries are all below `b`. -/
private def lowerList (b : Set.Iio lambda.ord) :
    (xs : List (Set.Iio lambda.ord)) →
      (∀ x ∈ xs, x.1 < b.1) → List (Set.Iio b.1)
  | [], _ => []
  | x :: xs, h =>
      ⟨x.1, by
        exact Set.mem_Iio.mpr (h x (by simp))⟩ ::
        lowerList b xs (fun y hy ↦ h y (by simp [hy]))

private theorem liftList_lowerList (b : Set.Iio lambda.ord)
    (xs : List (Set.Iio lambda.ord)) (h : ∀ x ∈ xs, x.1 < b.1) :
    liftList b (lowerList b xs h) = xs := by
  induction xs with
  | nil => simp [lowerList, liftList]
  | cons x xs ih =>
      simp only [lowerList, liftList, List.map_cons]
      apply congrArg₂ List.cons
      · exact Subtype.ext (by rfl)
      · change liftList b (lowerList b xs _) = xs
        exact ih (fun y hy ↦ h y (by simp [hy]))

/-- The supremum of all values of `F` on finite lists below `b`, with a
successor added so that it strictly dominates every such value. -/
private def outputSup
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (b : Set.Iio lambda.ord) : Ordinal :=
  ⨆ xs : List (Set.Iio b.1), ⨆ k : ℕ, (F k (liftList b xs)).1 + 1

private theorem outputSup_lt
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (b : Set.Iio lambda.ord) : outputSup F b < lambda.ord := by
  apply Ordinal.iSup_lt_ord_lift'
    (ι := List (Set.Iio b.1))
    (f := fun xs ↦ ⨆ k : ℕ, (F k (liftList b xs)).1 + 1)
  · rw [regular_lambda.cof_ord]
    refine (Cardinal.lift_le.2 (Cardinal.mk_list_le_max _)).trans_lt ?_
    rw [Cardinal.lift_max]
    apply max_lt
    · simpa only [Cardinal.lift_aleph0] using
        (Cardinal.lift_lt.{0, 1}.2
          (aleph0_lt_kappa.trans kappa_lt_lambda))
    · rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt]
      exact Cardinal.lt_ord.mp b.2
  · intro xs
    apply Ordinal.iSup_lt_of_lt_cof
    · rw [regular_lambda.cof_ord, Cardinal.mk_nat]
      exact aleph0_lt_kappa.trans kappa_lt_lambda
    · intro k
      exact (Cardinal.isSuccLimit_ord regular_lambda.aleph0_le).succ_lt
        (F k (liftList b xs)).2

/-- One closure step, strictly above `b` and above every relevant value of
`F` on parameters below `b`. -/
private def closeStep
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (b : Set.Iio lambda.ord) : Set.Iio lambda.ord :=
  ⟨max (b.1 + 1) (outputSup F b + 1), by
    change max (b.1 + 1) (outputSup F b + 1) < lambda.ord
    apply max_lt
    · exact (Cardinal.isSuccLimit_ord regular_lambda.aleph0_le).succ_lt b.2
    · exact (Cardinal.isSuccLimit_ord regular_lambda.aleph0_le).succ_lt
        (outputSup_lt F b)⟩

private theorem lt_closeStep
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (b : Set.Iio lambda.ord) : b.1 < (closeStep F b).1 := by
  exact (lt_add_one b.1).trans_le (le_max_left _ _)

private theorem value_lt_closeStep
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (b : Set.Iio lambda.ord) (k : ℕ) (xs : List (Set.Iio lambda.ord))
    (hxs : ∀ x ∈ xs, x.1 < b.1) :
    (F k xs).1 < (closeStep F b).1 := by
  let ys := lowerList b xs hxs
  have hEq : liftList b ys = xs := liftList_lowerList b xs hxs
  have hleInner : (F k (liftList b ys)).1 + 1 ≤
      (⨆ j : ℕ, (F j (liftList b ys)).1 + 1) :=
    le_ciSup Ordinal.bddAbove_of_small k
  have hleOuter : (⨆ j : ℕ, (F j (liftList b ys)).1 + 1) ≤
      outputSup F b :=
    le_ciSup Ordinal.bddAbove_of_small ys
  rw [← hEq]
  exact ((lt_add_one _).trans_le (hleInner.trans hleOuter)).trans
    ((lt_add_one _).trans_le (le_max_right _ _))

/-- The countable closure iteration starting at `p`. -/
private def closeIter
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (p : Set.Iio lambda.ord) : ℕ → Set.Iio lambda.ord
  | 0 => p
  | n + 1 => closeStep F (closeIter F p n)

private theorem closeIter_succ
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (p : Set.Iio lambda.ord) (n : ℕ) :
    closeIter F p (n + 1) = closeStep F (closeIter F p n) := rfl

private theorem closeIter_strictMono
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (p : Set.Iio lambda.ord) : StrictMono (fun n ↦ (closeIter F p n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [closeIter_succ]
  exact lt_closeStep F _

private theorem closeIter_sup_lt
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (p : Set.Iio lambda.ord) :
    (⨆ n : ℕ, (closeIter F p n).1) < lambda.ord := by
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [regular_lambda.cof_ord, Cardinal.mk_nat]
    exact aleph0_lt_kappa.trans kappa_lt_lambda
  · exact fun n ↦ (closeIter F p n).2

/-- A finite list below the supremum of a monotone sequence is already
bounded by one member of the sequence. -/
private theorem exists_common_stage
    (f : ℕ → Ordinal) (hf : Monotone f) (xs : List (Set.Iio lambda.ord))
    (hxs : ∀ x ∈ xs, x.1 < ⨆ n, f n) :
    ∃ n : ℕ, ∀ x ∈ xs, x.1 < f n := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
      obtain ⟨nx, hnx⟩ := Ordinal.lt_iSup_iff.mp (hxs x (by simp))
      obtain ⟨nxs, hnxs⟩ := ih (fun y hy ↦ hxs y (by simp [hy]))
      refine ⟨max nx nxs, ?_⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hnx.trans_le (hf (le_max_left _ _))
      · exact (hnxs y hy).trans_le (hf (le_max_right _ _))

/-- An ordinal is closed under all the selected finite-parameter functions. -/
def ClosedUnder
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (d : Ordinal) : Prop :=
  d < lambda.ord ∧
    ∀ k xs, (∀ x ∈ xs, x.1 < d) → (F k xs).1 < d

private theorem closeIter_sup_closed
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    (p : Set.Iio lambda.ord) :
    ClosedUnder F (⨆ n : ℕ, (closeIter F p n).1) := by
  refine ⟨closeIter_sup_lt F p, ?_⟩
  intro k xs hxs
  obtain ⟨n, hn⟩ := exists_common_stage
    (fun j ↦ (closeIter F p j).1)
    (closeIter_strictMono F p).monotone xs hxs
  have hv := value_lt_closeStep F (closeIter F p n) k xs hn
  rw [← closeIter_succ] at hv
  exact hv.trans_le (le_ciSup Ordinal.bddAbove_of_small (n + 1))

private def listMax : List (Set.Iio lambda.ord) → Ordinal
  | [] => 0
  | x :: xs => max x.1 (listMax xs)

private theorem le_listMax {x : Set.Iio lambda.ord} {xs}
    (hx : x ∈ xs) : x.1 ≤ listMax xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih hx).trans (le_max_right _ _)

private theorem listMax_lt {xs : List (Set.Iio lambda.ord)} {d : Ordinal}
    (hd : 0 < d) (hxs : ∀ x ∈ xs, x.1 < d) : listMax xs < d := by
  induction xs with
  | nil => simpa [listMax] using hd
  | cons x xs ih =>
      simp only [listMax]
      exact max_lt (hxs x (by simp))
        (ih (fun y hy ↦ hxs y (by simp [hy])))

/-- Closure points of `F` form a club in `lambda`. -/
theorem closedUnder_isClub
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord) :
    Ordinal.IsClub {d | ClosedUnder F d} lambda.ord := by
  constructor
  · rw [Ordinal.isClosedBelow_iff]
    intro d hd hacc
    refine ⟨hd, ?_⟩
    intro k xs hxs
    have hdpos : 0 < d := hacc.pos
    have hm : listMax xs < d := listMax_lt hdpos hxs
    obtain ⟨q, hq⟩ := hacc.forall_lt (listMax xs) hm
    exact hq.1.2 k xs (fun x hx ↦
      (le_listMax hx).trans_lt hq.2.1) |>.trans hq.2.2
  · rw [Ordinal.isAcc_iff]
    refine ⟨(Cardinal.isSuccLimit_ord regular_lambda.aleph0_le).pos.ne.symm, ?_⟩
    intro p hp
    let p' : Set.Iio lambda.ord := ⟨p, hp⟩
    let d : Ordinal := ⨆ n : ℕ, (closeIter F p' n).1
    refine ⟨d, closeIter_sup_closed F p', ?_⟩
    constructor
    · exact (lt_closeStep F p').trans_le
        (le_ciSup Ordinal.bddAbove_of_small 1)
    · exact closeIter_sup_lt F p'

/-- The bundled club of closure points. -/
def closureClub
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord) :
    Ordinal.Club lambda.ord :=
  ⟨{d | ClosedUnder F d}, closedUnder_isClub F⟩

theorem closureClub_closed
    (F : ℕ → List (Set.Iio lambda.ord) → Set.Iio lambda.ord)
    {d : Ordinal} (hd : d ∈ closureClub F) (k : ℕ)
    (xs : List (Set.Iio lambda.ord)) (hxs : ∀ x ∈ xs, x.1 < d) :
    (F k xs).1 < d :=
  hd.2 k xs hxs

end Height
end Erdos110
