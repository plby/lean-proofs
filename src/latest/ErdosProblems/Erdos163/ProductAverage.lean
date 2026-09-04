/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.TerminalMoment
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Nested coordinate averages as product-space averages

This file identifies the sequential independent-coordinate average used by
the neutralized random-greedy process with the literal finite product average
used in `FiniteDefect.familyMoment`.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace Process

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Fubini for a finite product whose coordinates are indexed by `Fin (n+1)`. -/
theorem expect_piFinset_cons {n : ℕ} (S : Fin (n + 1) → Finset β)
    (F : (Fin (n + 1) → β) → ℝ) :
    (𝔼 q ∈ Fintype.piFinset S, F q) =
      𝔼 z ∈ S 0, 𝔼 q ∈ Fintype.piFinset (Fin.tail S), F (Fin.cons z q) := by
  let e : β × (Fin n → β) ≃ (Fin (n + 1) → β) :=
    Fin.consEquiv (fun _ : Fin (n + 1) => β)
  have hmem : ∀ p : β × (Fin n → β),
      p ∈ S 0 ×ˢ Fintype.piFinset (Fin.tail S) ↔ e p ∈ Fintype.piFinset S := by
    intro p
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hzero, htail⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [e] using hzero
      · simpa [e, Fin.tail] using htail j
    · intro hall
      constructor
      · simpa [e] using hall 0
      · intro j
        simpa [e, Fin.tail] using hall j.succ
  calc
    (𝔼 q ∈ Fintype.piFinset S, F q) =
        𝔼 p ∈ S 0 ×ˢ Fintype.piFinset (Fin.tail S), F (e p) := by
          symm
          exact Finset.expect_equiv e hmem (fun _ _ => rfl)
    _ = 𝔼 z ∈ S 0, 𝔼 q ∈ Fintype.piFinset (Fin.tail S),
          F (Fin.cons z q) := by
          rw [Finset.expect_product]
          rfl

/-- The coordinate sets attached to the positions of a list. -/
def listTupleSets (A : α → Finset β) (xs : List α) :
    Fin xs.length → Finset β := fun i => A (xs.get i)

/-- Apply a tuple of choices, from left to right, to an initial assignment. -/
def applyTuple : (xs : List α) → (α → β) → (Fin xs.length → β) → α → β
  | [], f, _ => f
  | _x :: xs, f, q =>
      applyTuple xs (Function.update f _x (q 0)) (Fin.tail q)

theorem coordinateAverage_eq_tupleAverage (A : α → Finset β)
    (xs : List α) (f : α → β) (payoff : (α → β) → ℝ) :
    coordinateAverage A xs f payoff =
      𝔼 q ∈ Fintype.piFinset (listTupleSets A xs),
        payoff (applyTuple xs f q) := by
  induction xs generalizing f with
  | nil => simp [listTupleSets, applyTuple]
  | cons x xs ih =>
      rw [coordinateAverage_cons]
      simp_rw [ih]
      symm
      calc
        (𝔼 q ∈ Fintype.piFinset (listTupleSets A (x :: xs)),
            payoff (applyTuple (x :: xs) f q)) =
            𝔼 z ∈ listTupleSets A (x :: xs) 0,
              𝔼 q ∈ Fintype.piFinset (Fin.tail (listTupleSets A (x :: xs))),
                payoff (applyTuple (x :: xs) f (Fin.cons z q)) :=
          expect_piFinset_cons (listTupleSets A (x :: xs)) _
        _ = 𝔼 z ∈ A x,
              𝔼 q ∈ Fintype.piFinset (listTupleSets A xs),
                payoff (applyTuple xs (Function.update f x z) q) := by
          apply Finset.expect_congr
          · rfl
          · intro z hz
            apply Finset.expect_congr
            · congr 1
            · intro q hq
              simp [applyTuple, listTupleSets]

theorem applyTuple_eq_of_not_mem (Axs : List α) (f : α → β)
    (q : Fin Axs.length → β) {a : α} (ha : a ∉ Axs) :
    applyTuple Axs f q a = f a := by
  induction Axs generalizing f with
  | nil => rfl
  | cons x xs ih =>
      simp only [applyTuple]
      have hsplit : a ≠ x ∧ a ∉ xs := by simpa using ha
      rw [ih (Function.update f x (q 0)) (Fin.tail q) hsplit.2]
      have hax : a ≠ x := hsplit.1
      simp [Function.update, hax]

theorem applyTuple_get {xs : List α} (hxs : xs.Nodup)
    (f : α → β) (q : Fin xs.length → β) (i : Fin xs.length) :
    applyTuple xs f q (xs.get i) = q i := by
  induction xs generalizing f with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      obtain ⟨hx, htail⟩ := List.nodup_cons.mp hxs
      refine Fin.cases ?_ (fun j => ?_) i
      · change applyTuple xs (Function.update f x (q 0)) (Fin.tail q) x = q 0
        rw [applyTuple_eq_of_not_mem xs (Function.update f x (q 0)) (Fin.tail q) hx]
        simp
      · change applyTuple xs (Function.update f x (q 0)) (Fin.tail q) (xs.get j) = q j.succ
        simpa [Fin.tail] using
          ih htail (Function.update f x (q 0)) (Fin.tail q) j

/-- If `xs` enumerates the index type without repetition, applying a list
tuple is exactly transport of that tuple across the enumeration equivalence. -/
theorem applyTuple_eq_piCongrLeft {xs : List α} (hxs : xs.Nodup)
    (hall : ∀ a : α, a ∈ xs) (f : α → β) (q : Fin xs.length → β) :
    applyTuple xs f q =
      Equiv.piCongrLeft (fun _ : α => β)
        (hxs.getEquivOfForallMemList xs hall) q := by
  let e : Fin xs.length ≃ α := hxs.getEquivOfForallMemList xs hall
  let E : (Fin xs.length → β) ≃ (α → β) :=
    Equiv.piCongrLeft (fun _ : α => β) e
  change applyTuple xs f q = E q
  funext a
  let i : Fin xs.length := e.symm a
  have hget : xs.get i = a := by
    change e i = a
    exact e.apply_symm_apply a
  rw [← hget, applyTuple_get hxs]
  change q i = E q (e i)
  exact (Equiv.piCongrLeft_apply_apply (fun _ : α => β) e q i).symm

/-- A sequential independent-coordinate average over a complete, duplicate-free
list is the uniform average over the corresponding function product. -/
theorem coordinateAverage_eq_familyAverage [Fintype α] [Fintype β]
    (A : α → Finset β) (xs : List α) (hxs : xs.Nodup)
    (hall : ∀ a : α, a ∈ xs) (f : α → β) (payoff : (α → β) → ℝ) :
    coordinateAverage A xs f payoff =
      𝔼 g ∈ FiniteDefect.familyTuples A, payoff g := by
  rw [coordinateAverage_eq_tupleAverage]
  let e : Fin xs.length ≃ α := hxs.getEquivOfForallMemList xs hall
  let E : (Fin xs.length → β) ≃ (α → β) :=
    Equiv.piCongrLeft (fun _ : α => β) e
  apply Finset.expect_equiv E
  · intro q
    rw [Fintype.mem_piFinset]
    rw [FiniteDefect.mem_familyTuples A (E q)]
    constructor
    · intro h a
      let i : Fin xs.length := e.symm a
      have hei : e i = a := e.apply_symm_apply a
      rw [← hei]
      rw [show E q (e i) = q i by
        exact Equiv.piCongrLeft_apply_apply (fun _ : α => β) e q i]
      simpa [e, listTupleSets] using h i
    · intro h i
      have hi := h (e i)
      rw [show E q (e i) = q i by
        exact Equiv.piCongrLeft_apply_apply (fun _ : α => β) e q i] at hi
      simpa [e, listTupleSets] using hi
  · intro q hq
    congr 1
    exact applyTuple_eq_piCongrLeft hxs hall f q

/-- Coordinates outside `S` may be deleted from an independent process when
the payoff only depends on the coordinates in `S`. -/
theorem coordinateAverage_filter (A : α → Finset β)
    (hA : ∀ a, (A a).Nonempty) (S : Finset α) (xs : List α)
    (f : α → β) (payoff : (α → β) → ℝ)
    (hpayoff : ∀ f g, (∀ a ∈ S, f a = g a) → payoff f = payoff g) :
    coordinateAverage A xs f payoff =
      coordinateAverage A (xs.filter (· ∈ S)) f payoff := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
      rw [coordinateAverage_cons]
      by_cases hx : x ∈ S
      · rw [List.filter_cons_of_pos (by simpa using hx), coordinateAverage_cons]
        apply Finset.expect_congr rfl
        intro z hz
        exact ih (Function.update f x z)
      · rw [List.filter_cons_of_neg (by simpa using hx)]
        calc
          (𝔼 z ∈ A x,
              coordinateAverage A xs (Function.update f x z) payoff) =
              𝔼 z ∈ A x,
                coordinateAverage A (xs.filter (· ∈ S))
                  (Function.update f x z) payoff := by
                    apply Finset.expect_congr rfl
                    intro z hz
                    exact ih (Function.update f x z)
          _ = 𝔼 _z ∈ A x,
                coordinateAverage A (xs.filter (· ∈ S)) f payoff := by
                  apply Finset.expect_congr rfl
                  intro z hz
                  apply fixedAverage_congr_on A S (xs.filter (· ∈ S))
                  · intro a ha has
                    have hax : a ≠ x := fun h => hx (h ▸ ha)
                    simp [Function.update, hax]
                  · exact hpayoff
          _ = coordinateAverage A (xs.filter (· ∈ S)) f payoff :=
            Finset.expect_const (hA x) _

/-- A no-duplicate list whose members are exactly `S` realizes the product
average indexed by the subtype `S`.  Outside `S` the initial assignment is
left unchanged. -/
theorem coordinateAverage_eq_familyAverage_on [Fintype β]
    (A : α → Finset β) (S : Finset α) (xs : List α) (hxs : xs.Nodup)
    (hmem : ∀ a : α, a ∈ xs ↔ a ∈ S)
    (f : α → β) (payoff : (α → β) → ℝ) :
    coordinateAverage A xs f payoff =
      𝔼 g ∈ FiniteDefect.familyTuples (fun a : S => A a),
        payoff (fun a => if ha : a ∈ S then g ⟨a, ha⟩ else f a) := by
  rw [coordinateAverage_eq_tupleAverage]
  let es : {a // a ∈ xs} ≃ S :=
    { toFun := fun a => ⟨a, (hmem a).mp a.property⟩
      invFun := fun a => ⟨a, (hmem a).mpr a.property⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun a => Subtype.ext rfl }
  let e : Fin xs.length ≃ S := (hxs.getEquiv xs).trans es
  let E : (Fin xs.length → β) ≃ (S → β) :=
    Equiv.piCongrLeft (fun _ : S => β) e
  apply Finset.expect_equiv E
  · intro q
    rw [Fintype.mem_piFinset]
    rw [FiniteDefect.mem_familyTuples (fun a : S => A a) (E q)]
    constructor
    · intro h a
      have hi := h (e.symm a)
      rw [show E q a = q (e.symm a) by
        simpa only [e.apply_symm_apply] using
          (Equiv.piCongrLeft_apply_apply (fun _ : S => β) e q (e.symm a))]
      simpa [e, es, listTupleSets] using hi
    · intro h i
      have hi := h (e i)
      rw [show E q (e i) = q i by
        exact Equiv.piCongrLeft_apply_apply (fun _ : S => β) e q i] at hi
      simpa [e, es, listTupleSets] using hi
  · intro q hq
    congr 1
    funext a
    by_cases ha : a ∈ S
    · let i : Fin xs.length := e.symm ⟨a, ha⟩
      have hget : xs.get i = a := by
        have he := e.apply_symm_apply ⟨a, ha⟩
        exact congrArg Subtype.val he
      calc
        applyTuple xs f q a = applyTuple xs f q (xs.get i) :=
          congrArg (applyTuple xs f q) hget.symm
        _ = q i := applyTuple_get hxs f q i
        _ = E q ⟨a, ha⟩ := by
          have he : e i = ⟨a, ha⟩ := e.apply_symm_apply ⟨a, ha⟩
          rw [← he]
          exact (Equiv.piCongrLeft_apply_apply (fun _ : S => β) e q i).symm
        _ = (if ha' : a ∈ S then E q ⟨a, ha'⟩ else f a) := by
          simp [ha]
    · have hnot : a ∉ xs := fun h => ha ((hmem a).mp h)
      rw [applyTuple_eq_of_not_mem xs f q hnot]
      simp [ha]

/-- Independent-coordinate averages do not depend on the order of a
duplicate-free enumeration. -/
theorem coordinateAverage_eq_of_nodup_same_mem [Fintype β]
    (A : α → Finset β) (xs ys : List α) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmem : ∀ a : α, a ∈ xs ↔ a ∈ ys)
    (f : α → β) (payoff : (α → β) → ℝ) :
    coordinateAverage A xs f payoff = coordinateAverage A ys f payoff := by
  let S := xs.toFinset
  have hxsS : ∀ a : α, a ∈ xs ↔ a ∈ S := by simp [S]
  have hysS : ∀ a : α, a ∈ ys ↔ a ∈ S := by
    intro a
    rw [← hmem]
    simp [S]
  rw [coordinateAverage_eq_familyAverage_on A S xs hxs hxsS f payoff]
  rw [coordinateAverage_eq_familyAverage_on A S ys hys hysS f payoff]

end Process

namespace RandomGreedy

universe w

variable [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β]
  {ι : Type w} [DecidableEq ι]

/-- The terminal second moment occurring in the propagation argument is
literally the fourth defect moment of the independent host-part product. -/
theorem terminalNeutralAverage_eq_familyMoment (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ)
    (D : ℕ) (default : β) (x : α)
    (hneutral : forwardNeighbors H x ⊆ I) :
    neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) =
      FiniteDefect.familyMoment G (threshold x) (4 * D)
        (fun y : forwardNeighbors H x => host (part y))
        (host (part x)) := by
  let S := forwardNeighbors H x
  let A : α → Finset β := fun y => host (part y)
  let payoff : (α → β) → ℝ := fun f =>
    FiniteDefect.defectPower G (threshold x)
      (fun y : S => f y) (host (part x)) (4 * D)
  have hpayoff : ∀ f g : α → β,
      (∀ y ∈ S, f y = g y) → payoff f = payoff g := by
    intro f g hfg
    unfold payoff
    congr 1
    funext y
    exact hfg y y.property
  have hmem : ∀ a : α, a ∈ (order.filter (· ∈ S) : List α) ↔ a ∈ S := by
    intro a
    simp [order_mem]
  calc
    neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) =
      Process.coordinateAverage A order (fun _ => default) payoff := by
        exact terminalNeutralAverage_eq_coordinateAverage I G H host hhost part
          threshold D default x hneutral
    _ = Process.coordinateAverage A (order.filter (· ∈ S))
        (fun _ => default) payoff := by
          apply Process.coordinateAverage_filter
          · exact fun y => hhost (part y)
          · exact hpayoff
    _ = 𝔼 g ∈ FiniteDefect.familyTuples (fun y : S => A y),
          payoff (fun a => if ha : a ∈ S then g ⟨a, ha⟩ else default) := by
            apply Process.coordinateAverage_eq_familyAverage_on
            · exact order_nodup.filter _
            · exact hmem
    _ = FiniteDefect.familyMoment G (threshold x) (4 * D)
        (fun y : S => host (part y)) (host (part x)) := by
          unfold FiniteDefect.familyMoment payoff A
          apply Finset.expect_congr rfl
          intro g hg
          congr 1
          funext y
          simp [y.property]

end RandomGreedy
end Erdos163
