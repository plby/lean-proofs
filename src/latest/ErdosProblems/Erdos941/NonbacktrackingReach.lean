import ErdosProblems.Erdos941.ModularRotations
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Reachability with a prescribed incoming axis

Each of the three choices is a permutation of the finite state space.
Hence every directed edge can be traversed backwards by a longer directed path.
-/

namespace Erdos941

def axisDelta : Fin 3 → Axis
  | 0 => (false, true)
  | 1 => (true, false)
  | 2 => (true, true)

def otherAxis (a : Axis) (i : Fin 3) : Axis :=
  (Bool.xor a.1 (axisDelta i).1, Bool.xor a.2 (axisDelta i).2)

theorem otherAxis_ne (a : Axis) (i : Fin 3) : otherAxis a i ≠ a := by
  revert a i
  decide

theorem otherAxis_involutive (i : Fin 3) : Function.Involutive (fun a => otherAxis a i) := by
  change ∀ a, otherAxis (otherAxis a i) i = a
  revert i
  decide

theorem exists_otherAxis {a b : Axis} (h : b ≠ a) : ∃ i : Fin 3, otherAxis a i = b := by
  revert a b
  decide

theorem exists_axis_avoiding_two (a b : Axis) : ∃ c : Axis, c ≠ a ∧ c ≠ b := by
  revert a b
  decide

section Reachability

variable {X : Type*} (rot : Axis → X → X)

def turnStateStep (s : Axis × X) (i : Fin 3) : Axis × X :=
  let b := otherAxis s.1 i
  (b, rot b s.2)

def TurnEdge (s t : Axis × X) : Prop := ∃ i : Fin 3, turnStateStep rot s i = t

abbrev TurnReach := Relation.ReflTransGen (TurnEdge rot)

theorem turnStateStep_injective (hrot : ∀ a, Function.Involutive (rot a)) (i : Fin 3) :
    Function.Injective (fun s => turnStateStep rot s i) := by
  rintro ⟨a, v⟩ ⟨b, w⟩ h
  have hab : a = b := (otherAxis_involutive i).injective (congrArg Prod.fst h)
  subst b
  apply Prod.ext
  · rfl
  exact (hrot (otherAxis a i)).injective (congrArg Prod.snd h)

theorem turnReach_iterate (s : Axis × X) (i : Fin 3) (k : ℕ) :
    TurnReach rot s ((fun z => turnStateStep rot z i)^[k] s) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail ⟨i, rfl⟩

theorem turnEdge_reverse [Finite X] (hrot : ∀ a, Function.Involutive (rot a))
    {s t : Axis × X} (h : TurnEdge rot s t) : TurnReach rot t s := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨k, hk, hperiod⟩ := (turnStateStep_injective rot hrot i).mem_periodicPts s
  cases k with
  | zero => omega
  | succ k =>
    have heq : (fun z => turnStateStep rot z i)^[k] (turnStateStep rot s i) = s := by
      simpa only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply] using hperiod
    have hreach := turnReach_iterate rot (turnStateStep rot s i) i k
    rw [heq] at hreach
    exact hreach

theorem turnEdge_of_ne {a b : Axis} (hab : b ≠ a) (v : X) :
    TurnEdge rot (a, v) (b, rot b v) := by
  obtain ⟨i, hi⟩ := exists_otherAxis hab
  exact ⟨i, by simp only [turnStateStep, hi]⟩

theorem turnReach_change_incoming [Finite X] (hrot : ∀ a, Function.Involutive (rot a))
    (a c : Axis) (v : X) : TurnReach rot (a, v) (c, v) := by
  obtain ⟨b, hba, hbc⟩ := exists_axis_avoiding_two a c
  have hfirst : TurnReach rot (a, v) (b, rot b v) := .single (turnEdge_of_ne rot hba v)
  exact hfirst.trans (turnEdge_reverse rot hrot (turnEdge_of_ne rot hbc v))

theorem turnReach_apply [Finite X] (hrot : ∀ a, Function.Involutive (rot a))
    (a b : Axis) (v : X) : TurnReach rot (a, v) (b, rot b v) := by
  obtain ⟨c, hcb, _⟩ := exists_axis_avoiding_two b b
  exact (turnReach_change_incoming rot hrot a c v).tail (turnEdge_of_ne rot hcb.symm v)

def runAxes : List Axis → X → X
  | [], v => v
  | a :: w, v => runAxes w (rot a v)

theorem turnReach_word [Finite X] (hrot : ∀ a, Function.Involutive (rot a))
    (a c : Axis) (v : X) (w : List Axis) : TurnReach rot (a, v) (c, runAxes rot w v) := by
  induction w generalizing a v with
  | nil => exact turnReach_change_incoming rot hrot a c v
  | cons b w ih => exact (turnReach_apply rot hrot a b v).trans (ih b (rot b v))

end Reachability

theorem runAxes_linearTurn {R : Type*} [CommRing R] (t : R) (w : List Axis) (v : R × R × R) :
    runAxes (fun a v => linearTurn t a v) w v = linearWord t w v := by
  induction w generalizing v with
  | nil => rfl
  | cons a w ih => exact ih (linearTurn t a v)

end Erdos941
