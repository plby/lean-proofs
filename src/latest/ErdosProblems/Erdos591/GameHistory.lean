import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Induction
import Mathlib.Order.WellFounded

/-!
# Finite legal histories and their finite sets of prefixes

The relation `r q p` points from a position to an immediate successor.
This module turns any countable, well-founded transition system into
the countable history tree required by conservative uniformization.
-/

namespace Erdos591.Positive.Game

namespace History

variable {Q : Type*} (r : Q → Q → Prop)

def ValidPath (start : Q) : List Q → Prop
  | [] => True
  | q :: qs => r q start ∧ ValidPath q qs

def current (start : Q) (path : List Q) : Q := path.getLastD start

@[simp] theorem current_nil (start : Q) : current start [] = start := rfl

@[simp] theorem current_cons (start q : Q) (path : List Q) :
    current start (q :: path) = current q path := List.getLastD_cons

@[simp] theorem current_concat (start q : Q) (path : List Q) :
    current start (path ++ [q]) = q := List.getLastD_concat

theorem validPath_append (start : Q) (xs ys : List Q) :
    ValidPath r start (xs ++ ys) ↔
      ValidPath r start xs ∧ ValidPath r (current start xs) ys := by
  induction xs generalizing start with
  | nil => simp [ValidPath]
  | cons x xs ih =>
      simp only [List.cons_append, ValidPath, current_cons, ih, and_assoc]

theorem ValidPath.take {start : Q} {path : List Q} (h : ValidPath r start path) (n : ℕ) :
    ValidPath r start (path.take n) := by
  have hsplit : ValidPath r start (path.take n ++ path.drop n) := by simpa using h
  exact ((validPath_append r start _ _).1 hsplit).1

theorem ValidPath.invariant (R : Q → Prop)
    (hstep : ∀ p q, r q p → R p → R q)
    {start : Q} {path : List Q} (h : ValidPath r start path) (hstart : R start) :
    R (current start path) := by
  induction path generalizing start with
  | nil => exact hstart
  | cons q qs ih =>
      rw [current_cons]
      exact ih h.2 (hstep start q h.1 hstart)

theorem ValidPath.eq_of_records {A : Type*} (record : Q → A)
    (hdet : ∀ p q t, r q p → r t p → record q = record t → q = t)
    {start : Q} {xs ys : List Q} (hx : ValidPath r start xs) (hy : ValidPath r start ys)
    (hrec : xs.map record = ys.map record) : xs = ys := by
  induction xs generalizing start ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hrec
  | cons x xs ih =>
      cases ys with
      | nil => simp at hrec
      | cons y ys =>
          have hp : record x = record y ∧ xs.map record = ys.map record := by simpa using hrec
          have hxy := hdet start x y hx.1 hy.1 hp.1
          subst y
          exact congrArg (List.cons x) (ih hx.2 hy.2 hp.2)

end History

/-- A finite path after the initial position. The empty path is the
root history; positions are not identified merely because their current
boards coincide. -/
def History {Q : Type*} (r : Q → Q → Prop) (root : Q) : Type _ :=
  {path : List Q // History.ValidPath r root path}

namespace History

variable {Q : Type*} {r : Q → Q → Prop} {root : Q}

def position (h : History r root) : Q := current root h.val

theorem invariant (R : Q → Prop) (hroot : R root)
    (hstep : ∀ p q, r q p → R p → R q) (h : History r root) : R h.position :=
  h.property.invariant r R hstep hroot

def initial (r : Q → Q → Prop) (root : Q) : History r root := ⟨[], trivial⟩

def take (h : History r root) (n : ℕ) : History r root :=
  ⟨h.val.take n, h.property.take r n⟩

@[simp] theorem take_length (h : History r root) : h.take h.val.length = h := by
  apply Subtype.ext
  exact List.take_length

def append (h : History r root) (q : Q) (hq : r q h.position) : History r root :=
  ⟨h.val ++ [q], (validPath_append r root h.val [q]).2 ⟨h.property, hq, trivial⟩⟩

@[simp] theorem position_append (h : History r root) (q : Q) (hq : r q h.position) :
    (h.append q hq).position = q := by
  simp [position, append]

@[elab_as_elim] theorem induction (M : History r root → Prop)
    (hinit : M (initial r root))
    (hstep : ∀ h q (hq : r q h.position), M h → M (h.append q hq))
    (h : History r root) : M h := by
  obtain ⟨path, hp⟩ := h
  induction path using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton path q ih =>
      have hsplit := (validPath_append r root path [q]).1 hp
      exact hstep ⟨path, hsplit.1⟩ q hsplit.2.1 (ih hsplit.1)

theorem records_injective {A : Type*} (record : Q → A)
    (hdet : ∀ p q t, r q p → r t p → record q = record t → q = t) :
    Function.Injective (fun h : History r root => h.val.map record) := by
  intro h k hrec
  apply Subtype.ext
  exact h.property.eq_of_records r record hdet k.property hrec

def Next (k h : History r root) : Prop :=
  ∃ q, ∃ hq : r q h.position, k = h.append q hq

theorem next_wellFounded (hr : WellFounded r) :
    WellFounded (Next (r := r) (root := root)) := by
  apply (InvImage.wf position hr).mono
  intro k h hnext
  obtain ⟨q, hq, rfl⟩ := hnext
  change r (h.append q hq).position h.position
  simpa using hq

noncomputable def past (h : History r root) : Finset (History r root) := by
  classical
  exact (Finset.range (h.val.length + 1)).image h.take

theorem self_mem_past (h : History r root) : h ∈ h.past := by
  classical
  exact Finset.mem_image.mpr ⟨h.val.length, Finset.mem_range.mpr (Nat.lt_succ_self _),
    take_length h⟩

theorem take_append_of_le (h : History r root) (q : Q) (hq : r q h.position)
    {n : ℕ} (hn : n ≤ h.val.length) : (h.append q hq).take n = h.take n := by
  apply Subtype.ext
  exact List.take_append_of_le_length hn

theorem past_mono {h k : History r root} (hnext : Next k h) : h.past ⊆ k.past := by
  classical
  obtain ⟨q, hq, rfl⟩ := hnext
  intro p hp
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
  have hnle : n ≤ h.val.length := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  apply Finset.mem_image.mpr
  refine ⟨n, Finset.mem_range.mpr ?_, take_append_of_le h q hq hnle⟩
  simp only [append, List.length_append, List.length_singleton]
  omega

#print axioms next_wellFounded
#print axioms past_mono

end History

end Erdos591.Positive.Game
