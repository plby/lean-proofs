/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Basic

/-!
# The deterministic lazy/external path decomposition

This file formalizes the pathwise part of the deletion construction used in
the upper bound for Erdős Problem 1165.  A finite path is read two steps at a
time.  In the even version, every block `(x, x + e₁, x)` is erased; in the
shifted version, every block `(x + e₁, x, x + e₁)` is erased after dropping
the initial point.  The points left after deletion form the external path and
the erased points form the lazy contribution.

The principal results are `listLocalTime_split`, `finiteLocalTime_split`, and
`shiftedFiniteLocalTime_split`.  They are deterministic identities: at every
site, the original local time is exactly the external local time plus the
number of erased point occurrences (with a separate time-zero term in the
shifted construction).  The length identity `externalClock_eq` says that each
erased excursion removes exactly two clock ticks.

The probabilistic assertion that the numbers of consecutive erased excursions
are conditionally independent geometric random variables is deliberately not
claimed here.  It requires the IID increment law and conditioning on the
external sigma-algebra, and is not a consequence of these pathwise identities.
-/

open scoped BigOperators

namespace Erdos1165.LazyDecomposition

/-! ## Lattice parity and the two horizontal orientations -/

/-- Parity of the sum of the two coordinates. -/
def pointParity (x : Point) : ZMod 2 := x.1 + x.2

/-- The even and odd checkerboard classes. -/
def EvenPoint (x : Point) : Prop := pointParity x = 0

def OddPoint (x : Point) : Prop := pointParity x = 1

/-- The first coordinate vector. -/
def e₁ : Point := (1, 0)

/-- The two deletion orientations.  `even` deletes `(x,x+e₁,x)`; `shifted`
deletes `(x,x-e₁,x)`, which is `(y+e₁,y,y+e₁)` after putting
`x = y + e₁`. -/
inductive Orientation where
  | even
  | shifted
  deriving DecidableEq

/-- The middle point of a removable excursion based at `x`. -/
def excursionMiddle : Orientation → Point → Point
  | .even, x => x + e₁
  | .shifted, x => x - e₁

/-- A two-step block is removable precisely when it leaves in the selected
horizontal orientation and immediately returns. -/
def Removable (o : Orientation) (a b c : Point) : Prop :=
  b = excursionMiddle o a ∧ c = a

instance (o : Orientation) (a b c : Point) : Decidable (Removable o a b c) :=
  by
    unfold Removable
    infer_instance

@[simp] lemma pointParity_e₁ : pointParity e₁ = 1 := by
  decide

lemma pointParity_add (x y : Point) : pointParity (x + y) = pointParity x + pointParity y := by
  simp only [pointParity, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

@[simp] lemma pointParity_add_e₁ (x : Point) : pointParity (x + e₁) = pointParity x + 1 := by
  simp only [pointParity, e₁, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one,
    add_zero]
  ring

@[simp] lemma pointParity_sub_e₁ (x : Point) : pointParity (x - e₁) = pointParity x + 1 := by
  simp only [pointParity, e₁, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_one,
    sub_zero]
  rw [sub_eq_add_neg, show (-1 : ZMod 2) = 1 by decide]
  ring

lemma even_middle_is_odd {x : Point} (hx : EvenPoint x) :
    OddPoint (excursionMiddle .even x) := by
  simpa [EvenPoint, OddPoint, excursionMiddle, hx]

lemma shifted_middle_is_even {x : Point} (hx : OddPoint x) :
    EvenPoint (excursionMiddle .shifted x) := by
  rw [EvenPoint, excursionMiddle, pointParity_sub_e₁, show pointParity x = 1 from hx]
  decide

@[simp] lemma pointParity_directionVector (d : Direction) :
    pointParity (directionVector d) = 1 := by
  fin_cases d <;> decide

/-- A planar simple random walk started at the origin lies in the checkerboard
class determined by the parity of its time. -/
theorem pointParity_trajectory (w : StepPath) (n : ℕ) :
    pointParity (trajectory w n) = (n : ZMod 2) := by
  induction n with
  | zero => simp [pointParity]
  | succ n ih =>
      rw [trajectory_succ, pointParity_add, pointParity_directionVector, ih]
      norm_cast

lemma trajectory_even_time (w : StepPath) (k : ℕ) : EvenPoint (trajectory w (2 * k)) := by
  rw [EvenPoint, pointParity_trajectory]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide]
  simp

lemma trajectory_odd_time (w : StepPath) (k : ℕ) : OddPoint (trajectory w (2 * k + 1)) := by
  rw [OddPoint, pointParity_trajectory]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide]
  simp

/-! ## Pairwise deletion on lists -/

/-- The part of the compressed path strictly after the current retained point
`a`.  Its input is the as-yet unread part of the original path.  Blocks are
therefore disjoint: the recursive call consumes exactly two input points. -/
def compressTail (o : Orientation) (a : Point) : List Point → List Point
  | [] => []
  | [b] => [b]
  | b :: c :: rest =>
      if Removable o a b c then
        compressTail o c rest
      else
        b :: c :: compressTail o c rest

/-- The erased point occurrences, in their original order.  A removable block
contributes both its middle point and its return point. -/
def removedTail (o : Orientation) (a : Point) : List Point → List Point
  | [] => []
  | [_] => []
  | b :: c :: rest =>
      if Removable o a b c then
        b :: c :: removedTail o c rest
      else
        removedTail o c rest

/-- The external path obtained by deleting the selected two-step excursions. -/
def externalPath (o : Orientation) : List Point → List Point
  | [] => []
  | a :: rest => a :: compressTail o a rest

/-- All point occurrences removed from a finite path. -/
def lazyPoints (o : Orientation) : List Point → List Point
  | [] => []
  | a :: rest => removedTail o a rest

/-- The number of removed two-step excursions. -/
def removedExcursionsTail (o : Orientation) (a : Point) : List Point → ℕ
  | [] => 0
  | [_] => 0
  | b :: c :: rest =>
      if Removable o a b c then
        1 + removedExcursionsTail o c rest
      else
        removedExcursionsTail o c rest

def removedExcursions (o : Orientation) : List Point → ℕ
  | [] => 0
  | a :: rest => removedExcursionsTail o a rest

/-- A list-form local time, counting occurrences of `x`. -/
def listLocalTime (p : List Point) (x : Point) : ℕ := p.count x

/-- The number of steps of the compressed path. -/
def externalClock (o : Orientation) (p : List Point) : ℕ :=
  (externalPath o p).length - 1

lemma compressTail_length_add_removedTail_length (o : Orientation) (a : Point) :
    ∀ rest : List Point,
      (compressTail o a rest).length + (removedTail o a rest).length = rest.length := by
  intro rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => simp [compressTail, removedTail]
  | singleton b => simp [compressTail, removedTail]
  | cons_cons b c rest ih _ =>
      simp only [compressTail, removedTail]
      split_ifs <;> simp only [List.length_cons] <;> specialize ih c <;> omega

lemma removedTail_length (o : Orientation) (a : Point) :
    ∀ rest : List Point,
      (removedTail o a rest).length = 2 * removedExcursionsTail o a rest := by
  intro rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => simp [removedTail, removedExcursionsTail]
  | singleton b => simp [removedTail, removedExcursionsTail]
  | cons_cons b c rest ih _ =>
      simp only [removedTail, removedExcursionsTail]
      split_ifs
      · specialize ih c
        simp only [List.length_cons]
        omega
      · exact ih c

theorem externalPath_length_add_lazyPoints_length (o : Orientation) (p : List Point) :
    (externalPath o p).length + (lazyPoints o p).length = p.length := by
  cases p with
  | nil => simp [externalPath, lazyPoints]
  | cons a rest =>
      have h := compressTail_length_add_removedTail_length o a rest
      simp only [externalPath, lazyPoints, List.length_cons]
      omega

theorem lazyPoints_length (o : Orientation) (p : List Point) :
    (lazyPoints o p).length = 2 * removedExcursions o p := by
  cases p with
  | nil => simp [lazyPoints, removedExcursions]
  | cons a rest => simpa [lazyPoints, removedExcursions] using removedTail_length o a rest

lemma externalPath_nonempty (o : Orientation) {p : List Point} (hp : p ≠ []) :
    externalPath o p ≠ [] := by
  cases p with
  | nil => contradiction
  | cons a rest => simp [externalPath]

/-- Deleting `q` excursions reduces a nonempty path's clock by exactly `2q`. -/
theorem externalClock_eq (o : Orientation) {p : List Point} (hp : p ≠ []) :
    externalClock o p + 2 * removedExcursions o p = p.length - 1 := by
  have hext : 0 < (externalPath o p).length :=
    Nat.pos_of_ne_zero (by simpa using externalPath_nonempty o hp)
  have hlen := externalPath_length_add_lazyPoints_length o p
  have hlazy := lazyPoints_length o p
  unfold externalClock
  omega

lemma count_compressTail_add_count_removedTail (o : Orientation) (a x : Point) :
    ∀ rest : List Point,
      rest.count x = (compressTail o a rest).count x + (removedTail o a rest).count x := by
  intro rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => simp [compressTail, removedTail]
  | singleton b => simp [compressTail, removedTail]
  | cons_cons b c rest ih _ =>
      simp only [compressTail, removedTail]
      split_ifs <;> simp only [List.count_cons] <;> specialize ih c <;> omega

/-- Exact pathwise splitting of local time into external and erased
contributions. -/
theorem listLocalTime_split (o : Orientation) (p : List Point) (x : Point) :
    listLocalTime p x =
      listLocalTime (externalPath o p) x + listLocalTime (lazyPoints o p) x := by
  cases p with
  | nil => simp [listLocalTime, externalPath, lazyPoints]
  | cons a rest =>
      have h := count_compressTail_add_count_removedTail o a x rest
      simp only [listLocalTime, externalPath, lazyPoints, List.count_cons]
      omega

/-! ## Finite paths and the shifted decomposition -/

/-- The list of positions at times `0,…,n`. -/
def finitePathList {n : ℕ} (u : Fin (n + 1) → Point) : List Point := List.ofFn u

/-- Local time of a finite path, including both endpoints. -/
def finiteLocalTime {n : ℕ} (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  localTimePrefix u x

def finiteExternalPath {n : ℕ} (o : Orientation) (u : Fin (n + 1) → Point) : List Point :=
  externalPath o (finitePathList u)

def finiteLazyPoints {n : ℕ} (o : Orientation) (u : Fin (n + 1) → Point) : List Point :=
  lazyPoints o (finitePathList u)

def finiteExternalLocalTime {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  listLocalTime (finiteExternalPath o u) x

def finiteLazyLocalTime {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  listLocalTime (finiteLazyPoints o u) x

/-- External clock at the end of a finite path. -/
def finiteExternalClock {n : ℕ} (o : Orientation) (u : Fin (n + 1) → Point) : ℕ :=
  externalClock o (finitePathList u)

def finiteRemovedExcursions {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) : ℕ :=
  removedExcursions o (finitePathList u)

/-- The finite version of `N_n = n - 2 (# deleted excursions)`. -/
theorem finiteExternalClock_eq {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) :
    finiteExternalClock o u + 2 * finiteRemovedExcursions o u = n := by
  unfold finiteExternalClock finiteRemovedExcursions
  have hne : finitePathList u ≠ [] := by simp [finitePathList]
  simpa [finitePathList] using externalClock_eq o hne

lemma finiteLocalTime_eq_listLocalTime : ∀ {m : ℕ} (u : Fin m → Point) (x : Point),
    (Finset.univ.filter fun j ↦ u j = x).card = listLocalTime (List.ofFn u) x := by
  intro m
  induction m with
  | zero => simp [listLocalTime]
  | succ m ih =>
      intro u x
      rw [Finset.card_filter, Fin.sum_univ_succ]
      have hih := ih (fun i ↦ u i.succ) x
      rw [Finset.card_filter] at hih
      unfold listLocalTime at hih
      unfold listLocalTime
      simp only [List.ofFn_succ, List.count_cons, beq_iff_eq]
      omega

/-- Equation (6.1), in finite-path form, for either pairwise deletion
orientation. -/
theorem finiteLocalTime_split {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) (x : Point) :
    finiteLocalTime u x = finiteExternalLocalTime o u x + finiteLazyLocalTime o u x := by
  rw [finiteLocalTime, localTimePrefix, finiteLocalTime_eq_listLocalTime]
  exact listLocalTime_split o (finitePathList u) x

/-- The same identity stated directly for the canonical finite-prefix local
time from `Erdos1165.Basic`. -/
theorem localTimePrefix_split {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) (x : Point) :
    localTimePrefix u x = finiteExternalLocalTime o u x + finiteLazyLocalTime o u x := by
  exact finiteLocalTime_split o u x

/-- Equation (6.1) for the prefix of an infinite path through time `n`. -/
def externalLocalTime (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  finiteExternalLocalTime o (pathPrefix s n) x

def lazyLocalTime (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  finiteLazyLocalTime o (pathPrefix s n) x

theorem localTime_split (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x = externalLocalTime o s n x + lazyLocalTime o s n x := by
  exact localTimePrefix_split o (pathPrefix s n) x

/-- The shifted construction first discards time zero and then reads pairs
starting at original time one. -/
def shiftedInput {n : ℕ} (u : Fin (n + 1) → Point) : List Point :=
  (finitePathList u).drop 1

def shiftedExternalPath {n : ℕ} (u : Fin (n + 1) → Point) : List Point :=
  externalPath .shifted (shiftedInput u)

def shiftedLazyPoints {n : ℕ} (u : Fin (n + 1) → Point) : List Point :=
  lazyPoints .shifted (shiftedInput u)

def shiftedExternalLocalTime {n : ℕ} (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  listLocalTime (shiftedExternalPath u) x

def shiftedLazyLocalTime {n : ℕ} (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  listLocalTime (shiftedLazyPoints u) x

lemma finitePathList_cons_tail {n : ℕ} (u : Fin (n + 1) → Point) :
    finitePathList u = u 0 :: shiftedInput u := by
  simp [finitePathList, shiftedInput]

/-- Shifted local-time splitting.  The explicit indicator is the occurrence at
time zero, which is outside the shifted input. -/
theorem shiftedFiniteLocalTime_split {n : ℕ} (u : Fin (n + 1) → Point) (x : Point) :
    finiteLocalTime u x = (if u 0 = x then 1 else 0) +
      shiftedExternalLocalTime u x + shiftedLazyLocalTime u x := by
  rw [finiteLocalTime, localTimePrefix, finiteLocalTime_eq_listLocalTime,
    show List.ofFn u = u 0 :: shiftedInput u from finitePathList_cons_tail u]
  have hsplit := listLocalTime_split .shifted (shiftedInput u) x
  unfold shiftedExternalLocalTime shiftedLazyLocalTime shiftedExternalPath shiftedLazyPoints
  unfold listLocalTime at hsplit ⊢
  simp only [List.count_cons, beq_iff_eq]
  omega

def shiftedExternalLocalTimeAt (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  shiftedExternalLocalTime (pathPrefix s n) x

def shiftedLazyLocalTimeAt (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  shiftedLazyLocalTime (pathPrefix s n) x

theorem shiftedLocalTime_split (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x = (if s 0 = x then 1 else 0) +
      shiftedExternalLocalTimeAt s n x + shiftedLazyLocalTimeAt s n x := by
  exact shiftedFiniteLocalTime_split (pathPrefix s n) x

end Erdos1165.LazyDecomposition
