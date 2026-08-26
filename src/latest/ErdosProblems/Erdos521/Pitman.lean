/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A deterministic reflection transform for the cone-survival estimate in
Erdős Problem 521. Formal proof: Codex.

The transform sends a planar walk to a quadrant walk, preserving its length.
Together with injectivity at a fixed endpoint, it permits a lower bound on
survival counts by the number of ordinary planar bridges.
-/
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace Erdos521.Pitman

abbrev Site := ℤ × ℤ
abbrev Direction := Fin 4

def step (d : Direction) : Site :=
  match d.val with
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

def walk (w : List Direction) : Site := (w.map step).sum

@[simp] theorem walk_nil : walk [] = 0 := rfl

@[simp] theorem walk_append (u v : List Direction) : walk (u ++ v) = walk u + walk v := by
  simp [walk, List.sum_append]

@[simp] theorem walk_singleton (d : Direction) : walk [d] = step d := by simp [walk]

def updatedMinimum (p m : Site) (d : Direction) : Site :=
  (min m.1 (p.1 + (step d).1), min m.2 (p.2 + (step d).2))

/-- A step that makes a new minimum is reflected upwards in that coordinate. -/
def transformedDirection (p m : Site) (d : Direction) : Direction :=
  if d = 1 ∧ p.1 = m.1 then 0 else if d = 3 ∧ p.2 = m.2 then 2 else d

/-- The original last step is recoverable from the transformed step and the
original terminal position and minimum. -/
def decodedDirection (p m : Site) (d : Direction) : Direction :=
  if d = 0 ∧ p.1 = m.1 then 1 else if d = 2 ∧ p.2 = m.2 then 3 else d

theorem transformed_step (p m : Site) (h : m ≤ p) (d : Direction) :
    step (transformedDirection p m d) = step d - 2 * (updatedMinimum p m d - m) := by
  rcases h with ⟨hx, hy⟩
  fin_cases d <;>
    simp [transformedDirection, step, updatedMinimum, min_def, Prod.ext_iff] <;>
    split_ifs <;> simp_all <;> omega

theorem decoded_transformedDirection (p m : Site) (h : m ≤ p) (d : Direction) :
    decodedDirection (p + step d) (updatedMinimum p m d) (transformedDirection p m d) = d := by
  rcases h with ⟨hx, hy⟩
  fin_cases d <;>
    simp [decodedDirection, transformedDirection, step, updatedMinimum, min_def] <;>
    (try split_ifs) <;> (try simp_all [Fin.ext_iff]) <;> omega

structure State where
  position : Site
  minimum : Site
  output : List Direction

def initial : State := ⟨0, 0, []⟩

def update (s : State) (d : Direction) : State :=
  ⟨s.position + step d, updatedMinimum s.position s.minimum d,
    s.output ++ [transformedDirection s.position s.minimum d]⟩

def run (w : List Direction) : State := w.foldl update initial

@[simp] theorem run_nil : run [] = initial := rfl

theorem run_append_singleton (w : List Direction) (d : Direction) :
    run (w ++ [d]) = update (run w) d := by simp [run, List.foldl_append]

theorem run_valid (w : List Direction) :
    (run w).minimum ≤ (run w).position ∧ (run w).minimum ≤ 0 := by
  induction w using List.reverseRecOn with
  | nil => simp [initial]
  | append_singleton w d ih =>
    rw [run_append_singleton]
    constructor
    · exact ⟨min_le_right _ _, min_le_right _ _⟩
    · exact ⟨(min_le_left _ _).trans ih.2.1, (min_le_left _ _).trans ih.2.2⟩

theorem run_position (w : List Direction) : (run w).position = walk w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w d ih => simp [run_append_singleton, update, ih]

theorem run_output_length (w : List Direction) : (run w).output.length = w.length := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w d ih => simp [run_append_singleton, update, ih]

/-- The usual coordinatewise Pitman transform: current position minus twice
the running minimum. -/
theorem run_output_walk (w : List Direction) :
    walk (run w).output = (run w).position - 2 * (run w).minimum := by
  induction w using List.reverseRecOn with
  | nil => simp [initial]
  | append_singleton w d ih =>
    rw [run_append_singleton]
    change walk ((run w).output ++ [transformedDirection (run w).position (run w).minimum d]) = _
    rw [walk_append, walk_singleton, ih,
      transformed_step _ _ (run_valid w).1]
    change (run w).position - 2 * (run w).minimum +
      (step d - 2 * (updatedMinimum (run w).position (run w).minimum d - (run w).minimum)) =
      (run w).position + step d - 2 * updatedMinimum (run w).position (run w).minimum d
    ring

theorem run_output_nonneg (w : List Direction) : 0 ≤ walk (run w).output := by
  rw [run_output_walk]
  obtain ⟨⟨hx, hy⟩, ⟨hmx, hmy⟩⟩ := run_valid w
  change (run w).minimum.1 ≤ (0 : ℤ) at hmx
  change (run w).minimum.2 ≤ (0 : ℤ) at hmy
  change 0 ≤ (run w).position.1 - 2 * (run w).minimum.1 ∧
    0 ≤ (run w).position.2 - 2 * (run w).minimum.2
  constructor <;> omega

theorem minimum_eq_of_output_position_eq (u v : List Direction)
    (hout : (run u).output = (run v).output)
    (hpos : (run u).position = (run v).position) :
    (run u).minimum = (run v).minimum := by
  have hs := congrArg walk hout
  rw [run_output_walk, run_output_walk, hpos] at hs
  apply Prod.ext
  · have hx := congrArg Prod.fst hs
    change (run v).position.1 - 2 * (run u).minimum.1 =
      (run v).position.1 - 2 * (run v).minimum.1 at hx
    omega
  · have hy := congrArg Prod.snd hs
    change (run v).position.2 - 2 * (run u).minimum.2 =
      (run v).position.2 - 2 * (run v).minimum.2 at hy
    omega

theorem decoded_run_append (w : List Direction) (d : Direction) :
    decodedDirection (run (w ++ [d])).position (run (w ++ [d])).minimum
      (transformedDirection (run w).position (run w).minimum d) = d := by
  rw [run_append_singleton]
  exact decoded_transformedDirection _ _ (run_valid w).1 d

/-- The output word together with the original endpoint determines the input
word. In particular the transform is injective on bridges. -/
theorem run_injective_at_endpoint (u v : List Direction)
    (hout : (run u).output = (run v).output)
    (hpos : (run u).position = (run v).position) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil =>
    have hlen := congrArg List.length hout
    simp only [run_output_length, List.length_nil] at hlen
    have hv : v = [] := by simpa using hlen.symm
    exact hv.symm
  | append_singleton u d ih =>
    rcases List.eq_nil_or_concat' v with rfl | ⟨v, e, rfl⟩
    · have hlen := congrArg List.length hout
      simp only [run_output_length, List.length_append, List.length_singleton,
        List.length_nil] at hlen
      omega
    · have hmin := minimum_eq_of_output_position_eq _ _ hout hpos
      have hrev := congrArg List.reverse hout
      simp only [run_append_singleton, update, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.cons.injEq] at hrev
      have hde : d = e := by
        calc
          d = decodedDirection (run (u ++ [d])).position (run (u ++ [d])).minimum
              (transformedDirection (run u).position (run u).minimum d) :=
            (decoded_run_append u d).symm
          _ = decodedDirection (run (v ++ [e])).position (run (v ++ [e])).minimum
              (transformedDirection (run v).position (run v).minimum e) := by
            rw [hpos, hmin, hrev.1]
          _ = e := decoded_run_append v e
      subst e
      have hprefix : (run u).output = (run v).output := List.reverse_inj.mp hrev.2
      have hprefixPos : (run u).position = (run v).position := by
        simp only [run_append_singleton, update] at hpos
        change (run u).position + step d = (run v).position + step d at hpos
        exact add_right_cancel hpos
      rw [ih v hprefix hprefixPos]

/-- All prefix positions are in the closed first quadrant. -/
def StaysNonnegative (w : List Direction) : Prop :=
  ∀ k ≤ w.length, 0 ≤ walk (w.take k)

theorem run_output_staysNonnegative (w : List Direction) :
    StaysNonnegative (run w).output := by
  induction w using List.reverseRecOn with
  | nil => simp [StaysNonnegative, initial]
  | append_singleton w d ih =>
    intro k hk
    by_cases hkle : k ≤ (run w).output.length
    · rw [run_append_singleton]
      change 0 ≤ walk (((run w).output ++
        [transformedDirection (run w).position (run w).minimum d]).take k)
      rw [List.take_append_of_le_length hkle]
      exact ih k hkle
    · have hlen : (run (w ++ [d])).output.length ≤ k := by
        simp only [run_output_length, List.length_append, List.length_singleton] at hk ⊢
        rw [run_output_length] at hkle
        omega
      rw [List.take_of_length_le hlen]
      exact run_output_nonneg (w ++ [d])

end Erdos521.Pitman
