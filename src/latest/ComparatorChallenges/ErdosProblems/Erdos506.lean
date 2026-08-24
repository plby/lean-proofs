/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos506

abbrev Point := ℝ × ℝ

def det (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def Collinear (a b c : Point) : Prop := det a b c = 0

def ContainedInLine (P : Finset Point) : Prop :=
  ∃ a b : Point, a ≠ b ∧ ∀ p ∈ P, Collinear a b p

structure Circle where
  u : ℝ
  v : ℝ
  w : ℝ

def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2

def OnCircle (C : Circle) (p : Point) : Prop :=
  normSq p + C.u * p.1 + C.v * p.2 + C.w = 0

def ContainedInCircle (P : Finset Point) : Prop :=
  ∃ C : Circle, ∀ p ∈ P, OnCircle C p

def Admissible (n : ℕ) (P : Finset Point) : Prop :=
  P.card = n ∧ ¬ ContainedInLine P ∧ ¬ ContainedInCircle P

def Noncollinear (a b c : Point) : Prop := det a b c ≠ 0

noncomputable def noncollinearTriples (P : Finset Point) :
    Finset ((Point × Point) × Point) := by
  classical
  exact (((P ×ˢ P) ×ˢ P).filter fun t ↦ Noncollinear t.1.1 t.1.2 t.2)

noncomputable def circleThrough (a b c : Point) : Circle :=
  let d := det a b c
  let qab := normSq a - normSq b
  let qac := normSq a - normSq c
  let u := (qab * (c.2 - a.2) - (b.2 - a.2) * qac) / d
  let v := ((b.1 - a.1) * qac - qab * (c.1 - a.1)) / d
  { u := u
    v := v
    w := -normSq a - u * a.1 - v * a.2 }

noncomputable def determinedCircles (P : Finset Point) : Finset Circle := by
  classical
  exact (noncollinearTriples P).image fun t ↦ circleThrough t.1.1 t.1.2 t.2

def circleCounts (n : ℕ) : Set ℕ :=
  {m | ∃ P : Finset Point, Admissible n P ∧ (determinedCircles P).card = m}

def correctedBound (n : ℕ) : ℕ :=
  Nat.choose (n - 1) 2 + 1 - (n - 1) / 2

theorem erdos_506 {n : ℕ} (hn : 393 < n) :
    IsLeast (circleCounts n) (correctedBound n) := by
  sorry

end Erdos506
