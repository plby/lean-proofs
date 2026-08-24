/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos210

abbrev Point := ℝ × ℝ

def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def Collinear3 (a b c : Point) : Prop := orient a b c = 0

def HasNoncollinearTriple (P : Finset Point) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ Collinear3 a b c

def IsOrdinaryPair (P e : Finset Point) : Prop :=
  e.card = 2 ∧ e ⊆ P ∧
    ∀ ⦃a⦄, a ∈ e → ∀ ⦃b⦄, b ∈ e → a ≠ b →
      ∀ ⦃c⦄, c ∈ P → Collinear3 a b c → c ∈ e

noncomputable def ordinaryPairs (P : Finset Point) : Finset (Finset Point) :=
  by
    classical
    exact P.powersetCard 2 |>.filter (IsOrdinaryPair P)

noncomputable def ordinaryCount (P : Finset Point) : ℕ := (ordinaryPairs P).card

def attainableCounts (n : ℕ) : Set ℕ :=
  {m | ∃ P : Finset Point,
    P.card = n ∧ HasNoncollinearTriple P ∧ ordinaryCount P = m}

noncomputable def ordinaryMinimum (n : ℕ) : ℕ := sInf (attainableCounts n)

theorem erdos_210 : Filter.Tendsto ordinaryMinimum Filter.atTop Filter.atTop := by
  sorry

end Erdos210
