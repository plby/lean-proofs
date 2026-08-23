/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Topology

noncomputable section


namespace Erdos210

open scoped Classical in
abbrev Point := ℝ × ℝ

end Erdos210

namespace Erdos210

open scoped Classical in
def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

end Erdos210

namespace Erdos210

open scoped Classical in
def Collinear3 (a b c : Point) : Prop := orient a b c = 0

end Erdos210

namespace Erdos210

open scoped Classical in
def HasNoncollinearTriple (P : Finset Point) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ Collinear3 a b c

end Erdos210

namespace Erdos210

open scoped Classical in
def IsOrdinaryPair (P e : Finset Point) : Prop :=
  e.card = 2 ∧ e ⊆ P ∧
    ∀ ⦃a⦄, a ∈ e → ∀ ⦃b⦄, b ∈ e → a ≠ b →
      ∀ ⦃c⦄, c ∈ P → Collinear3 a b c → c ∈ e

end Erdos210

namespace Erdos210

open scoped Classical in
def ordinaryPairs (P : Finset Point) : Finset (Finset Point) :=
  by
    classical
    exact P.powersetCard 2 |>.filter (IsOrdinaryPair P)

end Erdos210

namespace Erdos210

open scoped Classical in
def ordinaryCount (P : Finset Point) : ℕ := (ordinaryPairs P).card

end Erdos210

namespace Erdos210

open scoped Classical in
def attainableCounts (n : ℕ) : Set ℕ :=
  {m | ∃ P : Finset Point,
    P.card = n ∧ HasNoncollinearTriple P ∧ ordinaryCount P = m}

end Erdos210

namespace Erdos210

open scoped Classical in
def ordinaryMinimum (n : ℕ) : ℕ := sInf (attainableCounts n)

/-! ### Nonemptiness, the near-pencil upper bound, and divergence -/

end Erdos210

namespace Erdos210

open scoped Classical in
theorem erdos_210 : Filter.Tendsto ordinaryMinimum Filter.atTop Filter.atTop := by
  sorry

end Erdos210

end
