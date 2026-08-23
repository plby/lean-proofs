/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos606

open scoped Classical in
abbrev Point := Fin 2 → ℝ

end Erdos606

namespace Erdos606

open scoped Classical in
def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.sym2.filter fun e ↦ ¬ e.IsDiag

end Erdos606

namespace Erdos606

open scoped Classical in
def lineThrough (p q : Point) : AffineSubspace ℝ Point :=
  affineSpan ℝ ({p, q} : Set Point)

open scoped Classical in
lemma lineThrough_comm (p q : Point) : lineThrough p q = lineThrough q p := by
  simp only [lineThrough, Set.pair_comm]

end Erdos606

namespace Erdos606

open scoped Classical in
def lineOfPair : Sym2 Point → AffineSubspace ℝ Point :=
  Sym2.lift ⟨lineThrough, lineThrough_comm⟩

end Erdos606

namespace Erdos606

open scoped Classical in
def determinedLines (P : Finset Point) : Finset (AffineSubspace ℝ Point) := by
  classical
  exact (pointPairs P).image lineOfPair

end Erdos606

namespace Erdos606

open scoped Classical in
def lineCount (P : Finset Point) : ℕ :=
  (determinedLines P).card

end Erdos606

namespace Erdos606

open scoped Classical in
def PossibleLineCount (n m : ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧ lineCount P = m

end Erdos606

namespace Erdos606

open scoped Classical in
def transitionIndex (n : ℕ) : ℕ :=
  Nat.sqrt (n + 2)

end Erdos606

namespace Erdos606

open scoped Classical in
def Mmin (n k : ℕ) : ℕ :=
  k * (n - k) - k.choose 2 + 1

end Erdos606

namespace Erdos606

open scoped Classical in
def Mmax (n k : ℕ) : ℕ :=
  k * (n - k) + k.choose 2 + 1

end Erdos606

namespace Erdos606

open scoped Classical in
def BandValue (n k m : ℕ) : Prop :=
  Mmin n k ≤ m ∧ m ≤ Mmax n k ∧
    m ≠ Mmax n k - 1 ∧ m ≠ Mmax n k - 3

end Erdos606

namespace Erdos606

open scoped Classical in
def continuumBottom (n : ℕ) : ℕ :=
  let K := transitionIndex n
  if K * K = n + 2 ∨ K * K = n + 1 then
    Mmax n (K - 1) - 2
  else if K * K = n ∨ K * K + 1 = n then
    Mmax n (K - 1)
  else
    Mmin n K

end Erdos606

namespace Erdos606

open scoped Classical in
def ClassifiedValue (n m : ℕ) : Prop :=
  (∃ k < transitionIndex n, BandValue n k m) ∨
  (continuumBottom n ≤ m ∧ m ≤ n.choose 2 - 4) ∨
  m = n.choose 2 - 2 ∨ m = n.choose 2

end Erdos606

namespace Erdos606

open scoped Classical in
theorem erdos606 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      PossibleLineCount n m ↔ ClassifiedValue n m := by
  sorry

end Erdos606

end
