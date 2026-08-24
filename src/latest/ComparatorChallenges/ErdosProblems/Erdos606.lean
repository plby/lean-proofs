/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos606

abbrev Point := Fin 2 → ℝ

noncomputable def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.sym2.filter fun e ↦ ¬ e.IsDiag

def lineThrough (p q : Point) : AffineSubspace ℝ Point :=
  affineSpan ℝ ({p, q} : Set Point)

lemma lineThrough_comm (p q : Point) : lineThrough p q = lineThrough q p := by
  simp only [lineThrough, Set.pair_comm]

def lineOfPair : Sym2 Point → AffineSubspace ℝ Point :=
  Sym2.lift ⟨lineThrough, lineThrough_comm⟩

noncomputable def determinedLines (P : Finset Point) : Finset (AffineSubspace ℝ Point) := by
  classical
  exact (pointPairs P).image lineOfPair

noncomputable def lineCount (P : Finset Point) : ℕ :=
  (determinedLines P).card

def PossibleLineCount (n m : ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧ lineCount P = m

def transitionIndex (n : ℕ) : ℕ :=
  Nat.sqrt (n + 2)

def Mmin (n k : ℕ) : ℕ :=
  k * (n - k) - k.choose 2 + 1

def Mmax (n k : ℕ) : ℕ :=
  k * (n - k) + k.choose 2 + 1

def BandValue (n k m : ℕ) : Prop :=
  Mmin n k ≤ m ∧ m ≤ Mmax n k ∧
    m ≠ Mmax n k - 1 ∧ m ≠ Mmax n k - 3

def continuumBottom (n : ℕ) : ℕ :=
  let K := transitionIndex n
  if K * K = n + 2 ∨ K * K = n + 1 then
    Mmax n (K - 1) - 2
  else if K * K = n ∨ K * K + 1 = n then
    Mmax n (K - 1)
  else
    Mmin n K

def ClassifiedValue (n m : ℕ) : Prop :=
  (∃ k < transitionIndex n, BandValue n k m) ∨
  (continuumBottom n ≤ m ∧ m ≤ n.choose 2 - 4) ∨
  m = n.choose 2 - 2 ∨ m = n.choose 2

theorem erdos_606 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      PossibleLineCount n m ↔ ClassifiedValue n m := by
  sorry

end Erdos606
