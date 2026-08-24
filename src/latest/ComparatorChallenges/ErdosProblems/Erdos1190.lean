/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos202

def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

end Erdos202

namespace Erdos1190

noncomputable def reciprocalSum (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹

def TailAdmissible (m : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, m < q) ∧
  ∃ a : Erdos202.ResidueAssignment Q, Erdos202.PairwiseDisjointResidues Q a

noncomputable def reciprocalSums1190 (m : ℕ) : Set ℝ :=
  {s : ℝ | ∃ Q : Finset ℕ, TailAdmissible m Q ∧ reciprocalSum Q = s}

noncomputable def epsilon1190 (m : ℕ) : ℝ :=
  sSup (reciprocalSums1190 m)

end Erdos1190

theorem Erdos1190.erdos_1190 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in Filter.atTop,
      Erdos202.Lscale (-(1 + ε)) m ≤ Erdos1190.epsilon1190 m ∧
      Erdos1190.epsilon1190 m ≤ Erdos202.Lscale (-(1 - ε)) m := by
  sorry
