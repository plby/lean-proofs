/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos832

structure FiniteHypergraph where
  V : Type
  fintypeV : Fintype V
  decidableEqV : DecidableEq V
  edges : Finset (Finset V)

end Erdos832

attribute [instance] Erdos832.FiniteHypergraph.fintypeV
  Erdos832.FiniteHypergraph.decidableEqV

namespace Erdos832.FiniteHypergraph

def IsUniform (H : FiniteHypergraph) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

def ProperColoring (H : FiniteHypergraph) {κ : Type} (c : H.V → κ) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

def Colorable (H : FiniteHypergraph) (k : ℕ) : Prop :=
  ∃ c : H.V → Fin k, H.ProperColoring c

def HasChromaticNumber (H : FiniteHypergraph) (k : ℕ) : Prop :=
  H.Colorable k ∧ ∀ j < k, ¬H.Colorable j

def IsCompleteOn (H : FiniteHypergraph) (r m : ℕ) : Prop :=
  Fintype.card H.V = m ∧
    H.edges = (Finset.univ : Finset H.V).powersetCard r

end Erdos832.FiniteHypergraph

namespace Erdos832

/-! ## The explicit binary construction -/

theorem not_erdos_832 :
    ¬(∀ r : ℕ, 3 ≤ r → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ H : Erdos832.FiniteHypergraph,
        H.IsUniform r → H.HasChromaticNumber k →
          ((r - 1) * (k - 1) + 1).choose r ≤ H.edges.card ∧
            (H.edges.card = ((r - 1) * (k - 1) + 1).choose r →
              H.IsCompleteOn r ((r - 1) * (k - 1) + 1))) := by
  sorry

end Erdos832
