/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open Finset

noncomputable section


namespace Erdos832

open scoped Classical in
structure FiniteHypergraph where
  V : Type
  fintypeV : Fintype V
  decidableEqV : DecidableEq V
  edges : Finset (Finset V)

end Erdos832

attribute [instance] Erdos832.FiniteHypergraph.fintypeV
  Erdos832.FiniteHypergraph.decidableEqV

namespace Erdos832.FiniteHypergraph

open scoped Classical in
def IsUniform (H : FiniteHypergraph) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

end Erdos832.FiniteHypergraph

namespace Erdos832.FiniteHypergraph

open scoped Classical in
def ProperColoring (H : FiniteHypergraph) {κ : Type} (c : H.V → κ) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

end Erdos832.FiniteHypergraph

namespace Erdos832.FiniteHypergraph

open scoped Classical in
def Colorable (H : FiniteHypergraph) (k : ℕ) : Prop :=
  ∃ c : H.V → Fin k, H.ProperColoring c

end Erdos832.FiniteHypergraph

namespace Erdos832.FiniteHypergraph

open scoped Classical in
def HasChromaticNumber (H : FiniteHypergraph) (k : ℕ) : Prop :=
  H.Colorable k ∧ ∀ j < k, ¬H.Colorable j

end Erdos832.FiniteHypergraph

namespace Erdos832.FiniteHypergraph

open scoped Classical in
def IsCompleteOn (H : FiniteHypergraph) (r m : ℕ) : Prop :=
  Fintype.card H.V = m ∧
    H.edges = (Finset.univ : Finset H.V).powersetCard r

end Erdos832.FiniteHypergraph

namespace Erdos832

open scoped Classical in
def Erdos832Claim : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ H : FiniteHypergraph,
      H.IsUniform r → H.HasChromaticNumber k →
        ((r - 1) * (k - 1) + 1).choose r ≤ H.edges.card ∧
          (H.edges.card = ((r - 1) * (k - 1) + 1).choose r →
            H.IsCompleteOn r ((r - 1) * (k - 1) + 1))

/-! ## The explicit binary construction -/

end Erdos832

namespace Erdos832

open scoped Classical in
theorem erdos832 : ¬Erdos832Claim := by
  sorry

end Erdos832

end
