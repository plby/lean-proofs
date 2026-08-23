/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Set Topology

noncomputable section

namespace Set

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

open scoped Classical in
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos72

open scoped Classical in
noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact (2 * G.edgeFinset.card : ℝ) / Fintype.card V

end Erdos72

namespace Erdos72

open scoped Classical in
def HasCycleLength {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = m

end Erdos72

namespace Erdos72

open scoped Classical in
def ResolutionStatement : Prop :=
  ∃ A : Set ℕ, A.HasDensity 0 ∧
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ G : SimpleGraph (Fin n),
        c ≤ averageDegree G → ∃ m ∈ A, HasCycleLength G m

end Erdos72

namespace Erdos72

open scoped Classical in
theorem erdos_72 : ResolutionStatement := by
  sorry

end Erdos72

end
