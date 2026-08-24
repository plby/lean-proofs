/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Erdos543.FinalLogic

def IsLittleOLogLog (g : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)

end Erdos543.FinalLogic

namespace Erdos543.Model

noncomputable def totalCount (G : Type*) [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  ((Finset.univ : Finset G).powersetCard k).card

open scoped Classical in
noncomputable def goodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset (Finset α) :=
  (U.powersetCard k).filter P

def SubsetSumComplete {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) : Prop :=
  ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ ∑ x ∈ S, x = g

open scoped Classical in
noncomputable def completeCount (G : Type*) [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  (goodSets (Finset.univ : Finset G) SubsetSumComplete k).card

def HalfComplete (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) : Prop :=
  totalCount G k ≤ 2 * completeCount G k

def UniversallyHalfComplete (N k : ℕ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Fintype.card G = N → HalfComplete G k

noncomputable def universalF (N : ℕ) : ℕ :=
  sInf {k : ℕ | UniversallyHalfComplete N k}

end Erdos543.Model

namespace Erdos543

noncomputable def cutoffArgument (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / Real.log 2 + g N

theorem not_erdos_543 :
    ¬ ((∃ g : ℕ → ℝ,
      Erdos543.FinalLogic.IsLittleOLogLog g ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (Model.universalF N : ℝ) ≤ Erdos543.cutoffArgument g N)) := by
  sorry

end Erdos543
