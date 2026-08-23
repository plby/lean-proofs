import Mathlib

open Filter
open scoped Topology

noncomputable section


namespace Erdos543.FinalLogic

open scoped Classical in
def IsLittleOLogLog (g : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)

end Erdos543.FinalLogic

namespace Erdos543.Model

open scoped Classical in
noncomputable def totalCount (G : Type*) [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  ((Finset.univ : Finset G).powersetCard k).card

end Erdos543.Model

namespace Erdos543.Model

open scoped Classical in
noncomputable def goodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset (Finset α) :=
  (U.powersetCard k).filter P

end Erdos543.Model

namespace Erdos543.Model

open scoped Classical in
def SubsetSumComplete {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) : Prop :=
  ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ ∑ x ∈ S, x = g

end Erdos543.Model

namespace Erdos543

open scoped Classical in
abbrev SubsetSumComplete {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) : Prop :=
  Model.SubsetSumComplete A

end Erdos543

namespace Erdos543.Model

open scoped Classical in
noncomputable def completeCount (G : Type*) [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  (goodSets (Finset.univ : Finset G) SubsetSumComplete k).card

end Erdos543.Model

namespace Erdos543.Model

open scoped Classical in
def HalfComplete (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) : Prop :=
  totalCount G k ≤ 2 * completeCount G k

end Erdos543.Model

namespace Erdos543.Model

open scoped Classical in
def UniversallyHalfComplete (N k : ℕ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Fintype.card G = N → HalfComplete G k

end Erdos543.Model

namespace Erdos543.Model

open scoped Classical in
noncomputable def universalF (N : ℕ) : ℕ :=
  sInf {k : ℕ | UniversallyHalfComplete N k}

end Erdos543.Model

namespace Erdos543

open scoped Classical in
noncomputable def cutoffArgument (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / Real.log 2 + g N

end Erdos543

namespace Erdos543.FinalLogic

open scoped Classical in
def Problem543UpperBound : Prop :=
  ∃ g : ℕ → ℝ,
    IsLittleOLogLog g ∧
    ∀ᶠ N : ℕ in atTop,
      (Model.universalF N : ℝ) ≤ cutoffArgument g N

end Erdos543.FinalLogic

namespace Erdos543

open scoped Classical in
abbrev Problem543UpperBound : Prop :=
  FinalLogic.Problem543UpperBound

end Erdos543

namespace Erdos543

open scoped Classical in
theorem erdos_543 : ¬ Problem543UpperBound := by
  sorry

end Erdos543

end
