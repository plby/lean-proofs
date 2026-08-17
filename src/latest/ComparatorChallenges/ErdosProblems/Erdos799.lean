import Mathlib

open Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos799

noncomputable def graphDensity
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (P n)).card : ℝ) /
    Fintype.card (SimpleGraph (Fin n))

end Erdos799

namespace Erdos753

def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, (L v).card = k) →
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

end Erdos753

namespace Erdos753

noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-! ### Basic Properties of Choosability -/

end Erdos753

namespace Erdos799

def AlmostAllListChromaticSublinear : Prop :=
  ∃ b : ℕ → ℕ,
    (fun n : ℕ ↦ (b n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
    Tendsto
      (graphDensity
        (fun n G ↦ Erdos753.listChromaticNumber G ≤ b n))
      atTop (nhds 1)

end Erdos799

namespace Erdos799

theorem erdos_799 : AlmostAllListChromaticSublinear := by
  sorry

end Erdos799

end
