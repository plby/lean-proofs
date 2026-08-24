/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos958

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

noncomputable def pairDist : Sym2 Point → ℝ :=
  Sym2.lift ⟨(fun p q : Point => dist p q), (fun p q => dist_comm p q)⟩

noncomputable def unorderedPairs (A : Finset Point) : Finset (Sym2 Point) :=
  (A.sym2).filter (fun z => ¬ z.IsDiag)

noncomputable def distances (A : Finset Point) : Finset ℝ :=
  (unorderedPairs A).image pairDist

noncomputable def distMultiplicity (A : Finset Point) (d : ℝ) : ℕ :=
  ((unorderedPairs A).filter (fun z => pairDist z = d)).card

def EquallySpacedOnLine (A : Finset Point) : Prop :=
  ∃ p₀ v : Point,
    v ≠ 0 ∧
      A = (Finset.range A.card).image (fun i : ℕ => p₀ + (i : ℝ) • v)

noncomputable def unitCircle (θ : ℝ) : Point :=
  !₂[Real.cos θ, Real.sin θ]

def EquallySpacedOnCircle (A : Finset Point) : Prop :=
  ∃ c : Point, ∃ r θ₀ Δθ : ℝ,
    0 < r ∧
      A =
        (Finset.range A.card).image (fun i : ℕ =>
          c + r • unitCircle (θ₀ + (i : ℝ) * Δθ))

def HasProfile (A : Finset Point) : Prop :=
  let n := A.card
  let D := distances A
  D.card = n - 1 ∧ D.image (distMultiplicity A) = Finset.Icc 1 (n - 1)

end Erdos958

theorem Erdos958.not_erdos_958 :
    Not (∀ A : Finset Erdos958.Point,
      Erdos958.HasProfile A ↔ (Erdos958.EquallySpacedOnLine A ∨ Erdos958.EquallySpacedOnCircle A)) := by
  sorry
