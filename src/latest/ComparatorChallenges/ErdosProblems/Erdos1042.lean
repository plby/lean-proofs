/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Polynomial
open scoped Topology

namespace Erdos1042

noncomputable def mutualDistanceProduct {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖

noncomputable def feketeValue {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  if 2 ≤ n then
    Real.rpow (mutualDistanceProduct z) ((Nat.choose n 2 : ℝ)⁻¹)
  else 0

noncomputable def feketeDiameter (K : Set ℂ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧ r = feketeValue z}

def HasTransfiniteDiameter (K : Set ℂ) (d : ℝ) : Prop :=
  Bornology.IsBounded K ∧ Tendsto (feketeDiameter K) atTop (𝓝 d)

def unitLemniscate (p : Polynomial ℂ) : Set ℂ :=
  {w | ‖p.eval w‖ < 1}

noncomputable def componentCount (p : Polynomial ℂ) : ℕ :=
  Nat.card (ConnectedComponents (unitLemniscate p))

noncomputable def rootPolynomial {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i, (X - C (z i))

def HasInfinitelyManyMaximalLemniscates (K : Set ℂ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧ ∃ z : Fin n → ℂ,
    (∀ i, z i ∈ K) ∧ componentCount (rootPolynomial z) = n

def HasUniformComponentGap (K : Set ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z : Fin n → ℂ,
    (∀ i, z i ∈ K) →
      (componentCount (rootPolynomial z) : ℝ) ≤ (1 - c) * n

theorem erdos_1042 :
    (∃ K : Set ℂ,
        IsClosed K ∧
        Erdos1042.HasTransfiniteDiameter K 1 ∧
        (¬ ∃ a : ℂ, K ⊆ Metric.closedBall a 1) ∧
        Erdos1042.HasInfinitelyManyMaximalLemniscates K) ∧
    (∀ K : Set ℂ, IsClosed K →
        ∀ d : ℝ, Erdos1042.HasTransfiniteDiameter K d → 0 < d → d < 1 →
          Erdos1042.HasUniformComponentGap K) ∧
    (∀ K : Set ℂ, IsClosed K → IsConnected K →
        ∀ d : ℝ, Erdos1042.HasTransfiniteDiameter K d → d ≤ 1 / 4 →
          ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, z i ∈ K) →
            Erdos1042.componentCount (Erdos1042.rootPolynomial z) = 1) := by
  sorry

end Erdos1042
