import Mathlib

open scoped BigOperators ENNReal NNReal Topology
open Filter Metric Polynomial Set Topology
open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1042

def mutualDistanceProduct {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖

end Erdos1042

namespace Erdos1042

def feketeValue {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  if 2 ≤ n then
    Real.rpow (mutualDistanceProduct z) ((Nat.choose n 2 : ℝ)⁻¹)
  else 0

end Erdos1042

namespace Erdos1042

def feketeDiameter (K : Set ℂ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧ r = feketeValue z}

end Erdos1042

namespace Erdos1042

def HasTransfiniteDiameter (K : Set ℂ) (d : ℝ) : Prop :=
  Bornology.IsBounded K ∧ Tendsto (feketeDiameter K) atTop (𝓝 d)

end Erdos1042

namespace Erdos1042

def unitLemniscate (p : Polynomial ℂ) : Set ℂ :=
  {w | ‖p.eval w‖ < 1}

end Erdos1042

namespace Erdos1042

def componentCount (p : Polynomial ℂ) : ℕ :=
  Nat.card (ConnectedComponents (unitLemniscate p))

end Erdos1042

namespace Erdos1042

def rootPolynomial {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i, (X - C (z i))

end Erdos1042

namespace Erdos1042

def HasInfinitelyManyMaximalLemniscates (K : Set ℂ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧ ∃ z : Fin n → ℂ,
    (∀ i, z i ∈ K) ∧ componentCount (rootPolynomial z) = n

end Erdos1042

namespace Erdos1042

def HasUniformComponentGap (K : Set ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z : Fin n → ℂ,
    (∀ i, z i ∈ K) →
      (componentCount (rootPolynomial z) : ℝ) ≤ (1 - c) * n

end Erdos1042

namespace Erdos1042

def Erdos1042Resolution : Prop :=
  (∃ K : Set ℂ,
      IsClosed K ∧
      HasTransfiniteDiameter K 1 ∧
      (¬ ∃ a : ℂ, K ⊆ closedBall a 1) ∧
      HasInfinitelyManyMaximalLemniscates K) ∧
  (∀ K : Set ℂ, IsClosed K →
      ∀ d : ℝ, HasTransfiniteDiameter K d → 0 < d → d < 1 →
        HasUniformComponentGap K) ∧
  (∀ K : Set ℂ, IsClosed K → IsConnected K →
      ∀ d : ℝ, HasTransfiniteDiameter K d → d ≤ 1 / 4 →
        ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, z i ∈ K) →
          componentCount (rootPolynomial z) = 1)

end Erdos1042

namespace Erdos1042

theorem erdos1042_resolution : Erdos1042Resolution := by
  sorry

end Erdos1042

end
