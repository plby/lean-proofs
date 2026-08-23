import Mathlib

noncomputable section


namespace Erdos651

open scoped Classical in
def HasSubexponentialUpperBound (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      (f n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

end Erdos651

namespace Erdos651

open scoped Classical in
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

end Erdos651

namespace Erdos651

open scoped Classical in
def InGeneralPosition (d : ℕ) (X : Finset (Point d)) : Prop :=
  ∀ S : Finset (Point d), S ⊆ X → S.card = d + 1 →
    AffineIndependent ℝ (fun p : ↥S ↦ (p : Point d))

end Erdos651

namespace Erdos651

open scoped Classical in
def InConvexPosition {d : ℕ} (X : Finset (Point d)) : Prop :=
  ∀ x ∈ X, x ∉ convexHull ℝ (↑(X.erase x) : Set (Point d))

end Erdos651

namespace Erdos651

open scoped Classical in
def ContainsConvexSubset (d n : ℕ) (X : Finset (Point d)) : Prop :=
  ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = n ∧ InConvexPosition Y

end Erdos651

namespace Erdos651

open scoped Classical in
def ForcesConvexSubset (d n N : ℕ) : Prop :=
  ∀ X : Finset (Point d), N ≤ X.card → InGeneralPosition d X →
    ContainsConvexSubset d n X

end Erdos651

namespace Erdos651

open scoped Classical in
noncomputable def erdosSzekeresNumber (d n : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesConvexSubset d n N}

end Erdos651

namespace Erdos651

open scoped Classical in
def PohoataZakharovConclusion : Prop :=
  HasSubexponentialUpperBound (erdosSzekeresNumber 3)

end Erdos651

namespace Erdos651

open scoped Classical in
def HasExponentialLowerBound (f : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, (1 + c) ^ n < (f n : ℝ)

end Erdos651

namespace Erdos651

open scoped Classical in
def Erdos651Claim : Prop :=
  HasExponentialLowerBound (erdosSzekeresNumber 3)

end Erdos651

namespace Erdos651

open scoped Classical in
theorem erdos_651 :
    ¬ (PohoataZakharovConclusion ∧ Erdos651Claim) := by
  sorry

end Erdos651

end
