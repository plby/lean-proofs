import ErdosProblems.Erdos118.Reused591.CriticalRootLabels
import ErdosProblems.Erdos118.Reused591.SeparatedRootLabels

namespace Erdos118.Reused591

/-!
# The common first-upper root interface for all strict root patterns

Only the upper minimum is needed to replay its initial response.
Later upper indices may lie between successive lower bodies or beyond
the entire lower root. The full pattern records are retained separately.
-/

namespace Erdos591.Positive.Game

structure FirstRootLabels (H : Set ℕ) (B e d j : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  shared : ℕ
  marker : ℕ
  lower_card : lower.card = e
  upper_card : upper.card = d
  shared_lower : shared ∈ lower
  shared_upper : shared ∈ upper
  shared_rank : (lower.filter (fun x => x ≤ shared)).card = j
  upper_ge : ∀ x ∈ upper, shared ≤ x
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

def CriticalRootLabels.first_view {H : Set ℕ} {B e d j : ℕ}
    (D : CriticalRootLabels H B e d j) : FirstRootLabels H B e d j where
  lower := D.lower
  upper := D.upper
  shared := D.shared
  marker := D.marker
  lower_card := D.lower_card
  upper_card := D.upper_card
  shared_lower := D.shared_lower
  shared_upper := D.shared_upper
  shared_rank := D.shared_rank
  upper_ge := fun x hx => (D.upper_bounds x hx).1
  lower_fresh := D.lower_fresh
  upper_fresh := D.upper_fresh
  marker_fresh := D.marker_fresh

def SplicedRootLabels.first_view {H : Set ℕ} {B e d j r : ℕ}
    (D : SplicedRootLabels H B e d j r) : FirstRootLabels H B e d j where
  lower := D.lower
  upper := D.upper
  shared := D.first
  marker := D.marker
  lower_card := D.lower_card
  upper_card := D.upper_card
  shared_lower := D.first_lower
  shared_upper := D.first_upper
  shared_rank := D.first_rank
  upper_ge := D.upper_first
  lower_fresh := D.lower_fresh
  upper_fresh := D.upper_fresh
  marker_fresh := D.marker_fresh

def SeparatedRootLabels.first_view {H : Set ℕ} {B e d j : ℕ}
    (D : SeparatedRootLabels H B e d j) : FirstRootLabels H B e d j where
  lower := D.lower
  upper := D.upper
  shared := D.first
  marker := D.marker
  lower_card := D.lower_card
  upper_card := D.upper_card
  shared_lower := D.first_lower
  shared_upper := D.first_upper
  shared_rank := D.first_rank
  upper_ge := D.upper_first
  lower_fresh := D.lower_fresh
  upper_fresh := D.upper_fresh
  marker_fresh := D.marker_fresh

end Erdos591.Positive.Game

end Erdos118.Reused591
