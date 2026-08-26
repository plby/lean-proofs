/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Deterministic comparison of distinct root counts on a bulk interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RootTransfer
import ErdosProblems.Erdos521.RootPairing
import ErdosProblems.Erdos521.EndpointCover

namespace Erdos521

theorem intervalRootCount_le_of_repulsion (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1)
    (hε₀ : ε 0 ≠ 0) (n m : ℕ) {a b δ ρ η : ℝ}
    (hI : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hsep : (n + 1 : ℝ) ^ 3 * (2 * ρ) ^ 2 ≤ δ)
    (hscale : (n + 1 : ℝ) ^ 3 * ρ ≤ δ / 2) (hη : η < δ * ρ / 2)
    (hrep : ∀ x ∈ Set.Icc a b,
      δ < max |(polynomial ε n).eval x| |(polynomial ε n).derivative.eval x|)
    (hclose : ∀ x ∈ Set.Icc a b,
      |(polynomial ε m).eval x - (polynomial ε n).eval x| ≤ η) :
    intervalRootCount ε n a b ≤ intervalRootCount ε m a b + 2 := by
  classical
  let F := (realRoots ε n).filter fun x ↦ x ∈ Set.Icc a b
  let G := (realRoots ε m).filter fun x ↦ x ∈ Set.Icc a b
  have hroot (x : ℝ) (hx : x ∈ F) : (polynomial ε n).eval x = 0 := by
    rw [polynomial_eval]
    exact (mem_realRoots ε n hε₀ x).mp (Finset.mem_filter.mp hx).1
  apply card_le_card_add_two_of_pairing F G hρ.le
  · exact fun x hx ↦ (Finset.mem_filter.mp hx).2
  · intro x hx y hy hne
    have hxI := (Finset.mem_filter.mp hx).2
    have hyI := (Finset.mem_filter.mp hy).2
    rcases lt_or_gt_of_ne hne with hxy | hxy
    · have h := root_gap_gt_of_repulsion ε hε n hI (by positivity) hsep hrep
        hxI hyI hxy (hroot x hx) (hroot y hy)
      simpa only [abs_of_neg (sub_neg.mpr hxy), neg_sub] using h
    · have h := root_gap_gt_of_repulsion ε hε n hI (by positivity) hsep hrep
        hyI hxI hxy (hroot y hy) (hroot x hx)
      simpa only [abs_of_pos (sub_pos.mpr hxy)] using h
  · intro x hx hlo hhi
    have hxI := (Finset.mem_filter.mp hx).2
    have hsub : Set.Icc (x - ρ) (x + ρ) ⊆ Set.Icc a b := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hderiv : δ < |(polynomial ε n).derivative.eval x| := by
      have h := hrep x hxI
      simpa only [hroot x hx, abs_zero,
        max_eq_right (abs_nonneg ((polynomial ε n).derivative.eval x))] using h
    obtain ⟨y, hy, hyroot⟩ := polynomial_root_transfer ε hε n (polynomial ε m)
      hδ hρ (hsub.trans hI) hscale hη (hroot x hx) hderiv
      (fun t ht ↦ hclose t (hsub ht))
    refine ⟨y, Finset.mem_filter.mpr ⟨?_, hsub hy⟩, ?_⟩
    · exact (mem_realRoots ε m hε₀ y).mpr ((polynomial_eval ε m y).symm.trans hyroot)
    · exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

end Erdos521
