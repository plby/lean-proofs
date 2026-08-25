import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.Step
import Mathlib.Data.Nat.Find

/-!
# Termination of the boundary-subarc orbit

The exact gap identity propagates an orbit arc whenever its relative interior
has not met the target.  Assuming that there is never such a meeting produces
pairwise disjoint isometric subarcs of a single fixed Jordan arc. The actual
finite-packing theorem rules out this infinite family.
-/

open Set Function Schoenflies

namespace Puzzling139335.CentralRotation.FirstOverlap

/-- Some positive image of the source arc lies in the ambient arc and has
relative-interior overlap with the target. Neither orbit containment nor
pairwise orbit disjointness is assumed for the subsequent images. -/
theorem exists_overlap_index
    {N Γ J : Set Schoenflies.Plane} {n₀ n₁ p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N n₀ n₁) (hΓ : IsArcBetween Γ p q)
    (hJ : IsArcBetween J a b) (hJN : J ⊆ N)
    {F : Schoenflies.Plane → Schoenflies.Plane} (hF : Isometry F)
    (hfirst : F '' Γ ⊆ N)
    (hgap : F '' (N \ (J \ {a, b})) = N \ F '' (Γ \ {p, q})) :
    ∃ n : ℕ, (F^[n + 1] '' Γ ⊆ N) ∧
      ((F^[n + 1] '' (Γ \ {p, q})) ∩ (J \ {a, b})).Nonempty := by
  classical
  by_contra hnever
  have havoid (n : ℕ) (hin : F^[n + 1] '' Γ ⊆ N) :
      Disjoint (F^[n + 1] '' (Γ \ {p, q})) (J \ {a, b}) := by
    exact disjoint_left.mpr fun x hx hxJ => hnever ⟨n, hin, x, hx, hxJ⟩
  have hinside : ∀ n : ℕ, F^[n + 1] '' Γ ⊆ N := by
    intro n
    induction n with
    | zero => simpa only [Nat.zero_add, Function.iterate_one] using hfirst
    | succ n ih =>
        exact (next_subset_gap hN hΓ hJ hJN hF hgap ih (havoid n ih)).trans sdiff_subset
  have hmissfirst : ∀ n : ℕ,
      Disjoint (F '' (Γ \ {p, q})) (F^[n + 2] '' (Γ \ {p, q})) := by
    intro n
    have hnext := next_subset_gap hN hΓ hJ hJN hF hgap (hinside n) (havoid n (hinside n))
    refine disjoint_left.mpr ?_
    intro x hxfirst hxnext
    exact (hnext (image_mono sdiff_subset hxnext)).2 hxfirst
  have hpairs := pairwise_disjoint_positive_images hF.injective hmissfirst
  have hactual : Pairwise fun i j : ℕ =>
      Disjoint ((F^[i + 1] '' Γ) \ {F^[i + 1] p, F^[i + 1] q})
        ((F^[j + 1] '' Γ) \ {F^[j + 1] p, F^[j + 1] q}) := by
    simpa only [iterate_image_arc_interior hF.injective] using hpairs
  have : Finite ℕ := ArcPacking.finite_of_disjoint_isometric_subarcs hN hΓ
    (fun n => isometry_iterate hF (n + 1)) hinside hactual
  exact _root_.not_finite ℕ

/-- There is a first positive overlap. Every preceding orbit arc, and the
overlapping arc itself, lies in the fixed ambient arc; the earlier relative
interiors all miss the target. This is the finite-orbit step of the central
rotation argument. -/
theorem exists_first_overlap_of_image_gap
    {N Γ J : Set Schoenflies.Plane} {n₀ n₁ p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N n₀ n₁) (hΓ : IsArcBetween Γ p q)
    (hJ : IsArcBetween J a b) (hJN : J ⊆ N)
    {F : Schoenflies.Plane → Schoenflies.Plane} (hF : Isometry F)
    (hfirst : F '' Γ ⊆ N)
    (hgap : F '' (N \ (J \ {a, b})) = N \ F '' (Γ \ {p, q})) :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ m → F^[k] '' Γ ⊆ N) ∧
      ((F^[m] '' (Γ \ {p, q})) ∩ (J \ {a, b})).Nonempty ∧
      (∀ k : ℕ, 1 ≤ k → k < m →
        Disjoint (F^[k] '' (Γ \ {p, q})) (J \ {a, b})) := by
  classical
  have hex := exists_overlap_index hN hΓ hJ hJN hF hfirst hgap
  let n : ℕ := Nat.find hex
  have hn : (F^[n + 1] '' Γ ⊆ N) ∧
      ((F^[n + 1] '' (Γ \ {p, q})) ∩ (J \ {a, b})).Nonempty := Nat.find_spec hex
  have havoid (k : ℕ) (hk : k < n) (hin : F^[k + 1] '' Γ ⊆ N) :
      Disjoint (F^[k + 1] '' (Γ \ {p, q})) (J \ {a, b}) := by
    refine disjoint_left.mpr ?_
    intro x hx hxJ
    exact Nat.find_min hex hk ⟨hin, x, hx, hxJ⟩
  have hprefix : ∀ k : ℕ, k ≤ n → F^[k + 1] '' Γ ⊆ N := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [Nat.zero_add, Function.iterate_one] using hfirst
    | succ k ih =>
        intro hk
        have hk' : k ≤ n := by omega
        have hkn : k < n := by omega
        exact (next_subset_gap hN hΓ hJ hJN hF hgap (ih hk')
          (havoid k hkn (ih hk'))).trans sdiff_subset
  refine ⟨n + 1, by omega, ?_, hn.2, ?_⟩
  · intro k hk hkn
    have heq : k - 1 + 1 = k := by omega
    simpa only [heq] using hprefix (k - 1) (by omega)
  · intro k hk hkn
    have heq : k - 1 + 1 = k := by omega
    have hsmall : k - 1 < n := by omega
    simpa only [heq] using havoid (k - 1) hsmall (hprefix (k - 1) hsmall.le)

end Puzzling139335.CentralRotation.FirstOverlap
