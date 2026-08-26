/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.CircleSums
import ErdosProblems.Erdos254.TailSubgroup

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- A circle character annihilating the tail subgroup has a summable norm
series. This is the small-subsum argument behind Bergelson–Simmons Claim 2.14. -/
theorem summable_character_of_annihilates_tail {G : Type*}
    [NormedAddCommGroup G] [CompactSpace G]
    (A : Set ℕ) (f : ℕ → G) (χ : G →+ UnitAddCircle) (hχ : Continuous χ)
    (hkill : ∀ x ∈ tailLimitSet A f, χ x = 0) :
    Summable (fun a : A ↦ ‖χ (f a)‖) := by
  classical
  let U : Set G := {x | ‖χ x‖ < 1 / 4}
  have hU : IsOpen U := isOpen_lt hχ.norm continuous_const
  have hsub : tailLimitSet A f ⊆ U := by
    intro x hx
    change ‖χ x‖ < 1 / 4
    rw [hkill x hx, norm_zero]
    norm_num
  obtain ⟨N, hN⟩ := exists_tail_subset_of_open A f hU hsub
  apply (summable_sdiff_finset_iff A (Finset.range N) (fun a ↦ ‖χ (f a)‖)).mp
  apply summable_of_sum_le (c := 1 / 2) (fun a ↦ norm_nonneg _)
  intro F
  apply (sum_norm_lt_half_of_subset_sums_small F (fun a ↦ χ (f a)) ?_).le
  intro K _hK
  let D : Finset ℕ := K.image (fun a : ↥(A \ (Finset.range N : Set ℕ)) ↦ (a : ℕ))
  have hD : ∀ a ∈ D, a ∈ A ∧ N ≤ a := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨b.2.1, ?_⟩
    have hb := b.2.2
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hb
  have hmem : (∑ a ∈ D, f a) ∈ finiteTailSums A f N := ⟨D, hD, rfl⟩
  have hnear : ‖χ (∑ a ∈ D, f a)‖ < 1 / 4 := hN (subset_closure hmem)
  have heq : χ (∑ a ∈ D, f a) = ∑ a ∈ K, χ (f a) := by
    rw [map_sum]
    apply Finset.sum_image
    intro a _ b _ h
    exact Subtype.ext h
  simpa only [heq] using hnear

/-- With divergence at every nonzero phase, every character that vanishes on
the tail subgroup also vanishes at the generating point itself. -/
theorem character_eq_zero_of_annihilates_tail {G : Type*}
    [NormedAddCommGroup G] [CompactSpace G]
    {A : Set ℕ} (hA : PhaseDivergent A) (θ : G)
    (χ : G →+ UnitAddCircle) (hχ : Continuous χ)
    (hkill : ∀ x ∈ tailLimitSet A (fun n ↦ n • θ), χ x = 0) : χ θ = 0 := by
  have hs := summable_character_of_annihilates_tail A (fun n ↦ n • θ) χ hχ hkill
  by_contra hne
  apply hA (χ θ) hne
  simpa only [map_nsmul] using hs

end Erdos254
