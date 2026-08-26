/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Simpson's theorem for minimal covering systems, with its inputs proved locally.
Informal result: R. J. Simpson; finite-grid argument formalized via Hall's theorem.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeGrid
import ErdosProblems.Erdos1189.GeometricSimpson
import ErdosProblems.Erdos1189.Density

namespace Erdos1189

open Finset

lemma gridCovers_iff {D : Finset ℕ} {N : ℕ} (a : ℕ → ℤ)
    (hN : 0 < N) (hpos : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ N) :
    Grid.CoversOn (fun d => congruenceBox N d (canonicalResidue a d)) D Set.univ ↔
      Covers D a := by
  constructor
  · intro h
    apply (covers_iff_finite_period hN hdiv).mpr
    intro x
    obtain ⟨d, hd, hdx⟩ := h (digitPoint N x) (Set.mem_univ _)
    exact ⟨d, hd, (nat_modEq_canonicalResidue_iff a (hpos d hd) x).mp
      ((contains_congruenceBox_iff hN.ne' (hdiv d hd)).mp hdx)⟩
  · intro h x _
    obtain ⟨n, rfl⟩ := digitPoint_surjective N x
    obtain ⟨d, hd, hnd⟩ := h n
    exact ⟨d, hd, (contains_congruenceBox_iff hN.ne' (hdiv d hd)).mpr
      ((nat_modEq_canonicalResidue_iff a (hpos d hd) n).mpr hnd)⟩

/-- A minimal covering system contains at least one more modulus than
the sum of `(p - 1)` over the prime factors of its lcm, counted with multiplicity. -/
theorem IsMinimalCoveringSystem.simpson {D : Finset ℕ} {a : ℕ → ℤ}
    (h : IsMinimalCoveringSystem D a) : simpsonWeight (D.lcm id) + 1 ≤ D.card := by
  have hpos : ∀ d ∈ D, 0 < d := fun d hd => lt_trans Nat.zero_lt_one (h.1 d hd)
  have hnz : ∀ d ∈ D, d ≠ 0 := fun d hd => (hpos d hd).ne'
  have hN : 0 < D.lcm id := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr hnz)
  have hdiv : ∀ d ∈ D, d ∣ D.lcm id := fun d hd => dvd_lcm hd
  let H := fun d => congruenceBox (D.lcm id) d (canonicalResidue a d)
  have hgrid : Grid.MinimalCoverOn H D Set.univ := by
    refine ⟨(gridCovers_iff a hN hpos hdiv).mpr h.2.1, ?_⟩
    intro E hE hcover
    exact h.2.2 E hE ((gridCovers_iff a hN
      (fun d hd => hpos d (hE.subset hd))
      (fun d hd => hdiv d (hE.subset hd))).mp hcover)
  have hbound := Grid.simpson_grid H D coordinateSize_pos hgrid
  rw [familyFixed_lcm D (canonicalResidue a) hnz, sum_coordinateSize] at hbound
  exact hbound

theorem IsIrreducibleCoveringSet.simpson {D : Finset ℕ}
    (h : IsIrreducibleCoveringSet D) : simpsonWeight (D.lcm id) + 1 ≤ D.card := by
  obtain ⟨a, ha⟩ := h.1.2
  exact (h.minimal_system ha).simpson

/-- The paper's obstruction tests every proper subset against its own lcm.
It therefore excludes all possible new residue assignments on that subset. -/
theorem irreducible_of_simpson_obstruction {D : Finset ℕ} (hD : IsCoveringSet D)
    (hcap : ∀ T ⊂ D, T.card ≤ simpsonWeight (T.lcm id)) :
    IsIrreducibleCoveringSet D := by
  refine ⟨hD, ?_⟩
  intro T hT hcover
  obtain ⟨U, hUT, hU⟩ := hcover.exists_irreducible_subset
  have hUD : U ⊂ D := lt_of_le_of_lt hUT hT
  have h1 := hcap U hUD
  have h2 := hU.simpson
  omega

end Erdos1189
