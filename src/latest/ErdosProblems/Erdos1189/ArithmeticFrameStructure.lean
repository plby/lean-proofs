/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The uniform generalized frame theorem for irreducible covering sets.
Informal source: BBMST Theorem 2.3, applied to the prime digit grid.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameStructure
import ErdosProblems.Erdos1189.FrameParameters
import ErdosProblems.Erdos1189.MaximumModulus

namespace Erdos1189

open Finset

lemma sum_real_coordinateSize (N : ℕ) :
    (∑ i : PrimeCoordinate N, ((coordinateSize i : ℝ) - 1)) = simpsonWeight N := by
  rw [← sum_coordinateSize, Nat.cast_sum]
  apply sum_congr rfl
  intro i _
  rw [Nat.cast_sub (coordinateSize_pos i)]
  norm_num

lemma IsMinimalCoveringSystem.gridMinimal {D : Finset ℕ} {a : ℕ → ℤ}
    (h : IsMinimalCoveringSystem D a) :
    Grid.MinimalCoverOn (fun d => congruenceBox (D.lcm id) d (canonicalResidue a d))
      D Set.univ := by
  have hpos : ∀ d ∈ D, 0 < d := fun d hd => lt_trans Nat.zero_lt_one (h.1 d hd)
  have hnz : ∀ d ∈ D, d ≠ 0 := fun d hd => (hpos d hd).ne'
  have hN : 0 < D.lcm id := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr hnz)
  have hdiv : ∀ d ∈ D, d ∣ D.lcm id := fun d hd => dvd_lcm hd
  refine ⟨(gridCovers_iff a hN hpos hdiv).mpr h.2.1, ?_⟩
  intro E hE hcover
  exact h.2.2 E hE ((gridCovers_iff a hN
    (fun d hd => hpos d (hE.subset hd))
    (fun d hd => hdiv d (hE.subset hd))).mp hcover)

theorem exists_uniform_arithmetic_frames {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ D : Finset ℕ, IsIrreducibleCoveringSet D →
        (D.card : ℝ) ≤ 4 * simpsonWeight (D.lcm id) →
        ∃ residue : ℕ → ℕ,
          ∃ frame : Grid.GeneralizedFrame
            (fun d => congruenceBox (D.lcm id) d (residue d)) D δ,
            (1 - η) * simpsonWeight (D.lcm id) ≤
              ∑ i, ((frame.families i).card : ℝ) := by
  obtain ⟨δ, hδ, hδ1, hframes⟩ := exists_uniform_generalized_frames
    (C := 4) (by norm_num) hη hη1
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro D hD hefficient
  obtain ⟨a, ha⟩ := hD.1.2
  have hminimal := hD.minimal_system ha
  have hnz : ∀ d ∈ D, d ≠ 0 := fun d hd => by have := hD.1.1 d hd; omega
  obtain ⟨frame, hframe⟩ := hframes (PrimeCoordinate (D.lcm id)) ℕ coordinateSize
    (fun d => congruenceBox (D.lcm id) d (canonicalResidue a d)) D
    (fun i => (Nat.prime_of_mem_primeFactors i.1.property).two_le)
    hminimal.gridMinimal (familyFixed_lcm D (canonicalResidue a) hnz)
    (by simpa only [sum_real_coordinateSize] using hefficient)
  exact ⟨canonicalResidue a, frame, by simpa only [sum_real_coordinateSize] using hframe⟩

theorem exists_uniform_frame_universe {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ T : ℕ, ∀ D : Finset ℕ, IsIrreducibleCoveringSet D →
      (D.card : ℝ) ≤ 4 * simpsonWeight (D.lcm id) →
        D ∈ frameUniverse (D.lcm id) T D.card η := by
  obtain ⟨δ, hδ, _, hframes⟩ := exists_uniform_arithmetic_frames hη hη1
  obtain ⟨T, hT⟩ := exists_nat_ge (1 / δ)
  refine ⟨T, ?_⟩
  intro D hD hefficient
  obtain ⟨residue, frame, hframe⟩ := hframes D hD hefficient
  exact mem_frameUniverse frame hδ hD.1.lcm_pos.ne' (fun d hd => dvd_lcm hd) hT rfl
    (by have := hD.simpson; omega) hframe

end Erdos1189
