/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The unconditional finite count for optimally ordered frames with an initial prime support.
Informal source: Section 8.3 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ProfileSupply
import ErdosProblems.Erdos1189.FrameEntropy

namespace Erdos1189

open Finset

theorem optimal_rank_profile_stock {N P : ℕ} (hN : N ≠ 0)
    (hP : P.Prime) (hP7 : 7 ≤ P) (hpf : N.primeFactors = Nat.primesLE P)
    {rank : PrimeCoordinate N → ℕ} (hinj : Function.Injective rank)
    (hrank : IsArithmeticRank rank)
    (href : ∀ c i, coordinateScore c.1 c.2 < coordinateScore i.1 i.2 → rank c < rank i) :
    (∀ c, coordinateSize c - 1 ≤ (admissibleFrameModuli rank c).card) ∧
      ∀ c, (profileModuli rank c).card ≤ 2 * (admissibleFrameModuli rank c).card := by
  have hpN : P ∈ N.primeFactors := by rw [hpf]; exact Nat.mem_primesLE.mpr ⟨le_rfl, hP⟩
  have hpExp : 0 < N.factorization P := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpN)
  have hnonempty : (univ : Finset (PrimeCoordinate N)).Nonempty :=
    ⟨⟨⟨P, hpN⟩, ⟨0, hpExp⟩⟩, mem_univ _⟩
  obtain ⟨star, _, hstar⟩ := exists_max_image univ rank hnonempty
  have hlast : ∀ i, i ≠ star → rank i < rank star := by
    intro i hi
    exact lt_of_le_of_ne (hstar i (mem_univ _)) (fun h => hi (hinj h))
  have hprimebound : ∀ c : PrimeCoordinate N, c.1.val ≤ P := by
    intro c
    have hmem : c.1.val ∈ Nat.primesLE P := by simpa only [hpf] using c.1.2
    exact Nat.le_of_mem_primesLE hmem
  have hprofiles : ∀ c, coordinateSize c - 1 ≤ (profileModuli rank c).card := by
    intro c
    apply profile_count_ge_prime_weight hrank href c
    intro q hq hqc
    rw [hpf]
    exact Nat.mem_primesLE.mpr ⟨hqc.le.trans (hprimebound c), hq⟩
  have hstock : ∀ c, coordinateSize c - 1 ≤ (admissibleFrameModuli rank c).card := by
    intro c
    by_cases hc : c = star
    · subst c
      have hterm := terminal_profile_count hP hP7 hpf hrank star hlast
      have hnear := profile_count_le_admissible_add_one hN hrank star
      rw [← card_profileModuli] at hnear
      have hbound := hprimebound star
      change star.1.val - 1 ≤ _
      omega
    · have hfull := profile_count_le_admissible_of_later hN hrank (hlast c hc)
      rw [← card_profileModuli] at hfull
      exact (hprofiles c).trans hfull
  refine ⟨hstock, ?_⟩
  intro c
  have hnear := profile_count_le_admissible_add_one hN hrank c
  rw [← card_profileModuli] at hnear
  have hpos := (coordinate_weight_pos c).trans (hstock c)
  omega

/-- A complete finite lower bound; the asymptotic optimization is performed separately. -/
theorem optimal_frame_count {N P : ℕ} (hN : 1 < N)
    (hP : P.Prime) (hP7 : 7 ≤ P) (hpf : N.primeFactors = Nat.primesLE P)
    {rank : PrimeCoordinate N → ℕ} (hinj : Function.Injective rank)
    (hrank : IsArithmeticRank rank)
    (href : ∀ c i, coordinateScore c.1 c.2 < coordinateScore i.1 i.2 → rank c < rank i) :
    frameEntropy rank - (simpsonWeight N : ℝ) *
      (Real.log 2 + 2 * Real.log (simpsonWeight N + 1 : ℕ)) ≤
        Real.log (irreducibleCount (simpsonWeight N + 1)) := by
  obtain ⟨hstock, hprofile⟩ := optimal_rank_profile_stock (by omega) hP hP7 hpf hinj hrank href
  exact frameEntropy_lower_count hN rank hstock hprofile

end Erdos1189
