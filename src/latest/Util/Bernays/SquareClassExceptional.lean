import Util.Bernays.SquareClassPrimes
import Util.Bernays.FewPrimeFactors

/-!
# Negligibility of square-class prime obstructions
-/

open Filter Topology
open scoped Classical

namespace Bernays

def squareBadPrime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))) → ℕ → Prop :=
  letI := quadraticOrderIsDomain hD
  fun H p => ∃ s : SplitPrime d b, s.1 = p ∧ classSquareElement (s.idealClass hD) ∉ H

theorem exists_squareBadPrime_natPacket {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ R : ℝ, ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ discriminantCharacter (b ^ 2 + 4 * d) hD.ne p ≠ -1 ∧
          squareBadPrime hD H p) ∧ R < ∑ p ∈ P, (p : ℝ)⁻¹ := by
  classical
  letI := quadraticOrderIsDomain hD
  intro H hH R
  obtain ⟨S, hS, hmass⟩ := exists_squareBadPrimePacket hD H hH R
  refine ⟨S.image (fun s : SplitPrime d b => s.1), ?_, ?_⟩
  · intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨s.2.1, SplitPrime.character_ne_neg_one hD.ne s, s, rfl, hS s hs⟩
  · rw [Finset.sum_image (fun (s : SplitPrime d b) _ (t : SplitPrime d b) _ h => Subtype.ext h)]
    exact hmass

theorem squareBadPrime_few_values_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ k : ℕ,
      Tendsto (fun N : ℕ =>
        ((fewPrimeFactorValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1)
          (squareBadPrime hD H) k N).card : ℝ) / scale N) atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD.ne).ne'⟩
  intro H hH k
  exact fewPrimeFactorValues_div_scale_tendsto_zero _ (discriminantCharacter_sq _ hD.ne)
    (discriminantCharacter_ne_one hD) _ (exists_squareBadPrime_natPacket hD H hH) k

end Bernays
