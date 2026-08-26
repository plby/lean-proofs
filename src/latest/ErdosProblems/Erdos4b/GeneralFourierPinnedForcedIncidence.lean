/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedCompatibility

/-!
# The prescribed pinned residue on prime-local coefficient states

The literal local affine equations are transported through the
squarefree prime-choice/divisor bijection without dropping empty states.
-/

namespace Erdos4b

noncomputable section

def PinnedForcedPrimeChoiceEquations {K : ℕ} (h : Fin K) (w m p₀ p a : ℕ)
    (c : DoubledPrimeChoice (PinnedShiftIndex h)) : Prop :=
  (∀ i, (∃ b, doubledPrimeChoiceIncidence c (.inl i) b) →
    (p₀ : ZMod p) + pinnedIndexSlope h w p i * (a : ZMod p) = 0) ∧
  (∀ i, (∃ b, doubledPrimeChoiceIncidence c (.inr i) b) →
    (m : ZMod p) * ((p₀ : ZMod p) + pinnedIndexSlope h w p i * (a : ZMod p)) = 1)

theorem prime_dvd_reconstructed_coordinate_lcm_iff
    {ι : Type*} (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (i : ι ⊕ ι) (p : P) :
    p.val ∣ Nat.lcm (doubledPrimeChoiceDivisor P c i false)
        (doubledPrimeChoiceDivisor P c i true) ↔
      ∃ b, doubledPrimeChoiceIncidence (c p) i b := by
  rw [prime_dvd_lcm_iff_or (hP p p.property),
    prime_dvd_doubledPrimeChoiceDivisor_iff P hP c i false p,
    prime_dvd_doubledPrimeChoiceDivisor_iff P hP c i true p]
  constructor
  · rintro (hf | ht)
    · exact ⟨false, hf⟩
    · exact ⟨true, ht⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

theorem pinnedForcedLocalEquations_reconstructed
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w m p₀ a : ℕ) (p : P) (c : P → DoubledPrimeChoice (PinnedShiftIndex h)) :
    PinnedForcedLocalEquations h w m p₀ p a (doubledPrimeChoiceDivisor P c) ↔
      PinnedForcedPrimeChoiceEquations h w m p₀ p a (c p) := by
  unfold PinnedForcedLocalEquations PinnedForcedPrimeChoiceEquations
  simp only [prime_dvd_reconstructed_coordinate_lcm_iff P hP c _ p]

theorem pinnedForcedPrimeChoiceEquations_none
    {K : ℕ} (h : Fin K) (w m p₀ p a : ℕ) :
    PinnedForcedPrimeChoiceEquations h w m p₀ p a none := by
  constructor <;> intro i hi <;>
    simp only [doubledPrimeChoiceIncidence, doubledPrimeChoicePairEquiv,
      Equiv.coe_fn_mk, primePairChoiceIncidence, reduceCtorEq, false_and,
      exists_false] at hi

end

end Erdos4b
