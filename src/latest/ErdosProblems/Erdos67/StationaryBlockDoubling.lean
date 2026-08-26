import ErdosProblems.Erdos67.StationaryBlockInformation
import ErdosProblems.Erdos67.StationaryEntropyOfLaw

/-!
# Conditional block doubling

Stationarity and the invertibility of residue translations give
`H(B_{2N} | Z) ≤ 2 H(B_N | Z)` for every finite residue tuple `Z`.
-/

open MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy

/-- Splitting a block into its two halves is a bijective recoding. -/
def splitBlockEquiv (N : ℕ) :
    (Fin (N + N) → Bool) ≃ ((Fin N → Bool) × (Fin N → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N ↦ Bool))

theorem splitBlockEquiv_left (N : ℕ) (x : Fin (N + N) → Bool) (j : Fin N) :
    (splitBlockEquiv N x).1 j = x (Fin.castAdd N j) := rfl

theorem splitBlockEquiv_right (N : ℕ) (x : Fin (N + N) → Bool) (j : Fin N) :
    (splitBlockEquiv N x).2 j = x (Fin.natAdd N j) := rfl

theorem splitBlockEquiv_signBlock (N : ℕ) (ω : Configuration) :
    splitBlockEquiv N (signBlock (N + N) ω) =
      (signBlock N ω, signBlock N (shift (N : ℤ) ω)) := by
  apply Prod.ext
  · funext j
    rw [splitBlockEquiv_left]
    rfl
  · funext j
    rw [splitBlockEquiv_right]
    simp [signBlock, shift, Nat.cast_add, add_assoc, add_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def conditionedBlockEntropy (Q : ProbabilityMeasure Configuration)
    (N : ℕ) (q : ι → ℕ+) : ℝ :=
  condEntropyOf Q (signBlock N) (residueTuple q)
    (continuous_signBlock N).measurable (continuous_residueTuple q).measurable

theorem conditionedBlockEntropy_nonneg (Q : ProbabilityMeasure Configuration)
    (N : ℕ) (q : ι → ℕ+) : 0 ≤ conditionedBlockEntropy Q N q :=
  condEntropyOf_nonneg Q _ _ _ _

theorem conditionedBlockEntropy_le (Q : ProbabilityMeasure Configuration)
    (N : ℕ) (q : ι → ℕ+) : conditionedBlockEntropy Q N q ≤ (N : ℝ) * Real.log 2 := by
  have h := condEntropyOf_le_log_card Q (signBlock N) (residueTuple q)
    (continuous_signBlock N).measurable (continuous_residueTuple q).measurable
  simpa only [conditionedBlockEntropy, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

noncomputable def residueTranslationEquiv (q : ι → ℕ+) (n : ℕ) :
    Equiv.Perm (∀ i, ZMod (q i).val) :=
  Equiv.addRight (fun i ↦ (n : ZMod (q i).val))

omit [Fintype ι] [DecidableEq ι] in
theorem residueTuple_comp_shift (q : ι → ℕ+) (n : ℕ) :
    residueTuple q ∘ shift (n : ℤ) = residueTranslationEquiv q n ∘ residueTuple q := by
  funext ω
  exact residueTuple_shift_nat q n ω

/-- Translating the sign block does not change its entropy conditional on the
residue tuple, because the translated residues are a bijective recoding. -/
theorem shiftedBlock_condEntropy_eq (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (N n : ℕ) (q : ι → ℕ+) :
    condEntropyOf Q (signBlock N ∘ shift (n : ℤ)) (residueTuple q)
      ((continuous_signBlock N).measurable.comp (continuous_shift _).measurable)
      (continuous_residueTuple q).measurable = conditionedBlockEntropy Q N q := by
  have hs := condEntropyOf_comp_preserving Q (shift (n : ℤ)) (continuous_shift _).measurable
    (shift_nat_preserving Q hQ n) (signBlock N) (residueTuple q)
    (continuous_signBlock N).measurable (continuous_residueTuple q).measurable
  have he := condEntropyOf_equiv Q (signBlock N ∘ shift (n : ℤ)) (residueTuple q)
    ((continuous_signBlock N).measurable.comp (continuous_shift _).measurable)
    (continuous_residueTuple q).measurable (Equiv.refl _) (residueTranslationEquiv q n)
  change condEntropyOf Q (signBlock N ∘ shift (n : ℤ))
      (residueTranslationEquiv q n ∘ residueTuple q) _ _ =
    condEntropyOf Q (signBlock N ∘ shift (n : ℤ)) (residueTuple q) _ _ at he
  have hg := condEntropyOf_congr Q (signBlock N ∘ shift (n : ℤ))
    (signBlock N ∘ shift (n : ℤ)) _ _
    ((continuous_signBlock N).measurable.comp (continuous_shift _).measurable)
    ((continuous_signBlock N).measurable.comp (continuous_shift _).measurable)
    ((continuous_residueTuple q).measurable.comp (continuous_shift _).measurable)
    ((measurable_of_countable (residueTranslationEquiv q n)).comp
      (continuous_residueTuple q).measurable) rfl (residueTuple_comp_shift q n)
  exact he.symm.trans (hg.symm.trans hs)

/-- The block-doubling inequality used in the entropy-decrement argument. -/
theorem conditionedBlockEntropy_double_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (N : ℕ) (q : ι → ℕ+) :
    conditionedBlockEntropy Q (N + N) q ≤ 2 * conditionedBlockEntropy Q N q := by
  have he := condEntropyOf_equiv Q (signBlock (N + N)) (residueTuple q)
    (continuous_signBlock _).measurable (continuous_residueTuple q).measurable
    (splitBlockEquiv N) (Equiv.refl _)
  have hfun : splitBlockEquiv N ∘ signBlock (N + N) =
      (fun ω ↦ (signBlock N ω, signBlock N (shift (N : ℤ) ω))) := by
    funext ω
    exact splitBlockEquiv_signBlock N ω
  have hg := condEntropyOf_congr Q _ _ _ _
    ((measurable_of_countable (splitBlockEquiv N)).comp (continuous_signBlock _).measurable)
    ((continuous_signBlock N).measurable.prodMk
      ((continuous_signBlock N).measurable.comp (continuous_shift _).measurable))
    (continuous_residueTuple q).measurable (continuous_residueTuple q).measurable hfun rfl
  have hs := condEntropyOf_pair_le Q (signBlock N) (signBlock N ∘ shift (N : ℤ))
    (residueTuple q) (continuous_signBlock _).measurable
    ((continuous_signBlock N).measurable.comp (continuous_shift _).measurable)
    (continuous_residueTuple q).measurable
  have hr := shiftedBlock_condEntropy_eq Q hQ N N q
  calc
    conditionedBlockEntropy Q (N + N) q =
        condEntropyOf Q (fun ω ↦ (signBlock N ω, signBlock N (shift (N : ℤ) ω)))
          (residueTuple q) _ _ := he.symm.trans hg
    _ ≤ conditionedBlockEntropy Q N q +
        condEntropyOf Q (signBlock N ∘ shift (N : ℤ)) (residueTuple q) _ _ := hs
    _ = 2 * conditionedBlockEntropy Q N q := by rw [hr]; ring

end Erdos67.StationaryModel
