import ErdosProblems.Erdos67.StationaryFiniteLaw
import ErdosProblems.Erdos67.StationaryEntropyBudget

/-!
# Entropy of finite-valued observables on a probability space

These are the finite entropy identities transported to an arbitrary underlying
probability space. In particular, they apply to the compact stationary model.
-/

open MeasureTheory

namespace Erdos67.FiniteEntropy

variable {Ω A B C D E : Type*} [MeasurableSpace Ω]
variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
variable [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
variable [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

noncomputable def entropyOf (Q : ProbabilityMeasure Ω) (X : Ω → A) (hX : Measurable X) : ℝ :=
  entropy (measureLaw Q X hX)

noncomputable def condEntropyOf (Q : ProbabilityMeasure Ω) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) : ℝ :=
  condEntropy (measureLaw Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY))

theorem condEntropyOf_congr (Q : ProbabilityMeasure Ω) (X X' : Ω → A) (Y Y' : Ω → B)
    (hX : Measurable X) (hX' : Measurable X') (hY : Measurable Y) (hY' : Measurable Y')
    (hx : X = X') (hy : Y = Y') :
    condEntropyOf Q X Y hX hY = condEntropyOf Q X' Y' hX' hY' := by
  subst X'
  subst Y'
  rfl

theorem condEntropyOf_eq_sub (Q : ProbabilityMeasure Ω) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) :
    condEntropyOf Q X Y hX hY =
      entropyOf Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY) - entropyOf Q Y hY := by
  rw [condEntropyOf, condEntropy, sndMarginal_measureLaw Q X Y hX hY]
  rfl

theorem condEntropyOf_nonneg (Q : ProbabilityMeasure Ω) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) : 0 ≤ condEntropyOf Q X Y hX hY :=
  condEntropy_nonneg _

theorem condEntropyOf_le_log_card [Nonempty A]
    (Q : ProbabilityMeasure Ω) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) :
    condEntropyOf Q X Y hX hY ≤ Real.log (Fintype.card A) := by
  have h := condEntropy_le_entropy_fst (measureLaw Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY))
  rw [fstMarginal_measureLaw Q X Y hX hY] at h
  exact h.trans (entropy_le_log_card _)

theorem entropyOf_equiv (Q : ProbabilityMeasure Ω) (X : Ω → A) (hX : Measurable X)
    (e : A ≃ B) :
    entropyOf Q (e ∘ X) ((measurable_of_countable e).comp hX) = entropyOf Q X hX := by
  unfold entropyOf
  rw [measureLaw_map Q X hX e (measurable_of_countable e), entropy_map_equiv]

theorem condEntropyOf_equiv (Q : ProbabilityMeasure Ω) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) (e : A ≃ C) (f : B ≃ D) :
    condEntropyOf Q (e ∘ X) (f ∘ Y)
      ((measurable_of_countable e).comp hX) ((measurable_of_countable f).comp hY) =
        condEntropyOf Q X Y hX hY := by
  rw [condEntropyOf_eq_sub, condEntropyOf_eq_sub]
  have hpair := entropyOf_equiv Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY) (e.prodCongr f)
  change entropyOf Q (fun ω ↦ (e (X ω), f (Y ω))) _ =
    entropyOf Q (fun ω ↦ (X ω, Y ω)) _ at hpair
  change entropyOf Q (fun ω ↦ (e (X ω), f (Y ω))) _ - entropyOf Q (f ∘ Y) _ = _
  rw [hpair, entropyOf_equiv Q Y hY f]

theorem condEntropyOf_comp_preserving (Q : ProbabilityMeasure Ω) (T : Ω → Ω)
    (hT : Measurable T) (hpres : Measure.map T (Q : Measure Ω) = (Q : Measure Ω))
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y) :
    condEntropyOf Q (X ∘ T) (Y ∘ T) (hX.comp hT) (hY.comp hT) =
      condEntropyOf Q X Y hX hY := by
  exact congrArg condEntropy
    (measureLaw_comp_preserving Q T hT hpres (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY))

theorem mapLeft_measureLaw (Q : ProbabilityMeasure Ω) (X : Ω → A) (Z : Ω → C)
    (hX : Measurable X) (hZ : Measurable Z) (f : A → B) :
    mapLeft (measureLaw Q (fun ω ↦ (X ω, Z ω)) (hX.prodMk hZ)) f =
      measureLaw Q (fun ω ↦ (f (X ω), Z ω))
        (((measurable_of_countable f).comp hX).prodMk hZ) := by
  exact (measureLaw_map Q (fun ω ↦ (X ω, Z ω)) (hX.prodMk hZ)
    (fun z ↦ (f z.1, z.2))
    (((measurable_of_countable f).comp measurable_fst).prodMk measurable_snd)).symm

theorem condEntropyOf_pair_le (Q : ProbabilityMeasure Ω) (X : Ω → A) (Y : Ω → B)
    (Z : Ω → C) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    condEntropyOf Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ ≤
      condEntropyOf Q X Z hX hZ + condEntropyOf Q Y Z hY hZ := by
  have h := condEntropy_pair_le
    (measureLaw Q (fun ω ↦ ((X ω, Y ω), Z ω)) ((hX.prodMk hY).prodMk hZ))
  rw [mapLeft_measureLaw Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ Prod.fst,
    mapLeft_measureLaw Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ Prod.snd] at h
  exact h

theorem entropyOf_triple_assoc (Q : ProbabilityMeasure Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    entropyOf Q (fun ω ↦ ((X ω, Y ω), Z ω)) ((hX.prodMk hY).prodMk hZ) =
      entropyOf Q (fun ω ↦ (X ω, (Y ω, Z ω))) (hX.prodMk (hY.prodMk hZ)) :=
  (entropyOf_equiv Q (fun ω ↦ ((X ω, Y ω), Z ω)) ((hX.prodMk hY).prodMk hZ)
    (Equiv.prodAssoc A B C)).symm

theorem condEntropyOf_chain_rule (Q : ProbabilityMeasure Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    condEntropyOf Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ =
      condEntropyOf Q Y Z hY hZ +
        condEntropyOf Q X (fun ω ↦ (Y ω, Z ω)) hX (hY.prodMk hZ) := by
  simp only [condEntropyOf_eq_sub]
  rw [entropyOf_triple_assoc Q X Y Z hX hY hZ]
  ring

theorem conditionalMutualInfo_measureLaw (Q : ProbabilityMeasure Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    conditionalMutualInfo
      (measureLaw Q (fun ω ↦ ((X ω, Y ω), Z ω)) ((hX.prodMk hY).prodMk hZ)) =
      condEntropyOf Q X Z hX hZ -
        condEntropyOf Q X (fun ω ↦ (Y ω, Z ω)) hX (hY.prodMk hZ) := by
  rw [conditionalMutualInfo_eq_condEntropy,
    mapLeft_measureLaw Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ Prod.fst,
    mapLeft_measureLaw Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ Prod.snd]
  change condEntropyOf Q X Z hX hZ + condEntropyOf Q Y Z hY hZ -
    condEntropyOf Q (fun ω ↦ (X ω, Y ω)) Z (hX.prodMk hY) hZ = _
  rw [condEntropyOf_chain_rule Q X Y Z hX hY hZ]
  ring

end Erdos67.FiniteEntropy
