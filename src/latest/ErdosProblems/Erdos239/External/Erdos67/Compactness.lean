import ErdosProblems.Erdos239.External.Erdos67.CompletelyMultiplicative
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Bases

/-!
# Compactness of circle-valued completely multiplicative functions

This file packages the compactness step used in Tao's proof of the Erdős discrepancy theorem.
Completely multiplicative unit-circle-valued functions are modeled on the positive naturals:
using all of `ℕ` would make every monoid homomorphism trivial because `0` is absorbing.

The multiplicativity equations cut out a closed subspace of the compact product
`(ℕ+ → Circle)`.  Consequently the space of probability laws on these functions is compact,
and every sequence of laws has a weakly convergent subsequence.  The finite partial-sum-square
observables used in second-moment arguments are continuous, so their expectations pass to the
weak limit.
-/

open scoped BigOperators
open Filter Finset Set Topology TopologicalSpace MeasureTheory

namespace Erdos67

/-- The completely multiplicative circle-valued functions on positive naturals,
viewed as a subset of the product space. -/
def completelyMultiplicativeCircleSet : Set (ℕ+ → Circle) :=
  {g | g 1 = 1 ∧ ∀ a b : ℕ+, g (a * b) = g a * g b}

/-- The closed product-space model of circle-valued completely multiplicative functions. -/
abbrev CompactCircleCharacter := completelyMultiplicativeCircleSet

theorem isClosed_completelyMultiplicativeCircleSet :
    IsClosed completelyMultiplicativeCircleSet := by
  change IsClosed
    ({g : ℕ+ → Circle | g 1 = 1} ∩
      {g : ℕ+ → Circle | ∀ a b : ℕ+, g (a * b) = g a * g b})
  apply IsClosed.inter
  · exact isClosed_eq (continuous_apply 1) continuous_const
  · have hset :
        {g : ℕ+ → Circle | ∀ a b : ℕ+, g (a * b) = g a * g b} =
          ⋂ a, ⋂ b, {g : ℕ+ → Circle | g (a * b) = g a * g b} := by
      ext g
      simp only [mem_ofPred_eq, mem_iInter]
    rw [hset]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a * b))
        ((continuous_apply a).mul (continuous_apply b))

noncomputable instance : CompactSpace CompactCircleCharacter :=
  isCompact_iff_compactSpace.mp isClosed_completelyMultiplicativeCircleSet.isCompact

noncomputable instance : MeasurableSpace CompactCircleCharacter :=
  borel CompactCircleCharacter

instance : BorelSpace CompactCircleCharacter := ⟨rfl⟩

theorem compactCircleCharacter_property (g : CompactCircleCharacter) :
    g.1 1 = 1 ∧ ∀ a b : ℕ+, g.1 (a * b) = g.1 a * g.1 b :=
  g.2

/-- Forget the product-space subtype packaging and recover the bundled monoid homomorphism. -/
def compactCircleCharacterToCircleCharacter
    (g : CompactCircleCharacter) : CircleCharacter where
  toFun := g.1
  map_one' := g.2.1
  map_mul' := g.2.2

/-- Put a bundled circle character into the compact product-space model. -/
noncomputable def circleCharacterToCompactCircleCharacter
    (g : CircleCharacter) : CompactCircleCharacter :=
  ⟨g, g.map_one, g.map_mul⟩

/-- The closed-subspace model is exactly the usual bundled monoid-homomorphism type. -/
noncomputable def compactCircleCharacterEquivCircleCharacter :
    CompactCircleCharacter ≃ CircleCharacter where
  toFun := compactCircleCharacterToCircleCharacter
  invFun := circleCharacterToCompactCircleCharacter
  left_inv _ := Subtype.ext rfl
  right_inv _ := MonoidHom.ext fun _ ↦ rfl

@[simp]
theorem compactCircleCharacterEquivCircleCharacter_apply
    (g : CompactCircleCharacter) (n : ℕ+) :
    compactCircleCharacterEquivCircleCharacter g n = g.1 n :=
  rfl

/-- Evaluation at a positive natural is continuous. -/
theorem continuous_compactCircleCharacter_eval (n : ℕ+) :
    Continuous fun g : CompactCircleCharacter ↦ g.1 n :=
  (continuous_apply n).comp continuous_subtype_val

/-- Evaluation followed by the coercion `Circle → ℂ` is continuous. -/
theorem continuous_compactCircleCharacter_eval_complex (n : ℕ+) :
    Continuous fun g : CompactCircleCharacter ↦ (g.1 n : ℂ) :=
  continuous_subtype_val.comp (continuous_compactCircleCharacter_eval n)

/-- A prime-coordinate assignment determines a point of the compact character space. -/
noncomputable def compactCircleCharacterOfPrimeAssignment
    (z : PrimeAssignment) : CompactCircleCharacter :=
  ⟨positiveExtensionFamily z, by
    refine ⟨primeExtension_one z, ?_⟩
    intro a b
    exact primeExtension_mul z a.2.ne' b.2.ne'⟩

theorem continuous_compactCircleCharacterOfPrimeAssignment :
    Continuous compactCircleCharacterOfPrimeAssignment := by
  exact continuous_positiveExtensionFamily.subtype_mk _

/-- The length-`m` homogeneous partial sum with positive dilation `d`.
The `range` indexing is `1,…,m`, represented by `k+1`. -/
noncomputable def compactCharacterPartialSum
    (d : ℕ+) (m : ℕ) (g : CompactCircleCharacter) : ℂ :=
  ∑ k ∈ range m, (g.1 (⟨k + 1, by omega⟩ * d) : ℂ)

theorem continuous_compactCharacterPartialSum (d : ℕ+) (m : ℕ) :
    Continuous fun g : CompactCircleCharacter ↦ compactCharacterPartialSum d m g := by
  unfold compactCharacterPartialSum
  exact continuous_finsetSum (range m) fun k _ ↦
    continuous_compactCircleCharacter_eval_complex (⟨k + 1, by omega⟩ * d)

/-- Squared norm of a finite partial sum, the finite second-moment observable. -/
noncomputable def compactCharacterPartialSumSq
    (d : ℕ+) (m : ℕ) (g : CompactCircleCharacter) : ℝ :=
  ‖compactCharacterPartialSum d m g‖ ^ 2

theorem continuous_compactCharacterPartialSumSq (d : ℕ+) (m : ℕ) :
    Continuous fun g : CompactCircleCharacter ↦ compactCharacterPartialSumSq d m g := by
  exact (continuous_compactCharacterPartialSum d m).norm.pow 2

/-- Every sequence of probability laws on the compact character space admits a weakly
convergent subsequence. -/
theorem compactCircleCharacter_probabilityMeasure_tendsto_subseq
    (P : ℕ → ProbabilityMeasure CompactCircleCharacter) :
    ∃ (Q : ProbabilityMeasure CompactCircleCharacter) (r : ℕ → ℕ),
      StrictMono r ∧ Tendsto (P ∘ r) atTop (nhds Q) := by
  exact CompactSpace.tendsto_subseq P

/-- Weak convergence of laws passes every finite partial-sum-square expectation to the limit. -/
theorem tendsto_integral_compactCharacterPartialSumSq
    {P : ℕ → ProbabilityMeasure CompactCircleCharacter}
    {Q : ProbabilityMeasure CompactCircleCharacter}
    (hP : Tendsto P atTop (nhds Q)) (d : ℕ+) (m : ℕ) :
    Tendsto
      (fun j ↦ ∫ g, compactCharacterPartialSumSq d m g
        ∂(P j : Measure CompactCircleCharacter))
      atTop
      (nhds (∫ g, compactCharacterPartialSumSq d m g
        ∂(Q : Measure CompactCircleCharacter))) := by
  let F : C(CompactCircleCharacter, ℝ) :=
    ⟨compactCharacterPartialSumSq d m,
      continuous_compactCharacterPartialSumSq d m⟩
  simpa only [F, Function.comp_def, ContinuousMap.coe_mk] using
    (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto Q |>.comp hP

/-- Combined compactness/observable form: after passing to one subsequence, all finite
partial-sum-square expectations converge to their expectations under the same limit law. -/
theorem exists_subseq_tendsto_integral_compactCharacterPartialSumSq
    (P : ℕ → ProbabilityMeasure CompactCircleCharacter) :
    ∃ (Q : ProbabilityMeasure CompactCircleCharacter) (r : ℕ → ℕ),
      StrictMono r ∧
      Tendsto (P ∘ r) atTop (nhds Q) ∧
      ∀ (d : ℕ+) (m : ℕ),
        Tendsto
          (fun j ↦ ∫ g, compactCharacterPartialSumSq d m g
            ∂(P (r j) : Measure CompactCircleCharacter))
          atTop
          (nhds (∫ g, compactCharacterPartialSumSq d m g
            ∂(Q : Measure CompactCircleCharacter))) := by
  obtain ⟨Q, r, hr, hP⟩ := compactCircleCharacter_probabilityMeasure_tendsto_subseq P
  refine ⟨Q, r, hr, hP, ?_⟩
  intro d m
  simpa only [Function.comp_apply] using
    tendsto_integral_compactCharacterPartialSumSq hP d m

end Erdos67
