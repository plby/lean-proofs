/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Markov

/-!
# Consecutive deterministic increment blocks

This file gives the exact IID law of finitely many consecutive fixed-length
blocks of the canonical increment sequence.  It is the independent-block
input used in the amplification step of HLOZ Proposition 1.3.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos1165.ConsecutiveBlocks

noncomputable section

/-- The `i`-th consecutive block of `blockLength` increments. -/
def consecutiveStepBlock (blockLength : ℕ) (i : ℕ) :
    StepPath → (Fin blockLength → Direction) :=
  stepBlock (i * blockLength) blockLength

lemma measurable_consecutiveStepBlock (blockLength i : ℕ) :
    Measurable (consecutiveStepBlock blockLength i) := by
  exact measurable_stepBlock (i * blockLength) blockLength

/-- Every consecutive block has exactly the finite fair-product law. -/
theorem map_consecutiveStepBlock (blockLength i : ℕ) :
    fairSteps.map (consecutiveStepBlock blockLength i) = fairBlock blockLength := by
  exact fairSteps_map_stepBlock (i * blockLength) blockLength

/-- In particular, any two consecutive blocks are identically distributed.
This statement remains true for block length zero. -/
theorem identDistrib_consecutiveStepBlock (blockLength i j : ℕ) :
    IdentDistrib (consecutiveStepBlock blockLength i)
      (consecutiveStepBlock blockLength j) fairSteps fairSteps where
  aemeasurable_fst := (measurable_consecutiveStepBlock blockLength i).aemeasurable
  aemeasurable_snd := (measurable_consecutiveStepBlock blockLength j).aemeasurable
  map_eq := by
    rw [map_consecutiveStepBlock, map_consecutiveStepBlock]

/-- The flattening map from a block number and an offset to the corresponding
global increment index is injective when blocks have positive length. -/
lemma consecutiveIndex_injective {blockCount blockLength : ℕ}
    (hblockLength : 0 < blockLength) :
    Function.Injective
      (fun p : Fin blockCount × Fin blockLength ↦
        (p.1 : ℕ) * blockLength + (p.2 : ℕ)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij
  have hdiv := congrArg (fun z : ℕ ↦ z / blockLength) hij
  have hiVal : (i : ℕ) = (i' : ℕ) := by
    simpa [Nat.mul_comm, Nat.mul_add_div hblockLength,
      Nat.div_eq_of_lt j.isLt, Nat.div_eq_of_lt j'.isLt] using hdiv
  have hi : i = i' := Fin.ext hiVal
  subst i'
  have hjVal : (j : ℕ) = (j' : ℕ) := Nat.add_left_cancel hij
  have hj : j = j' := Fin.ext hjVal
  subst j'
  rfl

/-- The joint distribution of finitely many positive-length consecutive
blocks is exactly the product of their finite fair-product laws. -/
theorem map_consecutiveStepBlocks {blockCount blockLength : ℕ}
    (hblockLength : 0 < blockLength) :
    fairSteps.map
        (fun omega (i : Fin blockCount) ↦
          consecutiveStepBlock blockLength (i : ℕ) omega) =
      Measure.infinitePi (fun _ : Fin blockCount ↦ fairBlock blockLength) := by
  let index : (Fin blockCount × Fin blockLength) → ℕ :=
    fun p ↦ (p.1 : ℕ) * blockLength + (p.2 : ℕ)
  let flat : StepPath → (Fin blockCount × Fin blockLength → Direction) :=
    fun omega p ↦ omega (index p)
  let curryEquiv := MeasurableEquiv.curry (Fin blockCount) (Fin blockLength) Direction
  have hindex : Function.Injective index :=
    consecutiveIndex_injective hblockLength
  have hflat :
      fairSteps.map flat =
        Measure.infinitePi
          (fun _ : Fin blockCount × Fin blockLength ↦ fairStep) := by
    simpa [fairSteps, flat, index] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ ↦ fairStep) hindex)
  calc
    fairSteps.map
          (fun omega (i : Fin blockCount) ↦
            consecutiveStepBlock blockLength (i : ℕ) omega) =
        (fairSteps.map flat).map curryEquiv := by
      rw [Measure.map_map curryEquiv.measurable]
      · congr 1
      · exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
    _ = (Measure.infinitePi
          (fun _ : Fin blockCount × Fin blockLength ↦ fairStep)).map
          curryEquiv := by rw [hflat]
    _ = Measure.infinitePi
          (fun _ : Fin blockCount ↦ fairBlock blockLength) := by
      simpa [fairBlock, curryEquiv] using
        (Measure.infinitePi_map_curry
          (fun _ : Fin blockCount ↦ fun _ : Fin blockLength ↦ fairStep))

/-- Positive-length consecutive blocks are mutually independent. -/
theorem iIndepFun_consecutiveStepBlock {blockCount blockLength : ℕ}
    (hblockLength : 0 < blockLength) :
    iIndepFun
      (fun i : Fin blockCount ↦
        consecutiveStepBlock blockLength (i : ℕ)) fairSteps := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i : Fin blockCount ↦
      measurable_consecutiveStepBlock blockLength (i : ℕ))).2
  rw [map_consecutiveStepBlocks hblockLength]
  congr 1
  funext i
  exact (map_consecutiveStepBlock blockLength (i : ℕ)).symm

/-- Measurable events determined separately by the consecutive blocks are
mutually independent. -/
theorem iIndepSet_consecutiveBlockEvents
    {blockCount blockLength : ℕ} (hblockLength : 0 < blockLength)
    (event : Fin blockCount → Set (Fin blockLength → Direction))
    (hmeas : ∀ i, MeasurableSet (event i)) :
    iIndepSet
      (fun i : Fin blockCount ↦
        consecutiveStepBlock blockLength (i : ℕ) ⁻¹' event i)
      fairSteps := by
  let X : Fin blockCount → StepPath → (Fin blockLength → Direction) :=
    fun i ↦ consecutiveStepBlock blockLength (i : ℕ)
  have hX : iIndepFun X fairSteps :=
    iIndepFun_consecutiveStepBlock hblockLength
  have hpre (i : Fin blockCount) : MeasurableSet (X i ⁻¹' event i) :=
    (measurable_consecutiveStepBlock blockLength (i : ℕ)) (hmeas i)
  apply (iIndepSet_iff_meas_biInter hpre).2
  intro S
  simpa [X] using hX.measure_inter_preimage_eq_mul S
    (sets := event) (fun i _hi ↦ hmeas i)

/-- On the countable finite block space every set is measurable, so no
separate measurability hypothesis is needed by the event-level interface. -/
theorem iIndepSet_consecutiveBlockEvents_of_countable
    {blockCount blockLength : ℕ} (hblockLength : 0 < blockLength)
    (event : Fin blockCount → Set (Fin blockLength → Direction)) :
    iIndepSet
      (fun i : Fin blockCount ↦
        consecutiveStepBlock blockLength (i : ℕ) ⁻¹' event i)
      fairSteps := by
  exact iIndepSet_consecutiveBlockEvents hblockLength event fun i ↦
    (Set.to_countable (event i)).measurableSet

end

end Erdos1165.ConsecutiveBlocks
