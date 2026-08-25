/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CongruenceCertificates.Block00
import ErdosProblems.Erdos232.CongruenceCertificates.Block01
import ErdosProblems.Erdos232.CongruenceCertificates.Block02
import ErdosProblems.Erdos232.CongruenceCertificates.Block03
import ErdosProblems.Erdos232.CongruenceCertificates.Block04
import ErdosProblems.Erdos232.CongruenceCertificates.Block05
import ErdosProblems.Erdos232.CongruenceCertificates.Block06
import ErdosProblems.Erdos232.CongruenceCertificates.Block07
import ErdosProblems.Erdos232.CongruenceCertificates.Block08
import ErdosProblems.Erdos232.CongruenceCertificates.Block09
import ErdosProblems.Erdos232.CongruenceCertificates.Block10
import ErdosProblems.Erdos232.CongruenceCertificates.Block11
import ErdosProblems.Erdos232.CongruenceCertificates.Block12
import ErdosProblems.Erdos232.CongruenceCertificates.Block13
import ErdosProblems.Erdos232.CongruenceCertificates.Block14
import ErdosProblems.Erdos232.CongruenceCertificates.Block15
import ErdosProblems.Erdos232.CongruenceCertificates.Block16
import ErdosProblems.Erdos232.CongruenceCertificates.Block17
import ErdosProblems.Erdos232.CongruenceCertificates.Block18
import ErdosProblems.Erdos232.CongruenceCertificates.Block19
import ErdosProblems.Erdos232.CongruenceCertificates.Block20
import ErdosProblems.Erdos232.CongruenceCertificates.Block21
import ErdosProblems.Erdos232.CongruenceCertificates.Block22
import ErdosProblems.Erdos232.CongruenceCertificates.Block23

namespace Erdos232

theorem certificateMasks_congruent (i : Fin 24) :
    ∀ c ∈ atomCongruenceWeights i, MaskCongruent c.1 c.2.1 := by
  fin_cases i <;>
    first
    | exact maskCongruent_block00
    | exact maskCongruent_block01
    | exact maskCongruent_block02
    | exact maskCongruent_block03
    | exact maskCongruent_block04
    | exact maskCongruent_block05
    | exact maskCongruent_block06
    | exact maskCongruent_block07
    | exact maskCongruent_block08
    | exact maskCongruent_block09
    | exact maskCongruent_block10
    | exact maskCongruent_block11
    | exact maskCongruent_block12
    | exact maskCongruent_block13
    | exact maskCongruent_block14
    | exact maskCongruent_block15
    | exact maskCongruent_block16
    | exact maskCongruent_block17
    | exact maskCongruent_block18
    | exact maskCongruent_block19
    | exact maskCongruent_block20
    | exact maskCongruent_block21
    | exact maskCongruent_block22
    | exact maskCongruent_block23

private theorem certificateMasks_bounded00 :
    atomCongruenceWeights00.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded01 :
    atomCongruenceWeights01.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded02 :
    atomCongruenceWeights02.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded03 :
    atomCongruenceWeights03.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded04 :
    atomCongruenceWeights04.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded05 :
    atomCongruenceWeights05.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded06 :
    atomCongruenceWeights06.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded07 :
    atomCongruenceWeights07.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded08 :
    atomCongruenceWeights08.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded09 :
    atomCongruenceWeights09.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded10 :
    atomCongruenceWeights10.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded11 :
    atomCongruenceWeights11.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded12 :
    atomCongruenceWeights12.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded13 :
    atomCongruenceWeights13.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded14 :
    atomCongruenceWeights14.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded15 :
    atomCongruenceWeights15.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded16 :
    atomCongruenceWeights16.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded17 :
    atomCongruenceWeights17.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded18 :
    atomCongruenceWeights18.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded19 :
    atomCongruenceWeights19.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded20 :
    atomCongruenceWeights20.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded21 :
    atomCongruenceWeights21.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded22 :
    atomCongruenceWeights22.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide
private theorem certificateMasks_bounded23 :
    atomCongruenceWeights23.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true := by
  decide

/-- Both masks in every certified congruence row use only the 23 configuration bits. -/
theorem certificateMasks_bounded (i : Fin 24) :
    ∀ c ∈ atomCongruenceWeights i, c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23 := by
  have decode {l : List (Nat × Nat × Int)}
      (h : l.all (fun c ↦ decide (c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23)) = true) :
      ∀ c ∈ l, c.1 < 2 ^ 23 ∧ c.2.1 < 2 ^ 23 := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using h
  fin_cases i <;>
    first
    | exact decode certificateMasks_bounded00
    | exact decode certificateMasks_bounded01
    | exact decode certificateMasks_bounded02
    | exact decode certificateMasks_bounded03
    | exact decode certificateMasks_bounded04
    | exact decode certificateMasks_bounded05
    | exact decode certificateMasks_bounded06
    | exact decode certificateMasks_bounded07
    | exact decode certificateMasks_bounded08
    | exact decode certificateMasks_bounded09
    | exact decode certificateMasks_bounded10
    | exact decode certificateMasks_bounded11
    | exact decode certificateMasks_bounded12
    | exact decode certificateMasks_bounded13
    | exact decode certificateMasks_bounded14
    | exact decode certificateMasks_bounded15
    | exact decode certificateMasks_bounded16
    | exact decode certificateMasks_bounded17
    | exact decode certificateMasks_bounded18
    | exact decode certificateMasks_bounded19
    | exact decode certificateMasks_bounded20
    | exact decode certificateMasks_bounded21
    | exact decode certificateMasks_bounded22
    | exact decode certificateMasks_bounded23

end Erdos232
