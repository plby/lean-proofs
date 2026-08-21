import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058GapCertificate210Tails0
import ErdosProblems.Erdos1058.Erdos1058GapCertificate210Tails1
import ErdosProblems.Erdos1058.Erdos1058GapCertificate210Tails2
import ErdosProblems.Erdos1058.Erdos1058GapCertificate210Tails3
import ErdosProblems.Erdos1058.Erdos1058GapCertificate210Tails4
import ErdosProblems.Erdos1058.Erdos1058GapCertificate210Tails5

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap210Certificate

private lemma cubicAnyRange_eq_false_of' {start count : ℕ} {f : ℕ → Bool}
    (h : ∀ i, start ≤ i → i < start + count → f i = false) :
    cubicAnyRange start count f = false := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [cubicAnyRange.eq_2, h start (by omega) (by omega), Bool.false_or]
      apply ih
      intro i hlo hi
      exact h i (by omega) (by omega)













private lemma after13_0_1 : cubicCRTSearchAux 210 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_295, tail_0_337, tail_0_379]

private lemma after13_0_29 : cubicCRTSearchAux 210 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_113, tail_0_155, tail_0_197]

private lemma after13_0_13 : cubicCRTSearchAux 210 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_139, tail_0_181, tail_0_223]

private lemma after13_0_41 : cubicCRTSearchAux 210 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_41, tail_0_503, tail_0_545]

private lemma after3_0_1 : cubicCRTSearchAux 210 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_1, after13_0_29]

private lemma after3_0_13 : cubicCRTSearchAux 210 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_13, after13_0_41]

private lemma after2_0_1 : cubicCRTSearchAux 210 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_1]

private lemma after2_0_6 : cubicCRTSearchAux 210 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_13]

theorem search_0_false : cubicCRTSearch 210 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_1, after2_0_6]





































private lemma after13_1_1 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_43, tail_1_85, tail_1_337]

private lemma after13_1_29 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_155, tail_1_407, tail_1_449]

private lemma after13_1_23 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_233, tail_1_485, tail_1_527]

private lemma after13_1_37 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 37 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_121, tail_1_163, tail_1_415]

private lemma after13_1_17 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_17, tail_1_59, tail_1_311]

private lemma after13_1_31 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 31 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_199, tail_1_241, tail_1_493]

private lemma after13_1_11 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_95, tail_1_137, tail_1_389]

private lemma after13_1_25 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 25 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_25, tail_1_277, tail_1_319]

private lemma after13_1_5 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_173, tail_1_215, tail_1_467]

private lemma after13_1_19 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 19 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_103, tail_1_355, tail_1_397]

private lemma after13_1_13 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_181, tail_1_433, tail_1_475]

private lemma after13_1_41 : cubicCRTSearchAux 210 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_251, tail_1_293, tail_1_545]

private lemma after3_1_1 : cubicCRTSearchAux 210 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_1, after13_1_29]

private lemma after3_1_9 : cubicCRTSearchAux 210 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_23, after13_1_37]

private lemma after3_1_3 : cubicCRTSearchAux 210 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_17, after13_1_31]

private lemma after3_1_11 : cubicCRTSearchAux 210 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_11, after13_1_25]

private lemma after3_1_5 : cubicCRTSearchAux 210 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_5, after13_1_19]

private lemma after3_1_13 : cubicCRTSearchAux 210 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_13, after13_1_41]

private lemma after2_1_1 : cubicCRTSearchAux 210 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_1]

private lemma after2_1_2 : cubicCRTSearchAux 210 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_9]

private lemma after2_1_3 : cubicCRTSearchAux 210 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_3]

private lemma after2_1_4 : cubicCRTSearchAux 210 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_11]

private lemma after2_1_5 : cubicCRTSearchAux 210 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_5]

private lemma after2_1_6 : cubicCRTSearchAux 210 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_13]

theorem search_1_false : cubicCRTSearch 210 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_1, after2_1_2, after2_1_3, after2_1_4, after2_1_5, after2_1_6]

theorem check : cubicCRTSearchGapCheck 210 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap210Certificate

theorem cubicCRTSearchGapCheck_210_eq_true : cubicCRTSearchGapCheck 210 = true :=
  CubicCRTSearchGap210Certificate.check

end

end Erdos1058
