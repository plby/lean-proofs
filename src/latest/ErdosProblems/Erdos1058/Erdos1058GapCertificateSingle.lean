import ErdosProblems.Erdos1058.Erdos1058Core

-- Serialize concrete search reductions to bound elaborator memory.
set_option Elab.async false

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchSingleCertificate

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

private lemma tail_1 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 1 = false := by
  decide

private lemma tail_83 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 83 = false := by
  decide

private lemma tail_125 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 125 = false := by
  decide

private lemma tail_155 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 155 = false := by
  decide

private lemma tail_181 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 181 = false := by
  decide

private lemma tail_209 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 209 = false := by
  decide

private lemma tail_239 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 239 = false := by
  decide

private lemma tail_265 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 265 = false := by
  decide

private lemma tail_281 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 281 = false := by
  decide

private lemma tail_307 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 307 = false := by
  decide

private lemma tail_337 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 337 = false := by
  decide

private lemma tail_365 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 365 = false := by
  decide

private lemma tail_391 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 391 = false := by
  decide

private lemma tail_421 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 421 = false := by
  decide

private lemma tail_463 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 463 = false := by
  decide

private lemma tail_545 : cubicCRTSearchAux 0 2
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 545 = false := by
  decide

private lemma after13_1 : cubicCRTSearchAux 0 2
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht13
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes,
      tail_1, tail_337, tail_421, tail_463]

private lemma after13_29 : cubicCRTSearchAux 0 2
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht13
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes,
      tail_155, tail_239, tail_281, tail_365]

private lemma after13_13 : cubicCRTSearchAux 0 2
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht13
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes,
      tail_181, tail_265, tail_307, tail_391]

private lemma after13_41 : cubicCRTSearchAux 0 2
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht13
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes,
      tail_83, tail_125, tail_209, tail_545]

private lemma after3_1 : cubicCRTSearchAux 0 2
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht3
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes,
      after13_1, after13_29]

private lemma after3_13 : cubicCRTSearchAux 0 2
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht3
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes,
      after13_13, after13_41]

private lemma after2_1 : cubicCRTSearchAux 0 2
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht2
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1]

private lemma after2_6 : cubicCRTSearchAux 0 2
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
      157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
      331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht2
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_13]

private lemma search_root_false :
    cubicCRTSearchAux 0 2 cubicCRTConstraintList 1 0 = false := by
  rw [show cubicCRTConstraintList =
    [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139,
      151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307,
      313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht7
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1, after2_6]

theorem check : cubicCRTSearchSingleCheck = true := by
  simp only [cubicCRTSearchSingleCheck, cubicCRTSearch, search_root_false,
    Bool.not_false]

end CubicCRTSearchSingleCertificate

theorem cubicCRTSearchSingleCheck_eq_true : cubicCRTSearchSingleCheck = true :=
  CubicCRTSearchSingleCertificate.check

end

end Erdos1058
