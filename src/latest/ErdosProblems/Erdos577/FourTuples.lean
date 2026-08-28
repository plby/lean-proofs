import ErdosProblems.Erdos577.Tuples

/-! Explicit ordered four-tuples with distinct vertices. -/

namespace Erdos577

variable {V : Type*}

def fourTuple (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ V where
  toFun := ![a, b, c, d]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] lemma fourTuple_zero (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    fourTuple a b c d hab hac had hbc hbd hcd 0 = a := rfl

@[simp] lemma fourTuple_one (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    fourTuple a b c d hab hac had hbc hbd hcd 1 = b := rfl

@[simp] lemma fourTuple_two (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    fourTuple a b c d hab hac had hbc hbd hcd 2 = c := rfl

@[simp] lemma fourTuple_three (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    fourTuple a b c d hab hac had hbc hbd hcd 3 = d := rfl

lemma fourTuple_support [DecidableEq V] (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    tupleSupport (fourTuple a b c d hab hac had hbc hbd hcd) = {a, b, c, d} := by
  ext v
  simp only [mem_tupleSupport, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

end Erdos577
