import ErdosProblems.Erdos577.UnattachedModel

/-! Positive eight-vertex models for the outside-vertex clauses of patterns (3) and (8). -/

namespace Erdos577.FirstPawOutside

def rows (patternEight : Bool) : Fin 4 → ℕ :=
  if patternEight then ![0, 15, 15, 0] else ![0, 15, 9, 3]

def fixedMask (patternEight : Bool) : ℕ := if patternEight then 4080 else 14832

def mask (patternEight : Bool) (i j : Fin 4) : ℕ :=
  fixedMask patternEight + 2 ^ i.val + 2 ^ j.val

def graph (patternEight : Bool) (i j : Fin 4) : SimpleGraph (Fin 8) :=
  Unattached.graph 1 (mask patternEight i j)

instance (patternEight : Bool) (i j : Fin 4) : DecidableRel (graph patternEight i j).Adj :=
  inferInstanceAs (DecidableRel (Unattached.graph _ _).Adj)

lemma cross_bit (patternEight : Bool) (i j r s : Fin 4) (hne : i ≠ j) :
    (mask patternEight i j).testBit (4 * r.val + s.val) = true ↔
      if r = 0 then s = i ∨ s = j else (rows patternEight r).testBit s.val = true := by
  have hf : ∀ patternEight : Bool, ∀ i j r s : Fin 4, i ≠ j →
      ((mask patternEight i j).testBit (4 * r.val + s.val) = true ↔
        if r = 0 then s = i ∨ s = j else (rows patternEight r).testBit s.val = true) := by
    decide +kernel
  exact hf patternEight i j r s hne

end Erdos577.FirstPawOutside
