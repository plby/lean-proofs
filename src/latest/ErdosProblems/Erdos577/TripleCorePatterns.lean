import ErdosProblems.Erdos577.TripleRemainingExcluded

/-! The twelve exact ten-contact core patterns, with the source's distinguished paw labels. -/

namespace Erdos577.TripleCorePatterns

open Finset

def diagonal : Fin 12 → Fin 4 := ![3, 1, 3, 3, 3, 3, 3, 1, 3, 1, 3, 3]

def centerRow : Fin 12 → ℕ := ![5, 5, 7, 11, 7, 11, 15, 15, 15, 15, 15, 15]

def secondRow : Fin 12 → ℕ := ![15, 15, 7, 7, 15, 15, 3, 5, 15, 15, 7, 11]

def thirdRow : Fin 12 → ℕ := ![15, 15, 15, 15, 7, 7, 15, 15, 3, 5, 7, 7]

def rows (tag : Fin 12) : Fin 4 → ℕ := ![0, centerRow tag, secondRow tag, thirdRow tag]

def mask (tag : Fin 12) : ℕ :=
  16 * centerRow tag + 256 * secondRow tag + 4096 * thirdRow tag

def graph (tag : Fin 12) : SimpleGraph (Fin 8) := PawModel.graph (diagonal tag) (mask tag)

instance (tag : Fin 12) : DecidableRel (graph tag).Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph _ _).Adj)

def core : Finset (Fin 8) := {1, 2, 3, 4, 5, 6, 7}

def block : Finset (Fin 8) := {4, 5, 6, 7}

def paw (tag : Fin 12) : Paw (graph tag) where
  vertices := ⟨![0, 1, 2, 3], by decide +kernel⟩
  pendant := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  edge13 := by fin_cases tag <;> decide +kernel
  edge23 := by fin_cases tag <;> decide +kernel

lemma paw_core (tag : Fin 12) : (paw tag).triangle ∪ block = core := by
  change ({1, 2, 3} : Finset (Fin 8)) ∪ {4, 5, 6, 7} = {1, 2, 3, 4, 5, 6, 7}
  decide +kernel

lemma mask_bit (tag : Fin 12) (i j : Fin 4) :
    (mask tag).testBit (4 * i.val + j.val) = (rows tag i).testBit j.val := by
  have hf : ∀ tag : Fin 12, ∀ i j : Fin 4,
      (mask tag).testBit (4 * i.val + j.val) = (rows tag i).testBit j.val := by
    decide +kernel
  exact hf tag i j

lemma old_score (tag : Fin 12) :
    edgeCount (graph tag) block = Unattached.oldEdges (diagonal tag) := by
  fin_cases tag <;> decide +kernel

def kind : Fin 12 → Fin 4 → Fin 3 :=
  ![![2, 0, 2, 0],
    ![2, 0, 2, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![1, 1, 1, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 1, 0, 1],
    ![0, 0, 0, 0],
    ![2, 2, 2, 2],
    ![0, 0, 0, 2],
    ![0, 0, 0, 0]]

def first : Fin 12 → Fin 4 → Fin 8 :=
  ![![4, 3, 4, 3],
    ![4, 3, 4, 3],
    ![3, 3, 3, 3],
    ![7, 7, 3, 3],
    ![3, 3, 3, 4],
    ![3, 3, 3, 4],
    ![6, 6, 3, 3],
    ![3, 3, 3, 3],
    ![6, 6, 4, 4],
    ![4, 4, 5, 4],
    ![5, 4, 4, 4],
    ![3, 3, 3, 4]]

def second : Fin 12 → Fin 4 → Fin 8 :=
  ![![6, 7, 6, 5],
    ![6, 4, 6, 4],
    ![7, 7, 7, 4],
    ![6, 6, 7, 6],
    ![5, 4, 4, 5],
    ![6, 6, 4, 6],
    ![7, 7, 7, 6],
    ![5, 7, 5, 5],
    ![7, 7, 7, 6],
    ![5, 5, 6, 7],
    ![7, 7, 7, 7],
    ![6, 6, 4, 6]]

def marked (j : Fin 4) : Fin 8 := Fin.natAdd 4 j

def center (tag : Fin 12) (j : Fin 4) : Fin 8 := if kind tag j = 0 then marked j else 1

def triple (tag : Fin 12) (j : Fin 4) : Finset (Fin 8) :=
  {center tag j, first tag j, second tag j}

def target (tag : Fin 12) (j slot : Fin 4) : Finset (Fin 8) :=
  if slot = 0 ∨ kind tag j = 2 then core \ triple tag j
  else if slot = 1 then core \ {first tag j, second tag j, if kind tag j = 0 then 1 else marked j}
  else core \ {2, center tag j, if slot = 2 then first tag j else second tag j}

end Erdos577.TripleCorePatterns
