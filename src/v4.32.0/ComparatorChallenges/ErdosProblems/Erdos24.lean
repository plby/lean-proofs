import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fintype.Perm

attribute [local instance] Classical.propDecidable

namespace Erdos24

open scoped BigOperators

def pCert (i j : Fin 8) : ℚ :=
  match i.val, j.val with
  | 0, 0 => 24 | 0, 1 => -36 | 0, 2 => -36 | 0, 3 => 24
  | 0, 4 => -36 | 0, 5 => 24 | 0, 6 => 24 | 0, 7 => -36
  | 1, 0 => -36 | 1, 1 => 277 | 1, 2 => 97 | 1, 3 => -79
  | 1, 4 => 97 | 1, 5 => -79 | 1, 6 => -259 | 1, 7 => 54
  | 2, 0 => -36 | 2, 1 => 97 | 2, 2 => 277 | 2, 3 => -79
  | 2, 4 => 97 | 2, 5 => -259 | 2, 6 => -79 | 2, 7 => 54
  | 3, 0 => 24 | 3, 1 => -79 | 3, 2 => -79 | 3, 3 => 247
  | 3, 4 => -259 | 3, 5 => 67 | 3, 6 => 67 | 3, 7 => -36
  | 4, 0 => -36 | 4, 1 => 97 | 4, 2 => 97 | 4, 3 => -259
  | 4, 4 => 277 | 4, 5 => -79 | 4, 6 => -79 | 4, 7 => 54
  | 5, 0 => 24 | 5, 1 => -79 | 5, 2 => -259 | 5, 3 => 67
  | 5, 4 => -79 | 5, 5 => 247 | 5, 6 => 67 | 5, 7 => -36
  | 6, 0 => 24 | 6, 1 => -259 | 6, 2 => -79 | 6, 3 => 67
  | 6, 4 => -79 | 6, 5 => 67 | 6, 6 => 247 | 6, 7 => -36
  | 7, 0 => -36 | 7, 1 => 54 | 7, 2 => 54 | 7, 3 => -36
  | 7, 4 => 54 | 7, 5 => -36 | 7, 6 => -36 | 7, 7 => 54
  | _, _ => 0

def qCert (i j : Fin 6) : ℚ :=
  match i.val, j.val with
  | 0, 0 => 1728 | 0, 1 => -1551 | 0, 2 => -1551 | 0, 3 => -1308
  | 0, 4 => 687 | 0, 5 => 687
  | 1, 0 => -1551 | 1, 1 => 2336 | 1, 2 => 742 | 1, 3 => 908
  | 1, 4 => 2557 | 1, 5 => -4084
  | 2, 0 => -1551 | 2, 1 => 742 | 2, 2 => 2336 | 2, 3 => 908
  | 2, 4 => -4084 | 2, 5 => 2557
  | 3, 0 => -1308 | 3, 1 => 908 | 3, 2 => 908 | 3, 3 => 1728
  | 3, 4 => -254 | 3, 5 => -254
  | 4, 0 => 687 | 4, 1 => 2557 | 4, 2 => -4084 | 4, 3 => -254
  | 4, 4 => 15264 | 4, 5 => -14424
  | 5, 0 => 687 | 5, 1 => -4084 | 5, 2 => 2557 | 5, 3 => -254
  | 5, 4 => -14424 | 5, 5 => 15264
  | _, _ => 0

def rCert (i j : Fin 5) : ℚ :=
  match i.val, j.val with
  | 0, 0 => 1512 | 0, 1 => 568 | 0, 2 => -380 | 0, 3 => 568 | 0, 4 => -376
  | 1, 0 => 568 | 1, 1 => 475 | 1, 2 => -191 | 1, 3 => 0 | 1, 4 => -93
  | 2, 0 => -380 | 2, 1 => -191 | 2, 2 => 192 | 2, 3 => -191 | 2, 4 => -2
  | 3, 0 => 568 | 3, 1 => 0 | 3, 2 => -191 | 3, 3 => 475 | 3, 4 => -93
  | 4, 0 => -376 | 4, 1 => -93 | 4, 2 => -2 | 4, 3 => -93 | 4, 4 => 190
  | _, _ => 0

def σ₀FlagIdx (adjDA adjDB adjDC : Bool) : Fin 8 :=
  ⟨(if adjDA then 1 else 0) + (if adjDB then 2 else 0) + (if adjDC then 4 else 0),
   by cases adjDA <;> cases adjDB <;> cases adjDC <;> simp⟩

def σ₁FlagIdx (adjDA adjDB adjDC : Bool) : Option (Fin 6) :=
  match adjDA, adjDB, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | false, true, true => some 5
  | _, _, _ => none

def σ₂FlagIdx (adjDA adjDCenter adjDC : Bool) : Option (Fin 5) :=
  match adjDA, adjDCenter, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | _, _, _ => none

def quintContribOf (adj : Fin 5 → Fin 5 → Bool) (a b c d e : Fin 5) : ℚ :=
  let ab := adj a b
  let ac := adj a c
  let bc := adj b c
  if !ab && !ac && !bc then
    pCert (σ₀FlagIdx (adj d a) (adj d b) (adj d c))
      (σ₀FlagIdx (adj e a) (adj e b) (adj e c)) / 625
  else if ab && !ac && !bc then
    match σ₁FlagIdx (adj d a) (adj d b) (adj d c),
        σ₁FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => qCert fi fj / 2500
    | _, _ => 0
  else if ab && bc && !ac then
    match σ₂FlagIdx (adj d a) (adj d b) (adj d c),
        σ₂FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => rCert fi fj / 625
    | _, _ => 0
  else 0

def totalFlagContribPermSum (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  ∑ p : Equiv.Perm (Fin 5), quintContribOf adj (p 0) (p 1) (p 2) (p 3) (p 4)

def totalFlagContrib (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  totalFlagContribPermSum adj

def mkAdj5 (e : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0 => e 0 | 0, 2 | 2, 0 => e 1 | 0, 3 | 3, 0 => e 2
  | 0, 4 | 4, 0 => e 3 | 1, 2 | 2, 1 => e 4 | 1, 3 | 3, 1 => e 5
  | 1, 4 | 4, 1 => e 6 | 2, 3 | 3, 2 => e 7 | 2, 4 | 4, 2 => e 8
  | 3, 4 | 4, 3 => e 9
  | _, _ => false

def edgeBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 10 → Bool := fun i =>
  match i.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4
  | 5 => b5 | 6 => b6 | 7 => b7 | 8 => b8 | 9 => b9
  | _ => false

axiom totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1 :
    decide
      (∀ b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool,
        totalFlagContrib
            (mkAdj5 (edgeBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34)) =
          totalFlagContribPermSum
            (mkAdj5 (edgeBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34))) =
      true

end Erdos24

def SimpleGraph.IsLabeledC5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5, G.Adj (f i) (f (i + 1))

noncomputable def SimpleGraph.numC5 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → V)).filter (fun f => G.IsLabeledC5 f)).card / 10

namespace Erdos24

theorem erdos_pentagon_conjecture (n : ℕ) (G : SimpleGraph (Fin (5 * n)))
    (hG : G.CliqueFree 3) :
    G.numC5 ≤ n ^ 5 := by
  sorry

end Erdos24
