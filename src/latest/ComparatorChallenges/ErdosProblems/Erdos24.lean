import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Ring.Star
import PrivateName

namespace Erdos24

noncomputable section

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.maxHeartbeats false
set_option linter.style.show false
set_option maxHeartbeats 50000000
open Finset Function SimpleGraph Fintype Nat Matrix

attribute [local instance] Classical.propDecidable

def P_cert : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
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

def Q_cert : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
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

def R_cert : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
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
    P_cert (σ₀FlagIdx (adj d a) (adj d b) (adj d c))
           (σ₀FlagIdx (adj e a) (adj e b) (adj e c)) / 625
  else if ab && !ac && !bc then
    match σ₁FlagIdx (adj d a) (adj d b) (adj d c),
          σ₁FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => Q_cert fi fj / 2500
    | _, _ => 0
  else if ab && bc && !ac then
    match σ₂FlagIdx (adj d a) (adj d b) (adj d c),
          σ₂FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => R_cert fi fj / 625
    | _, _ => 0
  else 0
def _root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagPermTuples :
    List (List (Fin 5)) :=
  [
    [0, 1, 2, 3, 4],
    [0, 1, 2, 4, 3],
    [0, 1, 3, 2, 4],
    [0, 1, 3, 4, 2],
    [0, 1, 4, 2, 3],
    [0, 1, 4, 3, 2],
    [0, 2, 1, 3, 4],
    [0, 2, 1, 4, 3],
    [0, 2, 3, 1, 4],
    [0, 2, 3, 4, 1],
    [0, 2, 4, 1, 3],
    [0, 2, 4, 3, 1],
    [0, 3, 1, 2, 4],
    [0, 3, 1, 4, 2],
    [0, 3, 2, 1, 4],
    [0, 3, 2, 4, 1],
    [0, 3, 4, 1, 2],
    [0, 3, 4, 2, 1],
    [0, 4, 1, 2, 3],
    [0, 4, 1, 3, 2],
    [0, 4, 2, 1, 3],
    [0, 4, 2, 3, 1],
    [0, 4, 3, 1, 2],
    [0, 4, 3, 2, 1],
    [1, 0, 2, 3, 4],
    [1, 0, 2, 4, 3],
    [1, 0, 3, 2, 4],
    [1, 0, 3, 4, 2],
    [1, 0, 4, 2, 3],
    [1, 0, 4, 3, 2],
    [1, 2, 0, 3, 4],
    [1, 2, 0, 4, 3],
    [1, 2, 3, 0, 4],
    [1, 2, 3, 4, 0],
    [1, 2, 4, 0, 3],
    [1, 2, 4, 3, 0],
    [1, 3, 0, 2, 4],
    [1, 3, 0, 4, 2],
    [1, 3, 2, 0, 4],
    [1, 3, 2, 4, 0],
    [1, 3, 4, 0, 2],
    [1, 3, 4, 2, 0],
    [1, 4, 0, 2, 3],
    [1, 4, 0, 3, 2],
    [1, 4, 2, 0, 3],
    [1, 4, 2, 3, 0],
    [1, 4, 3, 0, 2],
    [1, 4, 3, 2, 0],
    [2, 0, 1, 3, 4],
    [2, 0, 1, 4, 3],
    [2, 0, 3, 1, 4],
    [2, 0, 3, 4, 1],
    [2, 0, 4, 1, 3],
    [2, 0, 4, 3, 1],
    [2, 1, 0, 3, 4],
    [2, 1, 0, 4, 3],
    [2, 1, 3, 0, 4],
    [2, 1, 3, 4, 0],
    [2, 1, 4, 0, 3],
    [2, 1, 4, 3, 0],
    [2, 3, 0, 1, 4],
    [2, 3, 0, 4, 1],
    [2, 3, 1, 0, 4],
    [2, 3, 1, 4, 0],
    [2, 3, 4, 0, 1],
    [2, 3, 4, 1, 0],
    [2, 4, 0, 1, 3],
    [2, 4, 0, 3, 1],
    [2, 4, 1, 0, 3],
    [2, 4, 1, 3, 0],
    [2, 4, 3, 0, 1],
    [2, 4, 3, 1, 0],
    [3, 0, 1, 2, 4],
    [3, 0, 1, 4, 2],
    [3, 0, 2, 1, 4],
    [3, 0, 2, 4, 1],
    [3, 0, 4, 1, 2],
    [3, 0, 4, 2, 1],
    [3, 1, 0, 2, 4],
    [3, 1, 0, 4, 2],
    [3, 1, 2, 0, 4],
    [3, 1, 2, 4, 0],
    [3, 1, 4, 0, 2],
    [3, 1, 4, 2, 0],
    [3, 2, 0, 1, 4],
    [3, 2, 0, 4, 1],
    [3, 2, 1, 0, 4],
    [3, 2, 1, 4, 0],
    [3, 2, 4, 0, 1],
    [3, 2, 4, 1, 0],
    [3, 4, 0, 1, 2],
    [3, 4, 0, 2, 1],
    [3, 4, 1, 0, 2],
    [3, 4, 1, 2, 0],
    [3, 4, 2, 0, 1],
    [3, 4, 2, 1, 0],
    [4, 0, 1, 2, 3],
    [4, 0, 1, 3, 2],
    [4, 0, 2, 1, 3],
    [4, 0, 2, 3, 1],
    [4, 0, 3, 1, 2],
    [4, 0, 3, 2, 1],
    [4, 1, 0, 2, 3],
    [4, 1, 0, 3, 2],
    [4, 1, 2, 0, 3],
    [4, 1, 2, 3, 0],
    [4, 1, 3, 0, 2],
    [4, 1, 3, 2, 0],
    [4, 2, 0, 1, 3],
    [4, 2, 0, 3, 1],
    [4, 2, 1, 0, 3],
    [4, 2, 1, 3, 0],
    [4, 2, 3, 0, 1],
    [4, 2, 3, 1, 0],
    [4, 3, 0, 1, 2],
    [4, 3, 0, 2, 1],
    [4, 3, 1, 0, 2],
    [4, 3, 1, 2, 0],
    [4, 3, 2, 0, 1],
    [4, 3, 2, 1, 0]
  ]
def _root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagTupleContrib
    (adj : Fin 5 → Fin 5 → Bool) : List (Fin 5) → ℚ
  | [a, b, c, d, e] => quintContribOf adj a b c d e
  | _ => 0
def _root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
    (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  (_root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagPermTuples.map
    (_root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagTupleContrib adj)).sum

comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagPermTuples
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagPermTuples"
comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagTupleContrib._sparseCasesOn_1
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagTupleContrib._sparseCasesOn_1"
comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagTupleContrib._sparseCasesOn_2
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagTupleContrib._sparseCasesOn_2"
comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagTupleContrib.match_1
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagTupleContrib.match_1"
comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagTupleContrib
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagTupleContrib"
comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagContribPermSum"

def totalFlagContribBits (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) : ℚ :=
  match b01, b02, b03, b04, b12, b13, b14, b23, b24, b34 with
  | false, false, false, false, false, false, false, false, false, false => 576 / 125
  | false, false, false, false, false, false, false, false, false, true => 576 / 125
  | false, false, false, false, false, false, false, false, true, false => 576 / 125
  | false, false, false, false, false, false, false, false, true, true => 576 / 125
  | false, false, false, false, false, false, false, true, false, false => 576 / 125
  | false, false, false, false, false, false, false, true, false, true => 576 / 125
  | false, false, false, false, false, false, false, true, true, false => 576 / 125
  | false, false, false, false, false, false, false, true, true, true => 9972 / 625
  | false, false, false, false, false, false, true, false, false, false => 576 / 125
  | false, false, false, false, false, false, true, false, false, true => 576 / 125
  | false, false, false, false, false, false, true, false, true, false => 576 / 125
  | false, false, false, false, false, false, true, false, true, true => 576 / 125
  | false, false, false, false, false, false, true, true, false, false => 576 / 125
  | false, false, false, false, false, false, true, true, false, true => 2826 / 625
  | false, false, false, false, false, false, true, true, true, false => 2826 / 625
  | false, false, false, false, false, false, true, true, true, true => 88 / 125
  | false, false, false, false, false, true, false, false, false, false => 576 / 125
  | false, false, false, false, false, true, false, false, false, true => 576 / 125
  | false, false, false, false, false, true, false, false, true, false => 576 / 125
  | false, false, false, false, false, true, false, false, true, true => 2826 / 625
  | false, false, false, false, false, true, false, true, false, false => 576 / 125
  | false, false, false, false, false, true, false, true, false, true => 576 / 125
  | false, false, false, false, false, true, false, true, true, false => 2826 / 625
  | false, false, false, false, false, true, false, true, true, true => 88 / 125
  | false, false, false, false, false, true, true, false, false, false => 576 / 125
  | false, false, false, false, false, true, true, false, false, true => 9972 / 625
  | false, false, false, false, false, true, true, false, true, false => 2826 / 625
  | false, false, false, false, false, true, true, false, true, true => 88 / 125
  | false, false, false, false, false, true, true, true, false, false => 2826 / 625
  | false, false, false, false, false, true, true, true, false, true => 88 / 125
  | false, false, false, false, false, true, true, true, true, false => 576 / 125
  | false, false, false, false, false, true, true, true, true, true => 2964 / 625
  | false, false, false, false, true, false, false, false, false, false => 576 / 125
  | false, false, false, false, true, false, false, false, false, true => 576 / 125
  | false, false, false, false, true, false, false, false, true, false => 576 / 125
  | false, false, false, false, true, false, false, false, true, true => 2826 / 625
  | false, false, false, false, true, false, false, true, false, false => 576 / 125
  | false, false, false, false, true, false, false, true, false, true => 2826 / 625
  | false, false, false, false, true, false, false, true, true, false => 576 / 125
  | false, false, false, false, true, false, false, true, true, true => 88 / 125
  | false, false, false, false, true, false, true, false, false, false => 576 / 125
  | false, false, false, false, true, false, true, false, false, true => 2826 / 625
  | false, false, false, false, true, false, true, false, true, false => 9972 / 625
  | false, false, false, false, true, false, true, false, true, true => 88 / 125
  | false, false, false, false, true, false, true, true, false, false => 2826 / 625
  | false, false, false, false, true, false, true, true, false, true => 576 / 125
  | false, false, false, false, true, false, true, true, true, false => 88 / 125
  | false, false, false, false, true, false, true, true, true, true => 2964 / 625
  | false, false, false, false, true, true, false, false, false, false => 576 / 125
  | false, false, false, false, true, true, false, false, false, true => 2826 / 625
  | false, false, false, false, true, true, false, false, true, false => 2826 / 625
  | false, false, false, false, true, true, false, false, true, true => 576 / 125
  | false, false, false, false, true, true, false, true, false, false => 9972 / 625
  | false, false, false, false, true, true, false, true, false, true => 88 / 125
  | false, false, false, false, true, true, false, true, true, false => 88 / 125
  | false, false, false, false, true, true, false, true, true, true => 2964 / 625
  | false, false, false, false, true, true, true, false, false, false => 576 / 125
  | false, false, false, false, true, true, true, false, false, true => 88 / 125
  | false, false, false, false, true, true, true, false, true, false => 88 / 125
  | false, false, false, false, true, true, true, false, true, true => 2964 / 625
  | false, false, false, false, true, true, true, true, false, false => 88 / 125
  | false, false, false, false, true, true, true, true, false, true => 2964 / 625
  | false, false, false, false, true, true, true, true, true, false => 2964 / 625
  | false, false, false, false, true, true, true, true, true, true => 0
  | false, false, false, true, false, false, false, false, false, false => 576 / 125
  | false, false, false, true, false, false, false, false, false, true => 576 / 125
  | false, false, false, true, false, false, false, false, true, false => 576 / 125
  | false, false, false, true, false, false, false, false, true, true => 576 / 125
  | false, false, false, true, false, false, false, true, false, false => 576 / 125
  | false, false, false, true, false, false, false, true, false, true => 2826 / 625
  | false, false, false, true, false, false, false, true, true, false => 2826 / 625
  | false, false, false, true, false, false, false, true, true, true => 88 / 125
  | false, false, false, true, false, false, true, false, false, false => 576 / 125
  | false, false, false, true, false, false, true, false, false, true => 576 / 125
  | false, false, false, true, false, false, true, false, true, false => 576 / 125
  | false, false, false, true, false, false, true, false, true, true => 576 / 125
  | false, false, false, true, false, false, true, true, false, false => 2576 / 625
  | false, false, false, true, false, false, true, true, false, true => 576 / 125
  | false, false, false, true, false, false, true, true, true, false => 576 / 125
  | false, false, false, true, false, false, true, true, true, true => 2064 / 625
  | false, false, false, true, false, true, false, false, false, false => 576 / 125
  | false, false, false, true, false, true, false, false, false, true => 2826 / 625
  | false, false, false, true, false, true, false, false, true, false => 2576 / 625
  | false, false, false, true, false, true, false, false, true, true => 576 / 125
  | false, false, false, true, false, true, false, true, false, false => 2576 / 625
  | false, false, false, true, false, true, false, true, false, true => 576 / 125
  | false, false, false, true, false, true, false, true, true, false => -1512 / 625
  | false, false, false, true, false, true, false, true, true, true => 5918 / 625
  | false, false, false, true, false, true, true, false, false, false => 2826 / 625
  | false, false, false, true, false, true, true, false, false, true => 88 / 125
  | false, false, false, true, false, true, true, false, true, false => 576 / 125
  | false, false, false, true, false, true, true, false, true, true => 2064 / 625
  | false, false, false, true, false, true, true, true, false, false => -1512 / 625
  | false, false, false, true, false, true, true, true, false, true => 5918 / 625
  | false, false, false, true, false, true, true, true, true, false => 576 / 125
  | false, false, false, true, false, true, true, true, true, true => -432 / 625
  | false, false, false, true, true, false, false, false, false, false => 576 / 125
  | false, false, false, true, true, false, false, false, false, true => 2576 / 625
  | false, false, false, true, true, false, false, false, true, false => 2826 / 625
  | false, false, false, true, true, false, false, false, true, true => 576 / 125
  | false, false, false, true, true, false, false, true, false, false => 2576 / 625
  | false, false, false, true, true, false, false, true, false, true => -1512 / 625
  | false, false, false, true, true, false, false, true, true, false => 576 / 125
  | false, false, false, true, true, false, false, true, true, true => 5918 / 625
  | false, false, false, true, true, false, true, false, false, false => 2826 / 625
  | false, false, false, true, true, false, true, false, false, true => 576 / 125
  | false, false, false, true, true, false, true, false, true, false => 88 / 125
  | false, false, false, true, true, false, true, false, true, true => 2064 / 625
  | false, false, false, true, true, false, true, true, false, false => -1512 / 625
  | false, false, false, true, true, false, true, true, false, true => 576 / 125
  | false, false, false, true, true, false, true, true, true, false => 5918 / 625
  | false, false, false, true, true, false, true, true, true, true => -432 / 625
  | false, false, false, true, true, true, false, false, false, false => 2576 / 625
  | false, false, false, true, true, true, false, false, false, true => -1512 / 625
  | false, false, false, true, true, true, false, false, true, false => -1512 / 625
  | false, false, false, true, true, true, false, false, true, true => 576 / 125
  | false, false, false, true, true, true, false, true, false, false => 5184 / 625
  | false, false, false, true, true, true, false, true, false, true => 1392 / 625
  | false, false, false, true, true, true, false, true, true, false => 1392 / 625
  | false, false, false, true, true, true, false, true, true, true => 15264 / 625
  | false, false, false, true, true, true, true, false, false, false => 576 / 125
  | false, false, false, true, true, true, true, false, false, true => 5918 / 625
  | false, false, false, true, true, true, true, false, true, false => 5918 / 625
  | false, false, false, true, true, true, true, false, true, true => -432 / 625
  | false, false, false, true, true, true, true, true, false, false => 1392 / 625
  | false, false, false, true, true, true, true, true, false, true => 15264 / 625
  | false, false, false, true, true, true, true, true, true, false => 15264 / 625
  | false, false, false, true, true, true, true, true, true, true => 0
  | false, false, true, false, false, false, false, false, false, false => 576 / 125
  | false, false, true, false, false, false, false, false, false, true => 576 / 125
  | false, false, true, false, false, false, false, false, true, false => 576 / 125
  | false, false, true, false, false, false, false, false, true, true => 2826 / 625
  | false, false, true, false, false, false, false, true, false, false => 576 / 125
  | false, false, true, false, false, false, false, true, false, true => 576 / 125
  | false, false, true, false, false, false, false, true, true, false => 2826 / 625
  | false, false, true, false, false, false, false, true, true, true => 88 / 125
  | false, false, true, false, false, false, true, false, false, false => 576 / 125
  | false, false, true, false, false, false, true, false, false, true => 2826 / 625
  | false, false, true, false, false, false, true, false, true, false => 2576 / 625
  | false, false, true, false, false, false, true, false, true, true => 576 / 125
  | false, false, true, false, false, false, true, true, false, false => 2576 / 625
  | false, false, true, false, false, false, true, true, false, true => 576 / 125
  | false, false, true, false, false, false, true, true, true, false => -1512 / 625
  | false, false, true, false, false, false, true, true, true, true => 5918 / 625
  | false, false, true, false, false, true, false, false, false, false => 576 / 125
  | false, false, true, false, false, true, false, false, false, true => 576 / 125
  | false, false, true, false, false, true, false, false, true, false => 2576 / 625
  | false, false, true, false, false, true, false, false, true, true => 576 / 125
  | false, false, true, false, false, true, false, true, false, false => 576 / 125
  | false, false, true, false, false, true, false, true, false, true => 576 / 125
  | false, false, true, false, false, true, false, true, true, false => 576 / 125
  | false, false, true, false, false, true, false, true, true, true => 2064 / 625
  | false, false, true, false, false, true, true, false, false, false => 2826 / 625
  | false, false, true, false, false, true, true, false, false, true => 88 / 125
  | false, false, true, false, false, true, true, false, true, false => -1512 / 625
  | false, false, true, false, false, true, true, false, true, true => 5918 / 625
  | false, false, true, false, false, true, true, true, false, false => 576 / 125
  | false, false, true, false, false, true, true, true, false, true => 2064 / 625
  | false, false, true, false, false, true, true, true, true, false => 576 / 125
  | false, false, true, false, false, true, true, true, true, true => -432 / 625
  | false, false, true, false, true, false, false, false, false, false => 576 / 125
  | false, false, true, false, true, false, false, false, false, true => 2576 / 625
  | false, false, true, false, true, false, false, false, true, false => 2576 / 625
  | false, false, true, false, true, false, false, false, true, true => -1512 / 625
  | false, false, true, false, true, false, false, true, false, false => 2826 / 625
  | false, false, true, false, true, false, false, true, false, true => 576 / 125
  | false, false, true, false, true, false, false, true, true, false => 576 / 125
  | false, false, true, false, true, false, false, true, true, true => 5918 / 625
  | false, false, true, false, true, false, true, false, false, false => 2576 / 625
  | false, false, true, false, true, false, true, false, false, true => -1512 / 625
  | false, false, true, false, true, false, true, false, true, false => 5184 / 625
  | false, false, true, false, true, false, true, false, true, true => 1392 / 625
  | false, false, true, false, true, false, true, true, false, false => -1512 / 625
  | false, false, true, false, true, false, true, true, false, true => 576 / 125
  | false, false, true, false, true, false, true, true, true, false => 1392 / 625
  | false, false, true, false, true, false, true, true, true, true => 15264 / 625
  | false, false, true, false, true, true, false, false, false, false => 2826 / 625
  | false, false, true, false, true, true, false, false, false, true => 576 / 125
  | false, false, true, false, true, true, false, false, true, false => -1512 / 625
  | false, false, true, false, true, true, false, false, true, true => 576 / 125
  | false, false, true, false, true, true, false, true, false, false => 88 / 125
  | false, false, true, false, true, true, false, true, false, true => 2064 / 625
  | false, false, true, false, true, true, false, true, true, false => 5918 / 625
  | false, false, true, false, true, true, false, true, true, true => -432 / 625
  | false, false, true, false, true, true, true, false, false, false => 576 / 125
  | false, false, true, false, true, true, true, false, false, true => 5918 / 625
  | false, false, true, false, true, true, true, false, true, false => 1392 / 625
  | false, false, true, false, true, true, true, false, true, true => 15264 / 625
  | false, false, true, false, true, true, true, true, false, false => 5918 / 625
  | false, false, true, false, true, true, true, true, false, true => -432 / 625
  | false, false, true, false, true, true, true, true, true, false => 15264 / 625
  | false, false, true, false, true, true, true, true, true, true => 0
  | false, false, true, true, false, false, false, false, false, false => 576 / 125
  | false, false, true, true, false, false, false, false, false, true => 9972 / 625
  | false, false, true, true, false, false, false, false, true, false => 2826 / 625
  | false, false, true, true, false, false, false, false, true, true => 88 / 125
  | false, false, true, true, false, false, false, true, false, false => 2826 / 625
  | false, false, true, true, false, false, false, true, false, true => 88 / 125
  | false, false, true, true, false, false, false, true, true, false => 576 / 125
  | false, false, true, true, false, false, false, true, true, true => 2964 / 625
  | false, false, true, true, false, false, true, false, false, false => 2826 / 625
  | false, false, true, true, false, false, true, false, false, true => 88 / 125
  | false, false, true, true, false, false, true, false, true, false => 576 / 125
  | false, false, true, true, false, false, true, false, true, true => 2064 / 625
  | false, false, true, true, false, false, true, true, false, false => -1512 / 625
  | false, false, true, true, false, false, true, true, false, true => 5918 / 625
  | false, false, true, true, false, false, true, true, true, false => 576 / 125
  | false, false, true, true, false, false, true, true, true, true => -432 / 625
  | false, false, true, true, false, true, false, false, false, false => 2826 / 625
  | false, false, true, true, false, true, false, false, false, true => 88 / 125
  | false, false, true, true, false, true, false, false, true, false => -1512 / 625
  | false, false, true, true, false, true, false, false, true, true => 5918 / 625
  | false, false, true, true, false, true, false, true, false, false => 576 / 125
  | false, false, true, true, false, true, false, true, false, true => 2064 / 625
  | false, false, true, true, false, true, false, true, true, false => 576 / 125
  | false, false, true, true, false, true, false, true, true, true => -432 / 625
  | false, false, true, true, false, true, true, false, false, false => 576 / 125
  | false, false, true, true, false, true, true, false, false, true => 2964 / 625
  | false, false, true, true, false, true, true, false, true, false => 576 / 125
  | false, false, true, true, false, true, true, false, true, true => -432 / 625
  | false, false, true, true, false, true, true, true, false, false => 576 / 125
  | false, false, true, true, false, true, true, true, false, true => -432 / 625
  | false, false, true, true, false, true, true, true, true, false => 576 / 125
  | false, false, true, true, false, true, true, true, true, true => 648 / 625
  | false, false, true, true, true, false, false, false, false, false => 2576 / 625
  | false, false, true, true, true, false, false, false, false, true => 5184 / 625
  | false, false, true, true, true, false, false, false, true, false => -1512 / 625
  | false, false, true, true, true, false, false, false, true, true => 1392 / 625
  | false, false, true, true, true, false, false, true, false, false => -1512 / 625
  | false, false, true, true, true, false, false, true, false, true => 1392 / 625
  | false, false, true, true, true, false, false, true, true, false => 576 / 125
  | false, false, true, true, true, false, false, true, true, true => 15264 / 625
  | false, false, true, true, true, false, true, false, false, false => -1512 / 625
  | false, false, true, true, true, false, true, false, false, true => 1392 / 625
  | false, false, true, true, true, false, true, false, true, false => 1392 / 625
  | false, false, true, true, true, false, true, false, true, true => 0
  | false, false, true, true, true, false, true, true, false, false => -14424 / 125
  | false, false, true, true, true, false, true, true, false, true => -15168 / 625
  | false, false, true, true, true, false, true, true, true, false => -15168 / 625
  | false, false, true, true, true, false, true, true, true, true => 0
  | false, false, true, true, true, true, false, false, false, false => -1512 / 625
  | false, false, true, true, true, true, false, false, false, true => 1392 / 625
  | false, false, true, true, true, true, false, false, true, false => -14424 / 125
  | false, false, true, true, true, true, false, false, true, true => -15168 / 625
  | false, false, true, true, true, true, false, true, false, false => 1392 / 625
  | false, false, true, true, true, true, false, true, false, true => 0
  | false, false, true, true, true, true, false, true, true, false => -15168 / 625
  | false, false, true, true, true, true, false, true, true, true => 0
  | false, false, true, true, true, true, true, false, false, false => 576 / 125
  | false, false, true, true, true, true, true, false, false, true => 15264 / 625
  | false, false, true, true, true, true, true, false, true, false => -15168 / 625
  | false, false, true, true, true, true, true, false, true, true => 0
  | false, false, true, true, true, true, true, true, false, false => -15168 / 625
  | false, false, true, true, true, true, true, true, false, true => 0
  | false, false, true, true, true, true, true, true, true, false => 152 / 125
  | false, false, true, true, true, true, true, true, true, true => 0
  | false, true, false, false, false, false, false, false, false, false => 576 / 125
  | false, true, false, false, false, false, false, false, false, true => 576 / 125
  | false, true, false, false, false, false, false, false, true, false => 576 / 125
  | false, true, false, false, false, false, false, false, true, true => 2826 / 625
  | false, true, false, false, false, false, false, true, false, false => 576 / 125
  | false, true, false, false, false, false, false, true, false, true => 2826 / 625
  | false, true, false, false, false, false, false, true, true, false => 576 / 125
  | false, true, false, false, false, false, false, true, true, true => 88 / 125
  | false, true, false, false, false, false, true, false, false, false => 576 / 125
  | false, true, false, false, false, false, true, false, false, true => 2576 / 625
  | false, true, false, false, false, false, true, false, true, false => 2826 / 625
  | false, true, false, false, false, false, true, false, true, true => 576 / 125
  | false, true, false, false, false, false, true, true, false, false => 2576 / 625
  | false, true, false, false, false, false, true, true, false, true => -1512 / 625
  | false, true, false, false, false, false, true, true, true, false => 576 / 125
  | false, true, false, false, false, false, true, true, true, true => 5918 / 625
  | false, true, false, false, false, true, false, false, false, false => 576 / 125
  | false, true, false, false, false, true, false, false, false, true => 2576 / 625
  | false, true, false, false, false, true, false, false, true, false => 2576 / 625
  | false, true, false, false, false, true, false, false, true, true => -1512 / 625
  | false, true, false, false, false, true, false, true, false, false => 2826 / 625
  | false, true, false, false, false, true, false, true, false, true => 576 / 125
  | false, true, false, false, false, true, false, true, true, false => 576 / 125
  | false, true, false, false, false, true, false, true, true, true => 5918 / 625
  | false, true, false, false, false, true, true, false, false, false => 2576 / 625
  | false, true, false, false, false, true, true, false, false, true => 5184 / 625
  | false, true, false, false, false, true, true, false, true, false => -1512 / 625
  | false, true, false, false, false, true, true, false, true, true => 1392 / 625
  | false, true, false, false, false, true, true, true, false, false => -1512 / 625
  | false, true, false, false, false, true, true, true, false, true => 1392 / 625
  | false, true, false, false, false, true, true, true, true, false => 576 / 125
  | false, true, false, false, false, true, true, true, true, true => 15264 / 625
  | false, true, false, false, true, false, false, false, false, false => 576 / 125
  | false, true, false, false, true, false, false, false, false, true => 2576 / 625
  | false, true, false, false, true, false, false, false, true, false => 576 / 125
  | false, true, false, false, true, false, false, false, true, true => 576 / 125
  | false, true, false, false, true, false, false, true, false, false => 576 / 125
  | false, true, false, false, true, false, false, true, false, true => 576 / 125
  | false, true, false, false, true, false, false, true, true, false => 576 / 125
  | false, true, false, false, true, false, false, true, true, true => 2064 / 625
  | false, true, false, false, true, false, true, false, false, false => 2826 / 625
  | false, true, false, false, true, false, true, false, false, true => -1512 / 625
  | false, true, false, false, true, false, true, false, true, false => 88 / 125
  | false, true, false, false, true, false, true, false, true, true => 5918 / 625
  | false, true, false, false, true, false, true, true, false, false => 576 / 125
  | false, true, false, false, true, false, true, true, false, true => 576 / 125
  | false, true, false, false, true, false, true, true, true, false => 2064 / 625
  | false, true, false, false, true, false, true, true, true, true => -432 / 625
  | false, true, false, false, true, true, false, false, false, false => 2826 / 625
  | false, true, false, false, true, true, false, false, false, true => -1512 / 625
  | false, true, false, false, true, true, false, false, true, false => 576 / 125
  | false, true, false, false, true, true, false, false, true, true => 576 / 125
  | false, true, false, false, true, true, false, true, false, false => 88 / 125
  | false, true, false, false, true, true, false, true, false, true => 5918 / 625
  | false, true, false, false, true, true, false, true, true, false => 2064 / 625
  | false, true, false, false, true, true, false, true, true, true => -432 / 625
  | false, true, false, false, true, true, true, false, false, false => 576 / 125
  | false, true, false, false, true, true, true, false, false, true => 1392 / 625
  | false, true, false, false, true, true, true, false, true, false => 5918 / 625
  | false, true, false, false, true, true, true, false, true, true => 15264 / 625
  | false, true, false, false, true, true, true, true, false, false => 5918 / 625
  | false, true, false, false, true, true, true, true, false, true => 15264 / 625
  | false, true, false, false, true, true, true, true, true, false => -432 / 625
  | false, true, false, false, true, true, true, true, true, true => 0
  | false, true, false, true, false, false, false, false, false, false => 576 / 125
  | false, true, false, true, false, false, false, false, false, true => 2826 / 625
  | false, true, false, true, false, false, false, false, true, false => 9972 / 625
  | false, true, false, true, false, false, false, false, true, true => 88 / 125
  | false, true, false, true, false, false, false, true, false, false => 2826 / 625
  | false, true, false, true, false, false, false, true, false, true => 576 / 125
  | false, true, false, true, false, false, false, true, true, false => 88 / 125
  | false, true, false, true, false, false, false, true, true, true => 2964 / 625
  | false, true, false, true, false, false, true, false, false, false => 2826 / 625
  | false, true, false, true, false, false, true, false, false, true => 576 / 125
  | false, true, false, true, false, false, true, false, true, false => 88 / 125
  | false, true, false, true, false, false, true, false, true, true => 2064 / 625
  | false, true, false, true, false, false, true, true, false, false => -1512 / 625
  | false, true, false, true, false, false, true, true, false, true => 576 / 125
  | false, true, false, true, false, false, true, true, true, false => 5918 / 625
  | false, true, false, true, false, false, true, true, true, true => -432 / 625
  | false, true, false, true, false, true, false, false, false, false => 2576 / 625
  | false, true, false, true, false, true, false, false, false, true => -1512 / 625
  | false, true, false, true, false, true, false, false, true, false => 5184 / 625
  | false, true, false, true, false, true, false, false, true, true => 1392 / 625
  | false, true, false, true, false, true, false, true, false, false => -1512 / 625
  | false, true, false, true, false, true, false, true, false, true => 576 / 125
  | false, true, false, true, false, true, false, true, true, false => 1392 / 625
  | false, true, false, true, false, true, false, true, true, true => 15264 / 625
  | false, true, false, true, false, true, true, false, false, false => -1512 / 625
  | false, true, false, true, false, true, true, false, false, true => 1392 / 625
  | false, true, false, true, false, true, true, false, true, false => 1392 / 625
  | false, true, false, true, false, true, true, false, true, true => 0
  | false, true, false, true, false, true, true, true, false, false => -14424 / 125
  | false, true, false, true, false, true, true, true, false, true => -15168 / 625
  | false, true, false, true, false, true, true, true, true, false => -15168 / 625
  | false, true, false, true, false, true, true, true, true, true => 0
  | false, true, false, true, true, false, false, false, false, false => 2826 / 625
  | false, true, false, true, true, false, false, false, false, true => -1512 / 625
  | false, true, false, true, true, false, false, false, true, false => 88 / 125
  | false, true, false, true, true, false, false, false, true, true => 5918 / 625
  | false, true, false, true, true, false, false, true, false, false => 576 / 125
  | false, true, false, true, true, false, false, true, false, true => 576 / 125
  | false, true, false, true, true, false, false, true, true, false => 2064 / 625
  | false, true, false, true, true, false, false, true, true, true => -432 / 625
  | false, true, false, true, true, false, true, false, false, false => 576 / 125
  | false, true, false, true, true, false, true, false, false, true => 576 / 125
  | false, true, false, true, true, false, true, false, true, false => 2964 / 625
  | false, true, false, true, true, false, true, false, true, true => -432 / 625
  | false, true, false, true, true, false, true, true, false, false => 576 / 125
  | false, true, false, true, true, false, true, true, false, true => 576 / 125
  | false, true, false, true, true, false, true, true, true, false => -432 / 625
  | false, true, false, true, true, false, true, true, true, true => 648 / 625
  | false, true, false, true, true, true, false, false, false, false => -1512 / 625
  | false, true, false, true, true, true, false, false, false, true => -14424 / 125
  | false, true, false, true, true, true, false, false, true, false => 1392 / 625
  | false, true, false, true, true, true, false, false, true, true => -15168 / 625
  | false, true, false, true, true, true, false, true, false, false => 1392 / 625
  | false, true, false, true, true, true, false, true, false, true => -15168 / 625
  | false, true, false, true, true, true, false, true, true, false => 0
  | false, true, false, true, true, true, false, true, true, true => 0
  | false, true, false, true, true, true, true, false, false, false => 576 / 125
  | false, true, false, true, true, true, true, false, false, true => -15168 / 625
  | false, true, false, true, true, true, true, false, true, false => 15264 / 625
  | false, true, false, true, true, true, true, false, true, true => 0
  | false, true, false, true, true, true, true, true, false, false => -15168 / 625
  | false, true, false, true, true, true, true, true, false, true => 152 / 125
  | false, true, false, true, true, true, true, true, true, false => 0
  | false, true, false, true, true, true, true, true, true, true => 0
  | false, true, true, false, false, false, false, false, false, false => 576 / 125
  | false, true, true, false, false, false, false, false, false, true => 2826 / 625
  | false, true, true, false, false, false, false, false, true, false => 2826 / 625
  | false, true, true, false, false, false, false, false, true, true => 576 / 125
  | false, true, true, false, false, false, false, true, false, false => 9972 / 625
  | false, true, true, false, false, false, false, true, false, true => 88 / 125
  | false, true, true, false, false, false, false, true, true, false => 88 / 125
  | false, true, true, false, false, false, false, true, true, true => 2964 / 625
  | false, true, true, false, false, false, true, false, false, false => 2576 / 625
  | false, true, true, false, false, false, true, false, false, true => -1512 / 625
  | false, true, true, false, false, false, true, false, true, false => -1512 / 625
  | false, true, true, false, false, false, true, false, true, true => 576 / 125
  | false, true, true, false, false, false, true, true, false, false => 5184 / 625
  | false, true, true, false, false, false, true, true, false, true => 1392 / 625
  | false, true, true, false, false, false, true, true, true, false => 1392 / 625
  | false, true, true, false, false, false, true, true, true, true => 15264 / 625
  | false, true, true, false, false, true, false, false, false, false => 2826 / 625
  | false, true, true, false, false, true, false, false, false, true => 576 / 125
  | false, true, true, false, false, true, false, false, true, false => -1512 / 625
  | false, true, true, false, false, true, false, false, true, true => 576 / 125
  | false, true, true, false, false, true, false, true, false, false => 88 / 125
  | false, true, true, false, false, true, false, true, false, true => 2064 / 625
  | false, true, true, false, false, true, false, true, true, false => 5918 / 625
  | false, true, true, false, false, true, false, true, true, true => -432 / 625
  | false, true, true, false, false, true, true, false, false, false => -1512 / 625
  | false, true, true, false, false, true, true, false, false, true => 1392 / 625
  | false, true, true, false, false, true, true, false, true, false => -14424 / 125
  | false, true, true, false, false, true, true, false, true, true => -15168 / 625
  | false, true, true, false, false, true, true, true, false, false => 1392 / 625
  | false, true, true, false, false, true, true, true, false, true => 0
  | false, true, true, false, false, true, true, true, true, false => -15168 / 625
  | false, true, true, false, false, true, true, true, true, true => 0
  | false, true, true, false, true, false, false, false, false, false => 2826 / 625
  | false, true, true, false, true, false, false, false, false, true => -1512 / 625
  | false, true, true, false, true, false, false, false, true, false => 576 / 125
  | false, true, true, false, true, false, false, false, true, true => 576 / 125
  | false, true, true, false, true, false, false, true, false, false => 88 / 125
  | false, true, true, false, true, false, false, true, false, true => 5918 / 625
  | false, true, true, false, true, false, false, true, true, false => 2064 / 625
  | false, true, true, false, true, false, false, true, true, true => -432 / 625
  | false, true, true, false, true, false, true, false, false, false => -1512 / 625
  | false, true, true, false, true, false, true, false, false, true => -14424 / 125
  | false, true, true, false, true, false, true, false, true, false => 1392 / 625
  | false, true, true, false, true, false, true, false, true, true => -15168 / 625
  | false, true, true, false, true, false, true, true, false, false => 1392 / 625
  | false, true, true, false, true, false, true, true, false, true => -15168 / 625
  | false, true, true, false, true, false, true, true, true, false => 0
  | false, true, true, false, true, false, true, true, true, true => 0
  | false, true, true, false, true, true, false, false, false, false => 576 / 125
  | false, true, true, false, true, true, false, false, false, true => 576 / 125
  | false, true, true, false, true, true, false, false, true, false => 576 / 125
  | false, true, true, false, true, true, false, false, true, true => 576 / 125
  | false, true, true, false, true, true, false, true, false, false => 2964 / 625
  | false, true, true, false, true, true, false, true, false, true => -432 / 625
  | false, true, true, false, true, true, false, true, true, false => -432 / 625
  | false, true, true, false, true, true, false, true, true, true => 648 / 625
  | false, true, true, false, true, true, true, false, false, false => 576 / 125
  | false, true, true, false, true, true, true, false, false, true => -15168 / 625
  | false, true, true, false, true, true, true, false, true, false => -15168 / 625
  | false, true, true, false, true, true, true, false, true, true => 152 / 125
  | false, true, true, false, true, true, true, true, false, false => 15264 / 625
  | false, true, true, false, true, true, true, true, false, true => 0
  | false, true, true, false, true, true, true, true, true, false => 0
  | false, true, true, false, true, true, true, true, true, true => 0
  | false, true, true, true, false, false, false, false, false, false => 576 / 125
  | false, true, true, true, false, false, false, false, false, true => 88 / 125
  | false, true, true, true, false, false, false, false, true, false => 88 / 125
  | false, true, true, true, false, false, false, false, true, true => 2964 / 625
  | false, true, true, true, false, false, false, true, false, false => 88 / 125
  | false, true, true, true, false, false, false, true, false, true => 2964 / 625
  | false, true, true, true, false, false, false, true, true, false => 2964 / 625
  | false, true, true, true, false, false, false, true, true, true => 0
  | false, true, true, true, false, false, true, false, false, false => 576 / 125
  | false, true, true, true, false, false, true, false, false, true => 5918 / 625
  | false, true, true, true, false, false, true, false, true, false => 5918 / 625
  | false, true, true, true, false, false, true, false, true, true => -432 / 625
  | false, true, true, true, false, false, true, true, false, false => 1392 / 625
  | false, true, true, true, false, false, true, true, false, true => 15264 / 625
  | false, true, true, true, false, false, true, true, true, false => 15264 / 625
  | false, true, true, true, false, false, true, true, true, true => 0
  | false, true, true, true, false, true, false, false, false, false => 576 / 125
  | false, true, true, true, false, true, false, false, false, true => 5918 / 625
  | false, true, true, true, false, true, false, false, true, false => 1392 / 625
  | false, true, true, true, false, true, false, false, true, true => 15264 / 625
  | false, true, true, true, false, true, false, true, false, false => 5918 / 625
  | false, true, true, true, false, true, false, true, false, true => -432 / 625
  | false, true, true, true, false, true, false, true, true, false => 15264 / 625
  | false, true, true, true, false, true, false, true, true, true => 0
  | false, true, true, true, false, true, true, false, false, false => 576 / 125
  | false, true, true, true, false, true, true, false, false, true => 15264 / 625
  | false, true, true, true, false, true, true, false, true, false => -15168 / 625
  | false, true, true, true, false, true, true, false, true, true => 0
  | false, true, true, true, false, true, true, true, false, false => -15168 / 625
  | false, true, true, true, false, true, true, true, false, true => 0
  | false, true, true, true, false, true, true, true, true, false => 152 / 125
  | false, true, true, true, false, true, true, true, true, true => 0
  | false, true, true, true, true, false, false, false, false, false => 576 / 125
  | false, true, true, true, true, false, false, false, false, true => 1392 / 625
  | false, true, true, true, true, false, false, false, true, false => 5918 / 625
  | false, true, true, true, true, false, false, false, true, true => 15264 / 625
  | false, true, true, true, true, false, false, true, false, false => 5918 / 625
  | false, true, true, true, true, false, false, true, false, true => 15264 / 625
  | false, true, true, true, true, false, false, true, true, false => -432 / 625
  | false, true, true, true, true, false, false, true, true, true => 0
  | false, true, true, true, true, false, true, false, false, false => 576 / 125
  | false, true, true, true, true, false, true, false, false, true => -15168 / 625
  | false, true, true, true, true, false, true, false, true, false => 15264 / 625
  | false, true, true, true, true, false, true, false, true, true => 0
  | false, true, true, true, true, false, true, true, false, false => -15168 / 625
  | false, true, true, true, true, false, true, true, false, true => 152 / 125
  | false, true, true, true, true, false, true, true, true, false => 0
  | false, true, true, true, true, false, true, true, true, true => 0
  | false, true, true, true, true, true, false, false, false, false => 576 / 125
  | false, true, true, true, true, true, false, false, false, true => -15168 / 625
  | false, true, true, true, true, true, false, false, true, false => -15168 / 625
  | false, true, true, true, true, true, false, false, true, true => 152 / 125
  | false, true, true, true, true, true, false, true, false, false => 15264 / 625
  | false, true, true, true, true, true, false, true, false, true => 0
  | false, true, true, true, true, true, false, true, true, false => 0
  | false, true, true, true, true, true, false, true, true, true => 0
  | false, true, true, true, true, true, true, false, false, false => 576 / 125
  | false, true, true, true, true, true, true, false, false, true => 152 / 125
  | false, true, true, true, true, true, true, false, true, false => 152 / 125
  | false, true, true, true, true, true, true, false, true, true => 0
  | false, true, true, true, true, true, true, true, false, false => 152 / 125
  | false, true, true, true, true, true, true, true, false, true => 0
  | false, true, true, true, true, true, true, true, true, false => 0
  | false, true, true, true, true, true, true, true, true, true => 0
  | true, false, false, false, false, false, false, false, false, false => 576 / 125
  | true, false, false, false, false, false, false, false, false, true => 576 / 125
  | true, false, false, false, false, false, false, false, true, false => 576 / 125
  | true, false, false, false, false, false, false, false, true, true => 2576 / 625
  | true, false, false, false, false, false, false, true, false, false => 576 / 125
  | true, false, false, false, false, false, false, true, false, true => 2576 / 625
  | true, false, false, false, false, false, false, true, true, false => 2576 / 625
  | true, false, false, false, false, false, false, true, true, true => 5184 / 625
  | true, false, false, false, false, false, true, false, false, false => 576 / 125
  | true, false, false, false, false, false, true, false, false, true => 2826 / 625
  | true, false, false, false, false, false, true, false, true, false => 2826 / 625
  | true, false, false, false, false, false, true, false, true, true => 576 / 125
  | true, false, false, false, false, false, true, true, false, false => 2576 / 625
  | true, false, false, false, false, false, true, true, false, true => -1512 / 625
  | true, false, false, false, false, false, true, true, true, false => -1512 / 625
  | true, false, false, false, false, false, true, true, true, true => 1392 / 625
  | true, false, false, false, false, true, false, false, false, false => 576 / 125
  | true, false, false, false, false, true, false, false, false, true => 2826 / 625
  | true, false, false, false, false, true, false, false, true, false => 2576 / 625
  | true, false, false, false, false, true, false, false, true, true => -1512 / 625
  | true, false, false, false, false, true, false, true, false, false => 2826 / 625
  | true, false, false, false, false, true, false, true, false, true => 576 / 125
  | true, false, false, false, false, true, false, true, true, false => -1512 / 625
  | true, false, false, false, false, true, false, true, true, true => 1392 / 625
  | true, false, false, false, false, true, true, false, false, false => 576 / 125
  | true, false, false, false, false, true, true, false, false, true => 88 / 125
  | true, false, false, false, false, true, true, false, true, false => 576 / 125
  | true, false, false, false, false, true, true, false, true, true => 5918 / 625
  | true, false, false, false, false, true, true, true, false, false => 576 / 125
  | true, false, false, false, false, true, true, true, false, true => 5918 / 625
  | true, false, false, false, false, true, true, true, true, false => 576 / 125
  | true, false, false, false, false, true, true, true, true, true => 15264 / 625
  | true, false, false, false, true, false, false, false, false, false => 576 / 125
  | true, false, false, false, true, false, false, false, false, true => 2576 / 625
  | true, false, false, false, true, false, false, false, true, false => 2826 / 625
  | true, false, false, false, true, false, false, false, true, true => -1512 / 625
  | true, false, false, false, true, false, false, true, false, false => 2826 / 625
  | true, false, false, false, true, false, false, true, false, true => -1512 / 625
  | true, false, false, false, true, false, false, true, true, false => 576 / 125
  | true, false, false, false, true, false, false, true, true, true => 1392 / 625
  | true, false, false, false, true, false, true, false, false, false => 576 / 125
  | true, false, false, false, true, false, true, false, false, true => 576 / 125
  | true, false, false, false, true, false, true, false, true, false => 88 / 125
  | true, false, false, false, true, false, true, false, true, true => 5918 / 625
  | true, false, false, false, true, false, true, true, false, false => 576 / 125
  | true, false, false, false, true, false, true, true, false, true => 576 / 125
  | true, false, false, false, true, false, true, true, true, false => 5918 / 625
  | true, false, false, false, true, false, true, true, true, true => 15264 / 625
  | true, false, false, false, true, true, false, false, false, false => 576 / 125
  | true, false, false, false, true, true, false, false, false, true => 576 / 125
  | true, false, false, false, true, true, false, false, true, false => 576 / 125
  | true, false, false, false, true, true, false, false, true, true => 576 / 125
  | true, false, false, false, true, true, false, true, false, false => 88 / 125
  | true, false, false, false, true, true, false, true, false, true => 5918 / 625
  | true, false, false, false, true, true, false, true, true, false => 5918 / 625
  | true, false, false, false, true, true, false, true, true, true => 15264 / 625
  | true, false, false, false, true, true, true, false, false, false => 576 / 125
  | true, false, false, false, true, true, true, false, false, true => 2064 / 625
  | true, false, false, false, true, true, true, false, true, false => 2064 / 625
  | true, false, false, false, true, true, true, false, true, true => -432 / 625
  | true, false, false, false, true, true, true, true, false, false => 2064 / 625
  | true, false, false, false, true, true, true, true, false, true => -432 / 625
  | true, false, false, false, true, true, true, true, true, false => -432 / 625
  | true, false, false, false, true, true, true, true, true, true => 0
  | true, false, false, true, false, false, false, false, false, false => 576 / 125
  | true, false, false, true, false, false, false, false, false, true => 2826 / 625
  | true, false, false, true, false, false, false, false, true, false => 2826 / 625
  | true, false, false, true, false, false, false, false, true, true => 576 / 125
  | true, false, false, true, false, false, false, true, false, false => 2576 / 625
  | true, false, false, true, false, false, false, true, false, true => -1512 / 625
  | true, false, false, true, false, false, false, true, true, false => -1512 / 625
  | true, false, false, true, false, false, false, true, true, true => 1392 / 625
  | true, false, false, true, false, false, true, false, false, false => 9972 / 625
  | true, false, false, true, false, false, true, false, false, true => 88 / 125
  | true, false, false, true, false, false, true, false, true, false => 88 / 125
  | true, false, false, true, false, false, true, false, true, true => 2064 / 625
  | true, false, false, true, false, false, true, true, false, false => 5184 / 625
  | true, false, false, true, false, false, true, true, false, true => 1392 / 625
  | true, false, false, true, false, false, true, true, true, false => 1392 / 625
  | true, false, false, true, false, false, true, true, true, true => 0
  | true, false, false, true, false, true, false, false, false, false => 2826 / 625
  | true, false, false, true, false, true, false, false, false, true => 576 / 125
  | true, false, false, true, false, true, false, false, true, false => -1512 / 625
  | true, false, false, true, false, true, false, false, true, true => 576 / 125
  | true, false, false, true, false, true, false, true, false, false => -1512 / 625
  | true, false, false, true, false, true, false, true, false, true => 576 / 125
  | true, false, false, true, false, true, false, true, true, false => -14424 / 125
  | true, false, false, true, false, true, false, true, true, true => -15168 / 625
  | true, false, false, true, false, true, true, false, false, false => 88 / 125
  | true, false, false, true, false, true, true, false, false, true => 2964 / 625
  | true, false, false, true, false, true, true, false, true, false => 5918 / 625
  | true, false, false, true, false, true, true, false, true, true => -432 / 625
  | true, false, false, true, false, true, true, true, false, false => 1392 / 625
  | true, false, false, true, false, true, true, true, false, true => 15264 / 625
  | true, false, false, true, false, true, true, true, true, false => -15168 / 625
  | true, false, false, true, false, true, true, true, true, true => 0
  | true, false, false, true, true, false, false, false, false, false => 2826 / 625
  | true, false, false, true, true, false, false, false, false, true => -1512 / 625
  | true, false, false, true, true, false, false, false, true, false => 576 / 125
  | true, false, false, true, true, false, false, false, true, true => 576 / 125
  | true, false, false, true, true, false, false, true, false, false => -1512 / 625
  | true, false, false, true, true, false, false, true, false, true => -14424 / 125
  | true, false, false, true, true, false, false, true, true, false => 576 / 125
  | true, false, false, true, true, false, false, true, true, true => -15168 / 625
  | true, false, false, true, true, false, true, false, false, false => 88 / 125
  | true, false, false, true, true, false, true, false, false, true => 5918 / 625
  | true, false, false, true, true, false, true, false, true, false => 2964 / 625
  | true, false, false, true, true, false, true, false, true, true => -432 / 625
  | true, false, false, true, true, false, true, true, false, false => 1392 / 625
  | true, false, false, true, true, false, true, true, false, true => -15168 / 625
  | true, false, false, true, true, false, true, true, true, false => 15264 / 625
  | true, false, false, true, true, false, true, true, true, true => 0
  | true, false, false, true, true, true, false, false, false, false => 576 / 125
  | true, false, false, true, true, true, false, false, false, true => 576 / 125
  | true, false, false, true, true, true, false, false, true, false => 576 / 125
  | true, false, false, true, true, true, false, false, true, true => 576 / 125
  | true, false, false, true, true, true, false, true, false, false => 1392 / 625
  | true, false, false, true, true, true, false, true, false, true => -15168 / 625
  | true, false, false, true, true, true, false, true, true, false => -15168 / 625
  | true, false, false, true, true, true, false, true, true, true => 152 / 125
  | true, false, false, true, true, true, true, false, false, false => 2064 / 625
  | true, false, false, true, true, true, true, false, false, true => -432 / 625
  | true, false, false, true, true, true, true, false, true, false => -432 / 625
  | true, false, false, true, true, true, true, false, true, true => 648 / 625
  | true, false, false, true, true, true, true, true, false, false => 0
  | true, false, false, true, true, true, true, true, false, true => 0
  | true, false, false, true, true, true, true, true, true, false => 0
  | true, false, false, true, true, true, true, true, true, true => 0
  | true, false, true, false, false, false, false, false, false, false => 576 / 125
  | true, false, true, false, false, false, false, false, false, true => 2826 / 625
  | true, false, true, false, false, false, false, false, true, false => 2576 / 625
  | true, false, true, false, false, false, false, false, true, true => -1512 / 625
  | true, false, true, false, false, false, false, true, false, false => 2826 / 625
  | true, false, true, false, false, false, false, true, false, true => 576 / 125
  | true, false, true, false, false, false, false, true, true, false => -1512 / 625
  | true, false, true, false, false, false, false, true, true, true => 1392 / 625
  | true, false, true, false, false, false, true, false, false, false => 2826 / 625
  | true, false, true, false, false, false, true, false, false, true => 576 / 125
  | true, false, true, false, false, false, true, false, true, false => -1512 / 625
  | true, false, true, false, false, false, true, false, true, true => 576 / 125
  | true, false, true, false, false, false, true, true, false, false => -1512 / 625
  | true, false, true, false, false, false, true, true, false, true => 576 / 125
  | true, false, true, false, false, false, true, true, true, false => -14424 / 125
  | true, false, true, false, false, false, true, true, true, true => -15168 / 625
  | true, false, true, false, false, true, false, false, false, false => 9972 / 625
  | true, false, true, false, false, true, false, false, false, true => 88 / 125
  | true, false, true, false, false, true, false, false, true, false => 5184 / 625
  | true, false, true, false, false, true, false, false, true, true => 1392 / 625
  | true, false, true, false, false, true, false, true, false, false => 88 / 125
  | true, false, true, false, false, true, false, true, false, true => 2064 / 625
  | true, false, true, false, false, true, false, true, true, false => 1392 / 625
  | true, false, true, false, false, true, false, true, true, true => 0
  | true, false, true, false, false, true, true, false, false, false => 88 / 125
  | true, false, true, false, false, true, true, false, false, true => 2964 / 625
  | true, false, true, false, false, true, true, false, true, false => 1392 / 625
  | true, false, true, false, false, true, true, false, true, true => 15264 / 625
  | true, false, true, false, false, true, true, true, false, false => 5918 / 625
  | true, false, true, false, false, true, true, true, false, true => -432 / 625
  | true, false, true, false, false, true, true, true, true, false => -15168 / 625
  | true, false, true, false, false, true, true, true, true, true => 0
  | true, false, true, false, true, false, false, false, false, false => 2826 / 625
  | true, false, true, false, true, false, false, false, false, true => -1512 / 625
  | true, false, true, false, true, false, false, false, true, false => -1512 / 625
  | true, false, true, false, true, false, false, false, true, true => -14424 / 125
  | true, false, true, false, true, false, false, true, false, false => 576 / 125
  | true, false, true, false, true, false, false, true, false, true => 576 / 125
  | true, false, true, false, true, false, false, true, true, false => 576 / 125
  | true, false, true, false, true, false, false, true, true, true => -15168 / 625
  | true, false, true, false, true, false, true, false, false, false => 576 / 125
  | true, false, true, false, true, false, true, false, false, true => 576 / 125
  | true, false, true, false, true, false, true, false, true, false => 1392 / 625
  | true, false, true, false, true, false, true, false, true, true => -15168 / 625
  | true, false, true, false, true, false, true, true, false, false => 576 / 125
  | true, false, true, false, true, false, true, true, false, true => 576 / 125
  | true, false, true, false, true, false, true, true, true, false => -15168 / 625
  | true, false, true, false, true, false, true, true, true, true => 152 / 125
  | true, false, true, false, true, true, false, false, false, false => 88 / 125
  | true, false, true, false, true, true, false, false, false, true => 5918 / 625
  | true, false, true, false, true, true, false, false, true, false => 1392 / 625
  | true, false, true, false, true, true, false, false, true, true => -15168 / 625
  | true, false, true, false, true, true, false, true, false, false => 2964 / 625
  | true, false, true, false, true, true, false, true, false, true => -432 / 625
  | true, false, true, false, true, true, false, true, true, false => 15264 / 625
  | true, false, true, false, true, true, false, true, true, true => 0
  | true, false, true, false, true, true, true, false, false, false => 2064 / 625
  | true, false, true, false, true, true, true, false, false, true => -432 / 625
  | true, false, true, false, true, true, true, false, true, false => 0
  | true, false, true, false, true, true, true, false, true, true => 0
  | true, false, true, false, true, true, true, true, false, false => -432 / 625
  | true, false, true, false, true, true, true, true, false, true => 648 / 625
  | true, false, true, false, true, true, true, true, true, false => 0
  | true, false, true, false, true, true, true, true, true, true => 0
  | true, false, true, true, false, false, false, false, false, false => 576 / 125
  | true, false, true, true, false, false, false, false, false, true => 88 / 125
  | true, false, true, true, false, false, false, false, true, false => 576 / 125
  | true, false, true, true, false, false, false, false, true, true => 5918 / 625
  | true, false, true, true, false, false, false, true, false, false => 576 / 125
  | true, false, true, true, false, false, false, true, false, true => 5918 / 625
  | true, false, true, true, false, false, false, true, true, false => 576 / 125
  | true, false, true, true, false, false, false, true, true, true => 15264 / 625
  | true, false, true, true, false, false, true, false, false, false => 88 / 125
  | true, false, true, true, false, false, true, false, false, true => 2964 / 625
  | true, false, true, true, false, false, true, false, true, false => 5918 / 625
  | true, false, true, true, false, false, true, false, true, true => -432 / 625
  | true, false, true, true, false, false, true, true, false, false => 1392 / 625
  | true, false, true, true, false, false, true, true, false, true => 15264 / 625
  | true, false, true, true, false, false, true, true, true, false => -15168 / 625
  | true, false, true, true, false, false, true, true, true, true => 0
  | true, false, true, true, false, true, false, false, false, false => 88 / 125
  | true, false, true, true, false, true, false, false, false, true => 2964 / 625
  | true, false, true, true, false, true, false, false, true, false => 1392 / 625
  | true, false, true, true, false, true, false, false, true, true => 15264 / 625
  | true, false, true, true, false, true, false, true, false, false => 5918 / 625
  | true, false, true, true, false, true, false, true, false, true => -432 / 625
  | true, false, true, true, false, true, false, true, true, false => -15168 / 625
  | true, false, true, true, false, true, false, true, true, true => 0
  | true, false, true, true, false, true, true, false, false, false => 2964 / 625
  | true, false, true, true, false, true, true, false, false, true => 0
  | true, false, true, true, false, true, true, false, true, false => 15264 / 625
  | true, false, true, true, false, true, true, false, true, true => 0
  | true, false, true, true, false, true, true, true, false, false => 15264 / 625
  | true, false, true, true, false, true, true, true, false, true => 0
  | true, false, true, true, false, true, true, true, true, false => 152 / 125
  | true, false, true, true, false, true, true, true, true, true => 0
  | true, false, true, true, true, false, false, false, false, false => 576 / 125
  | true, false, true, true, true, false, false, false, false, true => 1392 / 625
  | true, false, true, true, true, false, false, false, true, false => 576 / 125
  | true, false, true, true, true, false, false, false, true, true => -15168 / 625
  | true, false, true, true, true, false, false, true, false, false => 576 / 125
  | true, false, true, true, true, false, false, true, false, true => -15168 / 625
  | true, false, true, true, true, false, false, true, true, false => 576 / 125
  | true, false, true, true, true, false, false, true, true, true => 152 / 125
  | true, false, true, true, true, false, true, false, false, false => 5918 / 625
  | true, false, true, true, true, false, true, false, false, true => 15264 / 625
  | true, false, true, true, true, false, true, false, true, false => 15264 / 625
  | true, false, true, true, true, false, true, false, true, true => 0
  | true, false, true, true, true, false, true, true, false, false => -15168 / 625
  | true, false, true, true, true, false, true, true, false, true => 152 / 125
  | true, false, true, true, true, false, true, true, true, false => 152 / 125
  | true, false, true, true, true, false, true, true, true, true => 0
  | true, false, true, true, true, true, false, false, false, false => 5918 / 625
  | true, false, true, true, true, true, false, false, false, true => 15264 / 625
  | true, false, true, true, true, true, false, false, true, false => -15168 / 625
  | true, false, true, true, true, true, false, false, true, true => 152 / 125
  | true, false, true, true, true, true, false, true, false, false => 15264 / 625
  | true, false, true, true, true, true, false, true, false, true => 0
  | true, false, true, true, true, true, false, true, true, false => 152 / 125
  | true, false, true, true, true, true, false, true, true, true => 0
  | true, false, true, true, true, true, true, false, false, false => -432 / 625
  | true, false, true, true, true, true, true, false, false, true => 0
  | true, false, true, true, true, true, true, false, true, false => 0
  | true, false, true, true, true, true, true, false, true, true => 0
  | true, false, true, true, true, true, true, true, false, false => 0
  | true, false, true, true, true, true, true, true, false, true => 0
  | true, false, true, true, true, true, true, true, true, false => 0
  | true, false, true, true, true, true, true, true, true, true => 0
  | true, true, false, false, false, false, false, false, false, false => 576 / 125
  | true, true, false, false, false, false, false, false, false, true => 2576 / 625
  | true, true, false, false, false, false, false, false, true, false => 2826 / 625
  | true, true, false, false, false, false, false, false, true, true => -1512 / 625
  | true, true, false, false, false, false, false, true, false, false => 2826 / 625
  | true, true, false, false, false, false, false, true, false, true => -1512 / 625
  | true, true, false, false, false, false, false, true, true, false => 576 / 125
  | true, true, false, false, false, false, false, true, true, true => 1392 / 625
  | true, true, false, false, false, false, true, false, false, false => 2826 / 625
  | true, true, false, false, false, false, true, false, false, true => -1512 / 625
  | true, true, false, false, false, false, true, false, true, false => 576 / 125
  | true, true, false, false, false, false, true, false, true, true => 576 / 125
  | true, true, false, false, false, false, true, true, false, false => -1512 / 625
  | true, true, false, false, false, false, true, true, false, true => -14424 / 125
  | true, true, false, false, false, false, true, true, true, false => 576 / 125
  | true, true, false, false, false, false, true, true, true, true => -15168 / 625
  | true, true, false, false, false, true, false, false, false, false => 2826 / 625
  | true, true, false, false, false, true, false, false, false, true => -1512 / 625
  | true, true, false, false, false, true, false, false, true, false => -1512 / 625
  | true, true, false, false, false, true, false, false, true, true => -14424 / 125
  | true, true, false, false, false, true, false, true, false, false => 576 / 125
  | true, true, false, false, false, true, false, true, false, true => 576 / 125
  | true, true, false, false, false, true, false, true, true, false => 576 / 125
  | true, true, false, false, false, true, false, true, true, true => -15168 / 625
  | true, true, false, false, false, true, true, false, false, false => 576 / 125
  | true, true, false, false, false, true, true, false, false, true => 1392 / 625
  | true, true, false, false, false, true, true, false, true, false => 576 / 125
  | true, true, false, false, false, true, true, false, true, true => -15168 / 625
  | true, true, false, false, false, true, true, true, false, false => 576 / 125
  | true, true, false, false, false, true, true, true, false, true => -15168 / 625
  | true, true, false, false, false, true, true, true, true, false => 576 / 125
  | true, true, false, false, false, true, true, true, true, true => 152 / 125
  | true, true, false, false, true, false, false, false, false, false => 9972 / 625
  | true, true, false, false, true, false, false, false, false, true => 5184 / 625
  | true, true, false, false, true, false, false, false, true, false => 88 / 125
  | true, true, false, false, true, false, false, false, true, true => 1392 / 625
  | true, true, false, false, true, false, false, true, false, false => 88 / 125
  | true, true, false, false, true, false, false, true, false, true => 1392 / 625
  | true, true, false, false, true, false, false, true, true, false => 2064 / 625
  | true, true, false, false, true, false, false, true, true, true => 0
  | true, true, false, false, true, false, true, false, false, false => 88 / 125
  | true, true, false, false, true, false, true, false, false, true => 1392 / 625
  | true, true, false, false, true, false, true, false, true, false => 2964 / 625
  | true, true, false, false, true, false, true, false, true, true => 15264 / 625
  | true, true, false, false, true, false, true, true, false, false => 5918 / 625
  | true, true, false, false, true, false, true, true, false, true => -15168 / 625
  | true, true, false, false, true, false, true, true, true, false => -432 / 625
  | true, true, false, false, true, false, true, true, true, true => 0
  | true, true, false, false, true, true, false, false, false, false => 88 / 125
  | true, true, false, false, true, true, false, false, false, true => 1392 / 625
  | true, true, false, false, true, true, false, false, true, false => 5918 / 625
  | true, true, false, false, true, true, false, false, true, true => -15168 / 625
  | true, true, false, false, true, true, false, true, false, false => 2964 / 625
  | true, true, false, false, true, true, false, true, false, true => 15264 / 625
  | true, true, false, false, true, true, false, true, true, false => -432 / 625
  | true, true, false, false, true, true, false, true, true, true => 0
  | true, true, false, false, true, true, true, false, false, false => 2064 / 625
  | true, true, false, false, true, true, true, false, false, true => 0
  | true, true, false, false, true, true, true, false, true, false => -432 / 625
  | true, true, false, false, true, true, true, false, true, true => 0
  | true, true, false, false, true, true, true, true, false, false => -432 / 625
  | true, true, false, false, true, true, true, true, false, true => 0
  | true, true, false, false, true, true, true, true, true, false => 648 / 625
  | true, true, false, false, true, true, true, true, true, true => 0
  | true, true, false, true, false, false, false, false, false, false => 576 / 125
  | true, true, false, true, false, false, false, false, false, true => 576 / 125
  | true, true, false, true, false, false, false, false, true, false => 88 / 125
  | true, true, false, true, false, false, false, false, true, true => 5918 / 625
  | true, true, false, true, false, false, false, true, false, false => 576 / 125
  | true, true, false, true, false, false, false, true, false, true => 576 / 125
  | true, true, false, true, false, false, false, true, true, false => 5918 / 625
  | true, true, false, true, false, false, false, true, true, true => 15264 / 625
  | true, true, false, true, false, false, true, false, false, false => 88 / 125
  | true, true, false, true, false, false, true, false, false, true => 5918 / 625
  | true, true, false, true, false, false, true, false, true, false => 2964 / 625
  | true, true, false, true, false, false, true, false, true, true => -432 / 625
  | true, true, false, true, false, false, true, true, false, false => 1392 / 625
  | true, true, false, true, false, false, true, true, false, true => -15168 / 625
  | true, true, false, true, false, false, true, true, true, false => 15264 / 625
  | true, true, false, true, false, false, true, true, true, true => 0
  | true, true, false, true, false, true, false, false, false, false => 576 / 125
  | true, true, false, true, false, true, false, false, false, true => 576 / 125
  | true, true, false, true, false, true, false, false, true, false => 1392 / 625
  | true, true, false, true, false, true, false, false, true, true => -15168 / 625
  | true, true, false, true, false, true, false, true, false, false => 576 / 125
  | true, true, false, true, false, true, false, true, false, true => 576 / 125
  | true, true, false, true, false, true, false, true, true, false => -15168 / 625
  | true, true, false, true, false, true, false, true, true, true => 152 / 125
  | true, true, false, true, false, true, true, false, false, false => 5918 / 625
  | true, true, false, true, false, true, true, false, false, true => 15264 / 625
  | true, true, false, true, false, true, true, false, true, false => 15264 / 625
  | true, true, false, true, false, true, true, false, true, true => 0
  | true, true, false, true, false, true, true, true, false, false => -15168 / 625
  | true, true, false, true, false, true, true, true, false, true => 152 / 125
  | true, true, false, true, false, true, true, true, true, false => 152 / 125
  | true, true, false, true, false, true, true, true, true, true => 0
  | true, true, false, true, true, false, false, false, false, false => 88 / 125
  | true, true, false, true, true, false, false, false, false, true => 1392 / 625
  | true, true, false, true, true, false, false, false, true, false => 2964 / 625
  | true, true, false, true, true, false, false, false, true, true => 15264 / 625
  | true, true, false, true, true, false, false, true, false, false => 5918 / 625
  | true, true, false, true, true, false, false, true, false, true => -15168 / 625
  | true, true, false, true, true, false, false, true, true, false => -432 / 625
  | true, true, false, true, true, false, false, true, true, true => 0
  | true, true, false, true, true, false, true, false, false, false => 2964 / 625
  | true, true, false, true, true, false, true, false, false, true => 15264 / 625
  | true, true, false, true, true, false, true, false, true, false => 0
  | true, true, false, true, true, false, true, false, true, true => 0
  | true, true, false, true, true, false, true, true, false, false => 15264 / 625
  | true, true, false, true, true, false, true, true, false, true => 152 / 125
  | true, true, false, true, true, false, true, true, true, false => 0
  | true, true, false, true, true, false, true, true, true, true => 0
  | true, true, false, true, true, true, false, false, false, false => 5918 / 625
  | true, true, false, true, true, true, false, false, false, true => -15168 / 625
  | true, true, false, true, true, true, false, false, true, false => 15264 / 625
  | true, true, false, true, true, true, false, false, true, true => 152 / 125
  | true, true, false, true, true, true, false, true, false, false => 15264 / 625
  | true, true, false, true, true, true, false, true, false, true => 152 / 125
  | true, true, false, true, true, true, false, true, true, false => 0
  | true, true, false, true, true, true, false, true, true, true => 0
  | true, true, false, true, true, true, true, false, false, false => -432 / 625
  | true, true, false, true, true, true, true, false, false, true => 0
  | true, true, false, true, true, true, true, false, true, false => 0
  | true, true, false, true, true, true, true, false, true, true => 0
  | true, true, false, true, true, true, true, true, false, false => 0
  | true, true, false, true, true, true, true, true, false, true => 0
  | true, true, false, true, true, true, true, true, true, false => 0
  | true, true, false, true, true, true, true, true, true, true => 0
  | true, true, true, false, false, false, false, false, false, false => 576 / 125
  | true, true, true, false, false, false, false, false, false, true => 576 / 125
  | true, true, true, false, false, false, false, false, true, false => 576 / 125
  | true, true, true, false, false, false, false, false, true, true => 576 / 125
  | true, true, true, false, false, false, false, true, false, false => 88 / 125
  | true, true, true, false, false, false, false, true, false, true => 5918 / 625
  | true, true, true, false, false, false, false, true, true, false => 5918 / 625
  | true, true, true, false, false, false, false, true, true, true => 15264 / 625
  | true, true, true, false, false, false, true, false, false, false => 576 / 125
  | true, true, true, false, false, false, true, false, false, true => 576 / 125
  | true, true, true, false, false, false, true, false, true, false => 576 / 125
  | true, true, true, false, false, false, true, false, true, true => 576 / 125
  | true, true, true, false, false, false, true, true, false, false => 1392 / 625
  | true, true, true, false, false, false, true, true, false, true => -15168 / 625
  | true, true, true, false, false, false, true, true, true, false => -15168 / 625
  | true, true, true, false, false, false, true, true, true, true => 152 / 125
  | true, true, true, false, false, true, false, false, false, false => 88 / 125
  | true, true, true, false, false, true, false, false, false, true => 5918 / 625
  | true, true, true, false, false, true, false, false, true, false => 1392 / 625
  | true, true, true, false, false, true, false, false, true, true => -15168 / 625
  | true, true, true, false, false, true, false, true, false, false => 2964 / 625
  | true, true, true, false, false, true, false, true, false, true => -432 / 625
  | true, true, true, false, false, true, false, true, true, false => 15264 / 625
  | true, true, true, false, false, true, false, true, true, true => 0
  | true, true, true, false, false, true, true, false, false, false => 5918 / 625
  | true, true, true, false, false, true, true, false, false, true => 15264 / 625
  | true, true, true, false, false, true, true, false, true, false => -15168 / 625
  | true, true, true, false, false, true, true, false, true, true => 152 / 125
  | true, true, true, false, false, true, true, true, false, false => 15264 / 625
  | true, true, true, false, false, true, true, true, false, true => 0
  | true, true, true, false, false, true, true, true, true, false => 152 / 125
  | true, true, true, false, false, true, true, true, true, true => 0
  | true, true, true, false, true, false, false, false, false, false => 88 / 125
  | true, true, true, false, true, false, false, false, false, true => 1392 / 625
  | true, true, true, false, true, false, false, false, true, false => 5918 / 625
  | true, true, true, false, true, false, false, false, true, true => -15168 / 625
  | true, true, true, false, true, false, false, true, false, false => 2964 / 625
  | true, true, true, false, true, false, false, true, false, true => 15264 / 625
  | true, true, true, false, true, false, false, true, true, false => -432 / 625
  | true, true, true, false, true, false, false, true, true, true => 0
  | true, true, true, false, true, false, true, false, false, false => 5918 / 625
  | true, true, true, false, true, false, true, false, false, true => -15168 / 625
  | true, true, true, false, true, false, true, false, true, false => 15264 / 625
  | true, true, true, false, true, false, true, false, true, true => 152 / 125
  | true, true, true, false, true, false, true, true, false, false => 15264 / 625
  | true, true, true, false, true, false, true, true, false, true => 152 / 125
  | true, true, true, false, true, false, true, true, true, false => 0
  | true, true, true, false, true, false, true, true, true, true => 0
  | true, true, true, false, true, true, false, false, false, false => 2964 / 625
  | true, true, true, false, true, true, false, false, false, true => 15264 / 625
  | true, true, true, false, true, true, false, false, true, false => 15264 / 625
  | true, true, true, false, true, true, false, false, true, true => 152 / 125
  | true, true, true, false, true, true, false, true, false, false => 0
  | true, true, true, false, true, true, false, true, false, true => 0
  | true, true, true, false, true, true, false, true, true, false => 0
  | true, true, true, false, true, true, false, true, true, true => 0
  | true, true, true, false, true, true, true, false, false, false => -432 / 625
  | true, true, true, false, true, true, true, false, false, true => 0
  | true, true, true, false, true, true, true, false, true, false => 0
  | true, true, true, false, true, true, true, false, true, true => 0
  | true, true, true, false, true, true, true, true, false, false => 0
  | true, true, true, false, true, true, true, true, false, true => 0
  | true, true, true, false, true, true, true, true, true, false => 0
  | true, true, true, false, true, true, true, true, true, true => 0
  | true, true, true, true, false, false, false, false, false, false => 576 / 125
  | true, true, true, true, false, false, false, false, false, true => 2064 / 625
  | true, true, true, true, false, false, false, false, true, false => 2064 / 625
  | true, true, true, true, false, false, false, false, true, true => -432 / 625
  | true, true, true, true, false, false, false, true, false, false => 2064 / 625
  | true, true, true, true, false, false, false, true, false, true => -432 / 625
  | true, true, true, true, false, false, false, true, true, false => -432 / 625
  | true, true, true, true, false, false, false, true, true, true => 0
  | true, true, true, true, false, false, true, false, false, false => 2064 / 625
  | true, true, true, true, false, false, true, false, false, true => -432 / 625
  | true, true, true, true, false, false, true, false, true, false => -432 / 625
  | true, true, true, true, false, false, true, false, true, true => 648 / 625
  | true, true, true, true, false, false, true, true, false, false => 0
  | true, true, true, true, false, false, true, true, false, true => 0
  | true, true, true, true, false, false, true, true, true, false => 0
  | true, true, true, true, false, false, true, true, true, true => 0
  | true, true, true, true, false, true, false, false, false, false => 2064 / 625
  | true, true, true, true, false, true, false, false, false, true => -432 / 625
  | true, true, true, true, false, true, false, false, true, false => 0
  | true, true, true, true, false, true, false, false, true, true => 0
  | true, true, true, true, false, true, false, true, false, false => -432 / 625
  | true, true, true, true, false, true, false, true, false, true => 648 / 625
  | true, true, true, true, false, true, false, true, true, false => 0
  | true, true, true, true, false, true, false, true, true, true => 0
  | true, true, true, true, false, true, true, false, false, false => -432 / 625
  | true, true, true, true, false, true, true, false, false, true => 0
  | true, true, true, true, false, true, true, false, true, false => 0
  | true, true, true, true, false, true, true, false, true, true => 0
  | true, true, true, true, false, true, true, true, false, false => 0
  | true, true, true, true, false, true, true, true, false, true => 0
  | true, true, true, true, false, true, true, true, true, false => 0
  | true, true, true, true, false, true, true, true, true, true => 0
  | true, true, true, true, true, false, false, false, false, false => 2064 / 625
  | true, true, true, true, true, false, false, false, false, true => 0
  | true, true, true, true, true, false, false, false, true, false => -432 / 625
  | true, true, true, true, true, false, false, false, true, true => 0
  | true, true, true, true, true, false, false, true, false, false => -432 / 625
  | true, true, true, true, true, false, false, true, false, true => 0
  | true, true, true, true, true, false, false, true, true, false => 648 / 625
  | true, true, true, true, true, false, false, true, true, true => 0
  | true, true, true, true, true, false, true, false, false, false => -432 / 625
  | true, true, true, true, true, false, true, false, false, true => 0
  | true, true, true, true, true, false, true, false, true, false => 0
  | true, true, true, true, true, false, true, false, true, true => 0
  | true, true, true, true, true, false, true, true, false, false => 0
  | true, true, true, true, true, false, true, true, false, true => 0
  | true, true, true, true, true, false, true, true, true, false => 0
  | true, true, true, true, true, false, true, true, true, true => 0
  | true, true, true, true, true, true, false, false, false, false => -432 / 625
  | true, true, true, true, true, true, false, false, false, true => 0
  | true, true, true, true, true, true, false, false, true, false => 0
  | true, true, true, true, true, true, false, false, true, true => 0
  | true, true, true, true, true, true, false, true, false, false => 0
  | true, true, true, true, true, true, false, true, false, true => 0
  | true, true, true, true, true, true, false, true, true, false => 0
  | true, true, true, true, true, true, false, true, true, true => 0
  | true, true, true, true, true, true, true, false, false, false => 648 / 625
  | true, true, true, true, true, true, true, false, false, true => 0
  | true, true, true, true, true, true, true, false, true, false => 0
  | true, true, true, true, true, true, true, false, true, true => 0
  | true, true, true, true, true, true, true, true, false, false => 0
  | true, true, true, true, true, true, true, true, false, true => 0
  | true, true, true, true, true, true, true, true, true, false => 0
  | true, true, true, true, true, true, true, true, true, true => 0

def totalFlagContrib (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  totalFlagContribBits (adj 0 1) (adj 0 2) (adj 0 3) (adj 0 4) (adj 1 2)
    (adj 1 3) (adj 1 4) (adj 2 3) (adj 2 4) (adj 3 4)

def mkAdj5 (e : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0 => e 0 | 0, 2 | 2, 0 => e 1 | 0, 3 | 3, 0 => e 2 | 0, 4 | 4, 0 => e 3
  | 1, 2 | 2, 1 => e 4 | 1, 3 | 3, 1 => e 5 | 1, 4 | 4, 1 => e 6
  | 2, 3 | 3, 2 => e 7 | 2, 4 | 4, 2 => e 8 | 3, 4 | 4, 3 => e 9
  | _, _ => false
attribute [-instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

def _root_._private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 10 → Bool := fun i =>
  match i.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4
  | 5 => b5 | 6 => b6 | 7 => b7 | 8 => b8 | 9 => b9
  | _ => false

comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits.match_1
  as "_private.ErdosProblems.Erdos24.0.Erdos24.edgeBits.match_1"
comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits
  as "_private.ErdosProblems.Erdos24.0.Erdos24.edgeBits"

def _root_.SimpleGraph.IsLabeledC5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5, G.Adj (f i) (f (i + 1))

noncomputable def _root_.SimpleGraph.numC5 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → V)).filter (fun f => G.IsLabeledC5 f)).card / 10

axiom
    _root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1 :
    decide
      (∀ (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
        Erdos24.totalFlagContrib
            (Erdos24.mkAdj5
              (_root_._private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits
                b01 b02 b03 b04 b12 b13 b14 b23 b24 b34)) =
          _root_._private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
            (Erdos24.mkAdj5
              (_root_._private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits
                b01 b02 b03 b04 b12 b13 b14 b23 b24 b34))) =
      true

comparator_copy_declaration
  _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1
  as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1"
end

end Erdos24

attribute [local instance] Classical.propDecidable

universe u_1

open Lean Elab Command

theorem Erdos24.erdos_pentagon_conjecture :
    ∀ (n : Nat)
      (G :
        SimpleGraph.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))),
      @SimpleGraph.CliqueFree.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
          G (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @LE.le.{0} Nat instLENat
          (@SimpleGraph.numC5.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
            (Fin.fintype
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
            G)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
  := by
  sorry
