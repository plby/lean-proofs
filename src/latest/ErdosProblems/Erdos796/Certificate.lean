import ErdosProblems.Erdos796.Core

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite certificate for Erdős Problem 796

This file formalizes the seven cofactor fibers and the multiplication
certificate in Section 6 and Appendix A of the accompanying manuscript.

The convolution is *ordered*: `(u, v)` and `(v, u)` are different witnesses
when both occur.  Thus the bound `≤ 2` below is exactly the compatibility
condition used in the manuscript, including for a fiber paired with itself.
-/

namespace Erdos796.Certificate

open scoped BigOperators

abbrev Fiber := Finset ℕ

/-- The seven fibers displayed in Section 6. -/
def fiberA : Fiber := {1}
def fiberB : Fiber := {1, 2}
def fiberC : Fiber := {1, 2, 3}
def fiberD : Fiber := {1, 3, 4, 5}
def fiberE : Fiber := {1, 3, 4, 5, 6}
def fiberF : Fiber := {1, 3, 4, 5, 6, 7}
def fiberG : Fiber := {2, 3, 5, 7, 8, 9, 10}

/-- Names for the seven fibers, useful for exhaustive finite checking. -/
inductive FiberName
  | A | B | C | D | E | F | G
  deriving DecidableEq, Repr, Fintype

def fiber : FiberName → Fiber
  | .A => fiberA
  | .B => fiberB
  | .C => fiberC
  | .D => fiberD
  | .E => fiberE
  | .F => fiberF
  | .G => fiberG

/-- The ordered product convolution `r_{U,V}(m)`. -/
def orderedConvCount (U V : Fiber) (m : ℕ) : ℕ :=
  ((U.product V).filter fun uv => uv.1 * uv.2 = m).card

/-- The finite support of the ordered product convolution. -/
def productSupport (U V : Fiber) : Finset ℕ :=
  (U.product V).image fun uv => uv.1 * uv.2

/-- Finite, decidable form of the pairwise compatibility condition.  It is
enough to check the support because the convolution vanishes off it. -/
def PairCompatible (U V : Fiber) : Prop :=
  ∀ m ∈ productSupport U V, orderedConvCount U V m ≤ 2

instance instDecidablePairCompatible (U V : Fiber) : Decidable (PairCompatible U V) := by
  unfold PairCompatible
  infer_instance

/-- The finite predicate is equivalent to the manuscript's condition, which
quantifies over every natural number. -/
theorem pairCompatible_iff_all_products (U V : Fiber) :
    PairCompatible U V ↔ ∀ m : ℕ, orderedConvCount U V m ≤ 2 := by
  constructor
  · intro h m
    by_cases hm : m ∈ productSupport U V
    · exact h m hm
    · have hempty :
          ((U.product V).filter fun uv => uv.1 * uv.2 = m) = ∅ := by
        apply Finset.filter_false_of_mem
        intro uv huv huvProduct
        apply hm
        exact Finset.mem_image.mpr ⟨uv, huv, huvProduct⟩
      change ((U.product V).filter fun uv => uv.1 * uv.2 = m).card ≤ 2
      rw [hempty]
      decide
  · intro h m _
    exact h m

/-- Products whose ordered convolution coefficient is exactly two. -/
def doubleProducts (U V : Fiber) : Finset ℕ :=
  (productSupport U V).filter fun m => orderedConvCount U V m = 2

/-- One exhaustive kernel-checked computation of all `7 × 7` ordered fiber pairs. -/
theorem all_fiber_pairs_compatible :
    ∀ X Y : FiberName, PairCompatible (fiber X) (fiber Y) := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 2000000 in
  decide

/-- Every one of the `7 × 7` ordered fiber pairs is compatible. -/
theorem every_fiber_pair_compatible (X Y : FiberName) :
    PairCompatible (fiber X) (fiber Y) :=
  all_fiber_pairs_compatible X Y

/-- Consequently every ordered convolution coefficient of every named pair
is at most two, including coefficients outside the finite support. -/
theorem every_fiber_pair_convolution_le_two (X Y : FiberName) (m : ℕ) :
    orderedConvCount (fiber X) (fiber Y) m ≤ 2 :=
  (pairCompatible_iff_all_products _ _).mp (every_fiber_pair_compatible X Y) m

/-!
The next theorem is the complete table in Appendix A.  Since convolution is
symmetric in the two fibers, it lists the 28 unordered pairs.
-/

theorem appendix_A_double_product_table :
    doubleProducts fiberA fiberA = ∅ ∧
    doubleProducts fiberA fiberB = ∅ ∧
    doubleProducts fiberA fiberC = ∅ ∧
    doubleProducts fiberA fiberD = ∅ ∧
    doubleProducts fiberA fiberE = ∅ ∧
    doubleProducts fiberA fiberF = ∅ ∧
    doubleProducts fiberA fiberG = ∅ ∧
    doubleProducts fiberB fiberB = {2} ∧
    doubleProducts fiberB fiberC = {2} ∧
    doubleProducts fiberB fiberD = ∅ ∧
    doubleProducts fiberB fiberE = {6} ∧
    doubleProducts fiberB fiberF = {6} ∧
    doubleProducts fiberB fiberG = {10} ∧
    doubleProducts fiberC fiberC = {2, 3, 6} ∧
    doubleProducts fiberC fiberD = {3} ∧
    doubleProducts fiberC fiberE = {3, 6, 12} ∧
    doubleProducts fiberC fiberF = {3, 6, 12} ∧
    doubleProducts fiberC fiberG = {6, 9, 10} ∧
    doubleProducts fiberD fiberD = {3, 4, 5, 12, 15, 20} ∧
    doubleProducts fiberD fiberE = {3, 4, 5, 12, 15, 20} ∧
    doubleProducts fiberD fiberF = {3, 4, 5, 12, 15, 20} ∧
    doubleProducts fiberD fiberG = {8, 9, 10, 15, 40} ∧
    doubleProducts fiberE fiberE = {3, 4, 5, 6, 12, 15, 18, 20, 24, 30} ∧
    doubleProducts fiberE fiberF = {3, 4, 5, 6, 12, 15, 18, 20, 24, 30} ∧
    doubleProducts fiberE fiberG = {8, 9, 10, 12, 15, 30, 40} ∧
    doubleProducts fiberF fiberF = {3, 4, 5, 6, 7, 12, 15, 18, 20, 21,
      24, 28, 30, 35, 42} ∧
    doubleProducts fiberF fiberG = {8, 9, 10, 12, 15, 21, 30, 35, 40} ∧
    doubleProducts fiberG fiberG = {6, 10, 14, 15, 16, 18, 20, 21, 24, 27,
      30, 35, 40, 45, 50, 56, 63, 70, 72, 80, 90} := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 10000000 in
  decide

/-! ## The ten-fiber prefix and its excess -/

/-- The assignment `A,B,C,C,D,E,F,F,F,G` to indices `1,...,10`.

The argument is zero-based: `prefixFiber k` is the manuscript's fiber
`U_{k+1}`.
-/
def prefixFiberName (k : Fin 10) : FiberName :=
  match k.1 with
  | 0 => .A
  | 1 => .B
  | 2 => .C
  | 3 => .C
  | 4 => .D
  | 5 => .E
  | 6 => .F
  | 7 => .F
  | 8 => .F
  | _ => .G

def prefixFiber (k : Fin 10) : Fiber :=
  fiber (prefixFiberName k)

/-- The ten printed fibers as a family on natural indices; it is empty at
index zero and outside the certified prefix. -/
def certificatePrefix (j : ℕ) : Fiber :=
  if h : 1 ≤ j ∧ j ≤ 10 then
    prefixFiber ⟨j - 1, by omega⟩
  else
    ∅

@[simp] theorem certificatePrefix_zero : certificatePrefix 0 = ∅ := by
  simp [certificatePrefix]

@[simp] theorem certificatePrefix_succ (k : Fin 10) :
    certificatePrefix (k.1 + 1) = prefixFiber k := by
  simp [certificatePrefix]

/-- Each printed fiber lies in its required interval. -/
theorem all_prefix_fibers_bounded :
    ∀ k : Fin 10, prefixFiber k ⊆ positiveIcc (k.1 + 1) := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 2000000 in
  decide

/-- The actual ten-fiber prefix is pairwise compatible. -/
theorem ten_fiber_prefix_compatible (i j : Fin 10) :
    PairCompatible (prefixFiber i) (prefixFiber j) :=
  every_fiber_pair_compatible (prefixFiberName i) (prefixFiberName j)

/-- The prefix satisfies the manuscript's globally quantified convolution
bound, not merely its executable finite check. -/
theorem ten_fiber_prefix_convolution_le_two (i j : Fin 10) (m : ℕ) :
    orderedConvCount (prefixFiber i) (prefixFiber j) m ≤ 2 :=
  (pairCompatible_iff_all_products _ _).mp (ten_fiber_prefix_compatible i j) m

/-- The finite certificate satisfies the `CompatiblePrefix` definition from
`Erdos796.Core`. -/
theorem certificatePrefix_compatible : CompatiblePrefix 10 certificatePrefix := by
  constructor
  · intro j hj
    by_cases hpos : 1 ≤ j
    · let k : Fin 10 := ⟨j - 1, by omega⟩
      have hjk : j = k.1 + 1 := by
        dsimp [k]
        omega
      rw [hjk, certificatePrefix_succ]
      exact all_prefix_fibers_bounded k
    · have hj0 : j = 0 := by omega
      subst j
      simp
  · intro i hi j hj m
    by_cases hipos : 1 ≤ i
    · by_cases hjpos : 1 ≤ j
      · let ii : Fin 10 := ⟨i - 1, by omega⟩
        let jj : Fin 10 := ⟨j - 1, by omega⟩
        have hii : i = ii.1 + 1 := by
          dsimp [ii]
          omega
        have hjj : j = jj.1 + 1 := by
          dsimp [jj]
          omega
        rw [hii, hjj, certificatePrefix_succ, certificatePrefix_succ]
        exact ten_fiber_prefix_convolution_le_two ii jj m
      · have hj0 : j = 0 := by omega
        subst j
        simp [productRepCount]
    · have hi0 : i = 0 := by omega
      subst i
      simp [productRepCount]

/-- The elementary prime-counting function used in the excess. -/
def primeCount (n : ℕ) : ℕ := Nat.primeCounting n

/-- `|U_j| - 1 - π(j)` for the ten certified fibers. -/
def prefixExcess (k : Fin 10) : ℤ :=
  (prefixFiber k).card - 1 - primeCount (k.1 + 1)

/-- The certificate excess is literally the `excessInt` from the core API. -/
theorem prefixExcess_eq_core_excessInt (k : Fin 10) :
    prefixExcess k = excessInt certificatePrefix (k.1 + 1) := by
  simp [prefixExcess, primeCount, excessInt]

def prefixExcesses : List ℤ :=
  List.ofFn prefixExcess

/-- The manuscript's excess sequence `(0,0,0,0,0,1,1,1,1,2)`. -/
theorem prefix_excess_sequence :
    prefixExcesses = [0, 0, 0, 0, 0, 1, 1, 1, 1, 2] := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 2000000 in
  decide

/-- The weight `w_j = 1/(j(j+1))`, represented exactly in `ℚ`. -/
def cofactorWeight (j : ℕ) : ℚ :=
  1 / ((j : ℚ) * (j + 1 : ℚ))

/-- The exact weighted value of the ten-fiber prefix. -/
def prefixValue : ℚ :=
  ∑ k : Fin 10, (prefixExcess k : ℚ) * cofactorWeight (k.1 + 1)

theorem prefix_value_eq : prefixValue = 14 / 165 := by
  have hp1 : Nat.primeCounting 1 = 0 := by decide
  have hp2 : Nat.primeCounting 2 = 1 := by decide
  have hp3 : Nat.primeCounting 3 = 2 := by decide
  have hp4 : Nat.primeCounting 4 = 2 := by decide
  have hp5 : Nat.primeCounting 5 = 3 := by decide
  have hp6 : Nat.primeCounting 6 = 3 := by decide
  have hp7 : Nat.primeCounting 7 = 4 := by decide
  have hp8 : Nat.primeCounting 8 = 4 := by decide
  have hp9 : Nat.primeCounting 9 = 4 := by decide
  have hp10 : Nat.primeCounting 10 = 4 := by decide
  norm_num [prefixValue, Fin.sum_univ_succ, prefixExcess, primeCount,
    prefixFiber, prefixFiberName, fiber, fiberA, fiberB, fiberC, fiberD,
    fiberE, fiberF, fiberG, cofactorWeight, hp1, hp2, hp3, hp4, hp5,
    hp6, hp7, hp8, hp9, hp10]

/-- One summand of the constant-excess-two tail is a telescoping difference. -/
theorem twice_weight_telescope (j : ℕ) (hj : 0 < j) :
    2 * cofactorWeight j = (2 : ℚ) / j - 2 / (j + 1) := by
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hj10 : (j : ℚ) + 1 ≠ 0 := by positivity
  unfold Erdos796.Certificate.cofactorWeight
  field_simp [hj0, hj10]
  ring

/-- The first `N` terms of the canonical tail, beginning at `j = 11`. -/
def canonicalTailPartial (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, 2 * cofactorWeight (k + 11)

/-- Exact finite telescoping of the canonical tail. -/
theorem canonical_tail_partial_eq (N : ℕ) :
    canonicalTailPartial N = (2 : ℚ) / 11 - 2 / (N + 11) := by
  induction N with
  | zero => norm_num [canonicalTailPartial]
  | succ N ih =>
      rw [canonicalTailPartial, Finset.sum_range_succ, ← canonicalTailPartial, ih]
      rw [twice_weight_telescope (N + 11) (by omega)]
      push_cast
      ring

/-- The canonical extension has constant excess two after index ten, whose
telescoping tail has value `2/11`.  The preceding theorem supplies the exact
finite partial sums approaching this value. -/
def canonicalTailValue : ℚ := 2 / 11

def certificateValue : ℚ := prefixValue + canonicalTailValue

/-- The exact lower-bound certificate `14/165 + 2/11 = 4/15`. -/
theorem certificate_value_eq_four_fifteenths :
    certificateValue = 4 / 15 := by
  rw [certificateValue, prefix_value_eq]
  norm_num [canonicalTailValue]

end Erdos796.Certificate
