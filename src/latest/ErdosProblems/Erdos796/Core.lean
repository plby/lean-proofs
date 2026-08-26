import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.PSeries

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős's multiplicative representation problem

This file fixes the basic objects used throughout the formalization of the
second-order asymptotic for `g₃`.  Finite subsets of the positive integers are
represented by `Finset ℕ`.  We keep index `0` in the ambient Lean types but
force the zeroth cofactor fibre to be empty; all mathematical sums start at
index `1`.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

/-- The interval `[1,n]` as a finite set of natural numbers. -/
def positiveIcc (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Number of ordered pairs `(u,v) ∈ U × V` whose product is `m`. -/
def productRepCount (U V : Finset ℕ) (m : ℕ) : ℕ :=
  ((U ×ˢ V).filter fun uv => uv.1 * uv.2 = m).card

/-- Number of representations `m = ab` from `A` with `a < b`. -/
def strictProductRepCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun ab => ab.1 < ab.2 ∧ ab.1 * ab.2 = m).card

/-- The paper's admissibility condition for a subset of `[n]`. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ positiveIcc n ∧ ∀ m : ℕ, strictProductRepCount A m ≤ 2

/-- The extremal function in Erdős Problem 796: the largest cardinality of
an admissible subset of `[1,n]`.  The supremum is a genuine finite maximum,
because it is taken over a filtered powerset. -/
noncomputable def g3 (n : ℕ) : ℕ := by
  classical
  exact ((positiveIcc n).powerset.filter (Admissible n)).sup Finset.card

/-- A compatible cofactor family.  The condition at index `0` forces `U 0 = ∅`. -/
def Compatible (U : ℕ → Finset ℕ) : Prop :=
  (∀ j : ℕ, U j ⊆ positiveIcc j) ∧
    ∀ i j m : ℕ, productRepCount (U i) (U j) m ≤ 2

/-- Compatibility restricted to the first `J` fibres. -/
def CompatiblePrefix (J : ℕ) (U : ℕ → Finset ℕ) : Prop :=
  (∀ j ≤ J, U j ⊆ positiveIcc j) ∧
    ∀ i ≤ J, ∀ j ≤ J, ∀ m : ℕ,
      productRepCount (U i) (U j) m ≤ 2

/-- The number `N_j(n)` of primes in the `j`-th large-prime bucket. -/
def bucketCount (n j : ℕ) : ℕ :=
  ((Finset.Ioc n.sqrt n).filter fun q => q.Prime ∧ n / q = j).card

/-- The finite score of a compatible family in the cofactor model. -/
def modelScore (n : ℕ) (U : ℕ → Finset ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 n.sqrt, bucketCount n j * (U j).card

/-- Integer-valued excess of the `j`-th fibre above `{1} ∪ {p ≤ j}`. -/
def excessInt (U : ℕ → Finset ℕ) (j : ℕ) : ℤ :=
  (U j).card - 1 - Nat.primeCounting j

/-- Real-valued excess. -/
def excess (U : ℕ → Finset ℕ) (j : ℕ) : ℝ := excessInt U j

/-- The cofactor weight `1/(j(j+1))`. -/
noncomputable def cofactorWeight (j : ℕ) : ℝ :=
  1 / ((j : ℝ) * (j + 1 : ℕ))

/-- The weighted cofactor term at the positive index `j+1`. -/
noncomputable def cofactorTerm (U : ℕ → Finset ℕ) (j : ℕ) : ℝ :=
  cofactorWeight (j + 1) * excess U (j + 1)

/-- A family has a finite cofactor value when its weighted series is summable. -/
def HasCofactorValue (U : ℕ → Finset ℕ) : Prop :=
  Summable (cofactorTerm U)

/-- The cofactor value of a summable family. -/
noncomputable def cofactorValue (U : ℕ → Finset ℕ) : ℝ :=
  ∑' j : ℕ, cofactorTerm U j

/-- The variational constant `Γ`, restricted to finite-valued compatible families.

The manuscript assigns value `-∞` to families whose negative part diverges;
such families do not affect this real supremum.  A later theorem connects this
definition to that extended-real convention after proving the uniform positive
tail bound.
-/
noncomputable def Gamma : ℝ :=
  sSup {x : ℝ | ∃ U : ℕ → Finset ℕ,
    Compatible U ∧ HasCofactorValue U ∧ cofactorValue U = x}

@[simp] theorem mem_positiveIcc {n x : ℕ} : x ∈ positiveIcc n ↔ 1 ≤ x ∧ x ≤ n := by
  simp [positiveIcc]

theorem compatible_zero_empty {U : ℕ → Finset ℕ} (hU : Compatible U) : U 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := hU.1 0 hx
  simp [positiveIcc] at hx'

theorem compatible_prefix_mono {J K : ℕ} {U : ℕ → Finset ℕ}
    (hJK : J ≤ K) (hU : CompatiblePrefix K U) : CompatiblePrefix J U := by
  constructor
  · intro j hj
    exact hU.1 j (hj.trans hJK)
  · intro i hi j hj m
    exact hU.2 i (hi.trans hJK) j (hj.trans hJK) m

theorem compatible_compatiblePrefix {J : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) : CompatiblePrefix J U := by
  constructor
  · intro j _
    exact hU.1 j
  · intro i _ j _ m
    exact hU.2 i j m

end Erdos796
