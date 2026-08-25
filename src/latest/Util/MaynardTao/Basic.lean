/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise

/-- A set of integers is admissible if its residues omit a class modulo every
prime.  This is kept outside ErdosProblems.Axioms so unconditional Maynard
modules can use the definition without an import cycle. -/
def Admissible (B : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (Finset.image (· % (p : ℤ)) B).card < p
