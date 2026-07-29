import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open Finset BigOperators

namespace Erdos481

variable {r : ℕ}
variable (a b : Fin r → ℕ+)

noncomputable def C : ℝ := ∑ i : Fin r, (1 : ℝ) / (a i : ℝ)

def T (L : List ℕ+) : List ℕ+ :=
  L.flatMap fun x : ℕ+ => (List.finRange r).map fun i =>
    ⟨a i * x + b i, Nat.add_pos_right _ (b i).2⟩

def A : ℕ → List ℕ+
  | 0 => []
  | 1 => [1]
  | n + 2 => T a b (A (n + 1))
end Erdos481

attribute [local instance] Classical.propDecidable

theorem Erdos481.erdos_481 :
    ∀ {r : Nat} (a b : Fin r → PNat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Erdos481.C r a) →
          @Exists.{1} Nat fun (k : Nat) ↦
            And
              (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
              (Not (@List.Nodup.{0} PNat (@Erdos481.A r a b k)))
  := by
  sorry
