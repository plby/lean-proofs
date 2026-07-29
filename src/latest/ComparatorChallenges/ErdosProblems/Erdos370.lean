import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos370

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

noncomputable def maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}
end Erdos370

attribute [local instance] Classical.propDecidable

theorem Erdos370.erdos_370 :
    Iff
      (@Set.Infinite.{0} Nat
        (@setOf.{0} Nat fun (n : Nat) ↦
          And
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (Erdos370.maxPrimeFac n))
              (@Nat.cast.{0} Real Real.instNatCast n).sqrt)
            (@LT.lt.{0} Real Real.instLT
              (@Nat.cast.{0} Real Real.instNatCast
                (Erdos370.maxPrimeFac
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))).sqrt)))
      True
  := by
  sorry
