import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos798

noncomputable section

open Finset Int Real Filter Topology

variable {d : ℕ} [d.AtLeastTwo] {v : Fin d → ℤ}

def cube (d n : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ ↦ Icc 1 n
section MaxAbs

end MaxAbs

def Covers (a b c : Fin d → ℤ) : Prop :=
  ∃ t q : ℤ, q ≠ 0 ∧ (q - t) • a + t • b = q • c

def IsCubeCover (n : ℕ) (S : Finset (Fin d → ℤ)) : Prop :=
  S ⊆ cube d n ∧ ∀ x ∈ cube d n, ∃ y z, y ∈ S ∧ z ∈ S ∧ Covers y z x

variable (d) in
open scoped Classical in
def minCoverSize (n : ℕ) : ℕ :=
  {c ∈ Finset.range (n ^ d + 1) | ∃ S : Finset (Fin d → ℤ), #S = c ∧ IsCubeCover n S}.min'
  ⟨n ^ d, by
    simp_rw [mem_filter, mem_range_succ_iff, le_rfl, true_and]
    exact ⟨cube d n, by simp [cube], subset_rfl,
      fun a ma ↦ ⟨_, _, ma, ma, ⟨0, 1, by simp, by simp⟩⟩⟩⟩
end

end Erdos798

attribute [local instance] Classical.propDecidable

theorem Erdos798.erdos798 :
    @Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (fun (n : Nat) ↦
        @Nat.cast.{0} Real Real.instNatCast
          (Erdos798.minCoverSize (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      fun (n : Nat) ↦
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast n)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n))
  := by
  sorry
