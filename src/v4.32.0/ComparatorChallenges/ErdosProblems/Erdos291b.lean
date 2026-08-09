import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Complex.Exponential
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos291b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 300000

def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id
def X (r : ℕ → ℤ) (n : ℕ) : ℚ := (L n : ℚ) * ∑ i ∈ Finset.Icc 1 n, (r i : ℚ) / i
def z (m : ℕ) : ℕ := ((Finset.range m).filter Nat.Prime).card
structure ProblemParameters where
  r : ℕ → ℤ
  m : ℕ
  tilde_m : ℕ
  q0 : ℕ
  hm4 : 4 ≤ m
  h_r_nz : ∀ i, r i ≠ 0
  h_r_bdd : ∀ i, |r i| < m
  htilde_m : 20 * m^(2 * z m) < tilde_m
  hq0_prime : q0.Prime
  hq0_dvd : q0 ∣ tilde_m
  hq0_large : m^(2 * z m - 1) < q0
  h_priemteller : (m : ℝ)^(2 * z m) < Real.exp (2.52 * m)
  h_bla0 : ∀ w ∈ Finset.Ico (tilde_m - m^(2 * z m - 1)) tilde_m, ∀ k, L (w + k) > 2^(w + k)
def J1' (p : ProblemParameters) : Finset ℕ := Finset.Ico (p.tilde_m - p.m^(2 * z p.m - 1)) p.tilde_m
def J2' (p : ProblemParameters) : Finset ℕ := Finset.Ico p.tilde_m (p.tilde_m + p.m^(2 * z p.m - 1))
def X_int (r : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, r i * ((L n) / i : ℕ)
noncomputable def I0 (p : ProblemParameters) : Finset ℕ :=
  if ∀ n ∈ J1' p, |X p.r n| > (n : ℚ)^(z p.m) then J1' p else J2' p
end Erdos291b

attribute [local instance] Classical.propDecidable

namespace Erdos291b

end Erdos291b

theorem Erdos291b.ohyeah1 :
    ∀ (p : Erdos291b.ProblemParameters),
      @Exists.{1} Nat fun (n : Nat) ↦
        And
          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (Erdos291b.I0 p) n)
          (@Exists.{1} Nat fun (q : Nat) ↦
            And (Nat.Prime q)
              (And (@GE.ge.{0} Nat instLENat q p.m)
                (@Dvd.dvd.{0} Nat Nat.instDvd q (Erdos291b.X_int p.r n).natAbs)))
  := by
  sorry
theorem Erdos291b.generalErdos291 :
    ∀ (r : Nat → Int) (t : Nat),
      @GT.gt.{0} Nat instLTNat t (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Function.Periodic.{0, 0} Nat Int instAddNat r t →
          (∀ (i : Nat), @Ne.{1} Int (r i) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
            (∀ (m : Nat),
                @GE.ge.{0} Nat instLENat m
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  @LT.lt.{0} Real Real.instLT
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat
                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Erdos291b.z m)))
                    (Real.exp
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfScientific.ofScientific.{0} Real
                          (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) (nat_lit 252)
                          Bool.true (nat_lit 2))
                        (@Nat.cast.{0} Real Real.instNatCast m)))) →
              (∀ (n : Nat),
                  @GE.ge.{0} Nat instLENat n
                      (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))) →
                    @GT.gt.{0} Nat instLTNat (Erdos291b.L n)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat
                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)) →
                ∀ (N : Nat),
                  @Exists.{1} Nat fun (b : Nat) ↦
                    @GT.gt.{0} Nat instLTNat ((Erdos291b.X_int r b).natAbs.gcd (Erdos291b.L b)) N
  := by
  sorry
