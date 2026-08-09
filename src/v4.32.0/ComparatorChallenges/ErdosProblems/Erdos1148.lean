import Mathlib.Analysis.Real.Sqrt
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1148

def R_star_disc (d : ℤ) : Set (ℤ × ℤ × ℤ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = d ∧ Int.gcd t.1 (Int.gcd t.2.1 t.2.2) = 1 }
def V_disc_plus_1 : Set (ℝ × ℝ × ℝ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 1 }
def Omega_strict : Set (ℝ × ℝ × ℝ) :=
  { t | t ∈ V_disc_plus_1 ∧ |t.1 - t.2.2| < 1 ∧ |t.2.1| < 1 ∧ |t.1 + t.2.2| < 1 }
noncomputable def project_to_hyperboloid (n : ℤ) (t : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  let s := Real.sqrt (4 * (n : ℝ))
  ((t.1 : ℝ) / s, (t.2.1 : ℝ) / s, (t.2.2 : ℝ) / s)
def DukeTheoremStatement : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N →
  ∃ t ∈ R_star_disc (4 * n),
    project_to_hyperboloid n t ∈ Omega_strict ∧
    t.1 % 2 = t.2.2 % 2
end Erdos1148

attribute [local instance] Classical.propDecidable

theorem Erdos1148.erdos_problem_1148 :
    Erdos1148.DukeTheoremStatement →
      @Exists.{1} Int fun (N : Int) ↦
        ∀ (n : Int),
          @GE.ge.{0} Int Int.instLEInt n N →
            @Exists.{1} Int fun (x : Int) ↦
              @Exists.{1} Int fun (y : Int) ↦
                @Exists.{1} Int fun (z : Int) ↦
                  And
                    (@Eq.{1} Int n
                      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            y (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat
                            (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                          z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (@LE.le.{0} Int Int.instLEInt
                      (@Max.max.{0} Int Int.instMax
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat
                            (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                          x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Max.max.{0} Int Int.instMax
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            y (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HPow.hPow.{0, 0, 0} Int Nat Int
                            (@instHPow.{0, 0} Int Nat
                              (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                            z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      n)
  := by
  sorry
