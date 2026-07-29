import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Real Metric Set InnerProductSpace Complex
open scoped InnerProductSpace Pointwise Complex
attribute [local instance] Classical.propDecidable
namespace Erdos93
section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]

noncomputable def distinctDistances (s : Finset V) : Finset ℝ :=
  (s.product s).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]
set_option maxHeartbeats 200000 in
set_option maxHeartbeats 200000 in
end
end Erdos93

attribute [local instance] Classical.propDecidable

universe u_1 u_2

theorem Erdos93.altman_erdos :
    ∀ {V : Type u_2} [inst : NormedAddCommGroup.{u_2} V]
      [inst_1 :
        @InnerProductSpace.{0, u_2} Real V Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst)]
      [@FiniteDimensional.{0, u_2} Real V Real.instDivisionRing
          (@NormedAddCommGroup.toAddCommGroup.{u_2} V inst)
          (@NormedSpace.toModule.{0, u_2} Real V Real.normedField
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst)
            (@InnerProductSpace.toNormedSpace.{0, u_2} Real V Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst) inst_1))]
      [Fact
          (@Eq.{1} Nat
            (@Module.finrank.{0, u_2} Real V Real.semiring
              (@AddCommGroup.toAddCommMonoid.{u_2} V (@NormedAddCommGroup.toAddCommGroup.{u_2} V inst))
              (@NormedSpace.toModule.{0, u_2} Real V Real.normedField
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst) inst_1)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))]
      (s : Finset.{u_2} V) (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n →
        @Eq.{1} Nat (@Finset.card.{u_2} V s) n →
          @ConvexIndependent.{0, u_2, u_2} Real V
              (@Subtype.{u_2 + 1} V fun (x : V) ↦
                @Membership.mem.{u_2, u_2} V (Finset.{u_2} V)
                  (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} V) V (@Finset.instSetLike.{u_2} V))
                  s x)
              Real.semiring Real.partialOrder (@NormedAddCommGroup.toAddCommGroup.{u_2} V inst)
              (@NormedSpace.toModule.{0, u_2} Real V Real.normedField
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst)
                (@InnerProductSpace.toNormedSpace.{0, u_2} Real V Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_2} V inst) inst_1))
              (@Subtype.val.{u_2 + 1} V fun (x : V) ↦
                @Membership.mem.{u_2, u_2} V (Finset.{u_2} V)
                  (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} V) V (@Finset.instSetLike.{u_2} V))
                  s x) →
            @GE.ge.{0} Nat instLENat (@Finset.card.{0} Real (@Erdos93.distinctDistances.{u_2} V inst s))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry
