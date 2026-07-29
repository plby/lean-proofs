import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos639

variable {V : Type*} {C : Sym2 V → Fin 2} {u v w x y z : V}

variable (C) in
def NIMT (x y : V) : Prop :=
  x ≠ y ∧ ¬∃ z, x ≠ z ∧ y ≠ z ∧ C s(x, y) = C s(x, z) ∧ C s(x, y) = C s(y, z)
namespace NIMT

lemma symm (hxy : NIMT C x y) : NIMT C y x := by
  grind [NIMT]

lemma irrefl : ¬NIMT C x x := by
  simp [NIMT]

end NIMT

open Finset

namespace SimpleGraph

open _root_.SimpleGraph

variable (C) in
def nimt : SimpleGraph V where
  Adj := NIMT C
  symm.symm _ _ e := NIMT.symm (C := C) e
  loopless := ⟨fun _ ↦ NIMT.irrefl⟩
variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (V) in
abbrev n : ℕ := Fintype.card V
variable [DecidableEq V]

instance : DecidableRel (NIMT C) := by
  unfold NIMT
  infer_instance
instance : DecidableRel (nimt C).Adj :=
  inferInstanceAs <| DecidableRel (NIMT C)
end SimpleGraph

end Erdos639

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos639.SimpleGraph.erdos639 :
    ∀ {V : Type u_1}
      {C : Sym2.{u_1} V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))}
      [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V],
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
          (@Erdos639.SimpleGraph.n.{u_1} V inst) →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{u_1} (Sym2.{u_1} V)
            (@SimpleGraph.edgeFinset.{u_1} V (@Erdos639.SimpleGraph.nimt.{u_1} V C)
              (@SimpleGraph.fintypeEdgeSet.{u_1} V (@Erdos639.SimpleGraph.nimt.{u_1} V C)
                (@Sym2.instFintype.{u_1} V inst) fun (a b : V) ↦
                @Erdos639.SimpleGraph.instDecidableRelAdjNimt.{u_1} V C inst inst_1 a b)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@Erdos639.SimpleGraph.n.{u_1} V inst)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
