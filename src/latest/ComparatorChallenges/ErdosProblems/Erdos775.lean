import Mathlib.Data.Finset.Card

attribute [local instance] Classical.propDecidable

universe u_1

namespace Erdos775

structure KUniformHypergraph (α : Type*) (k : ℕ) where
  edges : Set (Finset α)
  uniform : ∀ e ∈ edges, e.card = k

end Erdos775

noncomputable def Erdos775.KUniformHypergraph.IsClique :
    {α : Type u_1} → {k : Nat} → Erdos775.KUniformHypergraph.{u_1} α k → Finset.{u_1} α → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos775.erdos_problem_775 :
    ∀ (C : Nat),
      @Exists.{1} Nat fun (N : Nat) ↦
        ∀ (n : Nat),
          @GE.ge.{0} Nat instLENat n N →
            ∀
              (H :
                Erdos775.KUniformHypergraph.{0} (Fin n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (sizes : Finset.{0} Nat),
              (∀ (s : Nat),
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                        (@Finset.instSetLike.{0} Nat))
                      sizes s →
                    @Exists.{1} (Finset.{0} (Fin n)) fun (S : Finset.{0} (Fin n)) ↦
                      And
                        (@Erdos775.KUniformHypergraph.IsClique.{0} (Fin n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) H S)
                        (@Eq.{1} Nat (@Finset.card.{0} (Fin n) S) s)) →
                @LE.le.{0} Nat instLENat (@Finset.card.{0} Nat sizes)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n C)
  := by
  sorry
