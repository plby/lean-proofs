import Wikipedia.HopfProblem.SheafCupProductCofaceCocycles

/-!
# Actual coefficient morphisms of the ring-coface data

A morphism is a degreewise ring map commuting with the cofaces.
Commutation with the alternating differential and with the literal
Alexander–Whitney product are consequences, not additional hypotheses.
-/

universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface.Data

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable {S0 : Type v₀} {S1 : Type v₁} {S2 : Type v₂} {S3 : Type v₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable [CommRing S0] [CommRing S1] [CommRing S2] [CommRing S3]

structure Morphism (D : Coface.Data R0 R1 R2 R3) (E : Coface.Data S0 S1 S2 S3) where
  f0 : R0 →+* S0
  f1 : R1 →+* S1
  f2 : R2 →+* S2
  f3 : R3 →+* S3
  comm0 : ∀ i, f1.comp (D.δ0 i) = (E.δ0 i).comp f0
  comm1 : ∀ i, f2.comp (D.δ1 i) = (E.δ1 i).comp f1
  comm2 : ∀ i, f3.comp (D.δ2 i) = (E.δ2 i).comp f2

namespace Morphism

variable {D : Coface.Data R0 R1 R2 R3} {E : Coface.Data S0 S1 S2 S3}
variable (M : D.Morphism E)

theorem comm0_apply (i : Fin 2) (r : R0) : M.f1 (D.δ0 i r) = E.δ0 i (M.f0 r) :=
  congrArg (fun f : R0 →+* S1 => f r) (M.comm0 i)

theorem comm1_apply (i : Fin 3) (a : R1) : M.f2 (D.δ1 i a) = E.δ1 i (M.f1 a) :=
  congrArg (fun f : R1 →+* S2 => f a) (M.comm1 i)

theorem comm2_apply (i : Fin 4) (a : R2) : M.f3 (D.δ2 i a) = E.δ2 i (M.f2 a) :=
  congrArg (fun f : R2 →+* S3 => f a) (M.comm2 i)

theorem d0_comm (r : R0) : M.f1 (D.d0 r) = E.d0 (M.f0 r) := by
  simp only [d0_apply, map_sub, M.comm0_apply]

theorem d1_comm (a : R1) : M.f2 (D.d1 a) = E.d1 (M.f1 a) := by
  simp only [d1_apply, map_sub, map_add, M.comm1_apply]

theorem d2_comm (a : R2) : M.f3 (D.d2 a) = E.d2 (M.f2 a) := by
  simp only [d2_apply, map_sub, map_add, M.comm2_apply]

theorem cupOne_comm (a b : R1) : M.f2 (D.cupOne a b) = E.cupOne (M.f1 a) (M.f1 b) := by
  simp only [cupOne, map_mul, M.comm1_apply]

def cocycleOneMap : D.CocycleOne →+ E.CocycleOne where
  toFun a := ⟨M.f1 a, by
    change E.d1 (M.f1 a) = 0
    rw [← M.d1_comm, a.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero M.f1)
  map_add' a b := Subtype.ext (map_add M.f1 (a : R1) (b : R1))

def cocycleTwoMap : D.CocycleTwo →+ E.CocycleTwo where
  toFun a := ⟨M.f2 a, by
    change E.d2 (M.f2 a) = 0
    rw [← M.d2_comm, a.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero M.f2)
  map_add' a b := Subtype.ext (map_add M.f2 (a : R2) (b : R2))

@[simp] theorem cocycleOneMap_coe (a : D.CocycleOne) :
    (M.cocycleOneMap a : S1) = M.f1 a := rfl

@[simp] theorem cocycleTwoMap_coe (a : D.CocycleTwo) :
    (M.cocycleTwoMap a : S2) = M.f2 a := rfl

theorem cocycleOneMap_boundary (r : R0) :
    M.cocycleOneMap (D.boundaryOne r) = E.boundaryOne (M.f0 r) :=
  Subtype.ext (M.d0_comm r)

theorem cocycleTwoMap_boundary (a : R1) :
    M.cocycleTwoMap (D.boundaryTwo a) = E.boundaryTwo (M.f1 a) :=
  Subtype.ext (M.d1_comm a)

theorem cocycleTwoMap_cup (a b : D.CocycleOne) :
    M.cocycleTwoMap (D.cupCocycle a b) = E.cupCocycle (M.cocycleOneMap a) (M.cocycleOneMap b) :=
  Subtype.ext (M.cupOne_comm a b)

end Morphism

end Wikipedia.HopfProblem.SheafCupProduct.Coface.Data
