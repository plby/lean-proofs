import ErdosProblems.Erdos73.DeletedComponents

/-! One representative in each deleted component meeting a specified finite set. -/

namespace Erdos73

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open scoped Classical in
theorem exists_deletedComponent_representatives (W S : Finset V)
    (hodd : ∀ C : (vertexDeletedGraph G W).ConnectedComponent,
      Odd C.supp.ncard → (S ∩ deletedComponentVertices C).Nonempty) :
    ∃ Z : Finset V, Z ⊆ S \ W ∧
      (vertexDeletedGraph G W).oddComponents.ncard ≤ Z.card ∧
      (∀ C : (vertexDeletedGraph G W).ConnectedComponent,
        (S ∩ deletedComponentVertices C).Nonempty →
          (Z ∩ deletedComponentVertices C).Nonempty) ∧
      (∀ C : (vertexDeletedGraph G W).ConnectedComponent,
        ∀ x ∈ Z, ∀ y ∈ Z,
          x ∈ deletedComponentVertices C → y ∈ deletedComponentVertices C → x = y) := by
  classical
  let I := {C : (vertexDeletedGraph G W).ConnectedComponent //
    (S ∩ deletedComponentVertices C).Nonempty}
  let z (i : I) : V := i.property.choose
  have hz (i : I) : z i ∈ S ∩ deletedComponentVertices i.val := i.property.choose_spec
  have hzinj : Function.Injective z := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (deletedComponentVertices_disjoint hne)
      (Finset.mem_inter.mp (hz i)).2 (hij ▸ (Finset.mem_inter.mp (hz j)).2)
  let Z := Finset.univ.image z
  have hcard : Z.card = Fintype.card I := by
    rw [Finset.card_image_of_injective _ hzinj, Finset.card_univ]
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hiS, hiC⟩ := Finset.mem_inter.mp (hz i)
    exact Finset.mem_sdiff.mpr ⟨hiS, deletedComponentVertices_not_mem _ hiC⟩
  · let f : (vertexDeletedGraph G W).oddComponents ↪ I :=
      ⟨fun C => ⟨C.val, hodd C.val C.property⟩, fun _ _ he =>
        Subtype.ext (congrArg (fun x : I => x.val) he)⟩
    have hh := Fintype.card_le_of_embedding f
    rw [hcard]
    simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] using hh
  · intro C hC
    let i : I := ⟨C, hC⟩
    exact ⟨z i, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      (Finset.mem_inter.mp (hz i)).2⟩⟩
  · intro C x hx y hy hxC hyC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hiC : i.val = C := by
      by_contra he
      exact Finset.disjoint_left.mp (deletedComponentVertices_disjoint he)
        (Finset.mem_inter.mp (hz i)).2 hxC
    have hjC : j.val = C := by
      by_contra he
      exact Finset.disjoint_left.mp (deletedComponentVertices_disjoint he)
        (Finset.mem_inter.mp (hz j)).2 hyC
    exact congrArg z (Subtype.ext (hiC.trans hjC.symm))

end Erdos73
