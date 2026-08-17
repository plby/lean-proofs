import ErdosProblems.Erdos780.External.TargetChains
import ErdosProblems.Erdos780.External.FinsetOrientation

open Function

namespace TargetChains

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable {W : Type v} [Fintype W] [LinearOrder W]

theorem map_single_of_injOn (f : V → W) (s : Finset V)
    (hf : Set.InjOn f s) :
    map (R := ℤ) f (Finsupp.single s 1) =
      Finsupp.single (s.image f)
        ((Finset.imageSign s f hf : ℤˣ) : ℤ) := by
  apply (toExterior ℤ W).injective
  rw [toExterior_map_single, toExterior_single]
  change ExteriorAlgebra.map (vertexMap f)
      ((vertexBasis ℤ V).ExteriorAlgebra s) =
    ((Finset.imageSign s f hf : ℤˣ) : ℤ) •
      (vertexBasis ℤ W).ExteriorAlgebra (s.image f)
  rw [ExteriorAlgebra.basis_apply (vertexBasis ℤ V) s,
    ExteriorAlgebra.basis_apply_ofCard (vertexBasis ℤ W)
      (Finset.card_image_of_injOn hf),
    ExteriorAlgebra.map_apply_ιMulti]
  simp only [Set.powersetCard.prodEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_family, Finset.imageSign]
  let v : Fin s.card → (W →₀ ℤ) :=
    (vertexBasis ℤ W) ∘
      Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard (Finset.card_image_of_injOn hf))
  let σ : Equiv.Perm (Fin s.card) := Finset.imagePerm s f hf
  have hfamily :
      (vertexMap f) ∘ (vertexBasis ℤ V) ∘
          Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofCard rfl) =
        v ∘ σ := by
    funext i
    simp only [Function.comp_apply, vertexBasis, v, σ,
      Finsupp.coe_basisSingleOne, vertexMap_single]
    congr 1
    exact congrArg Subtype.val
      ((s.image f).orderIsoOfFin (Finset.card_image_of_injOn hf) |>.apply_symm_apply
        ⟨f (s.orderIsoOfFin rfl i), Finset.mem_image_of_mem f
          (s.orderIsoOfFin rfl i).2⟩) |>.symm
  rw [hfamily]
  exact AlternatingMap.map_perm (ExteriorAlgebra.ιMulti ℤ s.card) v σ

end TargetChains
