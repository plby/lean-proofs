import Wikipedia.NoExoticSixSphere.ChainBiproductElements

/-!
# Original biproduct elements and the chain differential

The actual lifted map is the pair of its two component values. The
native differential acts on pairs by the two native differentials.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.ChainBiproduct

variable {K L N : ChainComplex (ModuleCat.{0} ℤ) ℕ}

theorem lift_eq_pair (f : N ⟶ K) (g : N ⟶ L) (n : ℕ) (a : N.X n) :
    ((biprod.lift f g).f n).hom a = pair n ((f.f n).hom a) ((g.f n).hom a) :=
  congrArg (fun m : N ⟶ K ⊞ L => (m.f n).hom a) (show
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr from biprod.lift_eq)

theorem boundary_pair (i j : ℕ) (a : K.X i) (b : L.X i) :
    ((K ⊞ L).d i j).hom (pair i a b) = pair j ((K.d i j).hom a) ((L.d i j).hom b) := by
  have h₁ := congrArg (fun m => m.hom a) ((biprod.inl : K ⟶ K ⊞ L).comm i j)
  have h₂ := congrArg (fun m => m.hom b) ((biprod.inr : L ⟶ K ⊞ L).comm i j)
  exact (((K ⊞ L).d i j).hom.map_add _ _).trans (congrArg₂ (fun x y => x + y) h₁ h₂)

end NoExoticSixSphere.ChainBiproduct
