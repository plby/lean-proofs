import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Elements in the original chain-complex biproduct

The two native injections construct an element with prescribed original
projections. Maps out of the actual biproduct retain the usual sum
formula, without replacing any chain-complex object by a product model.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.ChainBiproduct

variable {K L N : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- The element formed by the original two biproduct injections. -/
def pair (n : ℕ) (a : K.X n) (b : L.X n) : (K ⊞ L).X n :=
  ((biprod.inl : K ⟶ K ⊞ L).f n).hom a + ((biprod.inr : L ⟶ K ⊞ L).f n).hom b

theorem fst_pair (n : ℕ) (a : K.X n) (b : L.X n) :
    ((biprod.fst : K ⊞ L ⟶ K).f n).hom (pair n a b) = a := by
  have h₁ := congrArg (fun f : K ⟶ K => (f.f n).hom a) (biprod.inl_fst (X := K) (Y := L))
  have h₂ := congrArg (fun f : L ⟶ K => (f.f n).hom b) (biprod.inr_fst (X := K) (Y := L))
  exact (((biprod.fst : K ⊞ L ⟶ K).f n).hom.map_add _ _).trans
    ((congrArg₂ (fun x y => x + y) h₁ h₂).trans (add_zero a))

theorem snd_pair (n : ℕ) (a : K.X n) (b : L.X n) :
    ((biprod.snd : K ⊞ L ⟶ L).f n).hom (pair n a b) = b := by
  have h₁ := congrArg (fun f : K ⟶ L => (f.f n).hom a) (biprod.inl_snd (X := K) (Y := L))
  have h₂ := congrArg (fun f : L ⟶ L => (f.f n).hom b) (biprod.inr_snd (X := K) (Y := L))
  exact (((biprod.snd : K ⊞ L ⟶ L).f n).hom.map_add _ _).trans
    ((congrArg₂ (fun x y => x + y) h₁ h₂).trans (zero_add b))

/-- The original sum map acts by the two supplied original chain maps. -/
theorem desc_pair (f : K ⟶ N) (g : L ⟶ N) (n : ℕ) (a : K.X n) (b : L.X n) :
    ((biprod.desc f g).f n).hom (pair n a b) = (f.f n).hom a + (g.f n).hom b := by
  have h₁ := congrArg (fun m : K ⟶ N => (m.f n).hom a) (biprod.inl_desc f g)
  have h₂ := congrArg (fun m : L ⟶ N => (m.f n).hom b) (biprod.inr_desc f g)
  exact (((biprod.desc f g).f n).hom.map_add _ _).trans (congrArg₂ (fun x y => x + y) h₁ h₂)

/-- Projecting the original lifted map recovers its first supplied chain map. -/
theorem fst_lift (f : N ⟶ K) (g : N ⟶ L) (n : ℕ) (a : N.X n) :
    ((biprod.fst : K ⊞ L ⟶ K).f n).hom (((biprod.lift f g).f n).hom a) = (f.f n).hom a :=
  congrArg (fun m : N ⟶ K => (m.f n).hom a) (biprod.lift_fst f g)

end NoExoticSixSphere.ChainBiproduct
