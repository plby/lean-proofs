import Wikipedia.HopfProblem.OrbitPairRealizationRelations

/-!
# Descending compatible continuous simplex maps

The native quotient presentation supplies continuous maps out of realization
from continuous maps on its characteristic simplices, provided compatibility
is checked for every simplicial operator, not only for faces.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet) {Y : Type*} [TopologicalSpace Y]

def cellParameterMap (c : ∀ n, S _⦋n⦌ → C(Simplex n, Y)) : C(Parameters S, Y) where
  toFun a := c a.1.1 a.1.2 a.2
  continuous_toFun := continuous_sigma (fun a ↦ (c a.1 a.2).continuous)

theorem cellParameterMap_factorsThrough (c : ∀ n, S _⦋n⦌ → C(Simplex n, Y))
    (hc : ∀ m n (f : ⦋m⦌ ⟶ ⦋n⦌) (x : S _⦋n⦌),
      c m (S.map f.op x) = (c n x).comp (SimplexCategory.toTop₀.map f).hom) :
    Function.FactorsThrough (cellParameterMap S c) (projection S) := by
  intro a b hab
  have h := (projection_eq_iff S a b).mp hab
  clear hab
  induction h with
  | rel a b h =>
      cases h with
      | of_map m n f x t =>
          exact congrArg (fun g : C(Simplex m, Y) ↦ g t) (hc m n f x)
  | refl => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

def descend (c : ∀ n, S _⦋n⦌ → C(Simplex n, Y))
    (hc : ∀ m n (f : ⦋m⦌ ⟶ ⦋n⦌) (x : S _⦋n⦌),
      c m (S.map f.op x) = (c n x).comp (SimplexCategory.toTop₀.map f).hom) :
    C(SSet.toTop.obj S, Y) :=
  (projection_isQuotientMap S).lift (cellParameterMap S c)
    (cellParameterMap_factorsThrough S c hc)

theorem descend_characteristic (c : ∀ n, S _⦋n⦌ → C(Simplex n, Y))
    (hc : ∀ m n (f : ⦋m⦌ ⟶ ⦋n⦌) (x : S _⦋n⦌),
      c m (S.map f.op x) = (c n x).comp (SimplexCategory.toTop₀.map f).hom)
    (n : ℕ) (x : S _⦋n⦌) (t : Simplex n) :
    descend S c hc (characteristic S n x t) = c n x t := by
  exact congrArg (fun g : C(Parameters S, Y) ↦ g ⟨⟨n, x⟩, t⟩)
    ((projection_isQuotientMap S).lift_comp (cellParameterMap S c)
      (cellParameterMap_factorsThrough S c hc))

theorem continuousMap_ext_characteristic (f g : C(SSet.toTop.obj S, Y))
    (h : ∀ n (x : S _⦋n⦌) (t : Simplex n), f (characteristic S n x t) =
      g (characteristic S n x t)) : f = g := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨n, x, t, rfl⟩ := exists_characteristic S z
  exact h n x t

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
