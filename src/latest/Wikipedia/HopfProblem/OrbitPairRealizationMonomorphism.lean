import Wikipedia.HopfProblem.OrbitPairRealizationNormalParameters
import Wikipedia.HopfProblem.OrbitPairRealizationNaturality

/-!
# Monomorphisms are injective on native geometric realizations

A simplicial monomorphism preserves nondegeneracy and hence sends normal
parameters to normal parameters. Uniqueness of normal forms then proves
injectivity of the actual realized map.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable {S T : SSet}

def mapParameters (f : S ⟶ T) (p : Parameters S) : Parameters T :=
  ⟨⟨p.1.1, f.app (Opposite.op ⦋p.1.1⦌) p.1.2⟩, p.2⟩

theorem mapParameters_projection (f : S ⟶ T) (p : Parameters S) :
    projection T (mapParameters f p) = (SSet.toTop.map f) (projection S p) :=
  (realizedMap_characteristic f p.1.1 p.1.2 p.2).symm

theorem mapParameters_injective (f : S ⟶ T) [Mono f] :
    Function.Injective (mapParameters f) := by
  rintro ⟨⟨n, x⟩, t⟩ ⟨⟨m, y⟩, v⟩ h
  have hnm : n = m := congrArg (fun p : Parameters T ↦ p.1.1) h
  subst m
  have hxy : f.app (Opposite.op ⦋n⦌) x = f.app (Opposite.op ⦋n⦌) y :=
    eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Sigma.fst h)).2
  have hxy' : x = y := injective_of_mono (f.app (Opposite.op ⦋n⦌)) hxy
  subst y
  have htv : t = v := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst v
  rfl

theorem mapParameters_isNormal (f : S ⟶ T) [Mono f] (p : Parameters S)
    (hp : IsNormal S p) : IsNormal T (mapParameters f p) :=
  ⟨(SSet.nonDegenerate_iff_of_mono f p.1.2).mpr hp.1, hp.2⟩

theorem normalParameters_realizedMap (f : S ⟶ T) [Mono f] (z : SSet.toTop.obj S) :
    normalParameters T ((SSet.toTop.map f) z) = mapParameters f (normalParameters S z) := by
  apply normal_injective T (normalParameters_isNormal T _)
    (mapParameters_isNormal f _ (normalParameters_isNormal S z))
  have hp := (mapParameters_projection f (normalParameters S z)).trans
    (congrArg (SSet.toTop.map f) (projection_normalParameters S z))
  exact (projection_normalParameters T _).trans hp.symm

theorem realizedMap_injective (f : S ⟶ T) [Mono f] :
    Function.Injective (SSet.toTop.map f) := by
  intro x y h
  apply normalParameters_injective S
  apply mapParameters_injective f
  rw [← normalParameters_realizedMap f x, ← normalParameters_realizedMap f y, h]

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
