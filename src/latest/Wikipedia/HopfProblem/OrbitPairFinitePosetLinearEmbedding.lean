import Wikipedia.HopfProblem.OrbitPairFinitePosetSubdivisionMap
import Wikipedia.HopfProblem.OrbitPairRealizationMonomorphism
import Mathlib.Order.Extension.Linear

/-!
# Comparing finite-poset subdivisions with a standard simplex

A finite poset has a monotone injection into a finite linear order, obtained
from the native linear-extension theorem. Injective monotone maps induce
monomorphisms both on nerves and on nerves of nonempty face chains.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

variable (P : Type u) [PartialOrder P] [Fintype P]

def linearEmbedding :
    {f : P →o ULift.{u} (Fin (Fintype.card P + 1)) // Function.Injective f} := by
  letI : Fintype (LinearExtension P) := inferInstanceAs (Fintype P)
  let e : Fin (Fintype.card P) ≃o LinearExtension P :=
    Fintype.orderIsoFinOfCardEq (LinearExtension P) rfl
  refine ⟨{ toFun := fun p ↦ ULift.up (e.symm (toLinearExtension p)).castSucc
            monotone' := fun p q hpq ↦ e.symm.monotone (toLinearExtension.monotone hpq) }, ?_⟩
  intro p q hpq
  exact e.symm.injective (Fin.castSucc_injective (Fintype.card P) (ULift.up_injective hpq))

variable {P} {Q : Type u} [PartialOrder Q]

omit [Fintype P] in
theorem nerveMap_mono (f : P →o Q) (hf : Function.Injective f) :
    Mono (nerveMap f.monotone.functor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply ConcreteCategory.mono_of_injective
  intro x y hxy
  apply nerve.ext_of_isThin
  funext i
  exact hf (congrArg (fun a ↦ a.obj i) hxy)

omit [Fintype P] in
theorem chainOrderHomMap_injective (f : P →o Q) (hf : Function.Injective f) :
    Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  intro A B h
  apply NonemptyFiniteChains.ext
  have he := congrArg NonemptyFiniteChains.finset h
  change Finset.image f A.finset = Finset.image f B.finset at he
  exact Finset.image_injective hf he

omit [Fintype P] in
theorem chainNerveMap_mono (f : P →o Q) (hf : Function.Injective f) :
    Mono (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor) :=
  nerveMap_mono (NonemptyFiniteChains.orderHomMap f) (chainOrderHomMap_injective f hf)

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
