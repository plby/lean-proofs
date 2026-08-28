import Wikipedia.HopfProblem.OrbitPairFinitePosetSubdivisionCompatibility

/-!
# Compatible finite iterations of face-poset subdivision

The iteration is a native functor on partially ordered sets. For a finite
initial poset, every stage is finite, and its nerve realization is
homeomorphic to the initial realization. These homeomorphisms commute
with every injective monotone map. No identification with iterated `SSet.sd`
on arbitrary simplicial sets is assumed or asserted.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open RealizationSimplex

def iteratedChains (r : ℕ) : PartOrd.{u} ⥤ PartOrd.{u} :=
  Nat.rec (𝟭 _) (fun _ F ↦ F ⋙ PartOrd.nonemptyFiniteChainsFunctor) r

instance iteratedChainsFinite (r : ℕ) (P : PartOrd.{u}) [Finite P] :
    Finite ((iteratedChains r).obj P) := by
  induction r with
  | zero => exact inferInstanceAs (Finite P)
  | succ r ih =>
    letI : Finite ((iteratedChains r).obj P) := ih
    exact inferInstanceAs (Finite (NonemptyFiniteChains ((iteratedChains r).obj P)))

theorem iteratedChains_map_injective (r : ℕ) {P Q : PartOrd.{u}} (f : P ⟶ Q)
    (hf : Function.Injective f) : Function.Injective ((iteratedChains r).map f) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    exact chainOrderHomMap_injective ((iteratedChains r).map f).hom ih

def iterationHomeomorph (P : PartOrd.{u}) [Fintype P] (r : ℕ) :
    SSet.toTop.obj (nerve ((iteratedChains r).obj P)) ≃ₜ SSet.toTop.obj (nerve P) := by
  induction r with
  | zero => exact Homeomorph.refl _
  | succ r ih =>
    letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
    exact (subdivisionHomeomorph ((iteratedChains r).obj P)).trans ih

theorem iterationHomeomorph_zero (P : PartOrd.{u}) [Fintype P]
    (z : SSet.toTop.obj (nerve P)) : iterationHomeomorph P 0 z = z := rfl

theorem iterationHomeomorph_succ (P : PartOrd.{u}) [Fintype P] (r : ℕ)
    (z : SSet.toTop.obj (nerve ((iteratedChains (r + 1)).obj P))) :
    iterationHomeomorph P (r + 1) z =
      letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
      iterationHomeomorph P r (subdivisionHomeomorph ((iteratedChains r).obj P) z) := rfl

theorem iterationHomeomorph_naturality (r : ℕ) {P Q : PartOrd.{u}}
    [Fintype P] [Fintype Q] (f : P ⟶ Q) (hf : Function.Injective f)
    (z : SSet.toTop.obj (nerve ((iteratedChains r).obj P))) :
    iterationHomeomorph Q r
      ((SSet.toTop.map (PartOrd.nerveFunctor.map ((iteratedChains r).map f))) z) =
      (SSet.toTop.map (PartOrd.nerveFunctor.map f)) (iterationHomeomorph P r z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
    letI : Fintype ((iteratedChains r).obj Q) := Fintype.ofFinite _
    change iterationHomeomorph Q r
      (subdivisionHomeomorph ((iteratedChains r).obj Q)
        ((SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap
          ((iteratedChains r).map f).hom).monotone.functor)) z)) = _
    exact (congrArg (iterationHomeomorph Q r)
      (subdivisionHomeomorph_naturality ((iteratedChains r).obj P)
        ((iteratedChains r).map f).hom (iteratedChains_map_injective r f hf) z)).trans
      (ih (subdivisionHomeomorph ((iteratedChains r).obj P) z))

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
