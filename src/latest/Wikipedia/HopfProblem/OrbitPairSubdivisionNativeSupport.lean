import Wikipedia.HopfProblem.OrbitPairSubdivisionSupportSystem

/-!
# Native support systems for ordinary and dual subdivision

Every field of the support laws is proved here for the actual
cosimplicial models. The supporting faces are the explicit restrictions
already constructed, not assumed witnesses.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionSupport

open Subdivision

def chainVertexSet {n : ℕ} (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    Set (Fin (n + 1)) := {i | ULift.up i ∈ F.finset}

theorem chainVertexSet_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (F : NonemptyFiniteChains (ULift.{u} (Fin (m + 1)))) :
    chainVertexSet (F.map (SimplexCategory.toPartOrd.map f).hom) =
      f.toOrderHom '' chainVertexSet F := by
  ext j
  let g : ULift.{u} (Fin (m + 1)) →o ULift.{u} (Fin (n + 1)) :=
    (SimplexCategory.toPartOrd.map f).hom
  change ULift.up j ∈ (F.map g).finset ↔
    ∃ i, ULift.up i ∈ F.finset ∧ f.toOrderHom i = j
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨⟨i⟩, hi, hij⟩
    exact ⟨i, hi, congrArg ULift.down hij⟩
  · rintro ⟨i, hi, hij⟩
    exact ⟨ULift.up i, hi, congrArg ULift.up hij⟩

theorem chainVertexSet_full {n : ℕ} (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (hF : F.finset = Finset.univ) : chainVertexSet F = Set.univ := by
  ext i
  change ULift.up i ∈ F.finset ↔ True
  rw [hF]
  simp only [Finset.mem_univ]

theorem simplexOperator_ulift_injective {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] :
    Function.Injective (SimplexCategory.toPartOrd.{u}.map f).hom := by
  intro i j h
  apply ULift.ext
  exact (SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f))
    (congrArg ULift.down h)

theorem standardOperator_injective {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] (k : ℕ) :
    Function.Injective ((SimplexCategory.sd.{u}.map f).app (Opposite.op ⦋k⦌)) := by
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  apply FinitePoset.chainOrderHomMap_injective (SimplexCategory.toPartOrd.{u}.map f).hom
    (simplexOperator_ulift_injective f)
  exact congrArg (fun a ↦ a.obj i) h

theorem dualStandardOperator_injective {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] (k : ℕ) :
    Function.Injective ((dualStandard.{u}.map f).app (Opposite.op ⦋k⦌)) := by
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  apply FinitePoset.chainOrderHomMap_injective (SimplexCategory.toPartOrd.{u}.map f).hom
    (simplexOperator_ulift_injective f)
  exact congrArg (fun a ↦ a.obj i) h

def sdLaw (k : ℕ) : Law SimplexCategory.sd.{u} k where
  support _ t := chainVertexSet (faceSupport t)
  support_map f t := chainVertexSet_map f (faceSupport t)
  map_injective := by
    intro m n f hf
    exact standardOperator_injective f k

def dualLaw (k : ℕ) : Law dualStandard.{u} k where
  support _ t := chainVertexSet (dualFaceSupport t)
  support_map f t := chainVertexSet_map f (dualFaceSupport t)
  map_injective := by
    intro m n f hf
    exact dualStandardOperator_injective f k

def sdFace (k n : ℕ) (t : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) :
    Face (sdLaw k) n t where
  dim := (faceSupport t).finset.card - 1
  inclusion := simplexFaceInclusion (faceSupport t)
  mono_inclusion := inferInstance
  point := restrictFaceSimplex t
  full := chainVertexSet_full _ (restrictFaceSimplex_full_support t)
  map_point := map_restrictFaceSimplex t

def dualFace (k n : ℕ) (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    Face (dualLaw k) n t where
  dim := (dualFaceSupport t).finset.card - 1
  inclusion := simplexFaceInclusion (dualFaceSupport t)
  mono_inclusion := inferInstance
  point := restrictDualFaceSimplex t
  full := chainVertexSet_full _ (restrictDualFaceSimplex_full_support t)
  map_point := map_restrictDualFaceSimplex t

end Wikipedia.HopfProblem.OrbitPair.SubdivisionSupport
