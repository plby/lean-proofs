import Wikipedia.HopfProblem.OrbitPairSubdivisionChainRestriction
import Wikipedia.HopfProblem.OrbitPairSubdivisionCoreParameters

/-!
# The smallest supporting face of a subdivision simplex

For an increasing face chain the support is its last face; for a decreasing
face chain it is its first face. Enumerating that support gives an actual
simplex-category monomorphism and a restricted native simplex whose image
is exactly the original one. Support commutes with every simplex operator,
including noninjective operators.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

def simplexFaceEmbedding {n : ℕ} (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    ULift.{u} (Fin (F.finset.card - 1 + 1)) ↪o ULift.{u} (Fin (n + 1)) :=
  ULift.orderIso.toOrderEmbedding.trans (chainEmbedding F)

theorem simplexFaceEmbedding_range {n : ℕ}
    (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    Set.range (simplexFaceEmbedding F) = (F.finset : Set (ULift.{u} (Fin (n + 1)))) := by
  rw [← chainEmbedding_range F]
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

theorem simplexFaceEmbedding_mem {n : ℕ}
    (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (i : ULift.{u} (Fin (F.finset.card - 1 + 1))) : simplexFaceEmbedding F i ∈ F.finset := by
  change simplexFaceEmbedding F i ∈ (F.finset : Set (ULift.{u} (Fin (n + 1))))
  rw [← simplexFaceEmbedding_range]
  exact ⟨i, rfl⟩

def simplexFaceInclusion {n : ℕ} (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    ⦋F.finset.card - 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ (chainEmbedding F i).down
      monotone' := fun _ _ h ↦ (chainEmbedding F).monotone h }

instance simplexFaceInclusion_mono {n : ℕ}
    (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) : Mono (simplexFaceInclusion F) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j h
  apply (chainEmbedding F).injective
  exact ULift.ext _ _ h

theorem simplexFaceInclusion_orderHom {n : ℕ}
    (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    (SimplexCategory.toPartOrd.{u}.map (simplexFaceInclusion F)).hom =
      (simplexFaceEmbedding F).toOrderHom := by
  ext i
  rfl

def faceSupport {n k : ℕ} (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) := x.obj (Fin.last k)

def dualFaceSupport {n k : ℕ} (x : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) := x.obj 0

theorem face_le_support {n k : ℕ} (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌)
    (i : Fin (k + 1)) : x.obj i ≤ faceSupport x := x.monotone (Fin.le_last i)

theorem dual_face_le_support {n k : ℕ} (x : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌)
    (i : Fin (k + 1)) : (show NonemptyFiniteChains _ from x.obj i) ≤ dualFaceSupport x :=
  x.monotone (Fin.zero_le i)

theorem faceSupport_map {m n k : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : (SimplexCategory.sd.{u}.obj ⦋m⦌) _⦋k⦌) :
    faceSupport ((SimplexCategory.sd.map f).app (Opposite.op ⦋k⦌) x) =
      (faceSupport x).map (SimplexCategory.toPartOrd.map f).hom := rfl

theorem dualFaceSupport_map {m n k : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : (dualStandard.{u}.obj ⦋m⦌) _⦋k⦌) :
    dualFaceSupport ((dualStandard.map f).app (Opposite.op ⦋k⦌) x) =
      (dualFaceSupport x).map (SimplexCategory.toPartOrd.map f).hom := rfl

def restrictFaceSimplex {n k : ℕ} (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) :
    (SimplexCategory.sd.{u}.obj ⦋(faceSupport x).finset.card - 1⦌) _⦋k⦌ :=
  liftChainSimplex (simplexFaceEmbedding (faceSupport x)) k x (by
    intro i q hq
    rw [simplexFaceEmbedding_range]
    exact face_le_support x i hq)

def restrictDualFaceSimplex {n k : ℕ} (x : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    (dualStandard.{u}.obj ⦋(dualFaceSupport x).finset.card - 1⦌) _⦋k⦌ :=
  liftDualChainSimplex (simplexFaceEmbedding (dualFaceSupport x)) k x (by
    intro i q hq
    rw [simplexFaceEmbedding_range]
    exact dual_face_le_support x i hq)

theorem map_restrictFaceSimplex {n k : ℕ}
    (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) :
    (SimplexCategory.sd.map (simplexFaceInclusion (faceSupport x))).app (Opposite.op ⦋k⦌)
      (restrictFaceSimplex x) = x := by
  have h := map_liftChainSimplex (simplexFaceEmbedding (faceSupport x)) k x
    (by
      intro i q hq
      rw [simplexFaceEmbedding_range]
      exact face_le_support x i hq)
  change (nerveMap
    (NonemptyFiniteChains.orderHomMap
      (SimplexCategory.toPartOrd.{u}.map
        (simplexFaceInclusion (faceSupport x))).hom).monotone.functor).app
      (Opposite.op ⦋k⦌) (restrictFaceSimplex x) = x
  rw [simplexFaceInclusion_orderHom]
  exact h

theorem map_restrictDualFaceSimplex {n k : ℕ}
    (x : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    (dualStandard.map (simplexFaceInclusion (dualFaceSupport x))).app (Opposite.op ⦋k⦌)
      (restrictDualFaceSimplex x) = x := by
  have h := map_liftDualChainSimplex (simplexFaceEmbedding (dualFaceSupport x)) k x
    (by
      intro i q hq
      rw [simplexFaceEmbedding_range]
      exact dual_face_le_support x i hq)
  change (nerveMap
    (NonemptyFiniteChains.orderHomMap
      (SimplexCategory.toPartOrd.{u}.map
        (simplexFaceInclusion (dualFaceSupport x))).hom).dual.monotone.functor).app
      (Opposite.op ⦋k⦌) (restrictDualFaceSimplex x) = x
  rw [simplexFaceInclusion_orderHom]
  exact h

theorem restrictFaceSimplex_full_support {n k : ℕ}
    (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) :
    (faceSupport (restrictFaceSimplex x)).finset = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_univ, iff_true]
  apply (mem_preimageChain (simplexFaceEmbedding (faceSupport x)) (faceSupport x)
    (by intro q hq; rw [simplexFaceEmbedding_range]; exact hq) i).mpr
  exact simplexFaceEmbedding_mem (faceSupport x) i

theorem restrictDualFaceSimplex_full_support {n k : ℕ}
    (x : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    (dualFaceSupport (restrictDualFaceSimplex x)).finset = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_univ, iff_true]
  apply (mem_preimageChain (simplexFaceEmbedding (dualFaceSupport x)) (dualFaceSupport x)
    (by intro q hq; rw [simplexFaceEmbedding_range]; exact hq) i).mpr
  exact simplexFaceEmbedding_mem (dualFaceSupport x) i

end Wikipedia.HopfProblem.OrbitPair.Subdivision
