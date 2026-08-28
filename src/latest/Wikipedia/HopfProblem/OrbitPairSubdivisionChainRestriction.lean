import Wikipedia.HopfProblem.OrbitPairNativeSubdivisionParameters
import Mathlib.Data.Finset.Preimage

/-!
# Restricting native face chains to an embedded face

An order embedding pulls back a finite chain supported in its range.
Mapping that pullback forward recovers the original chain exactly. This
is the support-restriction operation used to find carriers of subdivision
cells before removing degeneracies in the original simplex.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

def preimageChain (f : P ↪o Q) (B : NonemptyFiniteChains Q)
    (hB : ∀ q ∈ B.finset, q ∈ Set.range f) : NonemptyFiniteChains P := by
  classical
  refine ⟨B.finset.preimage f f.injective.injOn, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := B.nonempty
    obtain ⟨p, rfl⟩ := hB q hq
    exact ⟨p, Finset.mem_preimage.mpr hq⟩
  · intro a b
    exact (B.comparable ⟨f a.val, Finset.mem_preimage.mp a.property⟩
      ⟨f b.val, Finset.mem_preimage.mp b.property⟩).imp
        (fun h ↦ f.le_iff_le.mp h) (fun h ↦ f.le_iff_le.mp h)

theorem mem_preimageChain (f : P ↪o Q) (B : NonemptyFiniteChains Q)
    (hB : ∀ q ∈ B.finset, q ∈ Set.range f) (p : P) :
    p ∈ (preimageChain f B hB).finset ↔ f p ∈ B.finset :=
  Finset.mem_preimage (hf := f.injective.injOn)

theorem preimageChain_monotone (f : P ↪o Q) (B C : NonemptyFiniteChains Q)
    (hB : ∀ q ∈ B.finset, q ∈ Set.range f) (hC : ∀ q ∈ C.finset, q ∈ Set.range f)
    (hBC : B ≤ C) : preimageChain f B hB ≤ preimageChain f C hC := by
  intro p hp
  exact (mem_preimageChain f C hC p).mpr (hBC ((mem_preimageChain f B hB p).mp hp))

theorem map_preimageChain (f : P ↪o Q) (B : NonemptyFiniteChains Q)
    (hB : ∀ q ∈ B.finset, q ∈ Set.range f) :
    (preimageChain f B hB).map f.toOrderHom = B := by
  classical
  apply NonemptyFiniteChains.ext
  ext q
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_preimageChain f B hB p).mp hp
  · intro hq
    obtain ⟨p, rfl⟩ := hB q hq
    exact ⟨p, (mem_preimageChain f B hB p).mpr hq, rfl⟩

def chainEmbedding (A : NonemptyFiniteChains P) : Fin (A.finset.card - 1 + 1) ↪o P :=
  (FinitePoset.chainEnumeration A).toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ A.finset))

theorem chainEmbedding_range (A : NonemptyFiniteChains P) :
    Set.range (chainEmbedding A) = (A.finset : Set P) := FinitePoset.chainVertices_range A

def restrictToFace (A B : NonemptyFiniteChains P) (hBA : B ≤ A) :
    NonemptyFiniteChains (Fin (A.finset.card - 1 + 1)) :=
  preimageChain (chainEmbedding A) B (by
    intro p hp
    rw [chainEmbedding_range]
    exact hBA hp)

theorem map_restrictToFace (A B : NonemptyFiniteChains P) (hBA : B ≤ A) :
    (restrictToFace A B hBA).map (chainEmbedding A).toOrderHom = B :=
  map_preimageChain (chainEmbedding A) B _

section Nerve

variable {R : Type u} [PartialOrder R]

def liftChainSimplex (f : P ↪o R) (k : ℕ)
    (x : (nerve (NonemptyFiniteChains R)) _⦋k⦌)
    (h : ∀ i, ∀ q ∈ (x.obj i).finset, q ∈ Set.range f) :
    (nerve (NonemptyFiniteChains P)) _⦋k⦌ := by
  let g : Fin (k + 1) →o NonemptyFiniteChains P :=
    { toFun := fun i ↦ preimageChain f (x.obj i) (h i)
      monotone' := fun i j hij ↦
        preimageChain_monotone f (x.obj i) (x.obj j) (h i) (h j) (x.monotone hij) }
  exact g.monotone.functor

theorem map_liftChainSimplex (f : P ↪o R) (k : ℕ)
    (x : (nerve (NonemptyFiniteChains R)) _⦋k⦌)
    (h : ∀ i, ∀ q ∈ (x.obj i).finset, q ∈ Set.range f) :
    (nerveMap (NonemptyFiniteChains.orderHomMap f.toOrderHom).monotone.functor).app
      (Opposite.op ⦋k⦌) (liftChainSimplex f k x h) = x := by
  apply nerve.ext_of_isThin
  funext i
  exact map_preimageChain f (x.obj i) (h i)

def liftDualChainSimplex (f : P ↪o R) (k : ℕ)
    (x : (nerve (OrderDual (NonemptyFiniteChains R))) _⦋k⦌)
    (h : ∀ i, ∀ q ∈ (x.obj i).finset, q ∈ Set.range f) :
    (nerve (OrderDual (NonemptyFiniteChains P))) _⦋k⦌ := by
  let g : Fin (k + 1) →o OrderDual (NonemptyFiniteChains P) :=
    { toFun := fun i ↦ preimageChain f (x.obj i) (h i)
      monotone' := fun i j hij ↦
        preimageChain_monotone f (x.obj j) (x.obj i) (h j) (h i) (x.monotone hij) }
  exact g.monotone.functor

theorem map_liftDualChainSimplex (f : P ↪o R) (k : ℕ)
    (x : (nerve (OrderDual (NonemptyFiniteChains R))) _⦋k⦌)
    (h : ∀ i, ∀ q ∈ (x.obj i).finset, q ∈ Set.range f) :
    (nerveMap (NonemptyFiniteChains.orderHomMap f.toOrderHom).dual.monotone.functor).app
      (Opposite.op ⦋k⦌) (liftDualChainSimplex f k x h) = x := by
  apply nerve.ext_of_isThin
  funext i
  exact map_preimageChain f (x.obj i) (h i)

end Nerve

end Wikipedia.HopfProblem.OrbitPair.Subdivision
