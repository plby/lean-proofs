import Wikipedia.HopfProblem.OrbitPairHomotopyFiberExactSequence

/-!
# Changing the target of the actual homotopy fiber

Postcomposition of the ambient map postcomposes the original fiber
paths, leaving their source points unchanged. The native induced map
commutes exactly with source projection and the fiber boundary map.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberTargetMap

open HomotopyFiber

variable {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  (f : C(A, B)) (g : C(B, C)) (a : A)

def map : C(Space f (f a), Space (g.comp f) ((g.comp f) a)) where
  toFun p := ⟨(p.val.1, g.comp p.val.2), congrArg g p.property.1, congrArg g p.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : Space f (f a) × unitInterval ↦ g (p.1.val.2 p.2))
      exact g.continuous.comp (continuous_eval.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))

theorem map_basepoint : map f g a (basepoint f a) = basepoint (g.comp f) a := rfl

def hom (d : ℕ) [NeZero d] :=
  HigherHomotopy.mapMonoidHom (N := Fin d) (map f g a) (map_basepoint f g a)

theorem projection_hom (d : ℕ) [NeZero d] (c : π_ d (Space f (f a)) (basepoint f a)) :
    HigherHomotopy.mapMonoidHom (N := Fin d) (projection (g.comp f) ((g.comp f) a))
      (projection_basepoint (g.comp f) a) (hom f g a d c) =
        HigherHomotopy.mapMonoidHom (N := Fin d) (projection f (f a))
          (projection_basepoint f a) c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

theorem boundary_hom (d : ℕ) [NeZero d] (c : π_ (d + 1) B (f a)) :
    hom f g a d (boundaryHom d f a c) = boundaryHom d (g.comp f) a
      (HigherHomotopy.map (N := Fin (d + 1)) g (y := f a) rfl c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

theorem source_map_factor (d : ℕ) (c : π_ d A a) :
    HigherHomotopy.map (N := Fin d) (g.comp f) (y := a) rfl c =
      HigherHomotopy.map (N := Fin d) g (y := f a) rfl
        (HigherHomotopy.map (N := Fin d) f (y := a) rfl c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

end NoExoticSixSphere.HomotopyFiberTargetMap
