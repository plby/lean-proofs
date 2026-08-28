import Wikipedia.HopfProblem.OrbitPairHomotopyFiberExactSequence

/-!
# The original homotopy-fiber to quotient-loop comparison

If a continuous map `q` is constant on the image of `f`, composing a
fiber path with `q` gives a genuine loop. The native dimension shift
gives the relative-to-quotient homomorphism. Its composite with the
actual fiber boundary map is exactly the original map induced by `q`.
No connectivity or homotopy-excision assertion is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.FiberQuotientComparison

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (q : C(Y, Z)) (z₀ : Z) (h : ∀ x, q (f x) = z₀) (x₀ : X)

def toLoops :
    C(HomotopyFiber.Space f (f x₀), Path z₀ z₀) where
  toFun p := {
    toContinuousMap := q.comp p.val.2
    source' := (congrArg q p.property.1).trans (h p.val.1)
    target' := (congrArg q p.property.2).trans (h x₀) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact q.continuous.comp (continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))

theorem toLoops_apply (p : HomotopyFiber.Space f (f x₀)) (t : unitInterval) :
    toLoops f q z₀ h x₀ p t = q (p.val.2 t) := rfl

theorem toLoops_basepoint :
    toLoops f q z₀ h x₀ (HomotopyFiber.basepoint f x₀) = Path.refl z₀ := by
  apply Path.ext
  funext t
  exact h x₀

def hom (d : ℕ) [NeZero d] :
    π_ d (HomotopyFiber.Space f (f x₀)) (HomotopyFiber.basepoint f x₀) →*
      π_ (d + 1) Z z₀ :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d z₀).toMonoidHom.comp
    (HigherHomotopy.mapMonoidHom (N := Fin d) (toLoops f q z₀ h x₀)
      (toLoops_basepoint f q z₀ h x₀))

theorem hom_boundary (d : ℕ) [NeZero d] (c : π_ (d + 1) Y (f x₀)) :
    hom f q z₀ h x₀ d (HomotopyFiber.boundaryHom d f x₀ c) =
      HigherHomotopy.map (N := Fin (d + 1)) q (h x₀) c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun r : GenLoop (Fin (d + 1)) Z z₀ ↦
    (Quotient.mk' r : π_ (d + 1) Z z₀))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  change q (p (CubeFirstCoordinate.join d (CubeFirstCoordinate.split d u))) = q (p u)
  rw [CubeFirstCoordinate.join_split]

end NoExoticSixSphere.FiberQuotientComparison
