import Wikipedia.NoExoticSixSphere.JamesSphereConeQuotientComparison
import Wikipedia.NoExoticSixSphere.HomotopyFiberSourceHomeomorph
import Wikipedia.HopfProblem.OrbitPairHigherHomotopyHomeomorph

/-!
# Finite quotient comparison for the original one-letter sphere

The lower-subspace homeomorphism has the original one-letter sphere as
its source. It changes only the source coordinate of the actual fiber,
leaving each path unchanged. Thus the finite comparison theorem applies
to the original sphere inclusion, with its precise basepoint retained.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiniteFiberQuotient

abbrev Fiber (n : ℕ) (a : Sphere n) :=
  HomotopyFiber.Space (SecondStageCone.attaching n) (SecondStageCone.attaching n a)

def basepoint (n : ℕ) (a : Sphere n) : Fiber n a :=
  HomotopyFiber.basepoint (SecondStageCone.attaching n) a

def lowerFiberHomeomorph (n : ℕ) (a : Sphere n) : Fiber n a ≃ₜ
    RelativeFiberHomology.Fiber (StageAttachment.lower n 1) (SecondStageCone.lowerSphere n a) :=
  HomotopyFiberSourceHomeomorph.equiv (subtypeInclusion (StageAttachment.lower n 1))
    (SecondStageCone.lowerSphere n) (SecondStageCone.attaching n a)

theorem lowerFiberHomeomorph_basepoint (n : ℕ) (a : Sphere n) :
    lowerFiberHomeomorph n a (basepoint n a) =
      HomotopyFiber.basepoint (subtypeInclusion (StageAttachment.lower n 1))
        (SecondStageCone.lowerSphere n a) := rfl

def toLoops (n : ℕ) (a : Sphere n) : C(Fiber n a,
    Path (SecondStageCone.quotientBasepoint n) (SecondStageCone.quotientBasepoint n)) :=
  FiberQuotientComparison.toLoops (SecondStageCone.attaching n) (SecondStage.quotientMap n)
    (SecondStageCone.quotientBasepoint n) (SecondStageCone.quotient_attaching n) a

theorem toLoops_basepoint (n : ℕ) (a : Sphere n) :
    toLoops n a (basepoint n a) = Path.refl (SecondStageCone.quotientBasepoint n) :=
  FiberQuotientComparison.toLoops_basepoint (SecondStageCone.attaching n)
    (SecondStage.quotientMap n) (SecondStageCone.quotientBasepoint n)
      (SecondStageCone.quotient_attaching n) a

theorem toLoops_factor (n : ℕ) (a : Sphere n) :
    (SecondStageCone.FiberComparison.finiteToLoops n (SecondStageCone.lowerSphere n a)).comp
      (lowerFiberHomeomorph n a : C(_, _)) = toLoops n a := rfl

theorem toLoops_map_bijective (n : ℕ) (a : Sphere n) (d : ℕ) [NeZero d]
    (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 3) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (toLoops n a) (toLoops_basepoint n a)) := by
  have he := (HigherHomotopyCoordinates.homeomorphEquiv (Fin d) (lowerFiberHomeomorph n a)
    (basepoint n a)).bijective
  have hb := (SecondStageCone.FiberComparison.finiteToLoops_map_bijective n
    (SecondStageCone.lowerSphere n a) d hn hdn).comp he
  have hf : HigherHomotopy.map (N := Fin d)
      (SecondStageCone.FiberComparison.finiteToLoops n (SecondStageCone.lowerSphere n a))
      (SecondStageCone.FiberComparison.finiteToLoops_basepoint n
        (SecondStageCone.lowerSphere n a)) ∘
        (HigherHomotopyCoordinates.homeomorphEquiv (Fin d) (lowerFiberHomeomorph n a)
          (basepoint n a)) =
      HigherHomotopy.map (N := Fin d) (toLoops n a) (toLoops_basepoint n a) := by
    funext c
    refine Quotient.inductionOn c fun p ↦ ?_
    rfl
  exact hf ▸ hb

def hom (n : ℕ) (a : Sphere n) (d : ℕ) [NeZero d] :=
  FiberQuotientComparison.hom (SecondStageCone.attaching n) (SecondStage.quotientMap n)
    (SecondStageCone.quotientBasepoint n) (SecondStageCone.quotient_attaching n) a d

theorem hom_bijective (n : ℕ) (a : Sphere n) (d : ℕ) [NeZero d]
    (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 3) : Function.Bijective (hom n a d) :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d (SecondStageCone.quotientBasepoint n)).bijective.comp
    (toLoops_map_bijective n a d hn hdn)

end NoExoticSixSphere.JamesSphere.FiniteFiberQuotient
