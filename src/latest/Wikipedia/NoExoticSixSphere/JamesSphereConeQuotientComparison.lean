import Wikipedia.NoExoticSixSphere.JamesSphereConeFiberComparison
import Wikipedia.NoExoticSixSphere.JamesSphereConeBasedCollapse
import Wikipedia.NoExoticSixSphere.FiberQuotientContractibleSource
import Wikipedia.NoExoticSixSphere.NativeHomotopyTargetEquality

/-!
# The original finite James fiber-to-quotient comparison

The cone-side factor is bijective by contractibility of the actual cone
image and the based native collapse theorem. Composing it with the
checked finite-pair fiber map gives exactly path composition with the
original second-stage quotient. The resulting finite comparison is
bijective through the required metastable range.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.SecondStageCone.FiberComparison

open RelativeFiberHomology

variable (n : ℕ) (a : StageAttachment.lower n 1)

theorem collapse_coneImage (x : Set.range (cone n)) :
    collapse n x.val = quotientBasepoint n := (collapse_eq_basepoint_iff n x.val).mpr x.property

theorem quotient_lower (x : StageAttachment.lower n 1) :
    SecondStage.quotientMap n x.val = quotientBasepoint n :=
  (quotient_eq_basepoint_iff n x.val).mpr x.property

def coneToLoops : C(Fiber (Set.range (cone n)) (conePoint n a),
    Path (quotientBasepoint n) (quotientBasepoint n)) :=
  FiberQuotientComparison.toLoops (subtypeInclusion (Set.range (cone n))) (collapse n)
    (quotientBasepoint n) (collapse_coneImage n) (conePoint n a)

theorem coneToLoops_basepoint :
    coneToLoops n a (HomotopyFiber.basepoint (subtypeInclusion (Set.range (cone n)))
      (conePoint n a)) = Path.refl (quotientBasepoint n) :=
  FiberQuotientComparison.toLoops_basepoint (subtypeInclusion (Set.range (cone n)))
    (collapse n) (quotientBasepoint n) (collapse_coneImage n) (conePoint n a)

def finiteToLoops : C(Fiber (StageAttachment.lower n 1) a,
    Path (quotientBasepoint n) (quotientBasepoint n)) :=
  FiberQuotientComparison.toLoops (subtypeInclusion (StageAttachment.lower n 1))
    (SecondStage.quotientMap n) (quotientBasepoint n) (quotient_lower n) a

theorem finiteToLoops_basepoint :
    finiteToLoops n a (HomotopyFiber.basepoint (subtypeInclusion (StageAttachment.lower n 1)) a) =
      Path.refl (quotientBasepoint n) :=
  FiberQuotientComparison.toLoops_basepoint (subtypeInclusion (StageAttachment.lower n 1))
    (SecondStage.quotientMap n) (quotientBasepoint n) (quotient_lower n) a

theorem coneToLoops_comp_map : (coneToLoops n a).comp (map n a) = finiteToLoops n a := by
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  funext t
  exact collapse_base n (p.val.2 t)

theorem coneToLoops_map_bijective (d : ℕ) [NeZero d] :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (coneToLoops n a)
      (coneToLoops_basepoint n a)) := by
  let D := CompactCellAttachment.Disk (ConeCoordinates n)
  let : ContractibleSpace D := (convex_closedBall (0 : ConeCoordinates n) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩
  let : ContractibleSpace (Set.range (cone n)) :=
    (cone_isClosedEmbedding n).isEmbedding.toHomeomorph.symm.contractibleSpace
  apply FiberQuotientComparison.toLoops_map_bijective_of_contractible
    (subtypeInclusion (Set.range (cone n))) (collapse n) (quotientBasepoint n)
      (collapse_coneImage n) (conePoint n a) d
  exact (NativeHomotopyTargetEquality.map_bijective_iff (d + 1) (collapse n)
    (collapse_coneImage n (conePoint n a))).mpr
      (collapse_map_bijective n (conePoint n a) (Fin (d + 1)))

theorem finiteToLoops_map_factor (d : ℕ) :
    HigherHomotopy.map (N := Fin d) (coneToLoops n a) (coneToLoops_basepoint n a) ∘
      HigherHomotopy.map (N := Fin d) (map n a) (map_basepoint n a) =
        HigherHomotopy.map (N := Fin d) (finiteToLoops n a) (finiteToLoops_basepoint n a) := by
  funext c
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun r : GenLoop (Fin d) (Path (quotientBasepoint n) (quotientBasepoint n))
      (Path.refl (quotientBasepoint n)) ↦
    (Quotient.mk _ r : π_ d (Path (quotientBasepoint n) (quotientBasepoint n))
      (Path.refl (quotientBasepoint n))))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact ContinuousMap.congr_fun (coneToLoops_comp_map n a) (p.val z)

theorem finiteToLoops_map_surjective (d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d ≤ 3 * n - 2) :
    Function.Surjective (HigherHomotopy.map (N := Fin d) (finiteToLoops n a)
      (finiteToLoops_basepoint n a)) := by
  have hb := (coneToLoops_map_bijective n a d).surjective.comp (map_surjective n a d hn hdn)
  rwa [finiteToLoops_map_factor] at hb

theorem finiteToLoops_map_bijective (d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d ≤ 3 * n - 3) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (finiteToLoops n a)
      (finiteToLoops_basepoint n a)) := by
  have hb := (coneToLoops_map_bijective n a d).comp (map_bijective n a d hn hdn)
  rwa [finiteToLoops_map_factor] at hb

def finiteHom (d : ℕ) [NeZero d] :=
  FiberQuotientComparison.hom (subtypeInclusion (StageAttachment.lower n 1))
    (SecondStage.quotientMap n) (quotientBasepoint n) (quotient_lower n) a d

theorem finiteHom_bijective (d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 3) :
    Function.Bijective (finiteHom n a d) :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d (quotientBasepoint n)).bijective.comp
    (finiteToLoops_map_bijective n a d hn hdn)

end NoExoticSixSphere.JamesSphere.SecondStageCone.FiberComparison
