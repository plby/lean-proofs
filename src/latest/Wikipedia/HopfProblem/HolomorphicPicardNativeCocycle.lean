import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeData
import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnitsSections
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# Actual unit-sheaf Čech cocycles of original native holomorphic line bundles

The transition functions are the actual native scalar coordinate changes.
They are bundled as nowhere-zero holomorphic sections on the actual pairwise
chart intersections. Their genuine Čech condition is proved by evaluating
the original native cocycle relation after actual sheaf restriction.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicCharacterBundle HolomorphicExponentialSheaf
  HolomorphicFunctionSheaf.SphereH1 PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

variable {ι : Type} (A : TransitionData M ι)

/-- The existing scalar transition cover, as actual open subsets. -/
def transitionCover (i : ι) : Opens M := ⟨A.baseSet i, A.isOpen_baseSet i⟩

theorem transitionCover_covers (x : M) : ∃ i, x ∈ transitionCover M A i :=
  ⟨A.indexAt x, A.mem_baseSet_at x⟩

variable [A.IsHolomorphic I]

/-- The actual transition function as a holomorphic section on its original
overlap, with the induced original complex charts. -/
def transitionSection (i j : ι) :
    HolomorphicFunctionSheaf.Section I M (transitionCover M A i ⊓ transitionCover M A j) :=
  ⟨fun x => (A.transition i j x : ℂ), by
    intro x
    have ht : ContMDiffAt I 𝓘(ℂ) ω (fun y : M => (A.transition i j y : ℂ)) x :=
      (A.transition_holomorphic I i j).contMDiffAt
        (((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds x.property)
    exact (contMDiffAt_subtype_iff (f := fun y : M => (A.transition i j y : ℂ))
      (x := x)).mpr ht⟩

def transitionUnitSection (i j : ι) :
    UnitSection I M (transitionCover M A i ⊓ transitionCover M A j) :=
  unitSectionOfNonvanishing (transitionSection I M A i j)
    (fun x => A.transition_ne_zero i j x)

@[simp] theorem transitionUnitSection_eval (i j : ι)
    (x : ↥(transitionCover M A i ⊓ transitionCover M A j)) :
    unitSectionEval (transitionUnitSection I M A i j) x = (A.transition i j x : ℂ) := rfl

/-- A genuine Čech cocycle in the actual holomorphic unit sheaf, not a
separate formal multiplicative cocycle type. -/
def transitionCocycle : CechOneCocycle (unitsSheaf I M) (transitionCover M A) where
  value := transitionUnitSection I M A
  condition i j k := by
    apply unitSection_ext
    intro x
    change (A.transition i j x : ℂ) * (A.transition j k x : ℂ) =
      (A.transition i k x : ℂ)
    exact (mul_comm _ _).trans
      (congrArg (fun u : ℂˣ => (u : ℂ)) (A.transition_comp i j k x x.property))

@[simp] theorem transitionCocycle_eval (i j : ι)
    (x : ↥(transitionCover M A i ⊓ transitionCover M A j)) :
    unitSectionEval ((transitionCocycle I M A).value i j) x =
      (A.transition i j x : ℂ) := rfl

variable (V : M → Type*)
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]

/-- The original native trivializing cover, not a replacement presentation. -/
def nativeCover (i : M) : Opens M := ⟨(nativeTriv V i).baseSet, (nativeTriv V i).open_baseSet⟩

@[simp] theorem nativeCover_coe (i : M) :
    (nativeCover M V i : Set M) = (nativeTriv V i).baseSet := rfl

theorem nativeCover_covers (x : M) : ∃ i, x ∈ nativeCover M V i :=
  ⟨x, FiberBundle.mem_baseSet_trivializationAt ℂ V x⟩

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I]

/-- Every arbitrary original native holomorphic line bundle determines an
actual Čech one-cocycle of the actual unit sheaf on its original cover. -/
def nativeCocycle : CechOneCocycle (unitsSheaf I M) (nativeCover M V) :=
  transitionCocycle I M (data V)

/-- Evaluation recovers exactly the original native scalar coordinate change. -/
@[simp] theorem nativeCocycle_eval (i j : M) (x : ↥(nativeCover M V i ⊓ nativeCover M V j)) :
    unitSectionEval ((nativeCocycle I M V).value i j) x = (scalarTransition V i j x : ℂ) := rfl

end Wikipedia.HopfProblem.HolomorphicPicardNative
