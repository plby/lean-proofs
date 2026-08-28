import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberClass
import Wikipedia.NoExoticSixSphere.SimplexBoundaryChains

/-!
# The whole simplex boundary lifted by actual cone paths

The actual signed boundary cycle maps to a cycle in the original
inclusion fiber. The cone apex can be any point of the simplex mapped
to the chosen basepoint. This whole-boundary representative will allow
the signed four-face relation to be proved before passing to homology.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.RelativeBoundaryFiberClass

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def source (n : ℕ) (smp : RelativeSimplex U n) : C(SimplexBoundary n, U) :=
  ⟨fun s ↦ ⟨smp.val s.val, smp.property s.val s.property⟩,
    (smp.val.continuous.comp continuous_subtype_val).subtype_mk _⟩

def coneHomotopy (n : ℕ) (smp : RelativeSimplex U n) (v : Simplex n) (hv : smp.val v = a.val) :
    ((subtypeInclusion U).comp (source U n smp)).Homotopy
      (ContinuousMap.const (SimplexBoundary n) a.val) where
  toContinuousMap := smp.val.comp ((SimplexVertexCone.segment n).comp
    ⟨fun p ↦ (p.1, (p.2.val, v)),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).prodMk
        continuous_const)⟩)
  map_zero_left s := congrArg smp.val (SimplexVertexCone.segment_zero n s.val v)
  map_one_left s := (congrArg smp.val (SimplexVertexCone.segment_one n s.val v)).trans hv

def lift (n : ℕ) (smp : RelativeSimplex U n) (v : Simplex n) (hv : smp.val v = a.val) :
    C(SimplexBoundary n, Fiber U a) :=
  HomotopyFiber.lift (subtypeInclusion U) a.val (source U n smp) (coneHomotopy U a n smp v hv)

theorem lift_path (n : ℕ) (smp : RelativeSimplex U n) (v : Simplex n) (hv : smp.val v = a.val)
    (s : SimplexBoundary n) (t : I) :
    (lift U a n smp v hv s).val.2 t = smp.val (SimplexVertexCone.segment n (t, (s.val, v))) :=
  rfl

def cycle (n : ℕ) (smp : RelativeSimplex U (n + 2)) (v : Simplex (n + 2))
    (hv : smp.val v = a.val) : ModuleHomology.Cycle (singularComplex (Fiber U a)) (n + 1) :=
  ModuleHomology.mapCycles (singularChainMap (lift U a (n + 2) smp v hv)) (n + 1)
    (SimplexBoundaryChains.cycle n)

theorem cycle_val (n : ℕ) (smp : RelativeSimplex U (n + 2)) (v : Simplex (n + 2))
    (hv : smp.val v = a.val) :
    (cycle U a n smp v hv).val =
      inducedChain (lift U a (n + 2) smp v hv) (n + 1) (SimplexBoundaryChains.chain (n + 1)) :=
  ModuleHomology.mapCycles_val _ _ _

theorem cycle_val_sum (n : ℕ) (smp : RelativeSimplex U (n + 2)) (v : Simplex (n + 2))
    (hv : smp.val v = a.val) :
    (cycle U a n smp v hv).val =
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • simplexChain (Fiber U a) (n + 1)
        ((lift U a (n + 2) smp v hv).comp (simplexFaceBoundary (n + 1) i)) := by
  rw [cycle_val, SimplexBoundaryChains.chain, map_sum]
  simp only [map_zsmul, inducedChain_simplex]

def homologyClass (n : ℕ) (smp : RelativeSimplex U (n + 2)) (v : Simplex (n + 2))
    (hv : smp.val v = a.val) : SingularHomology (Fiber U a) (n + 1) :=
  singularHomologyMap (lift U a (n + 2) smp v hv) (n + 1)
    (ModuleHomology.cycleClass (singularComplex (SimplexBoundary (n + 2))) (n + 1)
      (SimplexBoundaryChains.cycle n))

theorem homologyClass_eq_cycle (n : ℕ) (smp : RelativeSimplex U (n + 2))
    (v : Simplex (n + 2)) (hv : smp.val v = a.val) :
    homologyClass U a n smp v hv =
      ModuleHomology.cycleClass (singularComplex (Fiber U a)) (n + 1) (cycle U a n smp v hv) :=
  ModuleHomology.homologyMap_cycleClass _ _ _

end NoExoticSixSphere.RelativeBoundaryFiberClass
