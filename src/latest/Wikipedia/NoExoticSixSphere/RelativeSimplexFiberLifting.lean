import Wikipedia.NoExoticSixSphere.SimplexBoundaryFilling
import Wikipedia.NoExoticSixSphere.RelativeBoundaryFiberClass

/-!
# Relative simplex lifting from connectivity of the actual inclusion fiber

The whole boundary lifts by its original cone paths. Native connectivity
of the fiber fills this lifted boundary, so projection gives an exact
source filling. General relative simplex lifting then supplies the desired
homotopy, fixed on the whole original boundary.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexFiberLifting

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U) (n : ℕ)
  [hF : PathConnectedSpace (Fiber U a)]
  (hpi : ∀ k, 0 < k → k < n → ∀ p : Fiber U a, Subsingleton (π_ k (Fiber U a) p))

include hF hpi in
theorem exists_source_filling (smp : RelativeSimplex U n) (v : Simplex n)
    (hv : smp.val v = a.val) :
    ∃ g : C(Simplex n, U),
      ∀ s : SimplexBoundary n, g s.val = RelativeBoundaryFiberClass.source U n smp s := by
  obtain ⟨G, hG⟩ := SimplexBoundaryFilling.exists_extension (X := Fiber U a) n hpi
    (RelativeBoundaryFiberClass.lift U a n smp v hv)
    (HomotopyFiber.basepoint (subtypeInclusion U) a)
  refine ⟨(HomotopyFiber.projection (subtypeInclusion U) a.val).comp G, ?_⟩
  intro s
  change HomotopyFiber.projection (subtypeInclusion U) a.val (G s.val) = _
  rw [hG]
  rfl

include hF hpi in
theorem exists_lift
    (hs : ∀ b : U, Function.Surjective
      (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := b) rfl))
    (smp : RelativeSimplex U n) (v : Simplex n) (hv : smp.val v = a.val) :
    ∃ g : C(Simplex n, U),
      (∀ s : SimplexBoundary n, g s.val = RelativeBoundaryFiberClass.source U n smp s) ∧
      smp.val.HomotopicRel ((subtypeInclusion U).comp g) (simplexBoundary n) := by
  obtain ⟨g, hg⟩ := exists_source_filling U a n hpi smp v hv
  have hu (s : SimplexBoundary n) : smp.val s.val = subtypeInclusion U (g s.val) :=
    (congrArg Subtype.val (hg s)).symm
  obtain ⟨q, hq, H⟩ := RelativeSimplexLifting.exists_lift n (subtypeInclusion U) hs g smp.val hu
  exact ⟨q, fun s ↦ (hq s).trans (hg s), H.symm⟩

end NoExoticSixSphere.RelativeSimplexFiberLifting
