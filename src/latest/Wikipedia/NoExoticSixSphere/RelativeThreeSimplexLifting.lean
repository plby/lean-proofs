import Wikipedia.NoExoticSixSphere.RelativeBoundaryFiberClass
import Wikipedia.HopfProblem.OrbitPairTwoConnectedSimplexFilling
import Wikipedia.NoExoticSixSphere.RelativeSimplexLifting

/-!
# Lifting tetrahedra with their original subspace-valued boundary

Cone paths lift the whole boundary into the actual inclusion fiber.
Two-connectivity of that fiber fills this lifted boundary; projection
gives an exact source filling. The checked relative disk-lifting theorem
then adjusts the filling using native third-homotopy surjectivity and
fixes every original boundary point throughout the comparison homotopy.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeThreeSimplexLifting

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  [hF : SimplyConnectedSpace (Fiber U a)]
  [h₂ : Subsingleton (π_ 2 (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a))]

include hF h₂ in
theorem exists_source_filling (smp : RelativeSimplex U 3) (v : Simplex 3)
    (hv : smp.val v = a.val) :
    ∃ g : C(Simplex 3, U),
      ∀ s : SimplexBoundary 3, g s.val = RelativeBoundaryFiberClass.source U 3 smp s := by
  obtain ⟨G, hG⟩ := SimplexFilling.exists_boundary_extension (X := Fiber U a)
    (HomotopyFiber.basepoint (subtypeInclusion U) a)
    (RelativeBoundaryFiberClass.lift U a 3 smp v hv)
  refine ⟨(HomotopyFiber.projection (subtypeInclusion U) a.val).comp G, ?_⟩
  intro s
  change HomotopyFiber.projection (subtypeInclusion U) a.val (G s.val) = _
  rw [hG]
  rfl

include hF h₂ in
theorem exists_lift
    (hπ : ∀ b : U, Function.Surjective
      (HigherHomotopy.map (N := Fin 3) (subtypeInclusion U) (y := b) rfl))
    (smp : RelativeSimplex U 3) (v : Simplex 3) (hv : smp.val v = a.val) :
    ∃ g : C(Simplex 3, U),
      (∀ s : SimplexBoundary 3, g s.val = RelativeBoundaryFiberClass.source U 3 smp s) ∧
      smp.val.HomotopicRel ((subtypeInclusion U).comp g) (simplexBoundary 3) := by
  obtain ⟨g, hg⟩ := exists_source_filling U a smp v hv
  have hu (s : SimplexBoundary 3) : smp.val s.val = subtypeInclusion U (g s.val) :=
    (congrArg Subtype.val (hg s)).symm
  obtain ⟨q, hq, H⟩ := RelativeSimplexLifting.exists_lift 3 (subtypeInclusion U) hπ g smp.val hu
  exact ⟨q, fun s ↦ (hq s).trans (hg s), H.symm⟩

end NoExoticSixSphere.RelativeThreeSimplexLifting
