import Wikipedia.NoExoticSixSphere.ModTwoCapDegree

/-!
# Unit normalization for the actual mod-two cap product

The constant-one degree-zero cochain is a genuine cocycle. Its cap map
on original chains is the identity because the full back face is the
actual identity simplex map. The same normalization holds after descent.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularCohomologyCup
  SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

variable (X : Type) [TopologicalSpace X]

/-- The original constant-one zero-cochain. -/
def unitCochain : Cochain X 0 :=
  ConstantSheafSingularComparison.cochainFromValues X (AddCommGrpCat.of (ZMod 2)) 0 (fun _ => 1)

theorem unitCochain_simplex (σ : SingularSimplex X 0) :
    unitCochain X (simplexChain X 0 σ) = 1 :=
  ConstantSheafSingularComparison.cochainFromValues_simplex X
    (AddCommGrpCat.of (ZMod 2)) 0 (fun _ => 1) σ

/-- The two endpoint values cancel in the original mod-two coboundary. -/
theorem coboundary_unitCochain : coboundary (unitCochain X) = 0 := by
  apply ConstantSheafSingularComparison.cochain_ext X (AddCommGrpCat.of (ZMod 2)) 1
  intro σ
  change coboundary (unitCochain X) (simplexChain X 1 σ) = 0
  rw [coboundary_simplex]
  simp only [unitCochain_simplex, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  decide

def unitCocycle : Cocycle X 0 :=
  SingularCohomologyFree.mkCocycle (cochainComplex X) 0 (unitCochain X) (coboundary_unitCochain X)

/-- Its genuine degree-zero cohomology class. -/
def unitClass : Cohomology X 0 :=
  SingularCohomologyFree.cocycleClass (cochainComplex X) 0 (unitCocycle X)

/-- The full consecutive face is the original identity map of the simplex. -/
theorem windowFace_full (q : ℕ) :
    windowFace 0 q q (by omega) = ContinuousMap.id (Simplex q) := by
  have hi : windowIndex 0 q q (by omega) = (id : Fin (q + 1) → Fin (q + 1)) := by
    funext i
    apply Fin.ext
    simp only [Nat.zero_add, id_eq]
  exact (congrArg vertexMap hi).trans (vertexMap_id q)

/-- Cap with the actual constant-one cochain is the original identity chain map. -/
theorem capInDegree_unit (q : ℕ) :
    capInDegree (X := X) (p := 0) (q := q) (n := q) (Nat.zero_add q) (unitCochain X) =
      LinearMap.id := by
  apply CoefficientChains.map_ext Coefficient X q
  intro σ a
  have he := capInDegree_simplex (p := 0) (q := q) (n := q) (Nat.zero_add q)
    (unitCochain X) σ a
  simpa only [unitCochain_simplex, one_mul, windowFace_full,
    ContinuousMap.comp_id, LinearMap.id_apply] using! he

/-- The actual cohomology unit caps every native homology class to itself. -/
theorem capProductInDegree_unit (q : ℕ) :
    capProductInDegree X (p := 0) (q := q) (n := q) (Nat.zero_add q) (unitClass X) =
      LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (modComplex 2 X) q
  intro c
  have he := capProductInDegree_cocycle_cycle (p := 0) (q := q) (n := q)
    (Nat.zero_add q) (unitCocycle X) c
  apply he.trans
  apply congrArg (ModuleHomology.cycleClass (modComplex 2 X) q)
  apply Subtype.ext
  exact (capCyclesInDegree_val (Nat.zero_add q) (unitCochain X) _ c).trans
    (LinearMap.congr_fun (capInDegree_unit X q) c.val)

end NoExoticSixSphere.ModTwoCapProduct
