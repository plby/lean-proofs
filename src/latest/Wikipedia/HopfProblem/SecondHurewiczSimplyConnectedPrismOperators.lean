import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrism

/-!
# Chain operators from face-compatible simplex homotopies

These are linear operators on the original singular chain groups. Face
compatibility of the actual continuous homotopies proves the chain-map
and chain-homotopy identities. In degree two it gives equality of the
original and straightened cycle classes in actual singular homology.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

def simplexEndpointOperator (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X)) (t : I) :
    Chains X n →ₗ[ℤ] Chains X n :=
  chainLift X n fun smp => simplexChain X n (timeSlice (H smp) t)

@[simp] theorem simplexEndpointOperator_simplex (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X)) (t : I) (smp : SingularSimplex X n) :
    simplexEndpointOperator n H t (simplexChain X n smp) =
      simplexChain X n (timeSlice (H smp) t) :=
  chainLift_simplex X n _ smp

def simplexPrismOperator (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X)) :
    Chains X n →ₗ[ℤ] Chains X (n + 1) :=
  chainLift X n fun smp => simplexPrism n (H smp)

@[simp] theorem simplexPrismOperator_simplex (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X)) (smp : SingularSimplex X n) :
    simplexPrismOperator n H (simplexChain X n smp) = simplexPrism n (H smp) :=
  chainLift_simplex X n _ smp

/-- Compatibility on the literal face maps of the original singular simplices. -/
def FaceCompatibleHomotopies (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X)) : Prop :=
  ∀ smp i, (H' smp).comp ((ContinuousMap.id I).prodMap (simplexFace n i)) =
    H (smp.comp (simplexFace n i))

theorem timeSlice_face {n : ℕ}
    {H : SingularSimplex X n → C(I × Simplex n, X)}
    {H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X)}
    (h : FaceCompatibleHomotopies n H H') (smp : SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (t : I) :
    (timeSlice (H' smp) t).comp (simplexFace n i) =
      timeSlice (H (smp.comp (simplexFace n i))) t :=
  congrArg (fun F => timeSlice F t) (h smp i)

/-- The time slices give a chain map in each of the relevant adjacent degrees. -/
theorem simplexEndpointOperator_boundary (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (t : I) (c : Chains X (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom (simplexEndpointOperator (n + 1) H' t c) =
      simplexEndpointOperator n H t (((singularComplex X).d (n + 1) n).hom c) := by
  have hc : (((singularComplex X).d (n + 1) n).hom).comp
        (simplexEndpointOperator (n + 1) H' t) =
      (simplexEndpointOperator n H t).comp ((singularComplex X).d (n + 1) n).hom := by
    apply chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, simplexEndpointOperator_simplex,
      boundary_simplex, map_sum, map_zsmul, timeSlice_face h]
  exact LinearMap.congr_fun hc c

/-- The full chain-homotopy formula on arbitrary actual singular chains. -/
theorem simplexPrismOperator_boundary (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (c : Chains X (n + 1)) :
    ((singularComplex X).d (n + 2) (n + 1)).hom (simplexPrismOperator (n + 1) H' c) =
      simplexEndpointOperator (n + 1) H' 1 c -
        simplexEndpointOperator (n + 1) H' 0 c -
        simplexPrismOperator n H (((singularComplex X).d (n + 1) n).hom c) := by
  have hc : (((singularComplex X).d (n + 2) (n + 1)).hom).comp
        (simplexPrismOperator (n + 1) H') =
      simplexEndpointOperator (n + 1) H' 1 - simplexEndpointOperator (n + 1) H' 0 -
        (simplexPrismOperator n H).comp ((singularComplex X).d (n + 1) n).hom := by
    apply chainMap_ext X (n + 1)
    intro smp
    have hface := h smp
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, simplexPrismOperator_simplex,
      simplexPrism_boundary, simplexEndpointOperator_simplex, boundary_simplex,
      map_sum, map_zsmul, hface]
  exact LinearMap.congr_fun hc c

theorem simplexEndpointOperator_zero (n : ℕ)
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (h₀ : ∀ smp, timeSlice (H smp) 0 = smp) :
    simplexEndpointOperator n H 0 = LinearMap.id := by
  apply chainMap_ext X n
  intro smp
  rw [simplexEndpointOperator_simplex, h₀]
  rfl

/-- The terminal operator applied to an actual two-cycle, with its cycle
condition proved from face compatibility. -/
def straightenedTwoCycle
    (H₁ : SingularSimplex X 1 → C(I × Simplex 1, X))
    (H₂ : SingularSimplex X 2 → C(I × Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    ModuleHomology.Cycle (singularComplex X) 2 :=
  ModuleHomology.mkCycle (singularComplex X) 2 (simplexEndpointOperator 2 H₂ 1 c.1) (by
    rw [simplexEndpointOperator_boundary 1 H₁ H₂ h,
      ModuleHomology.cycle_condition (singularComplex X) 2 c, map_zero])

@[simp] theorem straightenedTwoCycle_val
    (H₁ : SingularSimplex X 1 → C(I × Simplex 1, X))
    (H₂ : SingularSimplex X 2 → C(I × Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    (straightenedTwoCycle H₁ H₂ h c).1 = simplexEndpointOperator 2 H₂ 1 c.1 := rfl

/-- Straightening by these actual compatible homotopies preserves the
genuine singular second homology class. -/
theorem straightenedTwoCycle_class
    (H₁ : SingularSimplex X 1 → C(I × Simplex 1, X))
    (H₂ : SingularSimplex X 2 → C(I × Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (h₀ : ∀ smp, timeSlice (H₂ smp) 0 = smp)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    ModuleHomology.cycleClass (singularComplex X) 2 (straightenedTwoCycle H₁ H₂ h c) =
      ModuleHomology.cycleClass (singularComplex X) 2 c := by
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 2 _ _).mpr
  refine ⟨simplexPrismOperator 2 H₂ c.1, ?_⟩
  rw [simplexPrismOperator_boundary 1 H₁ H₂ h,
    simplexEndpointOperator_zero 2 H₂ h₀,
    ModuleHomology.cycle_condition (singularComplex X) 2 c, map_zero, sub_zero]
  rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
