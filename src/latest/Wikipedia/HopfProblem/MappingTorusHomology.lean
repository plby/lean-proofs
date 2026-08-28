import Wikipedia.HopfProblem.MappingTorusHomologyMaps
import Wikipedia.HopfProblem.MappingTorusHomologyAlgebraShortExact

/-!
# The integral singular Wang sequence of an actual mapping torus

For an arbitrary homeomorphism `f : X ≃ₜ X`, the genuine two-arc open cover
of its mapping torus supplies the actual singular Mayer–Vietoris sequence.
The proved chart-transition formulas reduce that sequence to the Wang
sequence for `id - Hₙ(f)`. No homology comparison, local triviality, or
exactness is assumed: each is proved for the actual quotient and cover.

In each positive degree this gives the actual short exact extension
`0 → coker(id-Hₙ₊₁(f)) → Hₙ₊₁(Torus f) → ker(id-Hₙ(f)) → 0`.
The first map is induced by the genuine fibre inclusion, and the second
is the negative lower-component coordinate of the genuine connecting map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.MappingTorusHomology

open SingularMayerVietoris PeriodTorusHigherHomology
open MappingTorus MappingTorus.HomologyCover

variable {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)

/-- The actual monodromy difference in degree `n`. -/
def wangDifference (n : ℕ) : SingularHomology X n →ₗ[ℤ] SingularHomology X n :=
  Algebra.difference (monodromyHomologyMap f n)

@[simp] theorem wangDifference_apply (n : ℕ) (a : SingularHomology X n) :
    wangDifference f n a = a - singularHomologyMap (f : C(X, X)) n a := rfl

/-- Actual Mayer–Vietoris exactness, in the two interval-chart coordinates. -/
theorem twoArc_exact_at_pair (n : ℕ) :
    LinearMap.range (Algebra.twoArcMap (monodromyHomologyMap f n)) =
      LinearMap.ker ((fibreHomologyMap f n).comp (pairSumMap (SingularHomology X n))) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have h := LinearMap.congr_fun (leftHomologyMap_comp_right (U f) (V f) n)
      ((intersectionHomologyEquiv f n).symm b)
    change rightHomologyMap (U f) (V f) n
      (leftHomologyMap (U f) (V f) n ((intersectionHomologyEquiv f n).symm b)) = 0 at h
    rw [rightHomologyMap_coordinates, leftHomologyMap_coordinates,
      LinearEquiv.apply_symm_apply] at h
    exact h
  · intro ha
    have hright : (arcHomologyEquiv f n).symm a ∈
        LinearMap.ker (rightHomologyMap (U f) (V f) n) := by
      change rightHomologyMap (U f) (V f) n ((arcHomologyEquiv f n).symm a) = 0
      rw [rightHomologyMap_coordinates, LinearEquiv.apply_symm_apply]
      exact ha
    rw [← exact_at_pair (U f) (V f) (U_open f) (V_open f) (cover f) n] at hright
    obtain ⟨b, hb⟩ := hright
    refine ⟨intersectionHomologyEquiv f n b, ?_⟩
    rw [← leftHomologyMap_coordinates, hb, LinearEquiv.apply_symm_apply]

/-- The genuine connecting map of the actual two-arc open cover. -/
abbrev mayerVietorisConnecting (n : ℕ) :
    SingularHomology (Torus f) (n + 1) →ₗ[ℤ]
      SingularHomology (U f ∩ V f : Set (Torus f)) n :=
  connectingHomomorphism (U f) (V f) (U_open f) (V_open f) (cover f) n

/-- The two component coordinates of that actual connecting map. -/
def boundaryCoordinates (n : ℕ) :
    SingularHomology (Torus f) (n + 1) →ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  (intersectionHomologyEquiv f n).toLinearMap.comp (mayerVietorisConnecting f n)

@[simp] theorem boundaryCoordinates_apply (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    boundaryCoordinates f n a =
      intersectionHomologyEquiv f n (mayerVietorisConnecting f n a) := rfl

/-- Exactness identifies the connecting image with the actual twisted antidiagonal kernel. -/
theorem boundaryCoordinates_range (n : ℕ) :
    LinearMap.range (boundaryCoordinates f n) =
      LinearMap.ker (Algebra.twoArcMap (monodromyHomologyMap f n)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : mayerVietorisConnecting f n b ∈ LinearMap.range (mayerVietorisConnecting f n) :=
      ⟨b, rfl⟩
    rw [exact_at_intersection (U f) (V f) (U_open f) (V_open f) (cover f)] at hb
    have h := congrArg (arcHomologyEquiv f n) hb
    rw [leftHomologyMap_coordinates, map_zero] at h
    exact h
  · intro ha
    have hl : leftHomologyMap (U f) (V f) n
        ((intersectionHomologyEquiv f n).symm a) = 0 := by
      apply (arcHomologyEquiv f n).injective
      rw [leftHomologyMap_coordinates, LinearEquiv.apply_symm_apply, map_zero]
      exact ha
    have hr : (intersectionHomologyEquiv f n).symm a ∈
        LinearMap.range (mayerVietorisConnecting f n) := by
      rw [exact_at_intersection (U f) (V f) (U_open f) (V_open f) (cover f)]
      exact hl
    obtain ⟨b, hb⟩ := hr
    refine ⟨b, ?_⟩
    rw [boundaryCoordinates_apply, hb, LinearEquiv.apply_symm_apply]

/-- Both actual open inclusions together have exactly the fibre inclusion's image. -/
theorem rightHomologyMap_range (n : ℕ) :
    LinearMap.range (rightHomologyMap (U f) (V f) n) =
      LinearMap.range (fibreHomologyMap f n) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(arcHomologyEquiv f n a).1 + (arcHomologyEquiv f n a).2,
      (rightHomologyMap_coordinates f n a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(arcHomologyEquiv f n).symm (a, 0), ?_⟩
    rw [rightHomologyMap_coordinates, LinearEquiv.apply_symm_apply]
    exact congrArg (fibreHomologyMap f n) (add_zero a)

/-- Exactness at actual ambient homology, retaining both connecting coordinates. -/
theorem boundaryCoordinates_ker (n : ℕ) :
    LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (boundaryCoordinates f n) := by
  rw [boundaryCoordinates, rightTransport_second_ker]
  rw [← exact_at_ambient (U f) (V f) (U_open f) (V_open f) (cover f)]
  exact (rightHomologyMap_range f (n + 1)).symm

/-- The signed Wang boundary is the negative lower-component connecting coordinate. -/
def wangBoundary (n : ℕ) :
    SingularHomology (Torus f) (n + 1) →ₗ[ℤ] SingularHomology X n :=
  Algebra.boundary (boundaryCoordinates f n)

@[simp] theorem wangBoundary_apply (n : ℕ) (a : SingularHomology (Torus f) (n + 1)) :
    wangBoundary f n a = -(boundaryCoordinates f n a).1 := rfl

/-- Every raw connecting value is the antidiagonal of the actual signed Wang boundary. -/
theorem boundaryCoordinates_eq_antidiagonal (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    boundaryCoordinates f n a = (-wangBoundary f n a, wangBoundary f n a) :=
  Algebra.connecting_eq_antidiagonal _ _ (boundaryCoordinates_range f n) a

/-- Exactness at the actual fibre homology in every degree. -/
theorem wang_exact_at_fibre (n : ℕ) :
    LinearMap.range (wangDifference f n) = LinearMap.ker (fibreHomologyMap f n) :=
  Algebra.range_difference_eq_ker _ _ (twoArc_exact_at_pair f n)

/-- Exactness at actual positive-degree mapping-torus homology. -/
theorem wang_exact_at_mappingTorus (n : ℕ) :
    LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (wangBoundary f n) :=
  Algebra.range_inclusion_eq_ker_boundary _ _ _
    (boundaryCoordinates_ker f n) (boundaryCoordinates_range f n)

/-- The actual Wang boundary maps onto the invariant part of fibre homology. -/
theorem wangBoundary_range (n : ℕ) :
    LinearMap.range (wangBoundary f n) = LinearMap.ker (wangDifference f n) :=
  Algebra.boundary_range _ _ (boundaryCoordinates_range f n)

/-- The integral singular Wang sequence, exact in all three successive positions. -/
theorem wang_exact (n : ℕ) :
    LinearMap.range (wangDifference f (n + 1)) =
        LinearMap.ker (fibreHomologyMap f (n + 1)) ∧
      LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (wangBoundary f n) ∧
      LinearMap.range (wangBoundary f n) = LinearMap.ker (wangDifference f n) :=
  ⟨wang_exact_at_fibre f (n + 1), wang_exact_at_mappingTorus f n, wangBoundary_range f n⟩

/-- The actual quotient-to-mapping-torus homomorphism, in every degree. -/
def cokernelInclusion (n : ℕ) :
    (SingularHomology X n ⧸ LinearMap.range (wangDifference f n)) →ₗ[ℤ]
      SingularHomology (Torus f) n :=
  Algebra.cokernelInclusion _ _ (twoArc_exact_at_pair f n)

@[simp] theorem cokernelInclusion_mk (n : ℕ) (a : SingularHomology X n) :
    cokernelInclusion f n (Submodule.Quotient.mk a) = fibreHomologyMap f n a := rfl

theorem cokernelInclusion_injective (n : ℕ) : Function.Injective (cokernelInclusion f n) :=
  Algebra.cokernelInclusion_injective _ _ (twoArc_exact_at_pair f n)

/-- The actual connecting homomorphism with codomain restricted to the invariant kernel. -/
def kernelBoundary (n : ℕ) :
    SingularHomology (Torus f) (n + 1) →ₗ[ℤ] LinearMap.ker (wangDifference f n) :=
  Algebra.kernelBoundary _ _ (boundaryCoordinates_range f n)

@[simp] theorem kernelBoundary_coe (n : ℕ) (a : SingularHomology (Torus f) (n + 1)) :
    (kernelBoundary f n a : SingularHomology X n) = wangBoundary f n a := rfl

theorem kernelBoundary_surjective (n : ℕ) : Function.Surjective (kernelBoundary f n) :=
  Algebra.kernelBoundary_surjective _ _ (boundaryCoordinates_range f n)

theorem cokernelInclusion_range_eq_ker_kernelBoundary (n : ℕ) :
    LinearMap.range (cokernelInclusion f (n + 1)) = LinearMap.ker (kernelBoundary f n) :=
  Algebra.cokernelInclusion_range_eq_ker_kernelBoundary _ _ _ _
    (twoArc_exact_at_pair f (n + 1)) (boundaryCoordinates_ker f n) (boundaryCoordinates_range f n)

/-- The actual short complex of the mapping torus, with no additional hypotheses. -/
def wangShortComplex (n : ℕ) : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
  Algebra.wangShortComplex (monodromyHomologyMap f (n + 1)) (monodromyHomologyMap f n)
    (fibreHomologyMap f (n + 1)) (boundaryCoordinates f n)
    (twoArc_exact_at_pair f (n + 1)) (boundaryCoordinates_ker f n) (boundaryCoordinates_range f n)

/-- The genuine short exact integral Wang extension of any actual mapping torus. -/
theorem wangShortComplex_shortExact (n : ℕ) : (wangShortComplex f n).ShortExact :=
  Algebra.wangShortComplex_shortExact _ _ _ _
    (twoArc_exact_at_pair f (n + 1)) (boundaryCoordinates_ker f n) (boundaryCoordinates_range f n)

@[simp] theorem wangShortComplex_f_mk (n : ℕ) (a : SingularHomology X (n + 1)) :
    (wangShortComplex f n).f (Submodule.Quotient.mk a) = fibreHomologyMap f (n + 1) a := rfl

@[simp] theorem wangShortComplex_g_coe (n : ℕ) (a : SingularHomology (Torus f) (n + 1)) :
    @Subtype.val (SingularHomology X n) (fun b => b ∈ LinearMap.ker (wangDifference f n))
      ((wangShortComplex f n).g a) = wangBoundary f n a := rfl

/-- The degree-zero endpoint: every mapping-torus class comes from the actual fibre. -/
theorem fibreHomologyMap_zero_surjective : Function.Surjective (fibreHomologyMap f 0) := by
  intro b
  obtain ⟨a, ha⟩ := rightHomologyMap_zero_surjective (U f) (V f)
    (U_open f) (V_open f) (cover f) b
  exact ⟨(arcHomologyEquiv f 0 a).1 + (arcHomologyEquiv f 0 a).2,
    (rightHomologyMap_coordinates f 0 a).symm.trans ha⟩

theorem cokernelInclusion_zero_surjective : Function.Surjective (cokernelInclusion f 0) := by
  intro b
  obtain ⟨a, ha⟩ := fibreHomologyMap_zero_surjective f b
  exact ⟨Submodule.Quotient.mk a, ha⟩

/-- Degree-zero homology is the actual monodromy cokernel. -/
def degreeZeroHomologyEquiv : SingularHomology (Torus f) 0 ≃ₗ[ℤ]
    (SingularHomology X 0 ⧸ LinearMap.range (wangDifference f 0)) :=
  (LinearEquiv.ofBijective (cokernelInclusion f 0)
    ⟨cokernelInclusion_injective f 0, cokernelInclusion_zero_surjective f⟩).symm

end Wikipedia.HopfProblem.MappingTorusHomology
