import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod

/-!
# Kernel and cokernel of an identity diagonal block

For an integral linear map `f : K →ₗ[ℤ] H`, the map `(a,x) ↦ (a,f x)`
has the same kernel and cokernel as `f`. The equivalences below use the
actual kernel submodules and quotient modules, with explicit formulas.
No rank, freeness, or homological identification is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

variable {H K : Type*} [AddCommGroup H] [Module ℤ H]
  [AddCommGroup K] [Module ℤ K]

/-- The identity block on `H` together with the supplied integral map. -/
def diagonalMap (f : K →ₗ[ℤ] H) : (H × K) →ₗ[ℤ] (H × H) :=
  (LinearMap.id : H →ₗ[ℤ] H).prodMap f

@[simp] theorem diagonalMap_apply (f : K →ₗ[ℤ] H) (z : H × K) :
    diagonalMap f z = (z.1, f z.2) := rfl

/-- Kernel membership forces the first coordinate to vanish and the
second coordinate to belong to the original kernel. -/
theorem diagonalMap_mem_ker_iff (f : K →ₗ[ℤ] H) (z : H × K) :
    z ∈ LinearMap.ker (diagonalMap f) ↔ z.1 = 0 ∧ z.2 ∈ LinearMap.ker f := by
  change (z.1, f z.2) = (0, 0) ↔ z.1 = 0 ∧ f z.2 = 0
  simp only [Prod.mk.injEq]

/-- The first target coordinate is unrestricted in the range. -/
theorem diagonalMap_mem_range_iff (f : K →ₗ[ℤ] H) (z : H × H) :
    z ∈ LinearMap.range (diagonalMap f) ↔ z.2 ∈ LinearMap.range f := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.2, congrArg Prod.snd hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨(z.1, x), Prod.ext rfl hx⟩

/-- The actual diagonal kernel is identified with the original kernel
by the second-coordinate projection. -/
def diagonalKerEquiv (f : K →ₗ[ℤ] H) :
    LinearMap.ker (diagonalMap f) ≃ₗ[ℤ] LinearMap.ker f where
  toFun z := ⟨z.val.2, ((diagonalMap_mem_ker_iff f z.val).mp z.property).2⟩
  invFun x := ⟨(0, x.val), (diagonalMap_mem_ker_iff f (0, x.val)).mpr ⟨rfl, x.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext ((diagonalMap_mem_ker_iff f z.val).mp z.property).1.symm rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem diagonalKerEquiv_apply_val (f : K →ₗ[ℤ] H)
    (z : LinearMap.ker (diagonalMap f)) :
    (diagonalKerEquiv f z : K) = z.val.2 := rfl

@[simp] theorem diagonalKerEquiv_symm_apply_val (f : K →ₗ[ℤ] H)
    (x : LinearMap.ker f) :
    ((diagonalKerEquiv f).symm x : H × K) = (0, (x : K)) := rfl

/-- Projection to the second coordinate followed by the actual quotient
by the original range. -/
def diagonalCokernelProjection (f : K →ₗ[ℤ] H) :
    (H × H) →ₗ[ℤ] H ⧸ LinearMap.range f :=
  (LinearMap.range f).mkQ.comp (LinearMap.snd ℤ H H)

@[simp] theorem diagonalCokernelProjection_apply (f : K →ₗ[ℤ] H) (z : H × H) :
    diagonalCokernelProjection f z = Submodule.Quotient.mk z.2 := rfl

theorem diagonalCokernelProjection_surjective (f : K →ₗ[ℤ] H) :
    Function.Surjective (diagonalCokernelProjection f) := by
  intro y
  obtain ⟨b, rfl⟩ := (LinearMap.range f).mkQ_surjective y
  exact ⟨(0, b), rfl⟩

/-- This quotient projection kills exactly the range of the diagonal map. -/
theorem diagonalMap_range_eq_ker_projection (f : K →ₗ[ℤ] H) :
    LinearMap.range (diagonalMap f) = LinearMap.ker (diagonalCokernelProjection f) := by
  ext z
  rw [diagonalMap_mem_range_iff]
  change z.2 ∈ LinearMap.range f ↔
    (Submodule.Quotient.mk z.2 : H ⧸ LinearMap.range f) = 0
  exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range f) (x := z.2)).symm

/-- The actual quotient cokernel of the diagonal map is the original
quotient cokernel, induced by second-coordinate projection. -/
def diagonalCokernelEquiv (f : K →ₗ[ℤ] H) :
    ((H × H) ⧸ LinearMap.range (diagonalMap f)) ≃ₗ[ℤ] H ⧸ LinearMap.range f :=
  (Submodule.quotEquivOfEq _ _ (diagonalMap_range_eq_ker_projection f)).trans
    ((diagonalCokernelProjection f).quotKerEquivOfSurjective
      (diagonalCokernelProjection_surjective f))

@[simp] theorem diagonalCokernelEquiv_mk (f : K →ₗ[ℤ] H) (z : H × H) :
    diagonalCokernelEquiv f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk z.2 := by
  simp only [diagonalCokernelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, diagonalCokernelProjection_apply]

@[simp] theorem diagonalCokernelEquiv_symm_mk (f : K →ₗ[ℤ] H) (y : H) :
    (diagonalCokernelEquiv f).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (0, y) := by
  apply (diagonalCokernelEquiv f).injective
  rw [LinearEquiv.apply_symm_apply, diagonalCokernelEquiv_mk]

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
