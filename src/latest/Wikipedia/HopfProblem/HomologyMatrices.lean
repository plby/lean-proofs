import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Integral matrices in the homology calculation

This file checks the explicit matrix in Remark 7.20 of `tex/s6.tex`
(lines 32034–32063, original page 59). Its six source coordinates are
`(γ̂ ∧ û, γ̂ ∧ ŵ, γ̂ ∧ δ̂, û ∧ ŵ, û ∧ δ̂, ŵ ∧ δ̂)` and its four
target coordinates are `(θ₁, η₁, θ₂, η₂)`.

The proofs identify the exact integral images and kernels, not only their
rational ranks. In particular the cokernel of the printed matrix is `ℤ`,
and its second-surface projection has cokernel `ZMod 2`.

These are algebraic statements about the displayed matrices. No identification
of these free modules or maps with the homology of a geometric space is assumed
or asserted here.
-/

namespace Wikipedia.HopfProblem.HomologyMatrices

open scoped Matrix

abbrev Source := Fin 6 → ℤ
abbrev Target := Fin 4 → ℤ
abbrev Surface := Fin 2 → ℤ

/-- The matrix whose six columns are printed in Remark 7.20. The minus
sign in the second surface block is part of the Mayer–Vietoris convention
`α₂ = (π₁*, -π₂*)` in the source. -/
def alpha₂Matrix : Matrix (Fin 4) (Fin 6) ℤ :=
  !![2, 1, 3, 0, 0, 0;
    -4, -2, 0, 1, 0, 0;
    -2, -2, -4, 0, 0, 0;
    3, 3, 0, -1, 0, 0]

def alpha₂ : Source →ₗ[ℤ] Target := alpha₂Matrix.mulVecLin

/-- The primitive functional `Φ = (4, 2, 3, 2)` of Remark 7.20. -/
def phi : Target →ₗ[ℤ] ℤ where
  toFun v := 4 * v 0 + 2 * v 1 + 3 * v 2 + 2 * v 3
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' n v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem alpha₂_apply (x : Source) :
    alpha₂ x =
      ![2 * x 0 + x 1 + 3 * x 2,
        -4 * x 0 - 2 * x 1 + x 3,
        -2 * x 0 - 2 * x 1 - 4 * x 2,
        3 * x 0 + 3 * x 1 - x 3] := by
  change alpha₂Matrix *ᵥ x = _
  ext i
  fin_cases i <;>
    simp [alpha₂Matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

@[simp] theorem phi_apply (v : Target) :
    phi v = 4 * v 0 + 2 * v 1 + 3 * v 2 + 2 * v 3 := rfl

/-- The functional annihilates the whole image, hence every printed column. -/
@[simp] theorem phi_alpha₂ (x : Source) : phi (alpha₂ x) = 0 := by
  rw [alpha₂_apply]
  simp [phi]
  ring

theorem phi_comp_alpha₂ : phi.comp alpha₂ = 0 := by
  apply LinearMap.ext
  intro x
  exact phi_alpha₂ x

theorem phi_surjective : Function.Surjective phi := by
  intro n
  refine ⟨![0, -n, n, 0], ?_⟩
  simp [phi]
  ring

/-- Exact integral image, proving the saturation asserted in Lemma 7.19(c)
for the matrix displayed in Remark 7.20. -/
theorem alpha₂_range_iff (v : Target) :
    (∃ x : Source, alpha₂ x = v) ↔ phi v = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact phi_alpha₂ x
  · intro h
    have hphi : 4 * v 0 + 2 * v 1 + 3 * v 2 + 2 * v 3 = 0 := h
    have heven : v 2 % 2 = 0 := by omega
    refine ⟨![v 0 + v 2 / 2, -v 0 - v 2, 0, v 1 + 2 * v 0, 0, 0], ?_⟩
    rw [alpha₂_apply]
    ext i
    fin_cases i <;> simp <;> omega

theorem range_alpha₂_eq_ker_phi : LinearMap.range alpha₂ = LinearMap.ker phi := by
  ext v
  exact alpha₂_range_iff v

/-- The three unrestricted source coordinates in the kernel are the third,
fifth and sixth coordinates. -/
theorem alpha₂_kernel_iff (x : Source) :
    alpha₂ x = 0 ↔ x 0 = -x 2 ∧ x 1 = -x 2 ∧ x 3 = -6 * x 2 := by
  rw [alpha₂_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    omega
  · rintro ⟨h0, h1, h3⟩
    ext i
    fin_cases i <;> simp [h0, h1, h3] <;> ring

theorem alpha₂_kernel_param (x : Source) :
    alpha₂ x = 0 ↔ ∃ a b c : ℤ, x = ![-a, -a, a, -6 * a, b, c] := by
  rw [alpha₂_kernel_iff]
  constructor
  · rintro ⟨h0, h1, h3⟩
    refine ⟨x 2, x 4, x 5, ?_⟩
    ext i
    fin_cases i <;> simp [h0, h1, h3]
  · rintro ⟨a, b, c, rfl⟩
    simp

/-- The cokernel is genuinely isomorphic to `ℤ`, with quotient map induced
by `Φ`; thus there is no unaccounted finite torsion. -/
noncomputable def alpha₂CokernelEquiv :
    (Target ⧸ LinearMap.range alpha₂) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ range_alpha₂_eq_ker_phi).trans
    (phi.quotKerEquivOfSurjective phi_surjective)

@[simp] theorem alpha₂CokernelEquiv_mk (v : Target) :
    alpha₂CokernelEquiv (Submodule.Quotient.mk v) = phi v := by
  simp [alpha₂CokernelEquiv]

/-- A concrete quotient generator has `Φ`-value one. -/
theorem alpha₂CokernelEquiv_generator :
    alpha₂CokernelEquiv (Submodule.Quotient.mk (![0, -1, 1, 0] : Target)) = 1 := by
  rw [alpha₂CokernelEquiv_mk]
  decide

/-- The first surface block, with the sign specified before Lemma 7.19. -/
def firstSurface : Source →ₗ[ℤ] Surface :=
  (!![2, 1, 3, 0, 0, 0; -4, -2, 0, 1, 0, 0] :
    Matrix (Fin 2) (Fin 6) ℤ).mulVecLin

/-- The negative of the last two rows of `α₂`, namely the printed `π₂*`
map after removing the Mayer–Vietoris minus sign. -/
def secondSurface : Source →ₗ[ℤ] Surface :=
  (!![2, 2, 4, 0, 0, 0; -3, -3, 0, 1, 0, 0] :
    Matrix (Fin 2) (Fin 6) ℤ).mulVecLin

theorem firstSurface_apply (x : Source) :
    firstSurface x = ![2 * x 0 + x 1 + 3 * x 2, -4 * x 0 - 2 * x 1 + x 3] := by
  ext i
  fin_cases i <;>
    simp [firstSurface, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem secondSurface_apply (x : Source) :
    secondSurface x = ![2 * x 0 + 2 * x 1 + 4 * x 2, -3 * x 0 - 3 * x 1 + x 3] := by
  ext i
  fin_cases i <;>
    simp [secondSurface, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem alpha₂_blocks (x : Source) :
    alpha₂ x = ![firstSurface x 0, firstSurface x 1,
      -secondSurface x 0, -secondSurface x 1] := by
  rw [alpha₂_apply, firstSurface_apply, secondSurface_apply]
  ext i
  fin_cases i <;> simp <;> ring

theorem firstSurface_surjective : Function.Surjective firstSurface := by
  intro v
  refine ⟨![0, v 0, 0, v 1 + 2 * v 0, 0, 0], ?_⟩
  rw [firstSurface_apply]
  ext i
  fin_cases i <;> simp

/-- The second-surface image is exactly `⟨2 θ₂, η₂⟩`, not just a subgroup
of the claimed rank. -/
theorem secondSurface_range_iff (v : Surface) :
    (∃ x : Source, secondSurface x = v) ↔ 2 ∣ v 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [secondSurface_apply]
    exact ⟨x 0 + x 1 + 2 * x 2, by simp; ring⟩
  · rintro ⟨n, hn⟩
    refine ⟨![n, 0, 0, v 1 + 3 * n, 0, 0], ?_⟩
    rw [secondSurface_apply]
    ext i
    fin_cases i <;> simp [hn]

theorem secondSurface_range_param (v : Surface) :
    (∃ x : Source, secondSurface x = v) ↔ ∃ a b : ℤ, v = ![2 * a, b] := by
  rw [secondSurface_range_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, v 1, ?_⟩
    ext i
    fin_cases i <;> simp [ha]
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, rfl⟩

/-- Reduction of the `θ₂` coefficient modulo two. -/
def secondParity : Surface →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp (LinearMap.proj 0)

@[simp] theorem secondParity_apply (v : Surface) : secondParity v = (v 0 : ZMod 2) := rfl

theorem secondParity_surjective : Function.Surjective secondParity := by
  intro z
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨![n, 0], rfl⟩

theorem secondParity_eq_zero_iff (v : Surface) : secondParity v = 0 ↔ 2 ∣ v 0 := by
  exact CharP.intCast_eq_zero_iff (ZMod 2) 2 (v 0)

theorem range_secondSurface_eq_ker_parity :
    LinearMap.range secondSurface = LinearMap.ker secondParity := by
  ext v
  change (∃ x, secondSurface x = v) ↔ secondParity v = 0
  rw [secondSurface_range_iff, secondParity_eq_zero_iff]

/-- The index-two assertion is strengthened to an explicit quotient
isomorphism induced by the first-coordinate parity. -/
noncomputable def secondSurfaceCokernelEquiv :
    (Surface ⧸ LinearMap.range secondSurface) ≃ₗ[ℤ] ZMod 2 :=
  (Submodule.quotEquivOfEq _ _ range_secondSurface_eq_ker_parity).trans
    (secondParity.quotKerEquivOfSurjective secondParity_surjective)

@[simp] theorem secondSurfaceCokernelEquiv_mk (v : Surface) :
    secondSurfaceCokernelEquiv (Submodule.Quotient.mk v) = (v 0 : ZMod 2) := by
  simp [secondSurfaceCokernelEquiv]

theorem secondSurface_cokernel_card :
    Nat.card (Surface ⧸ LinearMap.range secondSurface) = 2 := by
  calc
    _ = Nat.card (ZMod 2) := Nat.card_congr secondSurfaceCokernelEquiv.toEquiv
    _ = 2 := by simp

theorem secondSurface_image_index : (LinearMap.range secondSurface).toAddSubgroup.index = 2 := by
  exact secondSurface_cokernel_card

/-! ## The normalization difference matrix in Appendix B.4

The source calculation at `tex/s6.tex:54134` uses
`L = a H - b₁ E₁ - b₂ E₂ - b₃ E₃` and gives
`d(L) = (s, -s, s)`, where `s = b₁ + b₂ + b₃ - a`.
The following results concern precisely this integer matrix. They do not
identify its source or target with a Picard or cohomology group.
-/

abbrev Triple := Fin 3 → ℤ

def normalizationDifference : Target →ₗ[ℤ] Triple :=
  (!![-1, 1, 1, 1; 1, -1, -1, -1; -1, 1, 1, 1] :
    Matrix (Fin 3) (Fin 4) ℤ).mulVecLin

theorem normalizationDifference_apply (x : Target) :
    normalizationDifference x =
      ![x 1 + x 2 + x 3 - x 0,
        -(x 1 + x 2 + x 3 - x 0),
        x 1 + x 2 + x 3 - x 0] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifference, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem normalizationDifference_kernel_iff (x : Target) :
    normalizationDifference x = 0 ↔ x 0 = x 1 + x 2 + x 3 := by
  rw [normalizationDifference_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp at h0
    omega
  · intro h
    simp [h]

/-- Exact image, including the assertion that the vector `(1, -1, 1)`
generates the integral image without any extra index. -/
theorem normalizationDifference_range_iff (v : Triple) :
    (∃ x : Target, normalizationDifference x = v) ↔ v 1 = -v 0 ∧ v 2 = v 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [normalizationDifference_apply]
    simp
  · rintro ⟨h1, h2⟩
    refine ⟨![0, v 0, 0, 0], ?_⟩
    rw [normalizationDifference_apply]
    ext i
    fin_cases i <;> simp [h1, h2]

/-- Coordinates on the quotient by the image of the normalization
difference map. -/
def normalizationQuotientCoordinates : Triple →ₗ[ℤ] Surface where
  toFun v := ![v 0 + v 1, v 2 - v 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' n v := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem normalizationQuotientCoordinates_apply (v : Triple) :
    normalizationQuotientCoordinates v = ![v 0 + v 1, v 2 - v 0] := rfl

theorem normalizationQuotientCoordinates_surjective :
    Function.Surjective normalizationQuotientCoordinates := by
  intro v
  refine ⟨![0, v 0, v 1], ?_⟩
  ext i
  fin_cases i <;> simp [normalizationQuotientCoordinates]

theorem range_normalizationDifference_eq_ker :
    LinearMap.range normalizationDifference = LinearMap.ker normalizationQuotientCoordinates := by
  ext v
  change (∃ x, normalizationDifference x = v) ↔ normalizationQuotientCoordinates v = 0
  rw [normalizationDifference_range_iff]
  constructor
  · rintro ⟨h1, h2⟩
    simp [normalizationQuotientCoordinates, h1, h2]
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [normalizationQuotientCoordinates] at h0 h1
    omega

/-- The normalization-difference cokernel is a free abelian group of
rank two, explicitly identified with `ℤ²`. -/
noncomputable def normalizationDifferenceCokernelEquiv :
    (Triple ⧸ LinearMap.range normalizationDifference) ≃ₗ[ℤ] Surface :=
  (Submodule.quotEquivOfEq _ _ range_normalizationDifference_eq_ker).trans
    (normalizationQuotientCoordinates.quotKerEquivOfSurjective
      normalizationQuotientCoordinates_surjective)

@[simp] theorem normalizationDifferenceCokernelEquiv_mk (v : Triple) :
    normalizationDifferenceCokernelEquiv (Submodule.Quotient.mk v) =
      ![v 0 + v 1, v 2 - v 0] := by
  simp [normalizationDifferenceCokernelEquiv]

end Wikipedia.HopfProblem.HomologyMatrices
