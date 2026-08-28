import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Explicit integral coordinates for a short exact extension

An exact sequence with right endpoint `ℤ` splits by choosing a preimage
of `1`.  The assembly map sends `(a,s)` to `i a + s • u`; injectivity
and exactness prove that it is a linear equivalence, rather than a rank
calculation.  When both endpoints are identified with `ℤ`, this gives
actual `Fin 2 → ℤ` coordinates for the middle group, with the second
coordinate equal to the normalized boundary map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

variable {A M : Type*} [AddCommGroup A] [Module ℤ A]
  [AddCommGroup M] [modM : Module ℤ M]

/-- A chosen preimage of the positive generator of the right endpoint. -/
def shortExtensionLiftOne (d : M →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : M :=
  Classical.choose (hd 1)

@[simp] theorem shortExtensionLiftOne_boundary (d : M →ₗ[ℤ] ℤ)
    (hd : Function.Surjective d) : d (shortExtensionLiftOne d hd) = 1 :=
  Classical.choose_spec (hd 1)

/-- Exactness forces the composite of the two maps to vanish. -/
theorem shortExtension_boundary_inclusion (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) : d (i a) = 0 := by
  have ha : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hexact] at ha
  exact ha

/-- The explicit assembly map of an extension and a chosen section value. -/
def shortExtensionAssembly (i : A →ₗ[ℤ] M) (u : M) : A × ℤ →ₗ[ℤ] M where
  toFun x := i x.1 + x.2 • u
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_zsmul]
    abel
  map_smul' r x := by
    change i (r • x.1) + (r * x.2) • u = modM.smul r (i x.1 + x.2 • u)
    rw [int_smul_eq_zsmul]
    simp [map_zsmul, mul_zsmul, zsmul_add]

@[simp] theorem shortExtensionAssembly_apply (i : A →ₗ[ℤ] M) (u : M) (x : A × ℤ) :
    shortExtensionAssembly i u x = i x.1 + x.2 • u := rfl

theorem shortExtensionAssembly_boundary (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (u : M) (hu : d u = 1)
    (x : A × ℤ) : d (shortExtensionAssembly i u x) = x.2 := by
  simp [shortExtensionAssembly_apply, shortExtension_boundary_inclusion i d hexact, hu]

theorem shortExtensionAssembly_injective (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker d)
    (u : M) (hu : d u = 1) : Function.Injective (shortExtensionAssembly i u) := by
  intro x y hxy
  have hs : x.2 = y.2 := by
    have h := congrArg d hxy
    simpa only [shortExtensionAssembly_boundary i d hexact u hu] using h
  have ha : x.1 = y.1 := by
    apply hi
    apply add_right_cancel (b := x.2 • u)
    simpa only [shortExtensionAssembly_apply, hs] using hxy
  exact Prod.ext ha hs

theorem shortExtensionAssembly_surjective (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (u : M) (hu : d u = 1) :
    Function.Surjective (shortExtensionAssembly i u) := by
  intro x
  have hx : x - d x • u ∈ LinearMap.range i := by
    rw [hexact]
    change d (x - d x • u) = 0
    simp [hu]
  obtain ⟨a, ha⟩ := hx
  refine ⟨(a, d x), ?_⟩
  change i a + d x • u = x
  rw [ha, sub_add_cancel]

/-- The middle module is linearly equivalent to the left endpoint times
`ℤ`, with its section chosen from the supplied surjectivity proof. -/
def shortExtensionProductEquiv (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) : M ≃ₗ[ℤ] A × ℤ :=
  (LinearEquiv.ofBijective (shortExtensionAssembly i (shortExtensionLiftOne d hd))
    ⟨shortExtensionAssembly_injective i d hi hexact _ (shortExtensionLiftOne_boundary d hd),
      shortExtensionAssembly_surjective i d hexact _ (shortExtensionLiftOne_boundary d hd)⟩).symm

@[simp] theorem shortExtensionProductEquiv_symm_apply
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : A × ℤ) :
    (shortExtensionProductEquiv i d hi hd hexact).symm x =
      i x.1 + x.2 • shortExtensionLiftOne d hd := rfl

/-- The second split coordinate is the actual boundary map. -/
@[simp] theorem shortExtensionProductEquiv_snd
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : M) :
    (shortExtensionProductEquiv i d hi hd hexact x).2 = d x := by
  obtain ⟨y, rfl⟩ := (shortExtensionProductEquiv i d hi hd hexact).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, shortExtensionProductEquiv_symm_apply]
  simp [shortExtension_boundary_inclusion i d hexact]

/-- The inclusion is the first coordinate axis, with its given orientation. -/
@[simp] theorem shortExtensionProductEquiv_inclusion
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) :
    shortExtensionProductEquiv i d hi hd hexact (i a) = (a, 0) := by
  apply (shortExtensionProductEquiv i d hi hd hexact).symm.injective
  simp

/-- An exact extension of `ℤ` by `ℤ` has actual integral two-coordinates. -/
def shortExtensionFinTwoEquiv (i : ℤ →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) : M ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (shortExtensionProductEquiv i d hi hd hexact).trans (LinearEquiv.finTwoArrow ℤ ℤ).symm

@[simp] theorem shortExtensionFinTwoEquiv_symm_apply
    (i : ℤ →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : Fin 2 → ℤ) :
    (shortExtensionFinTwoEquiv i d hi hd hexact).symm x =
      i (x 0) + x 1 • shortExtensionLiftOne d hd := rfl

@[simp] theorem shortExtensionFinTwoEquiv_one
    (i : ℤ →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : M) :
    shortExtensionFinTwoEquiv i d hi hd hexact x 1 = d x :=
  shortExtensionProductEquiv_snd i d hi hd hexact x

@[simp] theorem shortExtensionFinTwoEquiv_inclusion
    (i : ℤ →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (t : ℤ) :
    shortExtensionFinTwoEquiv i d hi hd hexact (i t) = ![t, 0] := by
  change (LinearEquiv.finTwoArrow ℤ ℤ).symm
    (shortExtensionProductEquiv i d hi hd hexact (i t)) = _
  rw [shortExtensionProductEquiv_inclusion]
  rfl

section Endpoints

variable {B : Type*} [AddCommGroup B] [Module ℤ B]

/-- Converting an identified left endpoint and an integer into ordered
integer coordinates, with the ambient integer-module structures. -/
def shortExtensionEndpointCoordinates (eA : A ≃ₗ[ℤ] ℤ) :
    (A × ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![eA x.1, x.2]
  invFun x := (eA.symm (x 0), x 1)
  left_inv x := by simp
  right_inv x := by ext k; fin_cases k <;> simp
  map_add' x y := by ext k; fin_cases k <;> simp
  map_smul' n x := by ext k; fin_cases k <;> simp

@[simp] theorem shortExtensionEndpointCoordinates_apply (eA : A ≃ₗ[ℤ] ℤ) (x : A × ℤ) :
    shortExtensionEndpointCoordinates eA x = ![eA x.1, x.2] := rfl

@[simp] theorem shortExtensionEndpointCoordinates_symm_apply
    (eA : A ≃ₗ[ℤ] ℤ) (x : Fin 2 → ℤ) :
    (shortExtensionEndpointCoordinates eA).symm x = (eA.symm (x 0), x 1) := rfl

/-- Normalizing the right endpoint by an equivalence preserves its kernel. -/
theorem shortExtension_normalized_boundary_ker (d : M →ₗ[ℤ] B) (eB : B ≃ₗ[ℤ] ℤ) :
    LinearMap.ker (eB.toLinearMap.comp d) = LinearMap.ker d := by
  ext x
  change eB (d x) = 0 ↔ d x = 0
  exact eB.map_eq_zero_iff

/-- Actual endpoint equivalences to `ℤ` give integral coordinates on the
middle module of the original exact sequence. -/
def shortExtensionFinTwoEquivOfEndpoints (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B)
    (eA : A ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) : M ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (shortExtensionProductEquiv i (eB.toLinearMap.comp d) hi
    (eB.surjective.comp hd)
    (hexact.trans (shortExtension_normalized_boundary_ker d eB).symm)).trans
      (shortExtensionEndpointCoordinates eA)

/-- The normalized boundary is literally the second coordinate. -/
@[simp] theorem shortExtensionFinTwoEquivOfEndpoints_one
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B) (eA : A ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : M) :
    shortExtensionFinTwoEquivOfEndpoints i d eA eB hi hd hexact x 1 = eB (d x) :=
  shortExtensionProductEquiv_snd i (eB.toLinearMap.comp d) hi
    (eB.surjective.comp hd) (hexact.trans (shortExtension_normalized_boundary_ker d eB).symm) x

/-- The actual original inclusion is the oriented first coordinate axis. -/
@[simp] theorem shortExtensionFinTwoEquivOfEndpoints_inclusion
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B) (eA : A ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) :
    shortExtensionFinTwoEquivOfEndpoints i d eA eB hi hd hexact (i a) = ![eA a, 0] := by
  change shortExtensionEndpointCoordinates eA
    (shortExtensionProductEquiv i (eB.toLinearMap.comp d) hi
      (eB.surjective.comp hd)
      (hexact.trans (shortExtension_normalized_boundary_ker d eB).symm) (i a)) = _
  rw [shortExtensionProductEquiv_inclusion]
  rfl

/-- The inverse uses the original inclusion and an actual preimage of
the positive normalized boundary generator. -/
@[simp] theorem shortExtensionFinTwoEquivOfEndpoints_symm_apply
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B) (eA : A ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : Fin 2 → ℤ) :
    (shortExtensionFinTwoEquivOfEndpoints i d eA eB hi hd hexact).symm x =
      i (eA.symm (x 0)) + x 1 •
        shortExtensionLiftOne (eB.toLinearMap.comp d) (eB.surjective.comp hd) := rfl

end Endpoints

end Wikipedia.HopfProblem.Elliptic.HigherHomology
