import ErdosProblems.Erdos117.AlternatingDecomposition
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Isotropic spread covers

A finite extension field supplies a spread in its two-dimensional plane. Any
linear functional taking `1` to `1` gives a nondegenerate alternating form on
this plane, so the construction does not require a trace-form assumption.
-/

namespace Erdos117

open Module

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

def fieldPlaneForm (φ : E →ₗ[K] K) : LinearMap.BilinForm K (E × E) where
  toFun x :=
    { toFun := fun y => φ (x.1 * y.2 - y.1 * x.2)
      map_add' := by
        intro y z
        rw [← map_add]
        congr 1
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      map_smul' := by
        intro a y
        simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, smul_mul_assoc,
          ← smul_sub, map_smul, RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change φ ((x.1 + y.1) * z.2 - z.1 * (x.2 + y.2)) =
      φ (x.1 * z.2 - z.1 * x.2) + φ (y.1 * z.2 - z.1 * y.2)
    rw [← map_add]
    congr 1
    ring
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change φ ((a • x.1) * y.2 - y.1 * (a • x.2)) = a • φ (x.1 * y.2 - y.1 * x.2)
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul]

@[simp] theorem fieldPlaneForm_apply (φ : E →ₗ[K] K) (x y : E × E) :
    fieldPlaneForm φ x y = φ (x.1 * y.2 - y.1 * x.2) := rfl

theorem fieldPlaneForm_isAlt (φ : E →ₗ[K] K) : (fieldPlaneForm φ).IsAlt := by
  intro x
  simp

theorem fieldPlaneForm_nondegenerate (φ : E →ₗ[K] K) (hφ : φ 1 = 1) :
    (fieldPlaneForm φ).Nondegenerate := by
  apply (fieldPlaneForm_isAlt φ).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  have h₁ : x.1 = 0 := by
    by_contra h
    have hz := hx (0, x.1⁻¹)
    simp [h, hφ] at hz
  have h₂ : x.2 = 0 := by
    by_contra h
    have hz := hx (x.2⁻¹, 0)
    simp [h, hφ] at hz
  exact Prod.ext h₁ h₂

/-- The finite-slope lines, together with the vertical line. -/
def fieldPlaneLine (t : Option E) : Submodule K (E × E) :=
  match t with
  | none => (LinearMap.fst K E E).ker
  | some a => (LinearMap.mulLeft K a).graph

theorem fieldPlaneLine_isotropic (φ : E →ₗ[K] K) (t : Option E)
    {x y : E × E} (hx : x ∈ fieldPlaneLine (K := K) t)
    (hy : y ∈ fieldPlaneLine (K := K) t) : fieldPlaneForm φ x y = 0 := by
  cases t with
  | none =>
    change x.1 = 0 at hx
    change y.1 = 0 at hy
    simp [hx, hy]
  | some a =>
    change x.2 = a * x.1 at hx
    change y.2 = a * y.1 at hy
    rw [fieldPlaneForm_apply, hx, hy]
    have heq : x.1 * (a * y.1) - y.1 * (a * x.1) = 0 := by ring
    rw [heq, map_zero]

theorem fieldPlaneLine_cover (x : E × E) :
    ∃ t : Option E, x ∈ fieldPlaneLine (K := K) t := by
  by_cases hx : x.1 = 0
  · exact ⟨none, hx⟩
  · refine ⟨some (x.2 / x.1), ?_⟩
    change x.2 = (x.2 / x.1) * x.1
    exact (div_mul_cancel₀ _ hx).symm

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A family of totally isotropic subspaces whose union is the whole space. -/
def IsotropicCover (B : LinearMap.BilinForm K V) {ι : Type*}
    (A : ι → Submodule K V) : Prop :=
  (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, B x y = 0) ∧ ∀ x, ∃ i, x ∈ A i

/-- The spread bound for a nondegenerate alternating form over a prime field. -/
theorem exists_isotropic_cover_nondegenerate {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    {m : ℕ} (hdim : finrank (ZMod p) V = 2 * m) :
    ∃ A : Fin (p ^ m + 1) → Submodule (ZMod p) V, IsotropicCover B A := by
  classical
  by_cases hm : m = 0
  · subst m
    have : Subsingleton V := finrank_zero_iff.mp (by simpa using hdim)
    refine ⟨fun _ => ⊤, ?_, fun x => ⟨0, Submodule.mem_top⟩⟩
    intro i x hx y hy
    have hx0 : x = 0 := Subsingleton.elim _ _
    simp [hx0]
  let E := GaloisField p m
  let := Fintype.ofFinite E
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod p)
    (show (1 : E) ≠ 0 from one_ne_zero)
  have hdimE : finrank (ZMod p) V = finrank (ZMod p) (E × E) := by
    rw [Module.finrank_prod]
    change finrank (ZMod p) V = finrank (ZMod p) (GaloisField p m) +
      finrank (ZMod p) (GaloisField p m)
    rw [GaloisField.finrank p hm, hdim]
    omega
  obtain ⟨e, he⟩ := alternating_isometry_of_finrank_eq B (fieldPlaneForm φ) halt
    (fieldPlaneForm_isAlt φ) hB (fieldPlaneForm_nondegenerate φ hφ) hdimE
  let j : Option E ≃ Fin (p ^ m + 1) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_option]
    exact congrArg (· + 1) ((Nat.card_eq_fintype_card (α := E)).symm.trans
      (GaloisField.card p m hm)))
  let A : Fin (p ^ m + 1) → Submodule (ZMod p) V := fun i =>
    (fieldPlaneLine (K := ZMod p) (j.symm i)).comap e.toLinearMap
  refine ⟨A, ?_, ?_⟩
  · intro i x hx y hy
    rw [← he x y]
    exact fieldPlaneLine_isotropic φ (j.symm i) hx hy
  · intro x
    obtain ⟨t, ht⟩ := fieldPlaneLine_cover (K := ZMod p) (e x)
    refine ⟨j t, ?_⟩
    change e x ∈ fieldPlaneLine (j.symm (j t))
    rwa [j.symm_apply_apply]

/-- The spread cover for an arbitrary alternating form, including a nonzero
radical. The number of subspaces is controlled by the rank of the form. -/
theorem exists_isotropic_cover_of_rank {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) (halt : B.IsAlt)
    {m : ℕ} (hrank : finrank (ZMod p) B.range = 2 * m) :
    ∃ A : Fin (p ^ m + 1) → Submodule (ZMod p) V, IsotropicCover B A := by
  obtain ⟨W, π, hW, hdim, hπ⟩ := exists_nondegenerate_model B halt
  obtain ⟨C, hC⟩ := exists_isotropic_cover_nondegenerate (B.restrict W)
    (fun x => halt x) hW (hdim.trans hrank)
  refine ⟨fun i => (C i).comap π, ?_, ?_⟩
  · intro i x hx y hy
    rw [← hπ x y]
    exact hC.1 i (π x) hx (π y) hy
  · intro x
    exact hC.2 (π x)

/-- Lemma 4.1 of the writeup, with the rank and its parity derived internally. -/
theorem exists_isotropic_cover {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) (halt : B.IsAlt) :
    ∃ A : Fin (p ^ (finrank (ZMod p) B.range / 2) + 1) → Submodule (ZMod p) V,
      IsotropicCover B A := by
  apply exists_isotropic_cover_of_rank B halt
  obtain ⟨m, hm⟩ := even_rank_of_alt B halt
  omega

end Erdos117
