import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffineCoefficients
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Holomorphic affine coefficients of actual permutation actions

When the base permutations are holomorphic, the elements admitting
holomorphic affine fibre coefficients form a subgroup. Closure under
inverses uses the explicitly proved inverse permutation formula, including
composition with the inverse base permutation. Uniqueness then proves that
the coefficients extracted from the actual action are holomorphic.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

variable {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A given actual permutation admits holomorphic affine fibre
coefficients. Holomorphicity refers to the complex-valued scale itself,
while its nonvanishing is recorded by the unit-valued coefficient. -/
def HolomorphicAffineFibres (g : G) : Prop :=
  ∃ a : B → ℂˣ, ∃ b : B → ℂ,
    (∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) ∧
      ContMDiff I I₁ ω (fun z => (a z : ℂ)) ∧ ContMDiff I I₁ ω b

theorem HolomorphicAffineFibres.toAffineFibres {g : G}
    (hg : HolomorphicAffineFibres ρ β I g) : AffineFibres ρ β g := by
  obtain ⟨a, b, hf, _, _⟩ := hg
  exact ⟨a, b, hf⟩

theorem holomorphicAffineFibres_one : HolomorphicAffineFibres ρ β I 1 :=
  ⟨fun _ => 1, fun _ => 0, affine_one_formula ρ β, contMDiff_const, contMDiff_const⟩

theorem holomorphicAffineFibres_mul
    (hβ : ∀ g, ContMDiff I I ω (β g)) {g h : G}
    (hg : HolomorphicAffineFibres ρ β I g) (hh : HolomorphicAffineFibres ρ β I h) :
    HolomorphicAffineFibres ρ β I (g * h) := by
  obtain ⟨a, b, hf, ha, hb⟩ := hg
  obtain ⟨c, d, hf', hc, hd⟩ := hh
  refine ⟨fun z => a (β h z) * c z,
    fun z => (a (β h z) : ℂ) * d z + b (β h z),
    affine_mul_formula ρ β hf hf', ?_, ?_⟩
  · change ContMDiff I I₁ ω (fun z => (a (β h z) : ℂ) * (c z : ℂ))
    exact (ha.comp (hβ h)).mul hc
  · exact ((ha.comp (hβ h)).mul hd).add (hb.comp (hβ h))

theorem holomorphicAffineFibres_inv
    (hβ : ∀ g, ContMDiff I I ω (β g)) {g : G}
    (hg : HolomorphicAffineFibres ρ β I g) : HolomorphicAffineFibres ρ β I g⁻¹ := by
  obtain ⟨a, b, hf, ha, hb⟩ := hg
  have hInv : ContMDiff I I₁ ω (fun z => (a (β g⁻¹ z) : ℂ)⁻¹) :=
    (ha.comp (hβ g⁻¹)).inv₀ (fun z => (a (β g⁻¹ z)).ne_zero)
  refine ⟨fun z => (a (β g⁻¹ z))⁻¹,
    fun z => -((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)),
    affine_inv_formula ρ β hf, ?_, ?_⟩
  · simpa only [Units.val_inv_eq_inv_val] using hInv
  · exact (hInv.mul (hb.comp (hβ g⁻¹))).neg

/-- The actual elements admitting holomorphic invertible affine fibre
maps form a subgroup of the given group. -/
def holomorphicAffineSubgroup (hβ : ∀ g, ContMDiff I I ω (β g)) : Subgroup G where
  carrier := HolomorphicAffineFibres ρ β I
  one_mem' := holomorphicAffineFibres_one ρ β I
  mul_mem' := holomorphicAffineFibres_mul ρ β I hβ
  inv_mem' := holomorphicAffineFibres_inv ρ β I hβ

@[simp] theorem mem_holomorphicAffineSubgroup
    (hβ : ∀ g, ContMDiff I I ω (β g)) (g : G) :
    g ∈ holomorphicAffineSubgroup ρ β I hβ ↔ HolomorphicAffineFibres ρ β I g := Iff.rfl

theorem holomorphicAffineSubgroup_le_affineSubgroup
    (hβ : ∀ g, ContMDiff I I ω (β g)) :
    holomorphicAffineSubgroup ρ β I hβ ≤ affineSubgroup ρ β := by
  intro g hg
  exact HolomorphicAffineFibres.toAffineFibres ρ β I hg

variable (h_all : ∀ g, AffineFibres ρ β g)

/-- The chosen scale equals any holomorphic affine scale representing
the actual permutation, hence is holomorphic itself. -/
theorem scale_holomorphic (g : G) (hg : HolomorphicAffineFibres ρ β I g) :
    ContMDiff I I₁ ω (fun z => (scale ρ β h_all g z : ℂ)) := by
  obtain ⟨a, b, hf, ha, _⟩ := hg
  rw [scale_eq_of_formula ρ β h_all hf]
  exact ha

/-- Holomorphicity of the extracted translation coefficient follows
from the same uniqueness of the actual affine action formula. -/
theorem shift_holomorphic (g : G) (hg : HolomorphicAffineFibres ρ β I g) :
    ContMDiff I I₁ ω (shift ρ β h_all g) := by
  obtain ⟨a, b, hf, _, hb⟩ := hg
  rw [shift_eq_of_formula ρ β h_all hf]
  exact hb

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
