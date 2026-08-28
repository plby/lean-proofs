import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.OrderOfElement

/-!
# Holomorphic functions with a character on a compact complex manifold

A holomorphic complex-valued function on a compact connected complex manifold
is constant.  Consequently a nonzero such function can transform under a group
action by a character only when that character is trivial.  Applied to powers
of a character, this gives the exact divisibility criterion by its order.

These statements concern actual holomorphic functions.  They do not define
triviality of a line bundle in terms of equivariant functions: applications to
associated bundles must separately prove the correspondence with sections.
No freeness, finiteness, or regularity of the group action is required here.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

variable {G A : Type*} [Group G] [MulAction G A]

/-- Transformation of a complex-valued function by a specified character. -/
def IsCharacterEquivariant (χ : G →* ℂˣ) (f : A → ℂ) : Prop :=
  ∀ (g : G) (a : A), f (g • a) = (χ g : ℂ) * f a

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ω A]
  [CompactSpace A] [ConnectedSpace A]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The analytic constancy used in the character obstruction.  Boundaryless
complex models include the standard model and products of standard models. -/
theorem holomorphic_apply_eq {f : A → ℂ} (hf : ContMDiff I I₁ ω f) (a b : A) :
    f a = f b :=
  (hf.mdifferentiable (by simp)).apply_eq_of_compactSpace a b

theorem holomorphic_eq_const {f : A → ℂ} (hf : ContMDiff I I₁ ω f) :
    ∃ c : ℂ, f = Function.const A c :=
  (hf.mdifferentiable (by simp)).exists_eq_const_of_compactSpace

/-- A nonzero value of a holomorphic function already implies that it vanishes
nowhere on this compact connected complex manifold. -/
theorem holomorphic_ne_zero_everywhere {f : A → ℂ}
    (hf : ContMDiff I I₁ ω f) (hne : ∃ a, f a ≠ 0) : ∀ a, f a ≠ 0 := by
  obtain ⟨b, hb⟩ := hne
  intro a
  rw [holomorphic_apply_eq hf a b]
  exact hb

/-- A holomorphic function transforming by a character, with at least one
nonzero value, forces the whole character to be trivial. -/
theorem character_eq_one_of_equivariant_holomorphic_nonzero
    {χ : G →* ℂˣ} {f : A → ℂ} (hf : ContMDiff I I₁ ω f)
    (he : IsCharacterEquivariant χ f) (hne : ∃ a, f a ≠ 0) : χ = 1 := by
  obtain ⟨a, ha⟩ := hne
  ext g
  change (χ g : ℂ) = 1
  apply mul_right_cancel₀ ha
  rw [← he g a, holomorphic_apply_eq hf (g • a) a, one_mul]

/-- For a nontrivial character every equivariant holomorphic function is the
zero function, rather than just having some zero. -/
theorem equivariant_holomorphic_eq_zero_of_character_ne_one
    {χ : G →* ℂˣ} {f : A → ℂ} (hχ : χ ≠ 1) (hf : ContMDiff I I₁ ω f)
    (he : IsCharacterEquivariant χ f) : f = 0 := by
  funext a
  by_contra ha
  exact hχ (character_eq_one_of_equivariant_holomorphic_nonzero hf he ⟨a, ha⟩)

/-- Existence of an actual nonzero equivariant holomorphic function is
equivalent to triviality of the character. -/
theorem equivariant_holomorphic_nonzero_iff (χ : G →* ℂˣ) :
    (∃ f : A → ℂ, ContMDiff I I₁ ω f ∧ IsCharacterEquivariant χ f ∧
      ∃ a, f a ≠ 0) ↔ χ = 1 := by
  constructor
  · rintro ⟨f, hf, he, hne⟩
    exact character_eq_one_of_equivariant_holomorphic_nonzero hf he hne
  · rintro rfl
    refine ⟨fun _ => 1, contMDiff_const, ?_, ?_⟩
    · intro g a
      simp
    · exact ⟨Classical.arbitrary A, one_ne_zero⟩

/-- The same criterion with the nonvanishing condition required everywhere. -/
theorem equivariant_holomorphic_nowhere_zero_iff (χ : G →* ℂˣ) :
    (∃ f : A → ℂ, ContMDiff I I₁ ω f ∧ IsCharacterEquivariant χ f ∧
      ∀ a, f a ≠ 0) ↔ χ = 1 := by
  constructor
  · rintro ⟨f, hf, he, hne⟩
    exact character_eq_one_of_equivariant_holomorphic_nonzero hf he
      ⟨Classical.arbitrary A, hne _⟩
  · rintro rfl
    refine ⟨fun _ => 1, contMDiff_const, ?_, fun _ => one_ne_zero⟩
    intro g a
    simp

/-- The exact obstruction for a natural power of a character. -/
theorem equivariant_holomorphic_nonzero_pow_iff (χ : G →* ℂˣ) (n : ℕ) :
    (∃ f : A → ℂ, ContMDiff I I₁ ω f ∧ IsCharacterEquivariant (χ ^ n) f ∧
      ∃ a, f a ≠ 0) ↔ χ ^ n = 1 :=
  equivariant_holomorphic_nonzero_iff (χ ^ n)

/-- The order convention also covers characters of infinite order: their
order is zero, and then only the zeroth natural power permits such a function. -/
theorem equivariant_holomorphic_nonzero_pow_iff_orderOf_dvd
    (χ : G →* ℂˣ) (n : ℕ) :
    (∃ f : A → ℂ, ContMDiff I I₁ ω f ∧ IsCharacterEquivariant (χ ^ n) f ∧
      ∃ a, f a ≠ 0) ↔ orderOf χ ∣ n :=
  (equivariant_holomorphic_nonzero_pow_iff χ n).trans orderOf_dvd_iff_pow_eq_one.symm

theorem equivariant_holomorphic_nowhere_zero_pow_iff_orderOf_dvd
    (χ : G →* ℂˣ) (n : ℕ) :
    (∃ f : A → ℂ, ContMDiff I I₁ ω f ∧ IsCharacterEquivariant (χ ^ n) f ∧
      ∀ a, f a ≠ 0) ↔ orderOf χ ∣ n :=
  (equivariant_holomorphic_nowhere_zero_iff (χ ^ n)).trans
    orderOf_dvd_iff_pow_eq_one.symm

/-- Negative powers, hence the inverse-character convention for an associated
line bundle, give the same order obstruction. -/
theorem equivariant_holomorphic_nonzero_zpow_iff_orderOf_dvd
    (χ : G →* ℂˣ) (n : ℤ) :
    (∃ f : A → ℂ, ContMDiff I I₁ ω f ∧ IsCharacterEquivariant (χ ^ n) f ∧
      ∃ a, f a ≠ 0) ↔ (orderOf χ : ℤ) ∣ n :=
  (equivariant_holomorphic_nonzero_iff (χ ^ n)).trans
    orderOf_dvd_iff_zpow_eq_one.symm

end Wikipedia.HopfProblem.HolomorphicCharacterBundle
