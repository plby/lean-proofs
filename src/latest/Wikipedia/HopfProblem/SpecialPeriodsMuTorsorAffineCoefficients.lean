import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Extracting affine coefficients from actual permutation actions

For an actual permutation representation on `B × ℂ` and an actual base
representation on `B`, the elements acting affinely on fibres form a
subgroup. When all elements act affinely, their unique coefficients are
extracted from the given permutations. The cocycle laws are consequences
of the representation law, not additional assumptions on the coefficients.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

variable {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B)

/-- A group element acts by a genuine invertible affine map on each fibre
and by the specified permutation on the base. -/
def AffineFibres (g : G) : Prop :=
  ∃ a : B → ℂˣ, ∃ b : B → ℂ, ∀ z u,
    ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)

/-- The affine coefficients of a given permutation are unique: its
values at fibre coordinates zero and one determine them. -/
theorem affine_coefficients_unique {g : G} {a c : B → ℂˣ} {b d : B → ℂ}
    (hf : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (hf' : ∀ z u, ρ g (z, u) = (β g z, (c z : ℂ) * u + d z)) :
    a = c ∧ b = d := by
  have hb : ∀ z, b z = d z := by
    intro z
    have h := congrArg Prod.snd ((hf z 0).symm.trans (hf' z 0))
    simpa only [mul_zero, zero_add] using h
  refine ⟨?_, funext hb⟩
  funext z
  apply Units.ext
  have h : (a z : ℂ) + b z = (c z : ℂ) + d z := by
    simpa only [mul_one] using congrArg Prod.snd ((hf z 1).symm.trans (hf' z 1))
  rw [hb z] at h
  exact add_right_cancel h

theorem affine_one_formula (z : B) (u : ℂ) :
    ρ 1 (z, u) = (β 1 z, ((1 : ℂˣ) : ℂ) * u + 0) := by
  simp

/-- The formula for composition of two actual affine fibre maps. -/
theorem affine_mul_formula {g h : G} {a c : B → ℂˣ} {b d : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (hh : ∀ z u, ρ h (z, u) = (β h z, (c z : ℂ) * u + d z))
    (z : B) (u : ℂ) :
    ρ (g * h) (z, u) =
      (β (g * h) z, ((a (β h z) * c z : ℂˣ) : ℂ) * u +
        ((a (β h z) : ℂ) * d z + b (β h z))) := by
  rw [map_mul, Equiv.Perm.mul_apply, hh, hg]
  apply Prod.ext
  · simp only [map_mul, Equiv.Perm.mul_apply]
  · simp only [Units.val_mul]
    ring

/-- The inverse affine formula is proved using the inverse of the actual
permutation, including its specified inverse action on the base. -/
theorem affine_inv_formula {g : G} {a : B → ℂˣ} {b : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (z : B) (u : ℂ) :
    ρ g⁻¹ (z, u) =
      (β g⁻¹ z, (((a (β g⁻¹ z))⁻¹ : ℂˣ) : ℂ) * u +
        (-((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)))) := by
  apply (ρ g).injective
  have hc : ρ g (ρ g⁻¹ (z, u)) = (z, u) := by
    rw [map_inv, Equiv.Perm.inv_def]
    exact (ρ g).apply_symm_apply _
  rw [hc, hg]
  apply Prod.ext
  · rw [map_inv, Equiv.Perm.inv_def]
    exact ((β g).apply_symm_apply z).symm
  · simp only [Units.val_inv_eq_inv_val, mul_add, mul_neg, ← mul_assoc,
      mul_inv_cancel₀ (a (β g⁻¹ z)).ne_zero, one_mul, neg_add_cancel_right]

theorem affineFibres_one : AffineFibres ρ β 1 :=
  ⟨fun _ => 1, fun _ => 0, affine_one_formula ρ β⟩

theorem affineFibres_mul {g h : G} (hg : AffineFibres ρ β g)
    (hh : AffineFibres ρ β h) : AffineFibres ρ β (g * h) := by
  obtain ⟨a, b, ha⟩ := hg
  obtain ⟨c, d, hc⟩ := hh
  exact ⟨fun z => a (β h z) * c z, fun z => (a (β h z) : ℂ) * d z + b (β h z),
    affine_mul_formula ρ β ha hc⟩

theorem affineFibres_inv {g : G} (hg : AffineFibres ρ β g) : AffineFibres ρ β g⁻¹ := by
  obtain ⟨a, b, ha⟩ := hg
  exact ⟨fun z => (a (β g⁻¹ z))⁻¹, fun z => -((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)),
    affine_inv_formula ρ β ha⟩

/-- The subgroup of elements with invertible affine fibre maps. -/
def affineSubgroup : Subgroup G where
  carrier := AffineFibres ρ β
  one_mem' := affineFibres_one ρ β
  mul_mem' := affineFibres_mul ρ β
  inv_mem' := affineFibres_inv ρ β

@[simp] theorem mem_affineSubgroup (g : G) : g ∈ affineSubgroup ρ β ↔ AffineFibres ρ β g :=
  Iff.rfl

variable (h_all : ∀ g, AffineFibres ρ β g)

/-- The unique unit scale extracted from the actual permutation. -/
def scale (g : G) : B → ℂˣ := (h_all g).choose

/-- The unique translation coefficient extracted from the actual permutation. -/
def shift (g : G) : B → ℂ := (h_all g).choose_spec.choose

theorem action_formula (g : G) (z : B) (u : ℂ) :
    ρ g (z, u) =
      (β g z, (scale ρ β h_all g z : ℂ) * u + shift ρ β h_all g z) :=
  (h_all g).choose_spec.choose_spec z u

theorem scale_ne_zero (g : G) (z : B) : (scale ρ β h_all g z : ℂ) ≠ 0 :=
  (scale ρ β h_all g z).ne_zero

theorem scale_eq_of_formula {g : G} {a : B → ℂˣ} {b : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) :
    scale ρ β h_all g = a :=
  (affine_coefficients_unique ρ β (action_formula ρ β h_all g) hg).1

theorem shift_eq_of_formula {g : G} {a : B → ℂˣ} {b : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) :
    shift ρ β h_all g = b :=
  (affine_coefficients_unique ρ β (action_formula ρ β h_all g) hg).2

@[simp] theorem scale_one (z : B) : scale ρ β h_all 1 z = 1 :=
  congrFun (scale_eq_of_formula ρ β h_all (affine_one_formula ρ β)) z

@[simp] theorem shift_one (z : B) : shift ρ β h_all 1 z = 0 :=
  congrFun (shift_eq_of_formula ρ β h_all (affine_one_formula ρ β)) z

theorem scale_mul (g h : G) (z : B) :
    scale ρ β h_all (g * h) z = scale ρ β h_all g (β h z) * scale ρ β h_all h z :=
  congrFun (scale_eq_of_formula ρ β h_all
    (affine_mul_formula ρ β (action_formula ρ β h_all g) (action_formula ρ β h_all h))) z

theorem shift_mul (g h : G) (z : B) :
    shift ρ β h_all (g * h) z =
      (scale ρ β h_all g (β h z) : ℂ) * shift ρ β h_all h z + shift ρ β h_all g (β h z) :=
  congrFun (shift_eq_of_formula ρ β h_all
    (affine_mul_formula ρ β (action_formula ρ β h_all g) (action_formula ρ β h_all h))) z

theorem scale_inv (g : G) (z : B) :
    scale ρ β h_all g⁻¹ z = (scale ρ β h_all g (β g⁻¹ z))⁻¹ :=
  congrFun (scale_eq_of_formula ρ β h_all (affine_inv_formula ρ β (action_formula ρ β h_all g))) z

theorem shift_inv (g : G) (z : B) :
    shift ρ β h_all g⁻¹ z =
      -((scale ρ β h_all g (β g⁻¹ z) : ℂ)⁻¹ * shift ρ β h_all g (β g⁻¹ z)) :=
  congrFun (shift_eq_of_formula ρ β h_all (affine_inv_formula ρ β (action_formula ρ β h_all g))) z

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
