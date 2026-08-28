import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Splitting an actual abelian group extension with infinite cyclic quotient

A preimage of the specified cyclic generator defines a genuine section.
The map from the product multiplies the original kernel inclusion by
that section. Exactness proves it bijective, and the quotient projection
is retained by the resulting group equivalence.
-/

noncomputable section

namespace NoExoticSixSphere.SplitCyclicGroupExtension

variable {A B C : Type*} [Group A] [CommGroup B] [Group C]
  (i : A →* B) (p : B →* C) (e : C ≃* Multiplicative ℤ)
  (hp : Function.Surjective p)

def generatorLift : B := (hp (e.symm (Multiplicative.ofAdd 1))).choose

theorem generatorLift_projection :
    p (generatorLift p e hp) = e.symm (Multiplicative.ofAdd 1) :=
  (hp (e.symm (Multiplicative.ofAdd 1))).choose_spec

def sectionMap : C →* B where
  toFun c := generatorLift p e hp ^ (e c).toAdd
  map_one' := by rw [map_one]; exact zpow_zero _
  map_mul' c d := by
    rw [map_mul]
    exact zpow_add _ _ _

theorem sectionMap_projection (c : C) : p (sectionMap p e hp c) = c := by
  apply e.injective
  change e (p (generatorLift p e hp ^ (e c).toAdd)) = e c
  rw [map_zpow, generatorLift_projection, map_zpow, MulEquiv.apply_symm_apply]
  change (e c).toAdd • (1 : ℤ) = (e c).toAdd
  simp

def productHom : A × C →* B where
  toFun a := i a.1 * sectionMap p e hp a.2
  map_one' := by
    change i 1 * sectionMap p e hp 1 = 1
    rw [map_one, map_one, mul_one]
  map_mul' a b := by
    change i (a.1 * b.1) * sectionMap p e hp (a.2 * b.2) =
      (i a.1 * sectionMap p e hp a.2) * (i b.1 * sectionMap p e hp b.2)
    rw [map_mul, map_mul]
    ac_rfl

variable (hi : Function.Injective i) (hker : ∀ b, p b = 1 ↔ ∃ a, i a = b)

include hker in
theorem projection_inclusion (a : A) : p (i a) = 1 := (hker (i a)).mpr ⟨a, rfl⟩

include hker in
theorem productHom_projection (a : A × C) : p (productHom i p e hp a) = a.2 := by
  change p (i a.1 * sectionMap p e hp a.2) = a.2
  rw [map_mul, projection_inclusion i p hker, sectionMap_projection, one_mul]

include hi hker in
theorem productHom_bijective : Function.Bijective (productHom i p e hp) := by
  constructor
  · intro a b hab
    have hc : a.2 = b.2 := (productHom_projection i p e hp hker a).symm.trans
      ((congrArg p hab).trans (productHom_projection i p e hp hker b))
    apply Prod.ext ?_ hc
    apply hi
    change i a.1 * sectionMap p e hp a.2 = i b.1 * sectionMap p e hp b.2 at hab
    rw [hc] at hab
    exact mul_right_cancel hab
  · intro b
    have hz : p (b / sectionMap p e hp (p b)) = 1 := by
      rw [map_div, sectionMap_projection, div_self']
    obtain ⟨a, ha⟩ := (hker _).mp hz
    refine ⟨(a, p b), ?_⟩
    change i a * sectionMap p e hp (p b) = b
    rw [ha, div_mul_cancel]

def equiv : A × C ≃* B :=
  MulEquiv.ofBijective (productHom i p e hp) (productHom_bijective i p e hp hi hker)

theorem equiv_symm_snd (b : B) : ((equiv i p e hp hi hker).symm b).2 = p b := by
  have h := productHom_projection i p e hp hker ((equiv i p e hp hi hker).symm b)
  change p (equiv i p e hp hi hker ((equiv i p e hp hi hker).symm b)) = _ at h
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

end NoExoticSixSphere.SplitCyclicGroupExtension
