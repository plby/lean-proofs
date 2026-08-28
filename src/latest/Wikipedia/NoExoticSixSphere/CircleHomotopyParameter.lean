import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith

/-!
# A closed parameter space for interval homotopies

The circle maps continuously to the unit interval by `(1 - re z) / 2`, sending
`1` to zero and `-1` to one. Restriction along a semicircle connects those two
fibers. The composite interval map need not be the identity.
-/

open Set
open scoped unitInterval

namespace NoExoticSixSphere.CircleHomotopyParameter

noncomputable def height : C(Circle, unitInterval) where
  toFun z := ⟨(1 - (z : ℂ).re) / 2, by
    have h := Complex.abs_re_le_norm (z : ℂ)
    rw [Circle.norm_coe] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.sub (Complex.continuous_re.comp
      (continuous_subtype_val : Continuous (fun z : Circle ↦ (z : ℂ))))).div_const 2

theorem height_one : height 1 = 0 := by
  apply Subtype.ext
  norm_num [height]

theorem height_neg_one : height (-1) = 1 := by
  apply Subtype.ext
  norm_num [height]

noncomputable def semicircle : C(unitInterval, Circle) :=
  Circle.exp.comp ⟨fun t ↦ Real.pi * (t : ℝ), continuous_const.mul continuous_subtype_val⟩

theorem semicircle_zero : semicircle 0 = 1 := by
  change Circle.exp (Real.pi * 0) = 1
  rw [mul_zero, Circle.exp_zero]

theorem semicircle_one : semicircle 1 = -1 := by
  apply Circle.ext
  change (Circle.exp (Real.pi * 1) : ℂ) = (-1 : Circle)
  rw [mul_one, Circle.coe_exp, Complex.exp_pi_mul_I]
  rfl

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def extend (F : C(unitInterval × X, Y)) : C(Circle × X, Y) :=
  F.comp ⟨fun p ↦ (height p.1, p.2), (height.continuous.comp continuous_fst).prodMk continuous_snd⟩

theorem extend_one (F : C(unitInterval × X, Y)) (x : X) : extend F (1, x) = F (0, x) := by
  change F (height 1, x) = _
  rw [height_one]

theorem extend_neg_one (F : C(unitInterval × X, Y)) (x : X) : extend F (-1, x) = F (1, x) := by
  change F (height (-1), x) = _
  rw [height_neg_one]

noncomputable def restrict (Q : C(Circle × X, Y)) : C(unitInterval × X, Y) :=
  Q.comp ⟨fun p ↦ (semicircle p.1, p.2),
    (semicircle.continuous.comp continuous_fst).prodMk continuous_snd⟩

theorem homotopy_in_subset_of_fixed_extension {f g : C(X, Y)} {S : Set X}
    (F : ContinuousMap.HomotopyRel f g S) (K : Set Y)
    (hf : ∀ x, f x ∈ K) (hg : ∀ x, g x ∈ K)
    (Q : C(Circle × X, Y)) (hQ : ∀ p, Q p ∈ K)
    (hfixed : ∀ p, extend F.toContinuousMap p ∈ K → Q p = extend F.toContinuousMap p) :
    ∃ G : ContinuousMap.HomotopyRel f g S, ∀ t x, G (t, x) ∈ K := by
  let G : ContinuousMap.HomotopyRel f g S :=
    { toContinuousMap := restrict Q
      map_zero_left := by
        intro x
        change Q (semicircle 0, x) = f x
        rw [semicircle_zero]
        have he : extend F.toContinuousMap (1, x) = f x :=
          (extend_one F.toContinuousMap x).trans (F.apply_zero x)
        exact (hfixed (1, x) (he.symm ▸ hf x)).trans he
      map_one_left := by
        intro x
        change Q (semicircle 1, x) = g x
        rw [semicircle_one]
        have he : extend F.toContinuousMap (-1, x) = g x :=
          (extend_neg_one F.toContinuousMap x).trans (F.apply_one x)
        exact (hfixed (-1, x) (he.symm ▸ hg x)).trans he
      prop' := by
        intro t x hx
        change Q (semicircle t, x) = f x
        have he : extend F.toContinuousMap (semicircle t, x) = f x := F.eq_fst _ hx
        exact (hfixed (semicircle t, x) (he.symm ▸ hf x)).trans he }
  exact ⟨G, fun t x ↦ hQ (semicircle t, x)⟩

end NoExoticSixSphere.CircleHomotopyParameter
