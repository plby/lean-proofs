import ErdosProblems.Erdos587.HooleyInnerBox
import ErdosProblems.Erdos587.HooleyLatticeRounding
import ErdosProblems.Erdos587.HooleyZonotope
import ErdosProblems.Erdos587.HooleyRobustSpanning

/-! # Adapted lattice coordinates retain the zonotope mass and all long widths -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

noncomputable def deltaRealCoordinate {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (intLinearMapRealExtension (latticeCoordinates b).toLinearMap)

lemma deltaRealCoordinate_intCast {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n) (v : Fin n → ℤ) :
    deltaRealCoordinate b i (intCastVec v) = (latticeCoordinates b v i : ℝ) := by
  simp only [deltaRealCoordinate, LinearMap.comp_apply, intLinearMapRealExtension_intCastVec,
    LinearMap.proj_apply]
  rfl

lemma deltaRealCoordinate_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n) :
    deltaRealCoordinate b i (intCastVec (b i)) = 1 := by
  rw [deltaRealCoordinate_intCast]
  simp only [latticeCoordinates_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    Int.cast_one]

lemma deltaRealCoordinate_ne_zero {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n) : deltaRealCoordinate b i ≠ 0 := by
  intro h
  have hh := deltaRealCoordinate_basis b i
  rw [h, LinearMap.zero_apply] at hh
  norm_num at hh

theorem delta_adapted_coordinate_mass (X : ConvexProgression) (D : MahlerBoxData X)
    (U : Finset (Fin X.rank → ℤ)) {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin X.rank → ℤ)), δ • x ∈ X.body)
    (hround : ∀ x : Fin X.rank → ℝ, ∃ v : Fin X.rank → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) X.body) (i : Fin X.rank) :
    (∑ u ∈ U, ((|latticeCoordinates D.basis u i| : ℤ) : ℝ)) ≤ 4 * D.bound i / δ := by
  let ℓ := deltaRealCoordinate D.basis i
  have hcover (v : Fin X.rank → ℤ) (hv : intCastVec v ∈ X.body) :
      |ℓ (intCastVec v)| ≤ D.bound i := by
    rw [deltaRealCoordinate_intCast, ← Int.cast_abs]
    exact D.cover v hv i
  have hbody := delta_real_width_le_twice_lattice_width
    (Metric.isCompact_of_isClosed_isBounded X.body_closed X.body_bounded)
    X.body_zero X.body_convex X.body_neg hround ℓ (D.bound i) hcover
  have hmass := CFP.delta_zonotope_coordinate_mass_le
    (fun u : U => intCastVec (u : Fin X.rank → ℤ)) hδ hsub ℓ hbody
  calc
    _ = ∑ u : U, |ℓ (intCastVec (u : Fin X.rank → ℤ))| := by
      rw [Finset.sum_coe_sort U (fun u => |ℓ (intCastVec u)|)]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [ℓ]
      rw [deltaRealCoordinate_intCast, Int.cast_abs]
    _ ≤ 2 * (2 * D.bound i) / δ := hmass
    _ = _ := by ring

theorem delta_adapted_width_of_robust_spanning (X : ConvexProgression) (D : MahlerBoxData X)
    (U : Finset (Fin X.rank → ℤ)) (k : ℕ) (hk : 2 * k ≤ U.card)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤)
    {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin X.rank → ℤ)), δ • x ∈ X.body)
    (hround : ∀ x : Fin X.rank → ℝ, ∃ v : Fin X.rank → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) X.body) (i : Fin X.rank) :
    (U.card : ℝ) ≤ 8 * D.bound i / δ := by
  classical
  let ℓ := deltaRealCoordinate D.basis i
  have hcount := CFP.delta_nonzero_functional_card_of_robust_spanning U intCastVec k hspan
    ℓ (deltaRealCoordinate_ne_zero D.basis i)
  have hfilter : U.filter (fun u => ℓ (intCastVec u) ≠ 0) =
      U.filter (fun u => latticeCoordinates D.basis u i ≠ 0) := by
    ext u
    simp only [Finset.mem_filter, ℓ, deltaRealCoordinate_intCast, Int.cast_ne_zero]
  rw [hfilter] at hcount
  have hnat := CFP.delta_nonzero_card_le_sum_natAbs U (fun u => latticeCoordinates D.basis u i)
  have htwice : U.card ≤ 2 * ∑ u ∈ U, (latticeCoordinates D.basis u i).natAbs := by omega
  have hreal : (U.card : ℝ) ≤ 2 * ∑ u ∈ U, ((|latticeCoordinates D.basis u i| : ℤ) : ℝ) := by
    have hh : (U.card : ℝ) ≤ 2 * ∑ u ∈ U, ((latticeCoordinates D.basis u i).natAbs : ℝ) := by
      exact_mod_cast htwice
    simpa only [Nat.cast_natAbs] using hh
  calc
    _ ≤ 2 * ∑ u ∈ U, ((|latticeCoordinates D.basis u i| : ℤ) : ℝ) := hreal
    _ ≤ 2 * (4 * D.bound i / δ) := mul_le_mul_of_nonneg_left
      (delta_adapted_coordinate_mass X D U hδ hsub hround i) (by norm_num)
    _ = _ := by ring

end Erdos587.GeneralizedAP
