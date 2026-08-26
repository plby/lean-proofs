import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

open LinearMap

/-- Three distinct isotropic lines in a two-dimensional symmetric bilinear
space force the cross term of a basis to vanish.  This is the algebraic core
of the safe-kernel cap-two construction. -/
theorem cross_zero_of_three_isotropic
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (u v w : V) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (hu : B u u = 0) (hv : B v v = 0) (hw : B w w = 0)
    (hwcomb : w = a • u + b • v) :
    B u v = 0 := by
  have huv_sym : B v u = B u v := hsym.eq v u
  have hcalc : B (a • u + b • v) (a • u + b • v) = 0 := by
    simpa [hwcomb] using hw
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul] at hcalc
  rw [hu, hv, huv_sym] at hcalc
  have hprod : 2 * a * b * B u v = 0 := by
    linear_combination hcalc
  have hcoef : 2 * a * b ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero htwo ha) hb
  exact (mul_eq_zero.mp hprod).resolve_left hcoef

/-- In a two-generated space, three pairwise-distinct isotropic lines force a
symmetric bilinear form to vanish identically.  The nonzero coefficients say
that the third line differs from each of the two basis lines. -/
theorem total_zero_of_three_isotropic
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (u v w : V) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (hu : B u u = 0) (hv : B v v = 0) (hw : B w w = 0)
    (hwcomb : w = a • u + b • v)
    (hgen : ∀ x : V, ∃ r s : K, x = r • u + s • v) :
    ∀ x y : V, B x y = 0 := by
  have huv := cross_zero_of_three_isotropic B hsym u v w a b ha hb htwo
    hu hv hw hwcomb
  have hvu : B v u = 0 := by simpa [hsym.eq v u] using huv
  intro x y
  rcases hgen x with ⟨r, s, rfl⟩
  rcases hgen y with ⟨t, z, rfl⟩
  simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hu, hv, huv, hvu]

/-- Two vectors with complementary nonzero coordinates generate any vector
space of finrank two. -/
theorem generate_of_two_cross_coordinates
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι]
    (coord : ι → V →ₗ[K] K) (u v : V) (x y : ι) (hxy : x ≠ y)
    (hu0 : coord x u = 0) (hv0 : coord y v = 0)
    (huy : coord y u ≠ 0) (hvx : coord x v ≠ 0)
    (hfin : Module.finrank K V = 2) :
    ∀ r : V, ∃ a b : K, r = a • u + b • v := by
  let pair : Fin 2 → V := ![u, v]
  have hli : LinearIndependent K pair := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have habx := congrArg (coord x) hab
    have haby := congrArg (coord y) hab
    simp [pair, hu0] at habx
    simp [pair, hv0] at haby
    have hb : b = 0 := habx.resolve_right hvx
    have ha : a = 0 := haby.resolve_right huy
    exact ⟨ha, hb⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank K V := by simp [hfin]
  let bas : Module.Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbas : (bas : Fin 2 → V) = pair :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  intro r
  refine ⟨bas.repr r 0, bas.repr r 1, ?_⟩
  have hr := bas.sum_repr r
  rw [Fin.sum_univ_two] at hr
  simpa [hbas, pair] using hr.symm

/-- Coordinate version of the safe-kernel cap mechanism.  If three isotropic
vectors generate three lines whose unique zero coordinates are distinct, then
on their two-generated relation space the form is totally isotropic. -/
theorem total_zero_of_three_unique_zero_vectors
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (coord : ι → V →ₗ[K] K)
    (u v w : V) (x y z : ι)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hu0 : coord x u = 0) (hv0 : coord y v = 0)
    (hu_full : ∀ t, t ≠ x → coord t u ≠ 0)
    (hv_full : ∀ t, t ≠ y → coord t v ≠ 0)
    (hw_full : ∀ t, t ≠ z → coord t w ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (hu : B u u = 0) (hv : B v v = 0) (hw : B w w = 0)
    (hgen : ∀ r : V, ∃ a b : K, r = a • u + b • v) :
    ∀ r s : V, B r s = 0 := by
  rcases hgen w with ⟨a, b, hwcomb⟩
  have ha : a ≠ 0 := by
    intro ha
    have hwy : coord y w ≠ 0 := hw_full y hyz
    rw [hwcomb, ha] at hwy
    simp [hv0] at hwy
  have hb : b ≠ 0 := by
    intro hb
    have hwx : coord x w ≠ 0 := hw_full x hxz
    rw [hwcomb, hb] at hwx
    simp [hu0] at hwx
  exact total_zero_of_three_isotropic B hsym u v w a b ha hb htwo
    hu hv hw hwcomb hgen

/-- Final deterministic kernel lemma: in a two-dimensional relation space,
three isotropic vectors with three distinct unique-zero coordinates force total
isotropy. -/
theorem finrank_two_total_zero_of_three_unique_zero_vectors
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (coord : ι → V →ₗ[K] K)
    (u v w : V) (x y z : ι)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hu0 : coord x u = 0) (hv0 : coord y v = 0)
    (hu_full : ∀ t, t ≠ x → coord t u ≠ 0)
    (hv_full : ∀ t, t ≠ y → coord t v ≠ 0)
    (hw_full : ∀ t, t ≠ z → coord t w ≠ 0)
    (hfin : Module.finrank K V = 2) (htwo : (2 : K) ≠ 0)
    (hu : B u u = 0) (hv : B v v = 0) (hw : B w w = 0) :
    ∀ r s : V, B r s = 0 := by
  have hgen := generate_of_two_cross_coordinates coord u v x y hxy hu0 hv0
    (hu_full y hxy.symm) (hv_full x hxy) hfin
  exact total_zero_of_three_unique_zero_vectors B hsym coord u v w x y z
    hxy hxz hyz hu0 hv0 hu_full hv_full hw_full htwo hu hv hw hgen

end Erdos538.IsotropicKernel
