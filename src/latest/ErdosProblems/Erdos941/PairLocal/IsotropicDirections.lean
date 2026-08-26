/- Adapted from the checked repository proof in Erdos1148/IsotropicDirections.lean. -/
import ErdosProblems.Erdos941.PairLocal.PairEmbeddings

/-!
# Isotropic directions for the split discriminant form

For fields of characteristic different from two, isotropic lines are
parametrized by the projective line: an affine parameter and one point at
infinity. These are the directions indexing neighbors in the local tree.
-/

namespace Erdos941.PairLocal

def isotropicDirection {K : Type*} [Field K] : Option K → K × K × K
  | none => (0, 0, 1)
  | some x => (1, 2 * x, x ^ 2)

lemma discr_isotropicDirection {K : Type*} [Field K] (x : Option K) :
    discr (isotropicDirection x) = 0 := by
  cases x <;> dsimp [isotropicDirection, discr] <;> ring

lemma isotropicDirection_ne_zero {K : Type*} [Field K] (x : Option K) :
    isotropicDirection x ≠ 0 := by
  cases x <;> simp [isotropicDirection]

lemma exists_isotropicDirection {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K × K × K} (ht : discr t = 0) (hne : t ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ∃ x : Option K, t = a • isotropicDirection x := by
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by norm_num] using mul_ne_zero h2 h2
  by_cases ha : t.1 = 0
  · have hb : t.2.1 = 0 := by
      apply sq_eq_zero_iff.mp
      simpa [discr, ha] using ht
    have hc : t.2.2 ≠ 0 := by
      intro hc
      exact hne (Prod.ext ha (Prod.ext hb hc))
    refine ⟨t.2.2, hc, none, ?_⟩
    ext <;> simp [isotropicDirection, ha, hb]
  · have hc : t.2.2 = t.2.1 ^ 2 / (4 * t.1) := by
      apply (eq_div_iff (mul_ne_zero h4 ha)).mpr
      dsimp [discr] at ht
      linear_combination -ht
    refine ⟨t.1, ha, some (t.2.1 / (2 * t.1)), ?_⟩
    apply Prod.ext
    · simp [isotropicDirection]
    · apply Prod.ext
      · dsimp [isotropicDirection]
        field_simp
      · dsimp [isotropicDirection]
        rw [hc]
        field_simp
        ring

lemma pairing_smul_smul {R : Type*} [CommRing R] (a b : R) (t u : R × R × R) :
    pairing (a • t) (b • u) = a * b * pairing t u := by
  dsimp [pairing]
  ring

lemma pairing_smul_left {R : Type*} [CommRing R] (a : R) (t u : R × R × R) :
    pairing (a • t) u = a * pairing t u := by
  simpa only [one_smul, mul_one] using pairing_smul_smul a 1 t u

lemma pairing_isotropicDirection_eq_zero_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (x y : Option K) : pairing (isotropicDirection x) (isotropicDirection y) = 0 ↔ x = y := by
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by norm_num] using mul_ne_zero h2 h2
  cases x with
  | none => cases y <;> simp [isotropicDirection, pairing, h4]
  | some x =>
    cases y with
    | none => simp [isotropicDirection, pairing, h4]
    | some y =>
      have heq : pairing (isotropicDirection (some x)) (isotropicDirection (some y)) =
          -4 * (x - y) ^ 2 := by
        dsimp [isotropicDirection, pairing]
        ring
      rw [heq]
      simp [mul_eq_zero, h4, sub_eq_zero]

/-- An isotropic nonzero vector determines exactly one orthogonal isotropic direction. -/
lemma existsUnique_orthogonal_direction_of_isotropic {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {t : K × K × K} (ht : discr t = 0) (hne : t ≠ 0) :
    ∃! x : Option K, pairing t (isotropicDirection x) = 0 := by
  obtain ⟨a, ha, x, htx⟩ := exists_isotropicDirection h2 ht hne
  refine ⟨x, ?_, ?_⟩
  · dsimp only
    rw [htx, pairing_smul_left,
      (pairing_isotropicDirection_eq_zero_iff h2 x x).mpr rfl, mul_zero]
  · intro y hy
    rw [htx, pairing_smul_left] at hy
    have hxy := (pairing_isotropicDirection_eq_zero_iff h2 x y).mp
      ((mul_eq_zero.mp hy).resolve_left ha)
    exact hxy.symm

/-- A totally isotropic plane cannot occur in this split nondegenerate ternary space. -/
lemma isotropic_orthogonal_collinear {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t u : K × K × K} (ht : discr t = 0) (hu : discr u = 0)
    (hne : t ≠ 0) (hpair : pairing t u = 0) : ∃ a : K, u = a • t := by
  by_cases hu0 : u = 0
  · exact ⟨0, by simp [hu0]⟩
  obtain ⟨a, ha, x, htx⟩ := exists_isotropicDirection h2 ht hne
  obtain ⟨b, hb, y, huy⟩ := exists_isotropicDirection h2 hu hu0
  rw [htx, huy, pairing_smul_smul] at hpair
  have hp := (mul_eq_zero.mp hpair).resolve_left (mul_ne_zero ha hb)
  have hxy := (pairing_isotropicDirection_eq_zero_iff h2 x y).mp hp
  refine ⟨b / a, ?_⟩
  rw [htx, huy, hxy, smul_smul, div_mul_cancel₀ b ha]

lemma pairing_isotropicDirection_some {K : Type*} [Field K] (t : K × K × K) (x : K) :
    pairing t (isotropicDirection (some x)) = -4 * (t.1 * x ^ 2 - t.2.1 * x + t.2.2) := by
  dsimp [pairing, isotropicDirection]
  ring

lemma pairing_isotropicDirection_none {K : Type*} [Field K] (t : K × K × K) :
    pairing t (isotropicDirection none) = -4 * t.1 := by
  dsimp [pairing, isotropicDirection]
  ring

lemma coefficients_zero_of_three_roots {K : Type*} [Field K] {a b c x y z : K}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : a * x ^ 2 - b * x + c = 0) (hy : a * y ^ 2 - b * y + c = 0)
    (hz : a * z ^ 2 - b * z + c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hxy' : a * (x + y) - b = 0 := by
    have hm : (x - y) * (a * (x + y) - b) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hxy)
  have hxz' : a * (x + z) - b = 0 := by
    have hm : (x - z) * (a * (x + z) - b) = 0 := by linear_combination hx - hz
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hxz)
  have ha : a = 0 := by
    have hm : a * (y - z) = 0 := by linear_combination hxy' - hxz'
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hyz)
  have hb : b = 0 := by simpa [ha] using hxy'
  have hc : c = 0 := by simpa [ha, hb] using hx
  exact ⟨ha, hb, hc⟩

lemma affine_root_of_orthogonal {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K × K × K} {x : K} (hx : pairing t (isotropicDirection (some x)) = 0) :
    t.1 * x ^ 2 - t.2.1 * x + t.2.2 = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by norm_num] using mul_ne_zero h2 h2
  rw [pairing_isotropicDirection_some] at hx
  exact (mul_eq_zero.mp hx).resolve_left (neg_ne_zero.mpr h4)

lemma eq_zero_of_three_affine_orthogonal {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K × K × K} {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : pairing t (isotropicDirection (some x)) = 0)
    (hy : pairing t (isotropicDirection (some y)) = 0)
    (hz : pairing t (isotropicDirection (some z)) = 0) : t = 0 := by
  obtain ⟨ha, hb, hc⟩ := coefficients_zero_of_three_roots hxy hxz hyz
    (affine_root_of_orthogonal h2 hx) (affine_root_of_orthogonal h2 hy)
    (affine_root_of_orthogonal h2 hz)
  exact Prod.ext ha (Prod.ext hb hc)

lemma eq_zero_of_infinity_two_affine_orthogonal {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K × K × K} {x y : K} (hxy : x ≠ y)
    (hinf : pairing t (isotropicDirection none) = 0)
    (hx : pairing t (isotropicDirection (some x)) = 0)
    (hy : pairing t (isotropicDirection (some y)) = 0) : t = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by norm_num] using mul_ne_zero h2 h2
  have ha : t.1 = 0 := by
    rw [pairing_isotropicDirection_none] at hinf
    exact (mul_eq_zero.mp hinf).resolve_left (neg_ne_zero.mpr h4)
  have hx' := affine_root_of_orthogonal h2 hx
  have hy' := affine_root_of_orthogonal h2 hy
  rw [ha, zero_mul, zero_sub] at hx' hy'
  have hb : t.2.1 = 0 := by
    have hm : t.2.1 * (x - y) = 0 := by linear_combination hy' - hx'
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hxy)
  have hc : t.2.2 = 0 := by simpa [hb] using hx'
  exact Prod.ext ha (Prod.ext hb hc)

lemma eq_zero_of_three_orthogonal_directions {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K × K × K} {x y z : Option K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : pairing t (isotropicDirection x) = 0)
    (hy : pairing t (isotropicDirection y) = 0)
    (hz : pairing t (isotropicDirection z) = 0) : t = 0 := by
  cases x with
  | none =>
    cases y with
    | none => exact (hxy rfl).elim
    | some y =>
      cases z with
      | none => exact (hxz rfl).elim
      | some z =>
        exact eq_zero_of_infinity_two_affine_orthogonal h2
          (fun h => hyz (congrArg some h)) hx hy hz
  | some x =>
    cases y with
    | none =>
      cases z with
      | none => exact (hyz rfl).elim
      | some z =>
        exact eq_zero_of_infinity_two_affine_orthogonal h2
          (fun h => hxz (congrArg some h)) hy hx hz
    | some y =>
      cases z with
      | none =>
        exact eq_zero_of_infinity_two_affine_orthogonal h2
          (fun h => hxy (congrArg some h)) hz hx hy
      | some z =>
        exact eq_zero_of_three_affine_orthogonal h2
          (fun h => hxy (congrArg some h)) (fun h => hxz (congrArg some h))
          (fun h => hyz (congrArg some h)) hx hy hz

/-- A nonzero vector is orthogonal to at most two isotropic directions. -/
theorem card_orthogonal_directions_le_two {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K × K × K} (ht : t ≠ 0) (s : Finset (Option K))
    (hs : ∀ x ∈ s, pairing t (isotropicDirection x) = 0) : s.card ≤ 2 := by
  by_contra hcard
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (by omega : 2 < s.card)
  exact ht (eq_zero_of_three_orthogonal_directions h2 hxy hxz hyz (hs x hx) (hs y hy) (hs z hz))

end Erdos941.PairLocal
