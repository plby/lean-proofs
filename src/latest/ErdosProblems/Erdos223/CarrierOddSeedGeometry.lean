/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos223.CarrierOdd

/-!
# Seed-frame geometry for odd-dimensional carriers

This module packages the dimension argument behind the odd carrier upgrade.
For `p` mutually cross-unit triples, the two affine directions selected in
each part form one linearly independent family of `2p` vectors.  In
`Point (2p+1)` their span therefore has a one-dimensional orthogonal
complement.  It also records the coordinate isometry associated to a full
orthonormal frame.
-/

open scoped BigOperators RealInnerProductSpace

namespace Erdos223.CarrierOdd

noncomputable section

private lemma inner_sub_sub_eq_zero_of_cross_unit_generic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c e : E}
    (hac : dist a c = 1) (hae : dist a e = 1)
    (hbc : dist b c = 1) (hbe : dist b e = 1) :
    inner ℝ (b - a) (e - c) = 0 := by
  have h_ac : inner ℝ (a - c) (a - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hac]
    norm_num
  have h_ae : inner ℝ (a - e) (a - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hae]
    norm_num
  have h_bc : inner ℝ (b - c) (b - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbc]
    norm_num
  have h_be : inner ℝ (b - e) (b - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbe]
    norm_num
  rw [real_inner_sub_sub_self] at h_ac h_ae h_bc h_be
  simp only [inner_sub_left, inner_sub_right] at ⊢
  linarith

private lemma three_points_on_unit_sphere_independent_generic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c q : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : dist a q = 1) (hbq : dist b q = 1) (hcq : dist c q = 1) :
    LinearIndependent ℝ ![b - a, c - a] := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [LinearIndependent.pair_iff' hu]
  intro t ht
  have h_a : inner ℝ (a - q) (a - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, haq]
    norm_num
  have h_b : inner ℝ (b - q) (b - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbq]
    norm_num
  have h_c : inner ℝ (c - q) (c - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hcq]
    norm_num
  have hu_pos : 0 < inner ℝ (b - a) (b - a) := (real_inner_self_pos).2 hu
  have hb_split : b - q = (a - q) + (b - a) := by abel
  have hc_split : c - q = (a - q) + (c - a) := by abel
  rw [hb_split] at h_b
  rw [hc_split, ← ht] at h_c
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h_b h_c
  rw [real_inner_comm (a - q) (b - a)] at h_b h_c
  have hpoly : (t * (t - 1)) * inner ℝ (b - a) (b - a) = 0 := by
    linear_combination h_c - h_a - t * h_b + t * h_a
  have ht_factor : t * (t - 1) = 0 :=
    (mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hu_pos)
  have ht_cases : t = 0 ∨ t = 1 := by
    rcases mul_eq_zero.mp ht_factor with ht0 | ht1
    · exact Or.inl ht0
    · exact Or.inr (sub_eq_zero.mp ht1)
  rcases ht_cases with rfl | rfl
  · apply hac
    have hca : c = a := sub_eq_zero.mp (by simpa using ht.symm)
    exact hca.symm
  · apply hbc
    have huv : b - a = c - a := by simpa using ht
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = (c - a) + a := congrArg (fun z : E ↦ z + a) huv
      _ = c := sub_add_cancel c a

/-- The two affine directions selected from each cross-unit triple. -/
def partDirectionGeneric {E : Type*} [AddGroup E] {p : ℕ}
    (x : Fin p → Fin 3 → E) (v : Fin p × Fin 2) : E :=
  x v.1 v.2.succ - x v.1 0

/-- In any real inner-product space, the `2p` selected directions from `p`
injective cross-unit triples are linearly independent. -/
theorem partDirections_linearIndependent_generic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ℕ} (hp : 2 ≤ p) {x : Fin p → Fin 3 → E}
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    LinearIndependent ℝ (partDirectionGeneric x) := by
  have hne (i : Fin p) {a b : Fin 3} (hab : a ≠ b) : x i a ≠ x i b :=
    fun h ↦ hab (hinj i h)
  have hblock (i : Fin p) :
      LinearIndependent ℝ (fun k : Fin 2 ↦ partDirectionGeneric x (i, k)) := by
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by
      rw [Fintype.card_fin]
      omega) i
    have h := three_points_on_unit_sphere_independent_generic
      (a := x i 0) (b := x i 1) (c := x i 2) (q := x j 0)
      (hne i (by decide)) (hne i (by decide)) (hne i (by decide))
      (hdist hji.symm 0 0) (hdist hji.symm 1 0) (hdist hji.symm 2 0)
    rw [show (fun k : Fin 2 ↦ partDirectionGeneric x (i, k)) =
        ![x i 1 - x i 0, x i 2 - x i 0] by
      funext k
      fin_cases k <;> rfl]
    exact h
  have hortho {i j : Fin p} (hij : i ≠ j) (k l : Fin 2) :
      inner ℝ (partDirectionGeneric x (i, k))
        (partDirectionGeneric x (j, l)) = 0 := by
    exact inner_sub_sub_eq_zero_of_cross_unit_generic
      (hdist hij 0 0) (hdist hij 0 l.succ)
      (hdist hij k.succ 0) (hdist hij k.succ l.succ)
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  let z : Fin p → E :=
    fun i ↦ ∑ k : Fin 2, g (i, k) • partDirectionGeneric x (i, k)
  have hsum : ∑ i : Fin p, z i = 0 := by
    change (∑ i : Fin p, ∑ k : Fin 2,
      g (i, k) • partDirectionGeneric x (i, k)) = 0
    calc
      _ = ∑ v : Fin p × Fin 2, g v • partDirectionGeneric x v :=
        (Fintype.sum_prod_type
          (fun v : Fin p × Fin 2 ↦ g v • partDirectionGeneric x v)).symm
      _ = 0 := hg
  have hcross {i j : Fin p} (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    simp only [z, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    exact Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ by
      rw [hortho hij]
      ring
  have hz (i : Fin p) : z i = 0 := by
    have hi := congrArg (fun y : E ↦ inner ℝ y (z i)) hsum
    simp only [sum_inner, inner_zero_left] at hi
    have hii : inner ℝ (z i) (z i) = 0 := by
      rw [← hi]
      symm
      exact Finset.sum_eq_single i
        (fun j _ hji ↦ hcross hji)
        (by intro hiu; exact (hiu (Finset.mem_univ i)).elim)
    exact inner_self_eq_zero.mp hii
  exact (Fintype.linearIndependent_iff.mp (hblock v.1)
    (fun k ↦ g (v.1, k)) (hz v.1)) v.2

/-- An orthonormal family with exactly the ambient number of vectors gives
the coordinate isometry required by `Carrier`. -/
def coordOfOrthonormalFrame {p : ℕ}
    (v : Fin (2 * p + 1) → Point (2 * p + 1))
    (hv : Orthonormal ℝ v) :
    Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1) := by
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by
      simp [finrank_euclideanSpace])
  exact (OrthonormalBasis.mk hv hspan.ge).repr.symm

@[simp] theorem coordOfOrthonormalFrame_single {p : ℕ}
    (v : Fin (2 * p + 1) → Point (2 * p + 1))
    (hv : Orthonormal ℝ v) (i : Fin (2 * p + 1)) :
    coordOfOrthonormalFrame v hv (EuclideanSpace.single i 1) = v i := by
  let b : OrthonormalBasis (Fin (2 * p + 1)) ℝ (Point (2 * p + 1)) := by
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
      hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by
        simp [finrank_euclideanSpace])
    exact OrthonormalBasis.mk hv hspan.ge
  change b.repr.symm (EuclideanSpace.single i 1) = v i
  apply b.repr.injective
  rw [b.repr.apply_symm_apply]
  have hb : b i = v i := by
    dsimp [b]
    rw [OrthonormalBasis.coe_mk]
  rw [← hb, b.repr_self]

@[simp] theorem coordOfOrthonormalFrame_symm_apply {p : ℕ}
    (v : Fin (2 * p + 1) → Point (2 * p + 1))
    (hv : Orthonormal ℝ v) (i : Fin (2 * p + 1)) :
    (coordOfOrthonormalFrame v hv).symm (v i) = EuclideanSpace.single i 1 := by
  apply (coordOfOrthonormalFrame v hv).injective
  rw [(coordOfOrthonormalFrame v hv).apply_symm_apply,
    coordOfOrthonormalFrame_single]

/-- The `2p` independent seed directions leave exactly one orthogonal
dimension in `Point (2p+1)`. -/
theorem finrank_orthogonal_span_partDirections_eq_one {p : ℕ}
    (v : Fin p × Fin 2 → Point (2 * p + 1))
    (hv : LinearIndependent ℝ v) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range v))ᗮ = 1 := by
  let W := Submodule.span ℝ (Set.range v)
  have hW : Module.finrank ℝ W = 2 * p := by
    rw [show Module.finrank ℝ W = Fintype.card (Fin p × Fin 2) from
      finrank_span_eq_card hv]
    simp [Nat.mul_comm]
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hamb : Module.finrank ℝ (Point (2 * p + 1)) = 2 * p + 1 := by
    simp [finrank_euclideanSpace]
  rw [hW, hamb] at hsum
  change Module.finrank ℝ Wᗮ = 1
  omega

/-- Four circle classes select an axis center that also completes every
point having unit distance to all seed circles outside its own class.  The
second conjunct is the form needed when a fixed seed frame is extended to
the rest of an exact cross-unit core. -/
theorem exists_axis_weak_center_of_four_le_with_completion
    {p : ℕ} (z radiusSq : Fin p → ℝ) (hp : 4 ≤ p)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1) :
    ∃ s : ℝ,
      (∀ m, radiusSq m + (z m - s) ^ 2 = (1 : ℝ) / 2) ∧
      ∀ (i : Fin p) (q R : ℝ),
        (∀ j, j ≠ i → R + radiusSq j + (q - z j) ^ 2 = 1) →
        R + (q - s) ^ 2 = (1 : ℝ) / 2 := by
  let j₀ : Fin p := ⟨0, by omega⟩
  by_cases hzall : ∀ m, z m = z j₀
  · let i₀ : Fin p := ⟨1, by omega⟩
    let k₀ : Fin p := ⟨2, by omega⟩
    have hi₀j₀ : i₀ ≠ j₀ := by norm_num [i₀, j₀]
    have hi₀k₀ : i₀ ≠ k₀ := by norm_num [i₀, k₀]
    have hj₀k₀ : j₀ ≠ k₀ := by norm_num [j₀, k₀]
    let s := z i₀
    have hs : ∀ m, radiusSq m + (z m - s) ^ 2 = (1 : ℝ) / 2 :=
      axis_center_of_three_equal_parts z radiusSq hcross
        (i := i₀) (j := j₀) (k := k₀) hi₀j₀ hi₀k₀ hj₀k₀
        (fun m ↦ (hzall m).trans (hzall i₀).symm)
    refine ⟨s, hs, ?_⟩
    intro i q R hq
    obtain ⟨t, hti⟩ := Fintype.exists_ne_of_one_lt_card (by
      rw [Fintype.card_fin]
      omega) i
    have hqt := hq t hti
    have hst := hs t
    have hzt : z t = s := (hzall t).trans (hzall i₀).symm
    rw [hzt] at hqt
    rw [hzt, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hst
    nlinarith
  · push Not at hzall
    obtain ⟨i₀, hzi₀j₀⟩ := hzall
    have hi₀j₀ : i₀ ≠ j₀ := by
      intro h
      exact hzi₀j₀ (congrArg z h)
    let S : Finset (Fin p) := (Finset.univ.erase i₀).erase j₀
    have hj₀mem : j₀ ∈ Finset.univ.erase i₀ := by simp [hi₀j₀.symm]
    have hScard : S.card = p - 2 := by
      dsimp [S]
      rw [Finset.card_erase_of_mem hj₀mem,
        Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hS : 1 < S.card := by omega
    obtain ⟨k, hkS, l, hlS, hkl⟩ := Finset.one_lt_card.mp hS
    have hki₀ : k ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hkS).2).1
    have hkj₀ : k ≠ j₀ := (Finset.mem_erase.mp hkS).1
    have hli₀ : l ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hlS).2).1
    have hlj₀ : l ≠ j₀ := (Finset.mem_erase.mp hlS).1
    have hi₀k := hcross hki₀.symm
    have hj₀k := hcross hkj₀.symm
    have hi₀l := hcross hli₀.symm
    have hj₀l := hcross hlj₀.symm
    have hzlk : z l = z k := by
      by_contra hne
      have hprod : (z i₀ - z j₀) * (z l - z k) = 0 := by nlinarith
      exact hzi₀j₀ (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
        (sub_ne_zero.mpr hne)))
    let s := z k
    have hs : ∀ m, radiusSq m + (z m - s) ^ 2 = (1 : ℝ) / 2 :=
      axis_center_of_four_parts z radiusSq hcross hi₀j₀ hki₀.symm
        hli₀.symm hkj₀.symm hlj₀.symm hkl hzi₀j₀
    refine ⟨s, hs, ?_⟩
    intro m q R hq
    by_cases hmk : m = k
    · have hql := hq l (by exact fun hlm ↦ hkl (hlm.trans hmk).symm)
      have hsl := hs l
      dsimp [s] at hql hsl ⊢
      rw [hzlk] at hql
      rw [hzlk, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hsl
      nlinarith
    · have hqk := hq k (fun hkm ↦ hmk hkm.symm)
      have hsk := hs k
      dsimp [s] at hqk hsk ⊢
      rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hsk
      nlinarith

lemma inner_eq_axis_mul_of_inAxisPlanes {p : ℕ} {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p + 1)} (hx : InAxisPlane i x) (hy : InAxisPlane j y) :
    inner ℝ x y = x (axisIndex p) * y (axisIndex p) := by
  classical
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  have hsum :
      (∑ k : Fin (2 * p + 1), y k * x k) =
        y (axisIndex p) * x (axisIndex p) := by
    apply Finset.sum_eq_single (axisIndex p)
    · intro k _ hka
      by_cases hkf : k = planeFirst p i
      · have hkyf : k ≠ planeFirst p j := by
          intro h
          apply hij
          exact planeFirst_injective p (hkf.symm.trans h)
        have hkys : k ≠ planeSecond p j := by
          intro h
          exact planeFirst_ne_planeSecond p i j (hkf.symm.trans h)
        rw [hy k hkyf hkys hka]
        simp
      · by_cases hks : k = planeSecond p i
        · have hkyf : k ≠ planeFirst p j := by
            intro h
            exact planeFirst_ne_planeSecond p j i (h.symm.trans hks)
          have hkys : k ≠ planeSecond p j := by
            intro h
            apply hij
            exact planeSecond_injective p (hks.symm.trans h)
          rw [hy k hkyf hkys hka]
          simp
        · rw [hx k hkf hks hka]
          simp
    · intro ha
      exact (ha (Finset.mem_univ _)).elim
  simpa [mul_comm] using hsum

/-- The distance from a supported point to one supported seed in another
part is exactly the scalar energy equation used by axis alignment. -/
lemma axisPlane_energy_eq_of_dist_seed
    {p : ℕ} (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    {i j : Fin p} (hij : i ≠ j)
    (x y : Point (2 * p + 1)) (z radiusSq : ℝ)
    (hx : InAxisPlane i (coord.symm (x - baseCenter)))
    (hy : InAxisPlane j (coord.symm (y - baseCenter)))
    (hyaxis : coord.symm (y - baseCenter) (axisIndex p) = z)
    (hynorm : ‖coord.symm (y - baseCenter)‖ ^ 2 = radiusSq + z ^ 2)
    (hdist : dist x y = 1) :
    (‖coord.symm (x - baseCenter)‖ ^ 2 -
        (coord.symm (x - baseCenter) (axisIndex p)) ^ 2) +
      radiusSq +
        (coord.symm (x - baseCenter) (axisIndex p) - z) ^ 2 = 1 := by
  let u := coord.symm (x - baseCenter)
  let v := coord.symm (y - baseCenter)
  have huv : inner ℝ u v = u (axisIndex p) * v (axisIndex p) :=
    inner_eq_axis_mul_of_inAxisPlanes hij hx hy
  have hvu : inner ℝ v u = u (axisIndex p) * v (axisIndex p) := by
    rw [real_inner_comm]
    exact huv
  have hduv : dist u v = 1 := by
    calc
      dist u v = dist (coord u) (coord v) := (coord.dist_map u v).symm
      _ = dist (x - baseCenter) (y - baseCenter) := by simp [u, v]
      _ = dist x y := dist_sub_right x y baseCenter
      _ = 1 := hdist
  have hsq : dist u v ^ 2 = 1 := by rw [hduv]; norm_num
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq] at hsq
  simp only [inner_sub_left, inner_sub_right] at hsq
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, huv, hvu] at hsq
  change v (axisIndex p) = z at hyaxis
  change ‖v‖ ^ 2 = radiusSq + z ^ 2 at hynorm
  change (‖u‖ ^ 2 - u (axisIndex p) ^ 2) + radiusSq +
    (u (axisIndex p) - z) ^ 2 = 1
  rw [hyaxis] at hsq
  nlinarith

/-- Exact cross-unit completion of a coaxial seed frame is a weak carrier
when there are at least four parts.  The completed points may have arbitrary
axis coordinate and therefore fill the whole three-dimensional component
sphere. -/
theorem isWeakCarrierSet_of_axisPlane_seed_certificate_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (seed : Fin p → Point (2 * p + 1))
    (z radiusSq : Fin p → ℝ)
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - baseCenter)))
    (hseedSupport : ∀ j,
      InAxisPlane j (coord.symm (seed j - baseCenter)))
    (hseedAxis : ∀ j,
      coord.symm (seed j - baseCenter) (axisIndex p) = z j)
    (hseedNorm : ∀ j,
      ‖coord.symm (seed j - baseCenter)‖ ^ 2 = radiusSq j + (z j) ^ 2)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1)
    (hdist : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}) j,
      j ≠ part x → dist x.1 (seed j) = 1) :
    IsWeakCarrierSet (p := p) A := by
  obtain ⟨s, _hs, hcomplete⟩ :=
    exists_axis_weak_center_of_four_le_with_completion z radiusSq hp hcross
  let center := baseCenter + coord (axisVector p s)
  apply isWeakCarrierSet_of_coordinate_certificate_sq center coord part
  · intro x q hqf hqs hqa
    have hu := hsupport x q hqf hqs hqa
    have he : axisVector p s q = 0 := by simp [axisVector_apply, hqa]
    change (coord.symm (x.1 - center)) q = 0
    have hcoord : coord.symm (x.1 - center) =
        coord.symm (x.1 - baseCenter) - axisVector p s := by
      dsimp [center]
      rw [show x.1 - (baseCenter + coord (axisVector p s)) =
          (x.1 - baseCenter) - coord (axisVector p s) by abel]
      rw [map_sub, coord.symm_apply_apply]
    rw [hcoord, PiLp.sub_apply, hu, he, sub_zero]
  · intro x
    let u := coord.symm (x.1 - baseCenter)
    let e := axisVector p s
    let q := u (axisIndex p)
    let R := ‖u‖ ^ 2 - q ^ 2
    have henergy : ∀ j, j ≠ part x →
        R + radiusSq j + (q - z j) ^ 2 = 1 := by
      intro j hj
      exact axisPlane_energy_eq_of_dist_seed baseCenter coord hj.symm x.1 (seed j)
        (z j) (radiusSq j) (hsupport x) (hseedSupport j)
        (hseedAxis j) (hseedNorm j) (hdist x j hj)
    have hscalar : R + (q - s) ^ 2 = (1 : ℝ) / 2 :=
      hcomplete (part x) q R henergy
    have hcoord : coord.symm (x.1 - center) = u - e := by
      dsimp [center, u, e]
      rw [show x.1 - (baseCenter + coord (axisVector p s)) =
          (x.1 - baseCenter) - coord (axisVector p s) by abel]
      rw [map_sub, coord.symm_apply_apply]
    rw [hcoord, norm_sub_sq_real]
    have hinner : inner ℝ u e = s * q := by
      dsimp [e, axisVector, q]
      rw [EuclideanSpace.inner_single_right]
      simp
    have hnorme : ‖e‖ ^ 2 = s ^ 2 := by
      dsimp [e, axisVector]
      rw [EuclideanSpace.norm_single, Real.norm_eq_abs, sq_abs]
    rw [hinner, hnorme]
    dsimp [R, q] at hscalar
    nlinarith

/-- Once a fixed coordinate frame puts every point in its assigned
axis-plane, exact cross-unit distances alone force the weak carrier. -/
theorem isWeakCarrierSet_of_axisPlane_cross_unit_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (seed : Fin p → Point (2 * p + 1))
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - baseCenter)))
    (hseedSupport : ∀ j,
      InAxisPlane j (coord.symm (seed j - baseCenter)))
    (hseedCross : ∀ {i j : Fin p}, i ≠ j → dist (seed i) (seed j) = 1)
    (hdist : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}) j,
      j ≠ part x → dist x.1 (seed j) = 1) :
    IsWeakCarrierSet (p := p) A := by
  let z : Fin p → ℝ := fun j ↦
    coord.symm (seed j - baseCenter) (axisIndex p)
  let radiusSq : Fin p → ℝ := fun j ↦
    ‖coord.symm (seed j - baseCenter)‖ ^ 2 - (z j) ^ 2
  apply isWeakCarrierSet_of_axisPlane_seed_certificate_four hp baseCenter coord
    part seed z radiusSq hsupport hseedSupport
  · intro j
    rfl
  · intro j
    dsimp [radiusSq]
    ring
  · intro i j hij
    have h := axisPlane_energy_eq_of_dist_seed baseCenter coord hij
      (seed i) (seed j) (z j) (radiusSq j)
      (hseedSupport i) (hseedSupport j) rfl (by
        dsimp [radiusSq]
        ring) (hseedCross hij)
    simpa [z, radiusSq] using h
  · exact hdist

end

end Erdos223.CarrierOdd
