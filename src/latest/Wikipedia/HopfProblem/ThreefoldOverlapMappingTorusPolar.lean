import Wikipedia.HopfProblem.EllipticLogGaugeRotation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Equiv

/-!
# Actual polar coordinates for the punctured elliptic tubes

The radius is the modulus of the root coordinate, not of its ramified
power.  Keeping the inequality on that power makes the domain exactly the
one used by the small filling.  These are homeomorphisms of the existing
subspace topologies; no complex structure is transported.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

open SpecialPeriods CuspUniformization

abbrev Circle := AddCircle (1 : ℝ)

/-- Root radii lying over the chosen punctured power disc. -/
abbrev Radius (n : ℕ) (r : ℝ) := {a : ℝ // 0 < a ∧ a < 1 ∧ a ^ n < r}

/-- The literal punctured root disc over the radius-`r` power disc. -/
abbrev RootDisc (n : ℕ) (r : ℝ) :=
  {z : Disc // (z : ℂ) ≠ 0 ∧ ‖(z : ℂ)‖ ^ n < r}

/-- The unit complex phase corresponding to the positively oriented circle. -/
def phase (t : Circle) : _root_.Circle := AddCircle.toCircle t

theorem phase_continuous : Continuous phase := AddCircle.continuous_toCircle

@[simp] theorem phase_zero : phase 0 = 1 := AddCircle.toCircle_zero

theorem phase_add (s t : Circle) : phase (s + t) = phase s * phase t :=
  AddCircle.toCircle_add s t

theorem phase_real (t : ℝ) : (phase (t : Circle) : ℂ) = exponential (t : ℂ) := by
  rw [phase, AddCircle.toCircle_apply_mk, _root_.Circle.coe_exp, exponential]
  congr 1
  push_cast
  ring

/-- Actual polar multiplication, with values in the original open disc. -/
def root (n : ℕ) (r : ℝ) (a : Radius n r) (t : Circle) : Disc :=
  ⟨(a : ℝ) • (phase t : ℂ), by
    have hn : ‖(a : ℝ) • (phase t : ℂ)‖ < 1 := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos a.property.1,
        _root_.Circle.norm_coe, mul_one] using a.property.2.1
    simpa [unitDisc] using hn⟩

@[simp] theorem root_norm (n : ℕ) (r : ℝ) (a : Radius n r) (t : Circle) :
    ‖(root n r a t : ℂ)‖ = (a : ℝ) := by
  simp only [root, norm_smul, Real.norm_eq_abs, abs_of_pos a.property.1,
    _root_.Circle.norm_coe, mul_one]

theorem root_ne_zero (n : ℕ) (r : ℝ) (a : Radius n r) (t : Circle) :
    (root n r a t : ℂ) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [root_norm]
  exact a.property.1.ne'

theorem root_continuous (n : ℕ) (r : ℝ) :
    Continuous (fun p : Radius n r × Circle => root n r p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp (phase_continuous.comp continuous_snd))).subtype_mk _

/-- Polar multiplication into the literal punctured root domain. -/
def polarRoot (n : ℕ) (r : ℝ) (p : Radius n r × Circle) : RootDisc n r :=
  ⟨root n r p.1 p.2, root_ne_zero n r p.1 p.2, by
    rw [root_norm]
    exact p.1.property.2.2⟩

theorem polarRoot_continuous (n : ℕ) (r : ℝ) : Continuous (polarRoot n r) :=
  (root_continuous n r).subtype_mk _

/-- The actual positive modulus of a nonzero root coordinate. -/
def rootRadius (n : ℕ) (r : ℝ) (z : RootDisc n r) : Radius n r :=
  ⟨‖((z : Disc) : ℂ)‖, norm_pos_iff.mpr z.property.1,
    disc_norm_lt_one z.val, z.property.2⟩

theorem rootRadius_continuous (n : ℕ) (r : ℝ) : Continuous (rootRadius n r) :=
  (continuous_subtype_val.comp continuous_subtype_val).norm.subtype_mk _

/-- The normalized unit complex number, without choosing an argument branch. -/
def unitPhase (n : ℕ) (r : ℝ) (z : RootDisc n r) : _root_.Circle :=
  ⟨‖((z : Disc) : ℂ)‖⁻¹ • ((z : Disc) : ℂ), by
    change ‖((z : Disc) : ℂ)‖⁻¹ • ((z : Disc) : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr z.property.1))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr z.property.1)⟩

theorem unitPhase_continuous (n : ℕ) (r : ℝ) : Continuous (unitPhase n r) := by
  have hz : Continuous (fun z : RootDisc n r => ((z : Disc) : ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((hz.norm.inv₀ fun z => norm_ne_zero_iff.mpr z.property.1).smul hz).subtype_mk _

/-- The additive phase of a nonzero root coordinate. -/
def rootAngle (n : ℕ) (r : ℝ) (z : RootDisc n r) : Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (unitPhase n r z)

theorem rootAngle_continuous (n : ℕ) (r : ℝ) : Continuous (rootAngle n r) :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp
    (unitPhase_continuous n r)

@[simp] theorem phase_rootAngle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    phase (rootAngle n r z) = unitPhase n r z := by
  rw [phase, ← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _

theorem polarRoot_radius_angle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    polarRoot n r (rootRadius n r z, rootAngle n r z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change ‖((z : Disc) : ℂ)‖ • (phase (rootAngle n r z) : ℂ) = ((z : Disc) : ℂ)
  rw [phase_rootAngle]
  change ‖((z : Disc) : ℂ)‖ • (‖((z : Disc) : ℂ)‖⁻¹ • ((z : Disc) : ℂ)) = _
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr z.property.1), one_smul]

@[simp] theorem rootRadius_polarRoot (n : ℕ) (r : ℝ) (p : Radius n r × Circle) :
    rootRadius n r (polarRoot n r p) = p.1 := Subtype.ext (root_norm n r p.1 p.2)

@[simp] theorem rootAngle_polarRoot (n : ℕ) (r : ℝ) (p : Radius n r × Circle) :
    rootAngle n r (polarRoot n r p) = p.2 := by
  apply (AddCircle.injective_toCircle one_ne_zero)
  change phase (rootAngle n r (polarRoot n r p)) = phase p.2
  rw [phase_rootAngle]
  apply Subtype.ext
  change ‖(root n r p.1 p.2 : ℂ)‖⁻¹ • ((p.1 : ℝ) • (phase p.2 : ℂ)) = _
  rw [root_norm, smul_smul, inv_mul_cancel₀ p.1.property.1.ne', one_smul]

/-- Polar coordinates in the genuine punctured small root disc. -/
def polarHomeomorph (n : ℕ) (r : ℝ) : RootDisc n r ≃ₜ Radius n r × Circle where
  toFun z := (rootRadius n r z, rootAngle n r z)
  invFun := polarRoot n r
  left_inv := polarRoot_radius_angle n r
  right_inv p := Prod.ext (rootRadius_polarRoot n r p) (rootAngle_polarRoot n r p)
  continuous_toFun := (rootRadius_continuous n r).prodMk (rootAngle_continuous n r)
  continuous_invFun := polarRoot_continuous n r

@[simp] theorem polarHomeomorph_symm_apply (n : ℕ) (r : ℝ) (p : Radius n r × Circle) :
    (polarHomeomorph n r).symm p = polarRoot n r p := rfl

/-- Every positive tube radius contains a positive root radius. -/
theorem radius_nonempty (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    Nonempty (Radius n r) := by
  let a : ℝ := min r 1 / 2
  have ha0 : 0 < a := half_pos (lt_min hr zero_lt_one)
  have ha1 : a < 1 := by
    have h := min_le_right r (1 : ℝ)
    dsimp only [a]
    linarith
  have har : a < r := by
    have h := min_le_left r (1 : ℝ)
    dsimp only [a] at ha0 ⊢
    linarith
  have hpow : a ^ n ≤ a := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1.le) ha0.le).trans_eq
      (one_mul a)
  exact ⟨⟨a, ha0, ha1, hpow.trans_lt har⟩⟩

/-- The straight segment between root radii stays inside the actual power bound. -/
def radiusSegment {n : ℕ} {r : ℝ} (a b : Radius n r) (t : unitInterval) : Radius n r :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ), by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have ha := a.property
    have hb := b.property
    have hmax : (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤
        max (a : ℝ) (b : ℝ) := by
      have h₁ := le_max_left (a : ℝ) (b : ℝ)
      have h₂ := le_max_right (a : ℝ) (b : ℝ)
      nlinarith
    have hpos : 0 < (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) := by
      by_cases ht : (t : ℝ) = 1
      · simp only [ht, sub_self, zero_mul, one_mul, zero_add]
        exact hb.1
      · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
        exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr ht') ha.1) (mul_nonneg ht0 hb.1.le)
    refine ⟨hpos, hmax.trans_lt (max_lt ha.2.1 hb.2.1), ?_⟩
    apply (pow_le_pow_left₀ hpos.le hmax n).trans_lt
    rcases le_total (a : ℝ) (b : ℝ) with hab | hba
    · rw [max_eq_right hab]
      exact hb.2.2
    · rw [max_eq_left hba]
      exact ha.2.2⟩

@[simp] theorem radiusSegment_zero {n : ℕ} {r : ℝ} (a b : Radius n r) :
    radiusSegment a b 0 = a := by
  apply Subtype.ext
  simp [radiusSegment]

@[simp] theorem radiusSegment_one {n : ℕ} {r : ℝ} (a b : Radius n r) :
    radiusSegment a b 1 = b := by
  apply Subtype.ext
  simp [radiusSegment]

@[simp] theorem radiusSegment_self {n : ℕ} {r : ℝ} (a : Radius n r) (t : unitInterval) :
    radiusSegment a a t = a := by
  apply Subtype.ext
  dsimp only [radiusSegment]
  ring

theorem radiusSegment_continuous {n : ℕ} {r : ℝ} (a : Radius n r) :
    Continuous (fun p : unitInterval × Radius n r => radiusSegment a p.2 p.1) := by
  exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    continuous_const).add ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Contracting only the radius leaves every boundary coordinate unchanged. -/
def radiusProductHomotopyEquiv {n : ℕ} {r : ℝ} (a : Radius n r)
    (X : Type*) [TopologicalSpace X] : (Radius n r × X) ≃ₕ X where
  toFun := ContinuousMap.snd
  invFun := ⟨fun x => (a, x), continuous_const.prodMk continuous_id⟩
  left_inv := ⟨{
    toFun := fun p => (radiusSegment a p.2.1 p.1, p.2.2)
    continuous_toFun := ((radiusSegment_continuous a).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd)
    map_zero_left := fun p => Prod.ext (radiusSegment_zero a p.1) rfl
    map_one_left := fun p => Prod.ext (radiusSegment_one a p.1) rfl }⟩
  right_inv := ContinuousMap.Homotopic.refl _

@[simp] theorem radiusProductHomotopyEquiv_apply {n : ℕ} {r : ℝ} (a : Radius n r)
    (X : Type*) [TopologicalSpace X] (p : Radius n r × X) :
    radiusProductHomotopyEquiv a X p = p.2 := rfl

@[simp] theorem radiusProductHomotopyEquiv_symm_apply {n : ℕ} {r : ℝ} (a : Radius n r)
    (X : Type*) [TopologicalSpace X] (x : X) :
    (radiusProductHomotopyEquiv a X).symm x = (a, x) := rfl

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
