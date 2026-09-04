import Mathlib.Analysis.LocallyConvex.Separation
import Wikipedia.SzemeredisTheorem.Finite.Mean

/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise

/-- Normalized pairing on a finite probability space. -/
noncomputable def finitePairing
    {Ω : Type*} [Fintype Ω] (f q : Ω → ℝ) : ℝ :=
  mean (fun x => f x * q x)

theorem finitePairing_add_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f + g) q =
      finitePairing f q + finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePairing_add_right
    {Ω : Type*} [Fintype Ω]
    (f q r : Ω → ℝ) :
    finitePairing f (q + r) =
      finitePairing f q + finitePairing f r := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePairing_sub_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f - g) q =
      finitePairing f q - finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_sub]
  apply congrArg mean
  funext x
  simp only [Pi.sub_apply]
  ring

theorem finitePairing_sub_right
    {Ω : Type*} [Fintype Ω]
    (f q r : Ω → ℝ) :
    finitePairing f (q - r) =
      finitePairing f q - finitePairing f r := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_sub]
  apply congrArg mean
  funext x
  simp only [Pi.sub_apply]
  ring

theorem finitePairing_smul_left
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing (c • f) q = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem finitePairing_smul_right
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing f (c • q) = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem finitePairing_comm
    {Ω : Type*} [Fintype Ω]
    (f q : Ω → ℝ) :
    finitePairing f q = finitePairing q f := by
  apply congrArg mean
  funext x
  exact mul_comm _ _

theorem finitePairing_mono_left
    {Ω : Type*} [Fintype Ω]
    {f g q : Ω → ℝ}
    (hfg : ∀ x, f x ≤ g x) (hq : ∀ x, 0 ≤ q x) :
    finitePairing f q ≤ finitePairing g q :=
  mean_mono fun x => mul_le_mul_of_nonneg_right (hfg x) (hq x)

theorem finitePairing_mono_right
    {Ω : Type*} [Fintype Ω]
    {f q r : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hqr : ∀ x, q x ≤ r x) :
    finitePairing f q ≤ finitePairing f r :=
  mean_mono fun x => mul_le_mul_of_nonneg_left (hqr x) (hf x)

/-- Pointwise membership in the dense-model cube. -/
def IsUnitBounded {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1

theorem IsUnitBounded.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, 0 ≤ g x :=
  hg.1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2

theorem isUnitBounded_zero {Ω : Type*} :
    IsUnitBounded (fun _ : Ω => (0 : ℝ)) :=
  ⟨fun _ => le_rfl, fun _ => zero_le_one⟩

theorem isUnitBounded_one {Ω : Type*} :
    IsUnitBounded (fun _ : Ω => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, fun _ => le_rfl⟩

/-- The unit cube as a subset of the finite-dimensional function space. -/
def unitCubeSet (Ω : Type*) : Set (Ω → ℝ) :=
  {g | IsUnitBounded g}

theorem unitCubeSet_eq_Icc (Ω : Type*) :
    unitCubeSet Ω =
      Set.Icc (fun _ : Ω => (0 : ℝ)) (fun _ => 1) := by
  ext g
  simp [unitCubeSet, IsUnitBounded, Set.mem_Icc, Pi.le_def]

theorem unitCubeSet_convex (Ω : Type*) :
    Convex ℝ (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact convex_Icc _ _

theorem unitCubeSet_compact (Ω : Type*) [Fintype Ω] :
    IsCompact (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact isCompact_Icc

theorem unitCubeSet_closed (Ω : Type*) :
    IsClosed (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact isClosed_Icc

theorem unitCubeSet_nonempty (Ω : Type*) :
    (unitCubeSet Ω).Nonempty :=
  ⟨fun _ => 0, isUnitBounded_zero⟩

/-- Pairing with a fixed test as a linear functional. -/
noncomputable def finitePairingLinearMap
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := finitePairing f q
  map_add' f g := finitePairing_add_left f g q
  map_smul' c f := by
    simpa [smul_eq_mul] using finitePairing_smul_left c f q

/-- Pairing is continuous because its domain is finite-dimensional. -/
noncomputable def finitePairingCLM
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] ℝ :=
  (finitePairingLinearMap q).toContinuousLinearMap

@[simp]
theorem finitePairingCLM_apply
    {Ω : Type*} [Fintype Ω] (q f : Ω → ℝ) :
    finitePairingCLM q f = finitePairing f q :=
  rfl

/-- The vector of pairings against a finite family of tests. -/
noncomputable def finiteTestProfile
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] (τ → ℝ) :=
  ContinuousLinearMap.pi (fun t => finitePairingCLM (q t))

@[simp]
theorem finiteTestProfile_apply
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (t : τ) :
    finiteTestProfile q f t = finitePairing f (q t) :=
  rfl

/-- Coordinatewise error cube in the finite profile space. -/
def profileErrorSet (τ : Type*) (ε : ℝ) : Set (τ → ℝ) :=
  Set.Icc (fun _ : τ => -ε) (fun _ => ε)

theorem mem_profileErrorSet_iff
    {τ : Type*} {ε : ℝ} {e : τ → ℝ} :
    e ∈ profileErrorSet τ ε ↔ ∀ t, |e t| ≤ ε := by
  constructor
  · rintro ⟨hlower, hupper⟩ t
    exact abs_le.mpr ⟨hlower t, hupper t⟩
  · intro h
    exact
      ⟨fun t => (abs_le.mp (h t)).1,
        fun t => (abs_le.mp (h t)).2⟩

theorem profileErrorSet_convex (τ : Type*) (ε : ℝ) :
    Convex ℝ (profileErrorSet τ ε) :=
  convex_Icc _ _

theorem profileErrorSet_compact
    (τ : Type*) [Fintype τ] (ε : ℝ) :
    IsCompact (profileErrorSet τ ε) :=
  isCompact_Icc

theorem profileErrorSet_closed (τ : Type*) (ε : ℝ) :
    IsClosed (profileErrorSet τ ε) :=
  isClosed_Icc

theorem profileErrorSet_nonempty
    (τ : Type*) {ε : ℝ} (hε : 0 ≤ ε) :
    (profileErrorSet τ ε).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [mem_profileErrorSet_iff]
  intro t
  simpa using hε

/-- Profiles attainable by a dense model, enlarged by the permitted
coordinatewise error. -/
noncomputable def denseModelProfileSet
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) : Set (τ → ℝ) :=
  finiteTestProfile q '' unitCubeSet Ω + profileErrorSet τ ε

theorem denseModelProfileSet_convex
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    Convex ℝ (denseModelProfileSet Ω τ q ε) := by
  change Convex ℝ
    (finiteTestProfile q '' unitCubeSet Ω +
      profileErrorSet τ ε)
  exact
    (unitCubeSet_convex Ω).linear_image
      (finiteTestProfile q).toLinearMap |>.add
        (profileErrorSet_convex τ ε)

theorem denseModelProfileSet_compact
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    IsCompact (denseModelProfileSet Ω τ q ε) := by
  change IsCompact
    (finiteTestProfile q '' unitCubeSet Ω +
      profileErrorSet τ ε)
  exact
    ((unitCubeSet_compact Ω).image
      (finiteTestProfile q).continuous).add
        (profileErrorSet_compact τ ε)

theorem denseModelProfileSet_closed
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    IsClosed (denseModelProfileSet Ω τ q ε) :=
  (denseModelProfileSet_compact Ω τ q ε).isClosed

theorem denseModelProfileSet_nonempty
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (denseModelProfileSet Ω τ q ε).Nonempty :=
  by
    change
      (finiteTestProfile q '' unitCubeSet Ω +
        profileErrorSet τ ε).Nonempty
    exact
      ((unitCubeSet_nonempty Ω).image
        (finiteTestProfile q)).add
          (profileErrorSet_nonempty τ hε)

/-- A bounded model matching `f` against every member of a finite test
family to accuracy `ε`. -/
def HasFiniteDenseModel
    {Ω τ : Type*} [Fintype Ω]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) : Prop :=
  ∃ g : Ω → ℝ, IsUnitBounded g ∧
    ∀ t, |finitePairing (f - g) (q t)| ≤ ε

/-- Feasibility of the finite dense-model problem is exactly membership of
the target profile in the enlarged profile set. -/
theorem hasFiniteDenseModel_iff_profile_mem
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) :
    HasFiniteDenseModel q f ε ↔
      finiteTestProfile q f ∈
        denseModelProfileSet Ω τ q ε := by
  constructor
  · rintro ⟨g, hg, hmatch⟩
    change
      finiteTestProfile q f ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε
    refine ⟨finiteTestProfile q g, ⟨g, hg, rfl⟩,
      finiteTestProfile q (f - g), ?_, ?_⟩
    · rw [mem_profileErrorSet_iff]
      intro t
      exact hmatch t
    · ext t
      simp only [Pi.add_apply, finiteTestProfile_apply]
      rw [finitePairing_sub_left]
      ring
  · intro hmem
    change
      finiteTestProfile q f ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε at hmem
    rcases hmem with ⟨p, ⟨g, hg, rfl⟩, e, he, hsum⟩
    refine ⟨g, hg, ?_⟩
    rw [mem_profileErrorSet_iff] at he
    intro t
    have ht := congrFun hsum t
    simp only [Pi.add_apply, finiteTestProfile_apply] at ht
    rw [finitePairing_sub_left]
    rw [← ht]
    simpa using he t

/-- Failure of the finite dense-model problem produces a nonzero continuous
linear functional which strictly separates the target profile from every
model profile plus every admissible error vector. -/
theorem exists_finiteDenseModel_separator
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : ¬HasFiniteDenseModel q f ε) :
    ∃ L : StrongDual ℝ (τ → ℝ), L ≠ 0 ∧
      ∀ (g : Ω → ℝ), IsUnitBounded g →
        ∀ e ∈ profileErrorSet τ ε,
          L (finiteTestProfile q g + e) <
            L (finiteTestProfile q f) := by
  have hnotmem :
      finiteTestProfile q f ∉
        denseModelProfileSet Ω τ q ε := by
    simpa [hasFiniteDenseModel_iff_profile_mem] using hfail
  obtain ⟨L, u, hleft, hright⟩ :=
    geometric_hahn_banach_closed_point
      (denseModelProfileSet_convex Ω τ q ε)
      (denseModelProfileSet_closed Ω τ q ε)
      hnotmem
  have hLne : L ≠ 0 := by
    obtain ⟨s, hs⟩ :=
      denseModelProfileSet_nonempty Ω τ q hε
    intro hzero
    have hslt := hleft s hs
    rw [hzero] at hslt hright
    simp only [zero_apply] at hslt hright
    linarith
  refine ⟨L, hLne, ?_⟩
  intro g hg e he
  have hmem :
      finiteTestProfile q g + e ∈
        denseModelProfileSet Ω τ q ε := by
    change
      finiteTestProfile q g + e ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε
    exact ⟨finiteTestProfile q g, ⟨g, hg, rfl⟩,
      e, he, rfl⟩
  exact (hleft _ hmem).trans hright

/-- Coordinates of a continuous linear functional on a finite function
space, relative to the standard single-coordinate basis. -/
noncomputable def dualCoefficient
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (t : τ) : ℝ := by
  classical
  exact L (Pi.single t 1)

/-- Every continuous linear functional on a finite function space is the
dot product with its coordinate vector. -/
theorem dual_apply_eq_sum_coefficient
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (v : τ → ℝ) :
    L v = ∑ t, dualCoefficient L t * v t := by
  classical
  calc
    L v =
        L (∑ t, (v t) •
          Pi.single (M := fun _ : τ => ℝ) t 1) := by
      rw [← pi_eq_sum_univ' v]
    _ = ∑ t,
        L ((v t) •
          Pi.single (M := fun _ : τ => ℝ) t 1) := by
      exact map_sum L _ _
    _ = ∑ t, dualCoefficient L t * v t := by
      apply Fintype.sum_congr
      intro t
      rw [map_smul]
      simp [dualCoefficient, mul_comm]

/-- The `ℓ¹` size of a coefficient vector. -/
noncomputable def coefficientL1
    {τ : Type*} [Fintype τ] (c : τ → ℝ) : ℝ :=
  ∑ t, |c t|

theorem coefficientL1_nonneg
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    0 ≤ coefficientL1 c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The coefficient `ℓ¹`-norm vanishes exactly on the zero vector. -/
theorem coefficientL1_eq_zero_iff
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    coefficientL1 c = 0 ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext t
    have ht : |c t| = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => abs_nonneg (c i))).mp h t
            (Finset.mem_univ t)
    exact abs_eq_zero.mp ht
  · rintro rfl
    simp [coefficientL1]

/-- Scaling law for the coefficient `ℓ¹`-norm. -/
theorem coefficientL1_smul
    {τ : Type*} [Fintype τ] (a : ℝ) (c : τ → ℝ) :
    coefficientL1 (a • c) = |a| * coefficientL1 c := by
  classical
  simp [coefficientL1, abs_mul, Finset.mul_sum]

/-- A nonzero dual functional has a strictly positive coordinate
`ℓ¹`-norm. -/
theorem coefficientL1_dualCoefficient_pos
    {τ : Type*} [Fintype τ]
    {L : StrongDual ℝ (τ → ℝ)} (hL : L ≠ 0) :
    0 < coefficientL1 (dualCoefficient L) := by
  classical
  have hexists : ∃ t, dualCoefficient L t ≠ 0 := by
    by_contra h
    push Not at h
    apply hL
    ext v
    rw [dual_apply_eq_sum_coefficient]
    simp [h]
  obtain ⟨t, ht⟩ := hexists
  unfold coefficientL1
  exact Finset.sum_pos'
    (fun i _ => abs_nonneg (dualCoefficient L i))
    ⟨t, Finset.mem_univ t, abs_pos.mpr ht⟩

/-- Linear combination of a finite test family. -/
noncomputable def finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) : Ω → ℝ :=
  ∑ t, c t • q t

@[simp]
theorem finiteTestCombination_zero
    {Ω τ : Type*} [Fintype τ] (q : τ → Ω → ℝ) :
    finiteTestCombination q 0 = 0 := by
  classical
  ext x
  simp [finiteTestCombination]

/-- Scaling coefficients scales the corresponding test combination. -/
theorem finiteTestCombination_smul_coeff
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (a : ℝ) (c : τ → ℝ) :
    finiteTestCombination q (a • c) =
      a • finiteTestCombination q c := by
  classical
  ext x
  simp [finiteTestCombination, Finset.mul_sum, mul_assoc]

/-- Pairing distributes across a finite linear combination of tests. -/
theorem finitePairing_finiteTestCombination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f (finiteTestCombination q c) =
      ∑ t, c t * finitePairing f (q t) := by
  rw [finiteTestCombination]
  unfold finitePairing mean
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Fintype.sum_congr
  intro t
  calc
    (Finset.univ.expect fun x => f x * (c t * q t x)) =
        Finset.univ.expect (fun x => c t * (f x * q t x)) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = c t *
        Finset.univ.expect (fun x => f x * q t x) := by
      exact (Finset.mul_expect Finset.univ
        (fun x => f x * q t x) (c t)).symm

/-- Applying a dual separator to a profile is the normalized pairing with
the corresponding linear combination of the original tests. -/
theorem dual_profile_eq_pairing_combination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ))
    (q : τ → Ω → ℝ) (f : Ω → ℝ) :
    L (finiteTestProfile q f) =
      finitePairing f
        (finiteTestCombination q (dualCoefficient L)) := by
  rw [dual_apply_eq_sum_coefficient,
    finitePairing_finiteTestCombination]
  apply Fintype.sum_congr
  intro t
  rw [finiteTestProfile_apply]

/-- The error vector which maximizes a dual functional on the
coordinatewise error cube. -/
noncomputable def dualErrorVector
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) : τ → ℝ :=
  fun t => ε *
    ((SignType.sign (dualCoefficient L t) : SignType) : ℝ)

theorem dualErrorVector_mem
    {τ : Type*} [Fintype τ]
    {ε : ℝ} (hε : 0 ≤ ε)
    (L : StrongDual ℝ (τ → ℝ)) :
    dualErrorVector ε L ∈ profileErrorSet τ ε := by
  rw [mem_profileErrorSet_iff]
  intro t
  rw [dualErrorVector, abs_mul, abs_of_nonneg hε]
  have hsign :
      |((SignType.sign (dualCoefficient L t) : SignType) : ℝ)| ≤ 1 := by
    rw [sign_apply]
    split_ifs <;> norm_num
  simpa using mul_le_mul_of_nonneg_left hsign hε

/-- Exact support value of the error cube under a dual functional. -/
theorem dual_apply_dualErrorVector
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) :
    L (dualErrorVector ε L) =
      ε * coefficientL1 (dualCoefficient L) := by
  rw [dual_apply_eq_sum_coefficient]
  calc
    (∑ t, dualCoefficient L t * dualErrorVector ε L t) =
        ∑ t, ε * |dualCoefficient L t| := by
      apply Fintype.sum_congr
      intro t
      rw [dualErrorVector]
      rw [← self_mul_sign (dualCoefficient L t)]
      ring
    _ = ε * coefficientL1 (dualCoefficient L) := by
      rw [coefficientL1, Finset.mul_sum]

/-- Pointwise positive part. -/
def positivePart {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => max (q x) 0

@[simp]
theorem positivePart_apply
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positivePart q x = max (q x) 0 :=
  rfl

theorem positivePart_nonneg
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    0 ≤ positivePart q x :=
  le_max_right _ _

theorem le_positivePart
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    q x ≤ positivePart q x :=
  le_max_left _ _

@[simp]
theorem positivePart_of_nonneg
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : 0 ≤ q x) :
    positivePart q x = q x :=
  max_eq_left hx

@[simp]
theorem positivePart_of_nonpos
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : q x ≤ 0) :
    positivePart q x = 0 :=
  max_eq_right hx

@[simp]
theorem positivePart_zero {Ω : Type*} :
    positivePart (0 : Ω → ℝ) = 0 := by
  ext x
  simp [positivePart]

/-- Positive part commutes with multiplication by a nonnegative scalar. -/
theorem positivePart_smul_of_nonneg
    {Ω : Type*} {a : ℝ} (ha : 0 ≤ a) (q : Ω → ℝ) :
    positivePart (a • q) = a • positivePart q := by
  ext x
  simp only [positivePart, Pi.smul_apply, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ ha, mul_zero]

/-- The Boolean vertex of the unit cube which maximizes pairing with `q`. -/
noncomputable def positiveSupportIndicator
    {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => if 0 ≤ q x then 1 else 0

theorem positiveSupportIndicator_unitBounded
    {Ω : Type*} (q : Ω → ℝ) :
    IsUnitBounded (positiveSupportIndicator q) := by
  constructor <;> intro x <;>
    simp only [positiveSupportIndicator] <;>
    split <;> norm_num

@[simp]
theorem positiveSupportIndicator_mul
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positiveSupportIndicator q x * q x =
      positivePart q x := by
  by_cases hx : 0 ≤ q x
  · simp [positiveSupportIndicator, positivePart, hx]
  · have hx' : q x ≤ 0 := le_of_not_ge hx
    simp [positiveSupportIndicator, positivePart, hx, hx']

/-- Exact support function of the pointwise unit cube. -/
theorem finitePairing_positiveSupportIndicator
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (positiveSupportIndicator q) q =
      mean (positivePart q) := by
  apply congrArg mean
  funext x
  exact positiveSupportIndicator_mul q x

/-- Every `[0,1]`-valued function pairs with `q` below the positive-part
support function. -/
theorem finitePairing_le_mean_positivePart
    {Ω : Type*} [Fintype Ω]
    {g q : Ω → ℝ} (hg : IsUnitBounded g) :
    finitePairing g q ≤ mean (positivePart q) := by
  apply mean_mono
  intro x
  by_cases hx : 0 ≤ q x
  · rw [positivePart_of_nonneg hx]
    exact mul_le_of_le_one_left hx (hg.le_one x)
  · rw [positivePart_of_nonpos (le_of_not_ge hx)]
    exact mul_nonpos_of_nonneg_of_nonpos
      (hg.nonneg x) (le_of_not_ge hx)

/-- Domination by a majorant turns an arbitrary separator into a
positive-part test of the majorant. -/
theorem finitePairing_le_majorant_positivePart
    {Ω : Type*} [Fintype Ω]
    {f ν q : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x) :
    finitePairing f q ≤ finitePairing ν (positivePart q) := by
  apply mean_mono
  intro x
  by_cases hx : 0 ≤ q x
  · rw [positivePart_of_nonneg hx]
    exact mul_le_mul_of_nonneg_right (hfν x) hx
  · rw [positivePart_of_nonpos (le_of_not_ge hx), mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos
      (hf0 x) (le_of_not_ge hx)

/-- The pairing of the constant-one function is the mean. -/
@[simp]
theorem finitePairing_one_left
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (fun _ : Ω => (1 : ℝ)) q = mean q := by
  simp [finitePairing]

/-- Core dual contradiction in the dense-model theorem.  If one separator
beats every function in the unit cube by a strict gap `δ`, then `ν - 1`
correlates with its positive part by more than `δ`. -/
theorem majorant_positivePart_correlation_of_separates_unitCube
    {Ω : Type*} [Fintype Ω]
    {f ν q : Ω → ℝ} {δ : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hsep :
      ∀ g : Ω → ℝ, IsUnitBounded g →
        finitePairing g q + δ < finitePairing f q) :
    δ < finitePairing (ν - fun _ => 1) (positivePart q) := by
  have hsupport := hsep (positiveSupportIndicator q)
    (positiveSupportIndicator_unitBounded q)
  rw [finitePairing_positiveSupportIndicator] at hsupport
  have hmajorant :
      finitePairing f q ≤ finitePairing ν (positivePart q) :=
    finitePairing_le_majorant_positivePart
      (q := q) hf0 hfν
  rw [finitePairing_sub_left, finitePairing_one_left]
  linarith

/-- The exact dual pseudorandomness hypothesis needed for a finite family
of tests.  It is homogeneous in the coefficients, so no separate
normalization convention is required. -/
def HasPositivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ) : Prop :=
  ∀ c : τ → ℝ,
    finitePairing (ν - fun _ => 1)
        (positivePart (finiteTestCombination q c)) ≤
      ε * coefficientL1 c

/-- Unit-`ℓ¹` form of the positive-part pseudorandomness hypothesis. -/
def HasNormalizedPositivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ) : Prop :=
  ∀ c : τ → ℝ, coefficientL1 c = 1 →
    finitePairing (ν - fun _ => 1)
        (positivePart (finiteTestCombination q c)) ≤ ε

/-- It suffices to verify the positive-part correlation estimate for
coefficient vectors of `ℓ¹`-norm one. -/
theorem hasPositivePartCorrelationBound_of_normalized
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ)
    (h :
      HasNormalizedPositivePartCorrelationBound q ν ε) :
    HasPositivePartCorrelationBound q ν ε := by
  intro c
  by_cases hc : coefficientL1 c = 0
  · have hc0 : c = 0 :=
      (coefficientL1_eq_zero_iff c).mp hc
    subst c
    rw [hc]
    simp [finitePairing, positivePart]
  · have hcpos : 0 < coefficientL1 c :=
      lt_of_le_of_ne (coefficientL1_nonneg c) (Ne.symm hc)
    let A := coefficientL1 c
    let c' : τ → ℝ := A⁻¹ • c
    have hApos : 0 < A := hcpos
    have hc'L1 : coefficientL1 c' = 1 := by
      change coefficientL1 (A⁻¹ • c) = 1
      rw [coefficientL1_smul, abs_of_pos (inv_pos.mpr hApos)]
      exact inv_mul_cancel₀ hApos.ne'
    have hnormalized := h c' hc'L1
    have hcombination :
        finiteTestCombination q c' =
          A⁻¹ • finiteTestCombination q c := by
      exact finiteTestCombination_smul_coeff q A⁻¹ c
    rw [hcombination,
      positivePart_smul_of_nonneg (inv_nonneg.mpr hApos.le),
      finitePairing_smul_right] at hnormalized
    have hmul :=
      mul_le_mul_of_nonneg_left hnormalized hApos.le
    rw [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul] at hmul
    simpa [A, mul_comm] using hmul

/-- Finite dense-model theorem.  A majorized nonnegative function admits a
`[0,1]`-valued model against every test in a finite family whenever the
majorant obeys the homogeneous positive-part correlation bound. -/
theorem hasFiniteDenseModel_of_positivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {f ν : Ω → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo : HasPositivePartCorrelationBound q ν ε) :
    HasFiniteDenseModel q f ε := by
  by_contra hfail
  obtain ⟨L, _hL, hsep⟩ :=
    exists_finiteDenseModel_separator q f hε hfail
  have hsepPair :
      ∀ g : Ω → ℝ, IsUnitBounded g →
        finitePairing g
            (finiteTestCombination q (dualCoefficient L)) +
              ε * coefficientL1 (dualCoefficient L) <
          finitePairing f
            (finiteTestCombination q (dualCoefficient L)) := by
    intro g hg
    have h := hsep g hg (dualErrorVector ε L)
      (dualErrorVector_mem hε L)
    rw [map_add, dual_profile_eq_pairing_combination,
      dual_apply_dualErrorVector,
      dual_profile_eq_pairing_combination] at h
    exact h
  have hpositive :=
    majorant_positivePart_correlation_of_separates_unitCube
      hf0 hfν hsepPair
  exact (not_lt_of_ge (hpseudo (dualCoefficient L))) hpositive

end Wikipedia.SzemeredisTheorem
