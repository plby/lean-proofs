import Mathlib

/-!
# Erdős Problem 526 (Dvoretzky--Shepp random covering)

This file formalizes random arcs on the unit circle and Shepp's necessary and
sufficient condition.  The mathematical source states the series criterion for
the nonincreasing rearrangement of the positive lengths; the rearrangement is
part of the formal statement below, since coverage is permutation invariant
but the displayed prefix-sum series is not.
-/

namespace Erdos526

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- The unit circle, represented as the additive quotient `ℝ ⧸ ℤ`. -/
abbrev Circle := UnitAddCircle

/-- Normalized Haar probability measure on the unit circle. -/
def uniformCircle : Measure Circle := AddCircle.haarAddCircle

/-- A sample is a sequence of arc centers. -/
abbrev Sample := ℕ → Circle

/-- The canonical law of independently and uniformly chosen centers. -/
def sampleMeasure : Measure Sample :=
  Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)

instance uniformCircle_isProbabilityMeasure :
    IsProbabilityMeasure uniformCircle := by
  unfold uniformCircle
  infer_instance

instance sampleMeasure_isProbabilityMeasure :
    IsProbabilityMeasure sampleMeasure := by
  unfold sampleMeasure
  infer_instance

/-- The open arc centered at `z` and having prescribed length `length`.

For the part of the sequence used in the proof, `0 ≤ length < 1`; on the unit
circle this ball then has Haar measure exactly `length`. -/
def arc (z : Circle) (length : ℝ) : Set Circle :=
  Metric.ball z (length / 2)

/-- A short circle arc is convex in any real coordinate interval of length at
most one half.  This oriented form is the geometric input in Shepp's
leftmost-gap argument. -/
lemma arc_interval_convex {z : Circle} {length y q x : ℝ}
    (hlength₀ : 0 ≤ length) (hlength : length ≤ 1 / 4)
    (hyq : y ≤ q) (hqx : q ≤ x) (hxy : x - y ≤ 1 / 2)
    (hy : (y : Circle) ∈ arc z length) (hx : (x : Circle) ∈ arc z length) :
    (q : Circle) ∈ arc z length := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective z
  simp only [arc, Metric.mem_ball, dist_eq_norm, ← QuotientAddGroup.mk_sub,
    UnitAddCircle.norm_eq] at hy hx ⊢
  let ky : ℤ := round (y - c)
  let kx : ℤ := round (x - c)
  let kq : ℤ := round (q - c)
  change |y - c - (ky : ℝ)| < length / 2 at hy
  change |x - c - (kx : ℝ)| < length / 2 at hx
  have hkdist : |(kx : ℝ) - (ky : ℝ)| < 1 := by
    calc
      |(kx : ℝ) - (ky : ℝ)| =
          |(x - y) - (x - c - (kx : ℝ)) + (y - c - (ky : ℝ))| := by ring_nf
      _ ≤ |x - y| + |x - c - (kx : ℝ)| + |y - c - (ky : ℝ)| := by
        calc
          _ ≤ |x - y| + |-(x - c - (kx : ℝ)) +
              (y - c - (ky : ℝ))| := by
            simpa only [sub_eq_add_neg, add_assoc] using
              abs_add_le (x - y)
                (-(x - c - (kx : ℝ)) + (y - c - (ky : ℝ)))
          _ ≤ |x - y| + (|-(x - c - (kx : ℝ))| +
              |y - c - (ky : ℝ)|) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right
                (abs_add_le (-(x - c - (kx : ℝ)))
                  (y - c - (ky : ℝ))) |x - y|
          _ = _ := by rw [abs_neg, add_assoc]
      _ < 1 := by
        have hxy₀ : 0 ≤ x - y := sub_nonneg.mpr (hyq.trans hqx)
        rw [abs_of_nonneg hxy₀]
        linarith
  have hk : kx = ky := by
    rw [abs_lt] at hkdist
    have hklo : (-1 : ℤ) < kx - ky := by exact_mod_cast hkdist.1
    have hkhi : kx - ky < (1 : ℤ) := by exact_mod_cast hkdist.2
    omega
  rw [hk] at hx
  have hq' : |q - c - (ky : ℝ)| < length / 2 := by
    rw [abs_lt] at hy hx ⊢
    constructor <;> linarith
  have hround : kq = ky := by
    have hqhalf : |q - c - (ky : ℝ)| < 1 / 2 := by linarith
    change round (q - c) = ky
    rw [round_eq_iff]
    rw [abs_lt] at hqhalf
    exact ⟨by linarith, by linarith⟩
  change |q - c - (kq : ℝ)| < length / 2
  rw [hround]
  exact hq'

/-- The standard `m`-point grid on the unit circle. -/
def gridPoint (m j : ℕ) : Circle := ((j : ℝ) / (m : ℝ) : Circle)

/-- The standard grid is a strict `1/m`-net.  The non-optimal constant makes
the quotient-coordinate proof particularly robust and is sufficient for the
nonsquare-summable branch of Shepp's theorem. -/
lemma exists_gridPoint_dist_lt (m : ℕ) (hm : 0 < m) (x : Circle) :
    ∃ j < m, dist x (gridPoint m j) < 1 / (m : ℝ) := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  let r : ℝ := Int.fract c
  let z : ℤ := ⌊(m : ℝ) * r⌋
  let j : ℕ := z.toNat
  have hr₀ : 0 ≤ r := Int.fract_nonneg c
  have hr₁ : r < 1 := Int.fract_lt_one c
  have hz₀ : 0 ≤ z := by
    rw [Int.floor_nonneg]
    positivity
  have hzle : (z : ℝ) ≤ (m : ℝ) * r := Int.floor_le _
  have hzgt : (m : ℝ) * r < (z : ℝ) + 1 := Int.lt_floor_add_one _
  have hjcast : (j : ℝ) = (z : ℝ) := by
    norm_cast
    exact Int.toNat_of_nonneg hz₀
  have hjm : j < m := by
    have hmℝ : (0 : ℝ) < m := by exact_mod_cast hm
    have hzlt : (z : ℝ) < (m : ℝ) :=
      hzle.trans_lt (by simpa using mul_lt_mul_of_pos_left hr₁ hmℝ)
    have hzlt' : z < (m : ℤ) := by exact_mod_cast hzlt
    exact (Int.toNat_lt hz₀).2 hzlt'
  refine ⟨j, hjm, ?_⟩
  have hcoe : (c : Circle) = (r : Circle) := by
    rw [QuotientAddGroup.eq]
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨-⌊c⌋, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    change ((-⌊c⌋ : ℤ) : ℝ) = -c + r
    simp only [Int.cast_neg, r, Int.fract]
    ring
  rw [hcoe]
  change dist (r : Circle) (((j : ℝ) / (m : ℝ) : ℝ) : Circle) < _
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  apply lt_of_le_of_lt QuotientAddGroup.norm_mk_le_norm
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · apply sub_lt_iff_lt_add.2
    rw [← add_div, hjcast]
    exact (lt_div_iff₀ (by exact_mod_cast hm)).2
      (by simpa [mul_comm, add_comm] using hzgt)
  · rw [sub_nonneg, div_le_iff₀ (by exact_mod_cast hm), hjcast]
    simpa [mul_comm] using hzle

lemma uniformCircle_eq_volume :
    (uniformCircle : Measure Circle) = volume := by
  symm
  simpa [uniformCircle] using
    (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

/-- A short arc has the prescribed Haar measure. -/
lemma measure_arc {z : Circle} {length : ℝ} (hlength₀ : 0 ≤ length)
    (hlength₁ : length ≤ 1) :
    uniformCircle (arc z length) = ENNReal.ofReal length := by
  rw [uniformCircle_eq_volume, arc,
    ← measure_congr (AddCircle.closedBall_ae_eq_ball
      (x := z) (ε := length / 2)), AddCircle.volume_closedBall]
  congr 1
  rw [min_eq_right]
  · ring
  · linarith

/-- Length of the overlap of two equal real intervals. -/
lemma real_volume_closedBall_inter (r t : ℝ) :
    volume (Metric.closedBall (0 : ℝ) r ∩ Metric.closedBall t r) =
      ENNReal.ofReal (max (2 * r - |t|) 0) := by
  rcases le_total 0 t with ht | ht
  · have hset : Metric.closedBall (0 : ℝ) r ∩ Metric.closedBall t r =
        Icc (t - r) r := by
      ext u
      simp only [Real.closedBall_eq_Icc, zero_sub, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨⟨hu₁, hu₂⟩, hu₃, hu₄⟩
        exact ⟨hu₃, by linarith⟩
      · rintro ⟨hu₁, hu₂⟩
        exact ⟨⟨by linarith, by linarith⟩, hu₁, by linarith⟩
    rw [hset, Real.volume_Icc]
    rw [abs_of_nonneg ht]
    by_cases h : 0 ≤ 2 * r - t
    · rw [max_eq_left h]
      congr 1
      ring
    · rw [max_eq_right (le_of_not_ge h)]
      have : r - (t - r) ≤ 0 := by linarith
      rw [ENNReal.ofReal_eq_zero.mpr this, ENNReal.ofReal_zero]
  · have hset : Metric.closedBall (0 : ℝ) r ∩ Metric.closedBall t r =
        Icc (-r) (t + r) := by
      ext u
      simp only [Real.closedBall_eq_Icc, zero_sub, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨⟨hu₁, hu₂⟩, hu₃, hu₄⟩
        exact ⟨hu₁, hu₄⟩
      · rintro ⟨hu₁, hu₂⟩
        exact ⟨⟨hu₁, by linarith⟩, by linarith, hu₂⟩
    rw [hset, Real.volume_Icc]
    rw [abs_of_nonpos ht]
    by_cases h : 0 ≤ 2 * r - -t
    · rw [max_eq_left h]
      congr 1
      ring
    · rw [max_eq_right (le_of_not_ge h)]
      have : t + r - -r ≤ 0 := by linarith
      rw [ENNReal.ofReal_eq_zero.mpr this, ENNReal.ofReal_zero]

lemma real_volume_closedBall_inter_two (r x y : ℝ) :
    volume (Metric.closedBall x r ∩ Metric.closedBall y r) =
      ENNReal.ofReal (max (2 * r - |x - y|) 0) := by
  calc
    volume (Metric.closedBall x r ∩ Metric.closedBall y r) =
        volume ((fun z : ℝ ↦ x + z) ⁻¹'
          (Metric.closedBall x r ∩ Metric.closedBall y r)) := by
            rw [measure_preimage_add]
    _ = volume (Metric.closedBall (0 : ℝ) r ∩ Metric.closedBall (-x + y) r) := by
      rw [preimage_inter, Metric.preimage_add_left_closedBall,
        Metric.preimage_add_left_closedBall]
      simp only [neg_add_cancel]
    _ = ENNReal.ofReal (max (2 * r - |-x + y|) 0) :=
      real_volume_closedBall_inter r (-x + y)
    _ = ENNReal.ofReal (max (2 * r - |x - y|) 0) := by
      rw [show -x + y = -(x - y) by ring, abs_neg]

/-- Local two-ball overlap formula on the unit circle.  The hypotheses keep
both centers and both short balls inside one fundamental interval. -/
lemma measure_closedBall_inter_coe (r x y : ℝ) (hr₀ : 0 ≤ r)
    (hr : r ≤ 1 / 8) (hxy : |x - y| ≤ 1 / 4) :
    uniformCircle
        (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r) =
      ENNReal.ofReal (max (2 * r - |x - y|) 0) := by
  let I : Set ℝ := Ioc (x - 1 / 2) ((x - 1 / 2) + 1)
  have hrhalf : r < |(1 : ℝ)| / 2 := by
    norm_num at hr ⊢
    linarith
  have hI : I ⊆ Metric.closedBall x (|(1 : ℝ)| / 2) := by
    intro z hz
    change |z - x| ≤ |(1 : ℝ)| / 2
    dsimp [I] at hz
    rw [abs_le]
    norm_num at hz ⊢
    constructor <;> linarith
  have hballI : Metric.closedBall x r ∩ I = Metric.closedBall x r := by
    apply inter_eq_left.2
    intro z hz
    have hz' : |z - x| ≤ r := by
      change dist z x ≤ r at hz
      simpa only [Real.dist_eq] using hz
    dsimp [I]
    norm_num
    constructor
    · have : -r ≤ z - x := (abs_le.1 hz').1
      linarith
    · have : z - x ≤ r := (abs_le.1 hz').2
      linarith
  have hxy' : Metric.closedBall x r ⊆
      Metric.closedBall y (|(1 : ℝ)| / 2) := by
    intro z hz
    have hzx : |z - x| ≤ r := by
      change dist z x ≤ r at hz
      simpa only [Real.dist_eq] using hz
    change |z - y| ≤ |(1 : ℝ)| / 2
    norm_num at hxy ⊢
    calc
      |z - y| = |(z - x) + (x - y)| := by ring_nf
      _ ≤ |z - x| + |x - y| := abs_add_le _ _
      _ ≤ r + 1 / 4 := add_le_add hzx hxy
      _ ≤ 1 / 2 := by linarith
  have hpre₁ :
      ((fun z : ℝ ↦ (z : Circle)) ⁻¹' Metric.closedBall (x : Circle) r) ∩ I =
        Metric.closedBall x r := by
    have h := AddCircle.coe_real_preimage_closedBall_inter_eq
      (1 : ℝ) (x := x) (ε := r) I hI
    rw [if_pos hrhalf, hballI] at h
    exact h
  have hpre₂ :
      ((fun z : ℝ ↦ (z : Circle)) ⁻¹' Metric.closedBall (y : Circle) r) ∩
          Metric.closedBall x r =
        Metric.closedBall y r ∩ Metric.closedBall x r := by
    have h := AddCircle.coe_real_preimage_closedBall_inter_eq
      (1 : ℝ) (x := y) (ε := r) (Metric.closedBall x r) hxy'
    rw [if_pos hrhalf] at h
    exact h
  have hpre :
      (fun z : ℝ ↦ (z : Circle)) ⁻¹'
          (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r) ∩ I =
        Metric.closedBall x r ∩ Metric.closedBall y r := by
    rw [preimage_inter]
    calc
      (_ ∩ _) ∩ I =
          ((fun z : ℝ ↦ (z : Circle)) ⁻¹' Metric.closedBall (y : Circle) r) ∩
            (((fun z : ℝ ↦ (z : Circle)) ⁻¹' Metric.closedBall (x : Circle) r) ∩ I) := by
              ext z
              simp only [mem_inter_iff, mem_preimage]
              tauto
      _ = ((fun z : ℝ ↦ (z : Circle)) ⁻¹' Metric.closedBall (y : Circle) r) ∩
            Metric.closedBall x r := by rw [hpre₁]
      _ = Metric.closedBall y r ∩ Metric.closedBall x r := hpre₂
      _ = Metric.closedBall x r ∩ Metric.closedBall y r := inter_comm _ _
  have hmp := UnitAddCircle.measurePreserving_mk (x - 1 / 2)
  have hmeas : MeasurableSet
      (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r) :=
    measurableSet_closedBall.inter measurableSet_closedBall
  have hmeasure :
      (volume.restrict I)
          ((fun z : ℝ ↦ (z : Circle)) ⁻¹'
            (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r)) =
        volume (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r) := by
    change (volume.restrict (Ioc (x - 1 / 2) ((x - 1 / 2) + 1)))
        (QuotientAddGroup.mk ⁻¹'
          (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r)) = _
    exact hmp.measure_preimage hmeas.nullMeasurableSet
  rw [Measure.restrict_apply
    (hmeas.preimage AddCircle.measurable_mk')] at hmeasure
  change volume
      ((fun z : ℝ ↦ (z : Circle)) ⁻¹'
          (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r) ∩ I) =
        volume (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r)
    at hmeasure
  rw [hpre, real_volume_closedBall_inter_two] at hmeasure
  rw [uniformCircle_eq_volume, ← hmeasure]

/-- Two short arcs whose centers are represented in one local coordinate
chart overlap in length `(length - distance)₊`. -/
lemma measure_arc_inter_coe (length x y : ℝ) (hlength₀ : 0 ≤ length)
    (hlength : length ≤ 1 / 4) (hxy : |x - y| ≤ 1 / 4) :
    uniformCircle (arc (x : Circle) length ∩ arc (y : Circle) length) =
      ENNReal.ofReal (max (length - |x - y|) 0) := by
  let r := length / 2
  have hr₀ : 0 ≤ r := by dsimp [r]; linarith
  have hr : r ≤ 1 / 8 := by dsimp [r]; linarith
  have hae :
      (Metric.closedBall (x : Circle) r ∩ Metric.closedBall (y : Circle) r : Set Circle)
        =ᵐ[volume]
      (Metric.ball (x : Circle) r ∩ Metric.ball (y : Circle) r : Set Circle) :=
    ae_eq_set_inter
      (AddCircle.closedBall_ae_eq_ball (x := (x : Circle)) (ε := r))
      (AddCircle.closedBall_ae_eq_ball (x := (y : Circle)) (ε := r))
  calc
    uniformCircle (arc (x : Circle) length ∩ arc (y : Circle) length) =
        volume (Metric.ball (x : Circle) r ∩ Metric.ball (y : Circle) r) := by
      rw [uniformCircle_eq_volume]
      rfl
    _ = volume (Metric.closedBall (x : Circle) r ∩
          Metric.closedBall (y : Circle) r) := (measure_congr hae).symm
    _ = uniformCircle (Metric.closedBall (x : Circle) r ∩
          Metric.closedBall (y : Circle) r) := by rw [uniformCircle_eq_volume]
    _ = ENNReal.ofReal (max (2 * r - |x - y|) 0) :=
      measure_closedBall_inter_coe r x y hr₀ hr hxy
    _ = ENNReal.ofReal (max (length - |x - y|) 0) := by
      congr 2
      dsimp [r]
      ring_nf

lemma measureReal_arc {z : Circle} {length : ℝ} (hlength₀ : 0 ≤ length)
    (hlength₁ : length ≤ 1) :
    uniformCircle.real (arc z length) = length := by
  rw [measureReal_def, measure_arc hlength₀ hlength₁,
    ENNReal.toReal_ofReal hlength₀]

lemma measureReal_arc_inter_coe (length x y : ℝ) (hlength₀ : 0 ≤ length)
    (hlength : length ≤ 1 / 4) (hxy : |x - y| ≤ 1 / 4) :
    uniformCircle.real (arc (x : Circle) length ∩ arc (y : Circle) length) =
      max (length - |x - y|) 0 := by
  rw [measureReal_def, measure_arc_inter_coe length x y hlength₀ hlength hxy,
    ENNReal.toReal_ofReal (le_max_right _ _)]

/-- Probability that a uniform short arc misses both local points. -/
lemma measureReal_compl_arc_inter_compl_arc_coe
    (length x y : ℝ) (hlength₀ : 0 ≤ length)
    (hlength : length ≤ 1 / 4) (hxy : |x - y| ≤ 1 / 4) :
    uniformCircle.real
        ((arc (x : Circle) length)ᶜ ∩ (arc (y : Circle) length)ᶜ) =
      1 - 2 * length + max (length - |x - y|) 0 := by
  let A := arc (x : Circle) length
  let B := arc (y : Circle) length
  have hA : MeasurableSet A := measurableSet_ball
  have hB : MeasurableSet B := measurableSet_ball
  have hU := measureReal_union_add_inter (μ := uniformCircle) (s := A) hB
  have hcomp := measureReal_compl (μ := uniformCircle) (hA.union hB)
  have hAr : uniformCircle.real A = length :=
    measureReal_arc hlength₀ (hlength.trans (by norm_num))
  have hBr : uniformCircle.real B = length :=
    measureReal_arc hlength₀ (hlength.trans (by norm_num))
  have hIr : uniformCircle.real (A ∩ B) = max (length - |x - y|) 0 :=
    measureReal_arc_inter_coe length x y hlength₀ hlength hxy
  have huniv : uniformCircle.real (Set.univ : Set Circle) = 1 := probReal_univ
  rw [hAr, hBr, hIr] at hU
  rw [huniv] at hcomp
  rw [compl_union] at hcomp
  change uniformCircle.real (Aᶜ ∩ Bᶜ) = _
  linarith

/-- Every circle point is covered by some arc with index at least `N`. -/
def CoversFrom (a : ℕ → ℝ) (ω : Sample) (N : ℕ) : Prop :=
  ∀ x : Circle, ∃ n : ℕ, N ≤ n ∧ x ∈ arc (ω n) (a n)

/-- Every circle point belongs to infinitely many of the random arcs. -/
def CoversInfinitelyOften (a : ℕ → ℝ) (ω : Sample) : Prop :=
  ∀ N : ℕ, CoversFrom a ω N

/-- Literal coverage by at least one arc. -/
def CoversOnce (a : ℕ → ℝ) (ω : Sample) : Prop :=
  CoversFrom a ω 0

/-- The finitely many arcs with indices in `[N, M)` cover the circle. -/
def FiniteCovers (a : ℕ → ℝ) (ω : Sample) (N M : ℕ) : Prop :=
  ∀ x : Circle, ∃ n ∈ Finset.Ico N M, x ∈ arc (ω n) (a n)

/-- If shortened arcs cover a fine grid, the original arcs cover the circle. -/
lemma finiteCovers_of_grid_shrunken {a : ℕ → ℝ} {ω : Sample} {M : ℕ}
    (hM : 0 < M) (hlength : ∀ n < M, 2 / (M : ℝ) < a n)
    (hgrid : ∀ j < M, ∃ n < M,
      gridPoint M j ∈ arc (ω n) (a n - 2 / (M : ℝ))) :
    FiniteCovers a ω 0 M := by
  intro x
  obtain ⟨j, hjM, hxj⟩ := exists_gridPoint_dist_lt M hM x
  obtain ⟨n, hnM, hjn⟩ := hgrid j hjM
  refine ⟨n, Finset.mem_Ico.2 ⟨Nat.zero_le n, hnM⟩, ?_⟩
  have hdist : dist x (ω n) < a n / 2 := by
    calc
      dist x (ω n) ≤ dist x (gridPoint M j) + dist (gridPoint M j) (ω n) :=
        dist_triangle _ _ _
      _ < 1 / (M : ℝ) + (a n - 2 / (M : ℝ)) / 2 := by
        exact add_lt_add hxj (by
          simpa only [arc, Metric.mem_ball] using hjn)
      _ = a n / 2 := by ring
  simpa only [arc, Metric.mem_ball] using hdist

/-- The event that a specified finite window covers the circle. -/
def finiteCoverEvent (a : ℕ → ℝ) (N M : ℕ) : Set Sample :=
  {ω | FiniteCovers a ω N M}

/-- Pairs consisting of a center sequence and a circle point missed by a
specified finite window. -/
def finiteMissPairs (a : ℕ → ℝ) (N M : ℕ) : Set (Sample × Circle) :=
  {p | ∀ n ∈ Finset.Ico N M, a n / 2 ≤ dist p.2 (p.1 n)}

lemma isClosed_finiteMissPairs (a : ℕ → ℝ) (N M : ℕ) :
    IsClosed (finiteMissPairs a N M) := by
  simp only [finiteMissPairs, setOf_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro _hn
  exact isClosed_le continuous_const
    (continuous_snd.dist ((continuous_apply n).comp continuous_fst))

lemma finiteCoverEvent_compl (a : ℕ → ℝ) (N M : ℕ) :
    (finiteCoverEvent a N M)ᶜ = Prod.fst '' finiteMissPairs a N M := by
  ext ω
  simp only [finiteCoverEvent, mem_compl_iff, mem_setOf_eq, FiniteCovers,
    image_image, mem_image, finiteMissPairs, Finset.mem_Ico, arc,
    Metric.mem_ball, not_forall, not_exists, not_and, not_lt]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨(ω, x), hx, rfl⟩
  · rintro ⟨⟨ω', x⟩, hx, hω⟩
    simp only [Prod.fst] at hω
    subst ω'
    exact ⟨x, hx⟩

lemma measurableSet_finiteCoverEvent (a : ℕ → ℝ) (N M : ℕ) :
    MeasurableSet (finiteCoverEvent a N M) := by
  have hc : IsClosed ((finiteCoverEvent a N M)ᶜ) := by
    rw [finiteCoverEvent_compl]
    exact isClosedMap_fst_of_compactSpace _ (isClosed_finiteMissPairs a N M)
  simpa using hc.isOpen_compl.measurableSet

lemma coversFrom_iff_exists_finiteCovers (a : ℕ → ℝ) (ω : Sample) (N : ℕ) :
    CoversFrom a ω N ↔ ∃ M : ℕ, FiniteCovers a ω N M := by
  constructor
  · intro hcover
    let U : {n : ℕ // N ≤ n} → Set Circle :=
      fun n ↦ arc (ω n) (a n)
    have hopen : ∀ n, IsOpen (U n) := fun n ↦ Metric.isOpen_ball
    have hsub : (Set.univ : Set Circle) ⊆ ⋃ n, U n := by
      intro x _hx
      obtain ⟨n, hn, hxn⟩ := hcover x
      exact mem_iUnion.2 ⟨⟨n, hn⟩, hxn⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hsub
    obtain ⟨B, hB⟩ := t.exists_le
    refine ⟨B + 1, fun x ↦ ?_⟩
    have hx : x ∈ ⋃ n ∈ t, U n := ht (mem_univ x)
    simp only [mem_iUnion] at hx
    obtain ⟨n, hn, hxn⟩ := hx
    refine ⟨n, ?_, hxn⟩
    exact Finset.mem_Ico.2 ⟨n.property, Nat.lt_succ_of_le (hB n hn)⟩
  · rintro ⟨M, hM⟩ x
    obtain ⟨n, hn, hxn⟩ := hM x
    exact ⟨n, (Finset.mem_Ico.1 hn).1, hxn⟩

/-- Measurable event that a tail covers the entire circle. -/
def coversFromEvent (a : ℕ → ℝ) (N : ℕ) : Set Sample :=
  {ω | CoversFrom a ω N}

lemma coversFromEvent_eq_iUnion (a : ℕ → ℝ) (N : ℕ) :
    coversFromEvent a N = ⋃ M : ℕ, finiteCoverEvent a N M := by
  ext ω
  simp only [coversFromEvent, mem_setOf_eq, mem_iUnion, finiteCoverEvent,
    coversFrom_iff_exists_finiteCovers]

lemma measurableSet_coversFromEvent (a : ℕ → ℝ) (N : ℕ) :
    MeasurableSet (coversFromEvent a N) := by
  rw [coversFromEvent_eq_iUnion]
  exact MeasurableSet.iUnion (fun M ↦ measurableSet_finiteCoverEvent a N M)

/-- Measurable event of Dvoretzky (limsup) coverage. -/
def fullCoverageEvent (a : ℕ → ℝ) : Set Sample :=
  {ω | CoversInfinitelyOften a ω}

lemma fullCoverageEvent_eq_iInter (a : ℕ → ℝ) :
    fullCoverageEvent a = ⋂ N : ℕ, coversFromEvent a N := by
  ext ω
  simp [fullCoverageEvent, CoversInfinitelyOften, coversFromEvent]

lemma measurableSet_fullCoverageEvent (a : ℕ → ℝ) :
    MeasurableSet (fullCoverageEvent a) := by
  rw [fullCoverageEvent_eq_iInter]
  exact MeasurableSet.iInter (measurableSet_coversFromEvent a)

/-- Measurable event of literal one-time coverage. -/
def onceCoverageEvent (a : ℕ → ℝ) : Set Sample :=
  {ω | CoversOnce a ω}

lemma onceCoverageEvent_eq (a : ℕ → ℝ) :
    onceCoverageEvent a = coversFromEvent a 0 := by
  rfl

lemma measurableSet_onceCoverageEvent (a : ℕ → ℝ) :
    MeasurableSet (onceCoverageEvent a) := by
  rw [onceCoverageEvent_eq]
  exact measurableSet_coversFromEvent a 0

lemma measure_fullCoverageEvent_eq_one_iff (a : ℕ → ℝ) :
    sampleMeasure (fullCoverageEvent a) = 1 ↔
      ∀ N : ℕ, sampleMeasure (coversFromEvent a N) = 1 := by
  constructor
  · intro h N
    apply (mem_ae_iff_prob_eq_one (measurableSet_coversFromEvent a N)).mp
    have hall : fullCoverageEvent a ∈ ae sampleMeasure :=
      (mem_ae_iff_prob_eq_one (measurableSet_fullCoverageEvent a)).mpr h
    filter_upwards [hall] with ω hω
    exact hω N
  · intro h
    apply (mem_ae_iff_prob_eq_one (measurableSet_fullCoverageEvent a)).mp
    have htail : ∀ N : ℕ, coversFromEvent a N ∈ ae sampleMeasure :=
      fun N ↦ (mem_ae_iff_prob_eq_one (measurableSet_coversFromEvent a N)).mpr (h N)
    have hall : ∀ᵐ ω ∂sampleMeasure, ∀ N : ℕ, ω ∈ coversFromEvent a N :=
      ae_all_iff.mpr htail
    filter_upwards [hall] with ω hω
    exact hω

/-- Prefix sum of the first `n` lengths. -/
def prefixLength (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, a k

/-- The zero-based version of Shepp's summand
`exp (a₁ + ⋯ + aₙ) / n²`. -/
def sheppTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (prefixLength a (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ 2

/-- Shepp's divergence condition.  The terms are positive, so failure of
summability is exactly divergence of the partial sums to `+∞`. -/
def SheppCondition (a : ℕ → ℝ) : Prop :=
  ¬ Summable (sheppTerm a)

/-- `b` lists, in nonincreasing order and with multiplicity, precisely the
positive terms of `a`. -/
def IsDecreasingRearrangement (a b : ℕ → ℝ) : Prop :=
  Antitone b ∧
    ∃ e : ℕ ≃ {n : ℕ // 0 < a n}, ∀ k : ℕ, b k = a (e k : ℕ)

/-- Coordinate evaluation on the canonical sample space. -/
def center (n : ℕ) (ω : Sample) : Circle := ω n

lemma center_measurable (n : ℕ) : Measurable (center n) := by
  exact measurable_pi_apply n

lemma center_iIndep : iIndepFun center sampleMeasure := by
  change iIndepFun (fun n (ω : ℕ → Circle) ↦ ω n)
    (Measure.infinitePi fun _ : ℕ ↦ uniformCircle)
  exact iIndepFun_infinitePi (P := fun _ : ℕ ↦ uniformCircle)
    (X := fun _ ↦ id) (fun _ ↦ measurable_id)

lemma center_map (n : ℕ) :
    sampleMeasure.map (center n) = uniformCircle := by
  change (Measure.infinitePi fun _ : ℕ ↦ uniformCircle).map
    (fun ω : ℕ → Circle ↦ ω n) = uniformCircle
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ uniformCircle) n

lemma center_hasLaw (n : ℕ) :
    HasLaw (center n) uniformCircle sampleMeasure := by
  exact ⟨(center_measurable n).aemeasurable, center_map n⟩

/-- The event that the `n`th random arc covers the fixed point `x`. -/
def hitEvent (a : ℕ → ℝ) (x : Circle) (n : ℕ) : Set Sample :=
  center n ⁻¹' Metric.ball x (a n / 2)

/-- Event that the `n`th arc misses a fixed point. -/
def missEvent (a : ℕ → ℝ) (x : Circle) (n : ℕ) : Set Sample :=
  (hitEvent a x n)ᶜ

/-- Event that the `n`th arc misses both specified points. -/
def twoMissEvent (a : ℕ → ℝ) (x y : Circle) (n : ℕ) : Set Sample :=
  missEvent a x n ∩ missEvent a y n

lemma mem_hitEvent_iff (a : ℕ → ℝ) (x : Circle) (n : ℕ) (ω : Sample) :
    ω ∈ hitEvent a x n ↔ x ∈ arc (ω n) (a n) := by
  simp only [hitEvent, mem_preimage, Metric.mem_ball, arc, center]
  rw [dist_comm]

lemma measurableSet_hitEvent (a : ℕ → ℝ) (x : Circle) (n : ℕ) :
    MeasurableSet (hitEvent a x n) :=
  (measurableSet_ball.preimage (center_measurable n))

lemma measurableSet_missEvent (a : ℕ → ℝ) (x : Circle) (n : ℕ) :
    MeasurableSet (missEvent a x n) :=
  (measurableSet_hitEvent a x n).compl

lemma measurableSet_twoMissEvent (a : ℕ → ℝ) (x y : Circle) (n : ℕ) :
    MeasurableSet (twoMissEvent a x y n) :=
  (measurableSet_missEvent a x n).inter (measurableSet_missEvent a y n)

lemma measure_hitEvent {a : ℕ → ℝ} (x : Circle) (n : ℕ)
    (ha₀ : 0 ≤ a n) (ha₁ : a n ≤ 1) :
    sampleMeasure (hitEvent a x n) = ENNReal.ofReal (a n) := by
  calc
    sampleMeasure (hitEvent a x n) =
        (sampleMeasure.map (center n)) (Metric.ball x (a n / 2)) := by
      rw [Measure.map_apply (center_measurable n) measurableSet_ball]
      rfl
    _ = uniformCircle (Metric.ball x (a n / 2)) := by rw [center_map]
    _ = ENNReal.ofReal (a n) := measure_arc ha₀ ha₁

lemma measureReal_missEvent {a : ℕ → ℝ} (x : Circle) (n : ℕ)
    (ha₀ : 0 ≤ a n) (ha₁ : a n ≤ 1) :
    sampleMeasure.real (missEvent a x n) = 1 - a n := by
  have hcomp := measureReal_compl (μ := sampleMeasure)
    (measurableSet_hitEvent a x n)
  rw [probReal_univ] at hcomp
  have hhit : sampleMeasure.real (hitEvent a x n) = a n := by
    rw [measureReal_def, measure_hitEvent x n ha₀ ha₁,
      ENNReal.toReal_ofReal ha₀]
  rw [hhit] at hcomp
  exact hcomp

lemma measureReal_iInter_missEvent
    {a : ℕ → ℝ} (M : ℕ) (x : Circle) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) :
    sampleMeasure.real (⋂ n ∈ Finset.range M, missEvent a x n) =
      ∏ n ∈ Finset.range M, (1 - a n) := by
  let S : ℕ → Set Circle := fun n ↦ (arc x (a n))ᶜ
  have hSm : ∀ n, MeasurableSet (S n) := fun n ↦ measurableSet_ball.compl
  have hset (n : ℕ) : missEvent a x n = center n ⁻¹' S n := by
    ext ω
    simp [missEvent, hitEvent, S, arc, center]
  have hprod := center_iIndep.measure_inter_preimage_eq_mul
    (Finset.range M) (sets := S) (fun n _hn ↦ hSm n)
  simp_rw [← hset] at hprod
  rw [measureReal_def, hprod, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro n hn
  rw [← measureReal_def, measureReal_missEvent x n (ha₀ n) (ha₁ n)]

/-- Lengths shortened by twice the mesh radius of the `M`-point grid. -/
def shrunkenLength (a : ℕ → ℝ) (M : ℕ) (n : ℕ) : ℝ :=
  a n - 2 / (M : ℝ)

lemma finiteCoverEvent_compl_subset_gridMiss {a : ℕ → ℝ} {M : ℕ}
    (hM : 0 < M) (hlength : ∀ n < M, 2 / (M : ℝ) < a n) :
    (finiteCoverEvent a 0 M)ᶜ ⊆
      ⋃ j ∈ Finset.range M,
        ⋂ n ∈ Finset.range M, missEvent (shrunkenLength a M) (gridPoint M j) n := by
  intro ω hω
  contrapose! hω
  rw [mem_compl_iff, not_not]
  apply finiteCovers_of_grid_shrunken hM hlength
  intro j hjM
  have hjnot : ω ∉ ⋂ n ∈ Finset.range M,
      missEvent (shrunkenLength a M) (gridPoint M j) n := by
    intro hj
    apply hω
    exact mem_iUnion.2 ⟨j,
      mem_iUnion.2 ⟨Finset.mem_range.2 hjM, hj⟩⟩
  simp only [mem_iInter] at hjnot
  push_neg at hjnot
  obtain ⟨n, hnM, hnmiss⟩ := hjnot
  have hhit : ω ∈ hitEvent (shrunkenLength a M) (gridPoint M j) n := by
    simpa only [missEvent, mem_compl_iff, not_not] using hnmiss
  exact ⟨n, Finset.mem_range.1 hnM, (mem_hitEvent_iff _ _ _ _).mp hhit⟩

/-- The elementary grid union bound used when the squared lengths diverge. -/
lemma measureReal_finiteCoverEvent_compl_le_gridProduct
    {a : ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (hlength : ∀ n < M, 2 / (M : ℝ) < a n)
    (ha : ∀ n, a n ≤ 1) :
    sampleMeasure.real (finiteCoverEvent a 0 M)ᶜ ≤
      (M : ℝ) * ∏ n ∈ Finset.range M, (1 - a n + 2 / (M : ℝ)) := by
  let b := shrunkenLength a M
  -- Outside the finite window the values of `b` are irrelevant.  Replacing
  -- them by zero gives global hypotheses for the product lemma.
  let b' : ℕ → ℝ := fun n ↦ if n < M then b n else 0
  have hb'₀ : ∀ n, 0 ≤ b' n := by
    intro n
    simp only [b']
    split_ifs with hn
    · dsimp only [b, shrunkenLength]
      linarith [hlength n hn]
    · exact le_rfl
  have hb'₁ : ∀ n, b' n ≤ 1 := by
    intro n
    simp only [b']
    split_ifs with hn
    · dsimp only [b, shrunkenLength]
      have hMℝ : (0 : ℝ) < M := by exact_mod_cast hM
      have htwo : 0 ≤ 2 / (M : ℝ) := by positivity
      linarith [ha n]
    · norm_num
  have heq (n : ℕ) (hn : n ∈ Finset.range M) : b' n = b n := by
    simp [b', Finset.mem_range.1 hn]
  let E : ℕ → Set Sample := fun j ↦
    ⋂ n ∈ Finset.range M, missEvent b' (gridPoint M j) n
  have hsubset : (finiteCoverEvent a 0 M)ᶜ ⊆ ⋃ j ∈ Finset.range M, E j := by
    intro ω hω
    have hω' := finiteCoverEvent_compl_subset_gridMiss hM hlength hω
    obtain ⟨j, hj⟩ := mem_iUnion.1 hω'
    obtain ⟨hjM, hj⟩ := mem_iUnion.1 hj
    apply mem_iUnion.2
    refine ⟨j, mem_iUnion.2 ⟨hjM, ?_⟩⟩
    dsimp only [E]
    apply mem_iInter.2
    intro n
    apply mem_iInter.2
    intro hn
    have hjn := mem_iInter.1 (mem_iInter.1 hj n) hn
    have hbn : b' n = shrunkenLength a M n := by
      simpa only [b] using heq n hn
    have hmiss : missEvent b' (gridPoint M j) n =
        missEvent (shrunkenLength a M) (gridPoint M j) n := by
      unfold missEvent hitEvent
      rw [hbn]
    rw [hmiss]
    exact hjn
  calc
    sampleMeasure.real (finiteCoverEvent a 0 M)ᶜ ≤
        sampleMeasure.real (⋃ j ∈ Finset.range M, E j) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range M, sampleMeasure.real (E j) :=
      measureReal_biUnion_finset_le (Finset.range M) E
    _ = ∑ _j ∈ Finset.range M, ∏ n ∈ Finset.range M, (1 - b' n) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact measureReal_iInter_missEvent M (gridPoint M j) hb'₀ hb'₁
    _ = (M : ℝ) * ∏ n ∈ Finset.range M, (1 - a n + 2 / (M : ℝ)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro n hn
      rw [heq n hn]
      dsimp only [b, shrunkenLength]
      ring

lemma gridProduct_le_exp_prefix {a : ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) :
    (M : ℝ) * ∏ n ∈ Finset.range M, (1 - a n + 2 / (M : ℝ)) ≤
      (M : ℝ) * Real.exp (2 - prefixLength a M) := by
  have hfactor (n : ℕ) : 0 ≤ 1 - a n + 2 / (M : ℝ) := by
    have hMℝ : (0 : ℝ) < M := by exact_mod_cast hM
    have htwo : 0 ≤ 2 / (M : ℝ) := by positivity
    linarith [ha₁ n]
  have hprod :
      (∏ n ∈ Finset.range M, (1 - a n + 2 / (M : ℝ))) ≤
        ∏ n ∈ Finset.range M, Real.exp (-a n + 2 / (M : ℝ)) := by
    apply Finset.prod_le_prod
    · intro n hn
      exact hfactor n
    · intro n hn
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        Real.add_one_le_exp (-a n + 2 / (M : ℝ))
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    (∏ n ∈ Finset.range M, (1 - a n + 2 / (M : ℝ))) ≤
        ∏ n ∈ Finset.range M, Real.exp (-a n + 2 / (M : ℝ)) := hprod
    _ = Real.exp (∑ n ∈ Finset.range M, (-a n + 2 / (M : ℝ))) := by
      rw [← Real.exp_sum]
    _ = Real.exp (2 - prefixLength a M) := by
      congr 1
      unfold prefixLength
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hMℝ : (M : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- A summable comparison scale used to extract the large terms in the
nonsquare-summable case. -/
def largeSquareThreshold (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))

lemma largeSquareThreshold_sq (n : ℕ) :
    largeSquareThreshold n ^ 2 =
      ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  unfold largeSquareThreshold
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  congr 2
  ring

lemma summable_largeSquareThreshold_sq :
    Summable (fun n ↦ largeSquareThreshold n ^ 2) := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  exact hshift.congr fun n ↦ by
    rw [largeSquareThreshold_sq]

lemma frequently_largeSquareThreshold {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (hsq : ¬ Summable (fun n ↦ a n ^ 2)) :
    ∀ N, ∃ n, N ≤ n ∧ largeSquareThreshold n < a n := by
  intro N
  by_contra h
  push_neg at h
  have hev : ∀ᶠ n in atTop, a n ≤ largeSquareThreshold n :=
    eventually_atTop.2 ⟨N, h⟩
  apply hsq
  apply Summable.of_norm_bounded_eventually summable_largeSquareThreshold_sq
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (ha₀ n) (Real.rpow_nonneg (by positivity) _)).2 hn

lemma tendsto_vanishingGridBound :
    Tendsto (fun M : ℕ ↦ (M : ℝ) *
      Real.exp (2 - (M : ℝ) ^ (1 / 4 : ℝ))) atTop (nhds 0) := by
  have hx : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  have hreal := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
  have hcomp := hreal.comp hx
  have hc : Tendsto (fun _ : ℕ ↦ Real.exp 2) atTop (nhds (Real.exp 2)) :=
    tendsto_const_nhds
  have hconst : Tendsto (fun M : ℕ ↦ Real.exp 2 *
      (((M : ℝ) ^ (1 / 4 : ℝ)) ^ 4 *
        Real.exp (-((M : ℝ) ^ (1 / 4 : ℝ))))) atTop (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using hc.mul hcomp
  convert hconst using 1
  · funext M
    rw [Real.exp_sub]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    rw [Real.exp_neg]
    ring

lemma eventually_two_div_lt_rpow_neg_three_quarters :
    ∀ᶠ M : ℕ in atTop,
      0 < M ∧ 2 / (M : ℝ) < (M : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hx : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ M : ℕ in atTop,
      (2 : ℝ) < (M : ℝ) ^ (1 / 4 : ℝ) := by
    filter_upwards [tendsto_atTop.1 hx 3] with M hM
    linarith
  filter_upwards [hlarge, eventually_gt_atTop 0] with M htwo hM
  refine ⟨hM, ?_⟩
  have hMℝ : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_lt_iff₀ hMℝ]
  calc
    (2 : ℝ) < (M : ℝ) ^ (1 / 4 : ℝ) := htwo
    _ = (M : ℝ) ^ (-(3 / 4 : ℝ) + 1) := by
      congr 1
      ring
    _ = (M : ℝ) ^ (-(3 / 4 : ℝ)) * (M : ℝ) := by
      rw [Real.rpow_add hMℝ, Real.rpow_one]

lemma prefixLength_ge_mul_of_antitone {a : ℕ → ℝ}
    (hanti : Antitone a) {M : ℕ} :
    (M : ℝ) * a (M - 1) ≤ prefixLength a M := by
  unfold prefixLength
  calc
    (M : ℝ) * a (M - 1) = ∑ _k ∈ Finset.range M, a (M - 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range M, a k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hanti (Nat.le_sub_one_of_lt (Finset.mem_range.1 hk))

lemma selected_prefix_bound {a : ℕ → ℝ}
    (hanti : Antitone a) {n : ℕ}
    (hn : largeSquareThreshold n < a n) :
    ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) < prefixLength a (n + 1) := by
  have hMpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hmul := mul_lt_mul_of_pos_left hn hMpos
  have hprefix := prefixLength_ge_mul_of_antitone hanti (M := n + 1)
  have hid : ((n + 1 : ℕ) : ℝ) * largeSquareThreshold n =
      ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
    unfold largeSquareThreshold
    calc
      ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) =
          ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) *
            ((n + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) := by
            congr 1
            exact (Real.rpow_one _).symm
      _ = ((n + 1 : ℕ) : ℝ) ^ (1 + -(3 / 4 : ℝ)) := by
        exact (Real.rpow_add (by positivity) _ _).symm
      _ = ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
        congr 1
        ring
  rw [hid] at hmul
  exact hmul.trans_le (by simpa using hprefix)

lemma finiteCover_probability_arbitrarily_close_one_of_not_summable_sq
    {a : ℕ → ℝ} (hanti : Antitone a)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hsq : ¬ Summable (fun n ↦ a n ^ 2)) {c : ℝ} (hc : 0 < c) :
    ∃ M : ℕ, sampleMeasure.real (finiteCoverEvent a 0 M)ᶜ < c := by
  have hvanish : ∀ᶠ M : ℕ in atTop,
      (M : ℝ) * Real.exp (2 - (M : ℝ) ^ (1 / 4 : ℝ)) < c :=
    (tendsto_order.1 tendsto_vanishingGridBound).2 c hc
  have hevent : ∀ᶠ M : ℕ in atTop,
      (0 < M ∧ 2 / (M : ℝ) < (M : ℝ) ^ (-(3 / 4 : ℝ))) ∧
        (M : ℝ) * Real.exp (2 - (M : ℝ) ^ (1 / 4 : ℝ)) < c :=
    eventually_two_div_lt_rpow_neg_three_quarters.and hvanish
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  obtain ⟨n, hnN, hnlarge⟩ := frequently_largeSquareThreshold ha₀ hsq (N - 1)
  let M := n + 1
  have hNM : N ≤ M := by
    dsimp only [M]
    omega
  have hgood := hN M hNM
  have hMpos : 0 < M := hgood.1.1
  have hmesh : 2 / (M : ℝ) < largeSquareThreshold n := by
    simpa only [M, largeSquareThreshold] using hgood.1.2
  have hlength : ∀ k < M, 2 / (M : ℝ) < a k := by
    intro k hk
    exact (hmesh.trans hnlarge).trans_le (hanti (by omega))
  have hprefix : (M : ℝ) ^ (1 / 4 : ℝ) < prefixLength a M := by
    simpa only [M] using selected_prefix_bound hanti hnlarge
  refine ⟨M, ?_⟩
  calc
    sampleMeasure.real (finiteCoverEvent a 0 M)ᶜ ≤
        (M : ℝ) * ∏ k ∈ Finset.range M,
          (1 - a k + 2 / (M : ℝ)) :=
      measureReal_finiteCoverEvent_compl_le_gridProduct hMpos hlength ha₁
    _ ≤ (M : ℝ) * Real.exp (2 - prefixLength a M) :=
      gridProduct_le_exp_prefix hMpos ha₀ ha₁
    _ ≤ (M : ℝ) * Real.exp (2 - (M : ℝ) ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      linarith
    _ < c := hgood.2

theorem measure_onceCoverageEvent_eq_one_of_not_summable_sq
    {a : ℕ → ℝ} (hanti : Antitone a)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hsq : ¬ Summable (fun n ↦ a n ^ 2)) :
    sampleMeasure (onceCoverageEvent a) = 1 := by
  have hzero : sampleMeasure.real (onceCoverageEvent a)ᶜ = 0 := by
    apply le_antisymm
    · by_contra hne
      have hpos : 0 < sampleMeasure.real (onceCoverageEvent a)ᶜ :=
        lt_of_not_ge hne
      obtain ⟨M, hM⟩ :=
        finiteCover_probability_arbitrarily_close_one_of_not_summable_sq
          hanti ha₀ ha₁ hsq hpos
      have hsubset : (onceCoverageEvent a)ᶜ ⊆ (finiteCoverEvent a 0 M)ᶜ := by
        intro ω hω hfinite
        apply hω
        rw [onceCoverageEvent_eq, coversFromEvent_eq_iUnion]
        exact mem_iUnion.2 ⟨M, hfinite⟩
      have hle := measureReal_mono (μ := sampleMeasure) hsubset
        (measure_ne_top _ _)
      linarith
    · exact measureReal_nonneg
  rw [measureReal_eq_zero_iff] at hzero
  have hadd := measure_add_measure_compl (μ := sampleMeasure)
    (measurableSet_onceCoverageEvent a)
  simpa only [hzero, add_zero, measure_univ] using hadd

lemma measureReal_missEvent_inter_missEvent_coe
    {a : ℕ → ℝ} (n : ℕ) (x y : ℝ) (ha₀ : 0 ≤ a n)
    (ha : a n ≤ 1 / 4) (hxy : |x - y| ≤ 1 / 4) :
    sampleMeasure.real
        (missEvent a (x : Circle) n ∩ missEvent a (y : Circle) n) =
      1 - 2 * a n + max (a n - |x - y|) 0 := by
  let S : Set Circle :=
    (arc (x : Circle) (a n))ᶜ ∩ (arc (y : Circle) (a n))ᶜ
  have hS : MeasurableSet S :=
    measurableSet_ball.compl.inter measurableSet_ball.compl
  have hset : missEvent a (x : Circle) n ∩ missEvent a (y : Circle) n =
      center n ⁻¹' S := by
    ext ω
    simp [missEvent, hitEvent, S, arc, center]
  rw [hset, measureReal_def, ← Measure.map_apply (center_measurable n) hS,
    center_map]
  exact measureReal_compl_arc_inter_compl_arc_coe (a n) x y ha₀ ha hxy

lemma measureReal_iInter_twoMissEvent_coe
    {a : ℕ → ℝ} (M : ℕ) (x y : ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n ≤ 1 / 4) (hxy : |x - y| ≤ 1 / 4) :
    sampleMeasure.real
        (⋂ n ∈ Finset.range M, twoMissEvent a (x : Circle) (y : Circle) n) =
      ∏ n ∈ Finset.range M,
        (1 - 2 * a n + max (a n - |x - y|) 0) := by
  let S : ℕ → Set Circle := fun n ↦
    (arc (x : Circle) (a n))ᶜ ∩ (arc (y : Circle) (a n))ᶜ
  have hSm : ∀ n, MeasurableSet (S n) := fun n ↦
    measurableSet_ball.compl.inter measurableSet_ball.compl
  have hset (n : ℕ) : twoMissEvent a (x : Circle) (y : Circle) n =
      center n ⁻¹' S n := by
    ext ω
    simp [twoMissEvent, missEvent, hitEvent, S, arc, center]
  have hprod := center_iIndep.measure_inter_preimage_eq_mul
    (Finset.range M) (sets := S) (fun n _hn ↦ hSm n)
  simp_rw [← hset] at hprod
  rw [measureReal_def, hprod, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro n hn
  change sampleMeasure.real
      (missEvent a (x : Circle) n ∩ missEvent a (y : Circle) n) = _
  exact measureReal_missEvent_inter_missEvent_coe n x y
    (ha₀ n) (ha n) hxy

/-! ### Finite local uncovered length -/

/-- Joint event that the `n`th arc misses the real-coordinate point `t`. -/
def jointMissSet (a : ℕ → ℝ) (n : ℕ) : Set (Sample × ℝ) :=
  {p | a n / 2 ≤ dist (p.1 n) (p.2 : Circle)}

lemma measurableSet_jointMissSet (a : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (jointMissSet a n) := by
  apply measurableSet_le measurable_const
  exact ((measurable_pi_apply n).comp measurable_fst).dist
    (AddCircle.measurable_mk'.comp measurable_snd)

/-- Joint set of pairs `(ω,t)` for which the point represented by `t` is
missed by all of the first `M` arcs. -/
def finiteUncoveredPairs (a : ℕ → ℝ) (M : ℕ) : Set (Sample × ℝ) :=
  ⋂ n ∈ Finset.range M, jointMissSet a n

lemma measurableSet_finiteUncoveredPairs (a : ℕ → ℝ) (M : ℕ) :
    MeasurableSet (finiteUncoveredPairs a M) := by
  exact Finset.measurableSet_biInter (Finset.range M)
    (fun n _hn ↦ measurableSet_jointMissSet a n)

/-- The `0`/`1` indicator of finite noncoverage at a local real coordinate. -/
def uncoveredIndicator (a : ℕ → ℝ) (M : ℕ) (p : Sample × ℝ) : ℝ :=
  (finiteUncoveredPairs a M).indicator (fun _ ↦ (1 : ℝ)) p

lemma measurable_uncoveredIndicator (a : ℕ → ℝ) (M : ℕ) :
    Measurable (uncoveredIndicator a M) :=
  measurable_const.indicator (measurableSet_finiteUncoveredPairs a M)

/-- Lebesgue length in `[0, ε]` missed by the first `M` arcs. -/
def localUncoveredLength (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) (ω : Sample) : ℝ :=
  ∫ t in Icc (0 : ℝ) ε, uncoveredIndicator a M (ω, t)

lemma stronglyMeasurable_localUncoveredLength (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    StronglyMeasurable (localUncoveredLength a M ε) := by
  exact (measurable_uncoveredIndicator a M).stronglyMeasurable.integral_prod_right'

lemma measurable_localUncoveredLength (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    Measurable (localUncoveredLength a M ε) :=
  (stronglyMeasurable_localUncoveredLength a M ε).measurable

lemma uncoveredIndicator_nonneg (a : ℕ → ℝ) (M : ℕ) (p : Sample × ℝ) :
    0 ≤ uncoveredIndicator a M p := by
  simp only [uncoveredIndicator]
  by_cases hp : p ∈ finiteUncoveredPairs a M <;> simp [Set.indicator, hp]

lemma uncoveredIndicator_le_one (a : ℕ → ℝ) (M : ℕ) (p : Sample × ℝ) :
    uncoveredIndicator a M p ≤ 1 := by
  simp only [uncoveredIndicator]
  by_cases hp : p ∈ finiteUncoveredPairs a M <;> simp [Set.indicator, hp]

lemma localUncoveredLength_nonneg (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) (ω : Sample) :
    0 ≤ localUncoveredLength a M ε ω := by
  unfold localUncoveredLength
  exact integral_nonneg_of_ae (ae_of_all _ fun t ↦ uncoveredIndicator_nonneg a M (ω, t))

lemma localUncoveredLength_le (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ω : Sample) : localUncoveredLength a M ε ω ≤ ε := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) ε)
  have hint : Integrable (fun t ↦ uncoveredIndicator a M (ω, t)) ν := by
    apply (integrable_const (μ := ν) (1 : ℝ)).mono'
      ((measurable_uncoveredIndicator a M).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    filter_upwards [] with t
    change ‖uncoveredIndicator a M (ω, t)‖ ≤ 1
    rw [Real.norm_of_nonneg (uncoveredIndicator_nonneg a M (ω, t))]
    exact uncoveredIndicator_le_one a M (ω, t)
  have hle : (∫ t, uncoveredIndicator a M (ω, t) ∂ν) ≤ ∫ _t, (1 : ℝ) ∂ν := by
    exact integral_mono_ae hint (integrable_const (1 : ℝ))
      (ae_of_all _ fun t ↦ uncoveredIndicator_le_one a M (ω, t))
  change (∫ t, uncoveredIndicator a M (ω, t) ∂ν) ≤ ε
  calc
    (∫ t, uncoveredIndicator a M (ω, t) ∂ν) ≤ ∫ _t, (1 : ℝ) ∂ν := hle
    _ = ε := by
      rw [integral_const]
      simp [ν, measureReal_def, Real.volume_Icc, hε]

/-- Event that the first `M` arcs leave a positive-length part of `[0,ε]`
uncovered. -/
def localUncoveredPositive (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) : Set Sample :=
  {ω | 0 < localUncoveredLength a M ε ω}

lemma measurableSet_localUncoveredPositive (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    MeasurableSet (localUncoveredPositive a M ε) := by
  exact measurableSet_lt measurable_const (measurable_localUncoveredLength a M ε)

lemma jointMissSet_section (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (fun ω : Sample ↦ (ω, t)) ⁻¹' jointMissSet a n =
      missEvent a (t : Circle) n := by
  ext ω
  simp only [jointMissSet, mem_preimage, mem_setOf_eq, Prod.fst, Prod.snd,
    missEvent, hitEvent, mem_compl_iff, Metric.mem_ball, center]
  rw [not_lt, dist_comm]

lemma finiteUncoveredPairs_section (a : ℕ → ℝ) (M : ℕ) (t : ℝ) :
    (fun ω : Sample ↦ (ω, t)) ⁻¹' finiteUncoveredPairs a M =
      ⋂ n ∈ Finset.range M, missEvent a (t : Circle) n := by
  simp only [finiteUncoveredPairs, preimage_iInter, jointMissSet_section]

lemma uncoveredIndicator_section (a : ℕ → ℝ) (M : ℕ) (t : ℝ) :
    (fun ω ↦ uncoveredIndicator a M (ω, t)) =
      (⋂ n ∈ Finset.range M, missEvent a (t : Circle) n).indicator
        (fun _ ↦ (1 : ℝ)) := by
  funext ω
  simp only [uncoveredIndicator]
  rw [← finiteUncoveredPairs_section a M t]
  rfl

lemma integral_uncoveredIndicator_sample
    {a : ℕ → ℝ} (M : ℕ) (t : ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) :
    ∫ ω, uncoveredIndicator a M (ω, t) ∂sampleMeasure =
      ∏ n ∈ Finset.range M, (1 - a n) := by
  rw [uncoveredIndicator_section, integral_indicator_const]
  · simp only [smul_eq_mul, mul_one]
    exact measureReal_iInter_missEvent M (t : Circle) ha₀ ha₁
  · exact Finset.measurableSet_biInter (Finset.range M)
      (fun n _hn ↦ measurableSet_missEvent a (t : Circle) n)

lemma iInter_miss_inter_iInter_miss (a : ℕ → ℝ) (M : ℕ) (x y : Circle) :
    (⋂ n ∈ Finset.range M, missEvent a x n) ∩
        (⋂ n ∈ Finset.range M, missEvent a y n) =
      ⋂ n ∈ Finset.range M, twoMissEvent a x y n := by
  ext ω
  simp only [mem_inter_iff, mem_iInter, twoMissEvent]
  constructor
  · rintro ⟨hx, hy⟩ n hn
    exact ⟨hx n hn, hy n hn⟩
  · intro h
    exact ⟨fun n hn ↦ (h n hn).1, fun n hn ↦ (h n hn).2⟩

lemma integral_uncoveredIndicator_mul_sample
    {a : ℕ → ℝ} (M : ℕ) (x y : ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n ≤ 1 / 4) (hxy : |x - y| ≤ 1 / 4) :
    ∫ ω, uncoveredIndicator a M (ω, x) *
        uncoveredIndicator a M (ω, y) ∂sampleMeasure =
      ∏ n ∈ Finset.range M,
        (1 - 2 * a n + max (a n - |x - y|) 0) := by
  let A : Set Sample := ⋂ n ∈ Finset.range M, missEvent a (x : Circle) n
  let B : Set Sample := ⋂ n ∈ Finset.range M, missEvent a (y : Circle) n
  let C : Set Sample := ⋂ n ∈ Finset.range M,
    twoMissEvent a (x : Circle) (y : Circle) n
  have hAB : A ∩ B = C := by
    exact iInter_miss_inter_iInter_miss a M (x : Circle) (y : Circle)
  have hfun : (fun ω ↦ uncoveredIndicator a M (ω, x) *
      uncoveredIndicator a M (ω, y)) = C.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    rw [congrFun (uncoveredIndicator_section a M x) ω,
      congrFun (uncoveredIndicator_section a M y) ω]
    change A.indicator (fun _ ↦ (1 : ℝ)) ω *
        B.indicator (fun _ ↦ (1 : ℝ)) ω = _
    by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B
    · have hC : ω ∈ C := by simpa [← hAB] using And.intro hA hB
      simp [Set.indicator_of_mem hA, Set.indicator_of_mem hB,
        Set.indicator_of_mem hC]
    · have hC : ω ∉ C := by simpa [← hAB, hA] using hB
      simp [Set.indicator_of_mem hA, Set.indicator, hB, hC]
    · have hC : ω ∉ C := by simpa [← hAB, hB] using hA
      simp [Set.indicator, hA, hC]
    · have hC : ω ∉ C := by simpa [← hAB, hA] using hB
      simp [Set.indicator, hA, hB, hC]
  rw [hfun, integral_indicator_const]
  · simp only [smul_eq_mul, mul_one]
    exact measureReal_iInter_twoMissEvent_coe M x y ha₀ ha hxy
  · exact Finset.measurableSet_biInter (Finset.range M)
      (fun n _hn ↦ measurableSet_twoMissEvent a (x : Circle) (y : Circle) n)

/-- First-moment identity for the local uncovered length. -/
lemma integral_localUncoveredLength
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) :
    ∫ ω, localUncoveredLength a M ε ω ∂sampleMeasure =
      ε * ∏ n ∈ Finset.range M, (1 - a n) := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) ε)
  have hint : Integrable (uncoveredIndicator a M)
      (sampleMeasure.prod ν) := by
    apply (integrable_const (μ := sampleMeasure.prod ν) (1 : ℝ)).mono'
      (measurable_uncoveredIndicator a M).aestronglyMeasurable
    filter_upwards [] with p
    simp only [uncoveredIndicator]
    by_cases hp : p ∈ finiteUncoveredPairs a M
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator, hp]
  have hint' : Integrable
      (Function.uncurry fun ω t ↦ uncoveredIndicator a M (ω, t))
      (sampleMeasure.prod ν) := by
    have hfun :
        (Function.uncurry fun ω t ↦ uncoveredIndicator a M (ω, t)) =
          uncoveredIndicator a M := by
      funext p
      rcases p with ⟨ω, t⟩
      rfl
    rw [hfun]
    exact hint
  change (∫ ω, ∫ t, uncoveredIndicator a M (ω, t) ∂ν ∂sampleMeasure) = _
  rw [integral_integral_swap hint']
  simp_rw [integral_uncoveredIndicator_sample M _ ha₀ ha₁]
  rw [integral_const]
  have hν : ν.real Set.univ = ε := by
    simp [ν, measureReal_def, Real.volume_Icc, hε]
  rw [hν]
  simp only [smul_eq_mul]

lemma localUncoveredLength_sq (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) (ω : Sample) :
    localUncoveredLength a M ε ω ^ 2 =
      ∫ x in Icc (0 : ℝ) ε, ∫ y in Icc (0 : ℝ) ε,
        uncoveredIndicator a M (ω, x) * uncoveredIndicator a M (ω, y) := by
  rw [pow_two]
  unfold localUncoveredLength
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_const_mul]

/-- The exact second-moment identity on a short real-coordinate interval. -/
lemma integral_localUncoveredLength_sq
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    ∫ ω, localUncoveredLength a M ε ω ^ 2 ∂sampleMeasure =
      ∫ x in Icc (0 : ℝ) ε, ∫ y in Icc (0 : ℝ) ε,
        ∏ n ∈ Finset.range M,
          (1 - 2 * a n + max (a n - |x - y|) 0) := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) ε)
  let f : (Sample × ℝ) × ℝ → ℝ := fun p ↦
    uncoveredIndicator a M (p.1.1, p.1.2) *
      uncoveredIndicator a M (p.1.1, p.2)
  have hfmeas : Measurable f := by
    exact ((measurable_uncoveredIndicator a M).comp measurable_fst).mul
      ((measurable_uncoveredIndicator a M).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hfint : Integrable f ((sampleMeasure.prod ν).prod ν) := by
    apply (integrable_const (μ := (sampleMeasure.prod ν).prod ν) (1 : ℝ)).mono'
      hfmeas.aestronglyMeasurable
    filter_upwards [] with p
    simp only [f, uncoveredIndicator]
    by_cases hx : (p.1.1, p.1.2) ∈ finiteUncoveredPairs a M <;>
      by_cases hy : (p.1.1, p.2) ∈ finiteUncoveredPairs a M <;>
      simp [Set.indicator, hx, hy]
  have hgint : Integrable
      (Function.uncurry fun ω x ↦
        ∫ y, uncoveredIndicator a M (ω, x) *
          uncoveredIndicator a M (ω, y) ∂ν)
      (sampleMeasure.prod ν) := by
    have h := hfint.integral_prod_left
    have hfun :
        (fun q : Sample × ℝ ↦ ∫ y, f (q, y) ∂ν) =
          Function.uncurry (fun ω x ↦
            ∫ y, uncoveredIndicator a M (ω, x) *
              uncoveredIndicator a M (ω, y) ∂ν) := by
      funext q
      rcases q with ⟨ω, x⟩
      rfl
    rw [← hfun]
    exact h
  have hslice (x : ℝ) : Integrable
      (Function.uncurry fun ω y ↦ uncoveredIndicator a M (ω, x) *
        uncoveredIndicator a M (ω, y)) (sampleMeasure.prod ν) := by
    let g : Sample × ℝ → ℝ := fun p ↦
      uncoveredIndicator a M (p.1, x) * uncoveredIndicator a M p
    have hgmeas : Measurable g := by
      exact ((measurable_uncoveredIndicator a M).comp
          (measurable_fst.prodMk measurable_const)).mul
        (measurable_uncoveredIndicator a M)
    have hgint : Integrable g (sampleMeasure.prod ν) := by
      apply (integrable_const (μ := sampleMeasure.prod ν) (1 : ℝ)).mono'
        hgmeas.aestronglyMeasurable
      filter_upwards [] with p
      simp only [g, uncoveredIndicator]
      by_cases hx : (p.1, x) ∈ finiteUncoveredPairs a M <;>
        by_cases hy : p ∈ finiteUncoveredPairs a M <;>
        simp [Set.indicator, hx, hy]
    have hfun :
        (Function.uncurry fun ω y ↦ uncoveredIndicator a M (ω, x) *
          uncoveredIndicator a M (ω, y)) = g := by
      funext p
      rcases p with ⟨ω, y⟩
      rfl
    rw [hfun]
    exact hgint
  change (∫ ω, localUncoveredLength a M ε ω ^ 2 ∂sampleMeasure) =
    ∫ x, ∫ y, ∏ n ∈ Finset.range M,
      (1 - 2 * a n + max (a n - |x - y|) 0) ∂ν ∂ν
  calc
    (∫ ω, localUncoveredLength a M ε ω ^ 2 ∂sampleMeasure) =
        ∫ ω, ∫ x, ∫ y, uncoveredIndicator a M (ω, x) *
          uncoveredIndicator a M (ω, y) ∂ν ∂ν ∂sampleMeasure := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact localUncoveredLength_sq a M ε ω
    _ = ∫ x, ∫ ω, ∫ y, uncoveredIndicator a M (ω, x) *
          uncoveredIndicator a M (ω, y) ∂ν ∂sampleMeasure ∂ν := by
      exact integral_integral_swap hgint
    _ = ∫ x, ∫ y, ∫ ω, uncoveredIndicator a M (ω, x) *
          uncoveredIndicator a M (ω, y) ∂sampleMeasure ∂ν ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact integral_integral_swap (hslice x)
    _ = ∫ x, ∫ y, ∏ n ∈ Finset.range M,
          (1 - 2 * a n + max (a n - |x - y|) 0) ∂ν ∂ν := by
      have hmem : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) ε := by
        exact ae_restrict_mem measurableSet_Icc
      apply integral_congr_ae
      filter_upwards [hmem] with x hx
      apply integral_congr_ae
      filter_upwards [hmem] with y hy
      apply integral_uncoveredIndicator_mul_sample M x y ha₀ ha
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma integral_Icc_integral_Icc_abs_sub_le
    (F : ℝ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hFcont : Continuous F)
    (hFnonneg : ∀ t, 0 ≤ F t) :
    (∫ x in Icc (0 : ℝ) ε, ∫ y in Icc (0 : ℝ) ε, F |x - y|) ≤
      2 * ε * ∫ t in Icc (0 : ℝ) ε, F t := by
  let P : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..s, F t
  let J : ℝ := P ε
  let q : ℝ → ℝ := fun x ↦ P x + P (ε - x)
  have hPcont : Continuous P := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hFcont.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hqcont : Continuous q := by
    exact hPcont.add (hPcont.comp (continuous_const.sub continuous_id))
  have hleft (x : ℝ) (hx : 0 ≤ x) :
      (∫ y in (0 : ℝ)..x, F |x - y|) = P x := by
    calc
      (∫ y in (0 : ℝ)..x, F |x - y|) =
          ∫ y in (0 : ℝ)..x, F (x - y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hx] at hy
        change F |x - y| = F (x - y)
        rw [abs_of_nonneg]
        linarith [hy.1, hy.2]
      _ = ∫ t in x - x..x - 0, F t :=
        intervalIntegral.integral_comp_sub_left F x
      _ = P x := by simp [P]
  have hright (x : ℝ) (hx : x ≤ ε) :
      (∫ y in x..ε, F |x - y|) = P (ε - x) := by
    calc
      (∫ y in x..ε, F |x - y|) =
          ∫ y in x..ε, F (y - x) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hx] at hy
        change F |x - y| = F (y - x)
        rw [abs_sub_comm, abs_of_nonneg]
        linarith [hy.1, hy.2]
      _ = ∫ t in x - x..ε - x, F t :=
        intervalIntegral.integral_comp_sub_right F x
      _ = P (ε - x) := by simp [P]
  have hinner (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ε) :
      (∫ y in (0 : ℝ)..ε, F |x - y|) = q x := by
    have hcont : Continuous (fun y ↦ F |x - y|) :=
      hFcont.comp ((continuous_const.sub continuous_id).abs)
    calc
      (∫ y in (0 : ℝ)..ε, F |x - y|) =
          (∫ y in (0 : ℝ)..x, F |x - y|) +
            ∫ y in x..ε, F |x - y| := by
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable 0 x) (hcont.intervalIntegrable x ε)).symm
      _ = q x := by rw [hleft x hx.1, hright x hx.2]
  have hqle (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ε) : q x ≤ 2 * J := by
    have hFint : IntervalIntegrable F volume 0 ε := hFcont.intervalIntegrable 0 ε
    have hFae : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) ε), 0 ≤ F t :=
      ae_of_all _ fun t ↦ hFnonneg t
    have hxle : P x ≤ J := by
      exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2 hFae hFint
    have hexle : P (ε - x) ≤ J := by
      apply intervalIntegral.integral_mono_interval le_rfl
        (by linarith [hx.2]) (by linarith [hx.1]) hFae hFint
    dsimp only [q]
    linarith
  have hinterval :
      (∫ x in (0 : ℝ)..ε, ∫ y in (0 : ℝ)..ε, F |x - y|) ≤
        2 * ε * ∫ t in (0 : ℝ)..ε, F t := by
    calc
      (∫ x in (0 : ℝ)..ε, ∫ y in (0 : ℝ)..ε, F |x - y|) =
          ∫ x in (0 : ℝ)..ε, q x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hε] at hx
        exact hinner x hx
      _ ≤ ∫ _x in (0 : ℝ)..ε, (2 * J) := by
        exact intervalIntegral.integral_mono_on hε
          (hqcont.intervalIntegrable 0 ε) (continuous_const.intervalIntegrable 0 ε) hqle
      _ = 2 * ε * ∫ t in (0 : ℝ)..ε, F t := by
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        dsimp only [J, P]
        ring
  have hset (g : ℝ → ℝ) :
      (∫ t in Icc (0 : ℝ) ε, g t) = ∫ t in (0 : ℝ)..ε, g t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε]
  calc
    (∫ x in Icc (0 : ℝ) ε, ∫ y in Icc (0 : ℝ) ε, F |x - y|) =
        ∫ x in Icc (0 : ℝ) ε, ∫ y in (0 : ℝ)..ε, F |x - y| := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hset (fun y ↦ F |x - y|)
    _ = ∫ x in (0 : ℝ)..ε, ∫ y in (0 : ℝ)..ε, F |x - y| :=
      hset (fun x ↦ ∫ y in (0 : ℝ)..ε, F |x - y|)
    _ ≤ 2 * ε * ∫ t in (0 : ℝ)..ε, F t := hinterval
    _ = 2 * ε * ∫ t in Icc (0 : ℝ) ε, F t := by rw [hset F]

/-- Finite two-point avoidance kernel for the first `M` arcs. -/
def finiteMissKernel (a : ℕ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∏ n ∈ Finset.range M, (1 - 2 * a n + max (a n - t) 0)

/-- Kernel normalized by the square of the one-point avoidance probability. -/
def finiteNormalizedKernel (a : ℕ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∏ n ∈ Finset.range M,
    (1 - 2 * a n + max (a n - t) 0) / (1 - a n) ^ 2

/-- Finite exponent in the permutation-invariant overlap kernel. -/
def finiteOverlapSum (a : ℕ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, max (a n - t) 0

def finiteExponentialKernel (a : ℕ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  Real.exp (finiteOverlapSum a M t)

/-- The finite energy integral which increases to Shepp's invariant kernel
integral.  Keeping the approximation finite avoids assigning a real value to
the (possibly infinite) exponent at `t = 0`. -/
def finiteEnergy (a : ℕ → ℝ) (ε : ℝ) (M : ℕ) : ℝ :=
  ∫ t in Icc (0 : ℝ) ε, finiteExponentialKernel a M t

/-- Divergence of the permutation-invariant overlap energy on `[0, ε]`. -/
def EnergyCondition (a : ℕ → ℝ) (ε : ℝ) : Prop :=
  Tendsto (finiteEnergy a ε) atTop atTop

lemma continuous_finiteMissKernel (a : ℕ → ℝ) (M : ℕ) :
    Continuous (finiteMissKernel a M) := by
  unfold finiteMissKernel
  fun_prop

lemma finiteMissKernel_nonneg {a : ℕ → ℝ} (M : ℕ)
    (ha : ∀ n, a n ≤ 1 / 4) (t : ℝ) :
    0 ≤ finiteMissKernel a M t := by
  unfold finiteMissKernel
  apply Finset.prod_nonneg
  intro n hn
  have hmax : 0 ≤ max (a n - t) 0 := le_max_right _ _
  nlinarith [ha n]

lemma finiteMissKernel_eq_mul_finiteNormalizedKernel
    {a : ℕ → ℝ} (M : ℕ) (ha : ∀ n, a n ≤ 1 / 4) (t : ℝ) :
    finiteMissKernel a M t =
      (∏ n ∈ Finset.range M, (1 - a n)) ^ 2 * finiteNormalizedKernel a M t := by
  unfold finiteMissKernel finiteNormalizedKernel
  calc
    (∏ n ∈ Finset.range M, (1 - 2 * a n + max (a n - t) 0)) =
        ∏ n ∈ Finset.range M, ((1 - a n) ^ 2 *
          ((1 - 2 * a n + max (a n - t) 0) / (1 - a n) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro n hn
      have hne : 1 - a n ≠ 0 := ne_of_gt (by linarith [ha n])
      field_simp [hne]
    _ = (∏ n ∈ Finset.range M, (1 - a n) ^ 2) *
        ∏ n ∈ Finset.range M,
          ((1 - 2 * a n + max (a n - t) 0) / (1 - a n) ^ 2) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ n ∈ Finset.range M, (1 - a n)) ^ 2 *
        ∏ n ∈ Finset.range M,
          ((1 - 2 * a n + max (a n - t) 0) / (1 - a n) ^ 2) := by
      rw [Finset.prod_pow]

lemma normalizedFactor_nonneg {a t : ℝ} (ha₀ : 0 ≤ a) (ha : a ≤ 1 / 4) :
    0 ≤ (1 - 2 * a + max (a - t) 0) / (1 - a) ^ 2 := by
  have hnum : 0 ≤ 1 - 2 * a + max (a - t) 0 := by
    have := le_max_right (a - t) 0
    linarith
  exact div_nonneg hnum (sq_nonneg _)

lemma normalizedFactor_le_exp {a t : ℝ} (ha₀ : 0 ≤ a) (ha : a ≤ 1 / 4)
    (ht : 0 ≤ t) :
    (1 - 2 * a + max (a - t) 0) / (1 - a) ^ 2 ≤
      Real.exp (max (a - t) 0 + 4 * a ^ 2) := by
  let ξ : ℝ := max (a - t) 0
  have hξ₀ : 0 ≤ ξ := le_max_right _ _
  have hξa : ξ ≤ a := by
    dsimp only [ξ]
    exact max_le (by linarith) ha₀
  have hd : 0 < (1 - a) ^ 2 := sq_pos_of_pos (by linarith)
  have hu : (ξ - a ^ 2) / (1 - a) ^ 2 ≤ ξ + 4 * a ^ 2 := by
    rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg (a - ξ), mul_nonneg ha₀ hξ₀]
  calc
    (1 - 2 * a + max (a - t) 0) / (1 - a) ^ 2 =
        1 + (ξ - a ^ 2) / (1 - a) ^ 2 := by
      dsimp only [ξ]
      field_simp [ne_of_gt (by linarith : 0 < 1 - a)]
      ring
    _ ≤ 1 + (ξ + 4 * a ^ 2) := by linarith
    _ ≤ Real.exp (ξ + 4 * a ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (ξ + 4 * a ^ 2)

lemma sub_two_sq_le_log_one_add {u : ℝ} (hu : -(1 / 3 : ℝ) ≤ u) :
    u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
  have hpos : 0 < 1 + u := by linarith
  have hfrac : u - 2 * u ^ 2 ≤ u / (1 + u) := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 + 2 * u)]
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hinv : (1 + u)⁻¹ - 1 = -u / (1 + u) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [hinv] at hlog
  have hneg : -u / (1 + u) = -(u / (1 + u)) := by ring
  rw [hneg] at hlog
  have hfraclog : u / (1 + u) ≤ Real.log (1 + u) := by linarith
  exact hfrac.trans hfraclog

lemma exp_sub_sq_le_normalizedFactor {a t : ℝ} (ha₀ : 0 ≤ a) (ha : a ≤ 1 / 4)
    (ht : 0 ≤ t) :
    Real.exp (max (a - t) 0 - 10 * a ^ 2) ≤
      (1 - 2 * a + max (a - t) 0) / (1 - a) ^ 2 := by
  let ξ : ℝ := max (a - t) 0
  let d : ℝ := (1 - a) ^ 2
  let u : ℝ := (ξ - a ^ 2) / d
  have hξ₀ : 0 ≤ ξ := le_max_right _ _
  have hξa : ξ ≤ a := by
    dsimp only [ξ]
    exact max_le (by linarith) ha₀
  have hd : 0 < d := by
    dsimp only [d]
    exact sq_pos_of_pos (by linarith)
  have hulower : -(1 / 3 : ℝ) ≤ u := by
    dsimp only [u]
    rw [le_div_iff₀ hd]
    dsimp only [d]
    nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (ξ - a)]
  have huupper : u ≤ 1 / 3 := by
    dsimp only [u]
    rw [div_le_iff₀ hd]
    dsimp only [d]
    nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (ξ - a)]
  have hu_lower_linear : -2 * a ≤ u := by
    dsimp only [u]
    rw [le_div_iff₀ hd]
    dsimp only [d]
    nlinarith [sq_nonneg a, sq_nonneg (a - 1 / 4)]
  have hu_upper_linear : u ≤ 2 * a := by
    dsimp only [u]
    rw [div_le_iff₀ hd]
    dsimp only [d]
    nlinarith [sq_nonneg a, sq_nonneg (a - 1 / 4), sq_nonneg (ξ - a)]
  have hu_sq : u ^ 2 ≤ 4 * a ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * a - u)
      (by linarith : 0 ≤ 2 * a + u)]
  have hu_xi : ξ - 2 * a ^ 2 ≤ u := by
    dsimp only [u]
    rw [le_div_iff₀ hd]
    dsimp only [d]
    have hdle : (1 - a) ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    have hdhalf : (1 / 2 : ℝ) ≤ (1 - a) ^ 2 := by
      nlinarith [sq_nonneg (a - 1 / 4)]
    have hξd : ξ * (1 - a) ^ 2 ≤ ξ := by
      simpa using mul_le_mul_of_nonneg_left hdle hξ₀
    have ha2d : a ^ 2 ≤ 2 * a ^ 2 * (1 - a) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg a)
        (by linarith [hdhalf] : 0 ≤ 2 * (1 - a) ^ 2 - 1)]
    nlinarith
  have hlog : ξ - 10 * a ^ 2 ≤ Real.log (1 + u) := by
    calc
      ξ - 10 * a ^ 2 ≤ u - 2 * u ^ 2 := by nlinarith
      _ ≤ Real.log (1 + u) := sub_two_sq_le_log_one_add hulower
  have hupos : 0 < 1 + u := by linarith
  calc
    Real.exp (max (a - t) 0 - 10 * a ^ 2) = Real.exp (ξ - 10 * a ^ 2) := rfl
    _ ≤ Real.exp (Real.log (1 + u)) := Real.exp_le_exp.mpr hlog
    _ = 1 + u := Real.exp_log hupos
    _ = (1 - 2 * a + max (a - t) 0) / (1 - a) ^ 2 := by
      dsimp only [u, d, ξ]
      field_simp [ne_of_gt (by linarith : 0 < 1 - a)]
      ring

lemma finiteNormalizedKernel_le_exponential
    {a : ℕ → ℝ} (M : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    finiteNormalizedKernel a M t ≤
      Real.exp (4 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
        finiteExponentialKernel a M t := by
  unfold finiteNormalizedKernel finiteExponentialKernel finiteOverlapSum
  calc
    (∏ n ∈ Finset.range M,
        (1 - 2 * a n + max (a n - t) 0) / (1 - a n) ^ 2) ≤
        ∏ n ∈ Finset.range M, Real.exp (max (a n - t) 0 + 4 * (a n) ^ 2) := by
      apply Finset.prod_le_prod
      · intro n hn
        exact normalizedFactor_nonneg (ha₀ n) (ha n)
      · intro n hn
        exact normalizedFactor_le_exp (ha₀ n) (ha n) ht
    _ = Real.exp (∑ n ∈ Finset.range M,
        (max (a n - t) 0 + 4 * (a n) ^ 2)) := by
      rw [← Real.exp_sum]
    _ = Real.exp (4 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
        Real.exp (∑ n ∈ Finset.range M, max (a n - t) 0) := by
      rw [← Real.exp_add]
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      ring

lemma exponential_le_finiteNormalizedKernel
    {a : ℕ → ℝ} (M : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    Real.exp (-10 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
        finiteExponentialKernel a M t ≤ finiteNormalizedKernel a M t := by
  unfold finiteNormalizedKernel finiteExponentialKernel finiteOverlapSum
  calc
    Real.exp (-10 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
        Real.exp (∑ n ∈ Finset.range M, max (a n - t) 0) =
        Real.exp (∑ n ∈ Finset.range M,
          (max (a n - t) 0 - 10 * (a n) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = ∏ n ∈ Finset.range M,
        Real.exp (max (a n - t) 0 - 10 * (a n) ^ 2) := by
      rw [Real.exp_sum]
    _ ≤ ∏ n ∈ Finset.range M,
        (1 - 2 * a n + max (a n - t) 0) / (1 - a n) ^ 2 := by
      apply Finset.prod_le_prod
      · intro n hn
        exact (Real.exp_pos _).le
      · intro n hn
        exact exp_sub_sq_le_normalizedFactor (ha₀ n) (ha n) ht

lemma continuous_finiteNormalizedKernel (a : ℕ → ℝ) (M : ℕ) :
    Continuous (finiteNormalizedKernel a M) := by
  unfold finiteNormalizedKernel
  fun_prop

lemma continuous_finiteExponentialKernel (a : ℕ → ℝ) (M : ℕ) :
    Continuous (finiteExponentialKernel a M) := by
  unfold finiteExponentialKernel finiteOverlapSum
  fun_prop

lemma finiteExponentialKernel_pos (a : ℕ → ℝ) (M : ℕ) (t : ℝ) :
    0 < finiteExponentialKernel a M t := by
  exact Real.exp_pos _

lemma finiteOverlapSum_mono_nat {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    {M L : ℕ} (hML : M ≤ L) (t : ℝ) :
    finiteOverlapSum a M t ≤ finiteOverlapSum a L t := by
  unfold finiteOverlapSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hML)
  intro n hn hnM
  exact le_max_right _ _

lemma finiteExponentialKernel_mono_nat {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) {M L : ℕ} (hML : M ≤ L) (t : ℝ) :
    finiteExponentialKernel a M t ≤ finiteExponentialKernel a L t := by
  exact Real.exp_le_exp.mpr (finiteOverlapSum_mono_nat ha₀ hML t)

lemma finiteEnergy_mono_nat {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (ε : ℝ) : Monotone (finiteEnergy a ε) := by
  intro M L hML
  unfold finiteEnergy
  apply setIntegral_mono_on
    (continuous_finiteExponentialKernel a M).integrableOn_Icc
    (continuous_finiteExponentialKernel a L).integrableOn_Icc
    measurableSet_Icc
  intro t ht
  exact finiteExponentialKernel_mono_nat ha₀ hML t

lemma finiteEnergy_nonneg (a : ℕ → ℝ) (M : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ finiteEnergy a ε M := by
  unfold finiteEnergy
  exact setIntegral_nonneg measurableSet_Icc (fun t _ ↦ (finiteExponentialKernel_pos a M t).le)

lemma finiteEnergy_zero (a : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEnergy a ε 0 = ε := by
  unfold finiteEnergy finiteExponentialKernel finiteOverlapSum
  simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero]
  rw [integral_const]
  simp [measureReal_def, Real.volume_Icc, hε]

lemma integral_Icc_max_sub_zero {c ε : ℝ} (hc₀ : 0 ≤ c) (hcε : c ≤ ε) :
    (∫ t in Icc (0 : ℝ) ε, max (c - t) 0) = c ^ 2 / 2 := by
  have hε₀ : 0 ≤ ε := hc₀.trans hcε
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε₀]
  calc
    (∫ t in (0 : ℝ)..ε, max (c - t) 0) =
        (∫ t in (0 : ℝ)..c, max (c - t) 0) +
          ∫ t in c..ε, max (c - t) 0 := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        ((by fun_prop : Continuous (fun t : ℝ ↦ max (c - t) 0)).intervalIntegrable 0 c)
        ((by fun_prop : Continuous (fun t : ℝ ↦ max (c - t) 0)).intervalIntegrable c ε)
    _ = (∫ t in (0 : ℝ)..c, c - t) + ∫ _t in c..ε, (0 : ℝ) := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hc₀] at ht
        exact max_eq_left (by linarith [ht.2])
      · apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hcε] at ht
        exact max_eq_right (by linarith [ht.1])
    _ = c ^ 2 / 2 := by
      have hlinear : (∫ t in (0 : ℝ)..c, c - t) = c ^ 2 / 2 := by
        calc
          (∫ t in (0 : ℝ)..c, c - t) =
              (∫ _t in (0 : ℝ)..c, c) - ∫ t in (0 : ℝ)..c, t := by
            exact intervalIntegral.integral_sub
              (continuous_const.intervalIntegrable 0 c)
              (continuous_id.intervalIntegrable 0 c)
          _ = c ^ 2 / 2 := by
            rw [intervalIntegral.integral_const, integral_id]
            simp only [sub_zero, smul_eq_mul, mul_one, zero_pow, OfNat.zero_ne_ofNat]
            ring
      rw [hlinear]
      simp

lemma finite_sum_sq_div_two_le_energy {a : ℕ → ℝ} {ε : ℝ}
    (hε₀ : 0 ≤ ε) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    (M : ℕ) :
    (∑ n ∈ Finset.range M, (a n) ^ 2 / 2) ≤ finiteEnergy a ε M := by
  have hoverlap_cont : Continuous (finiteOverlapSum a M) := by
    unfold finiteOverlapSum
    fun_prop
  have hpoint (t : ℝ) :
      finiteOverlapSum a M t ≤ finiteExponentialKernel a M t := by
    unfold finiteExponentialKernel
    linarith [Real.add_one_le_exp (finiteOverlapSum a M t)]
  have hint_overlap : IntegrableOn (finiteOverlapSum a M) (Icc (0 : ℝ) ε) :=
    hoverlap_cont.integrableOn_Icc
  have hint_exp : IntegrableOn (finiteExponentialKernel a M) (Icc (0 : ℝ) ε) :=
    (continuous_finiteExponentialKernel a M).integrableOn_Icc
  have hmono :
      (∫ t in Icc (0 : ℝ) ε, finiteOverlapSum a M t) ≤
        finiteEnergy a ε M := by
    unfold finiteEnergy
    exact setIntegral_mono_on hint_overlap hint_exp measurableSet_Icc
      (fun t ht ↦ hpoint t)
  calc
    (∑ n ∈ Finset.range M, (a n) ^ 2 / 2) =
        ∫ t in Icc (0 : ℝ) ε, finiteOverlapSum a M t := by
      unfold finiteOverlapSum
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro n hn
        exact (integral_Icc_max_sub_zero (ha₀ n) (haε n)).symm
      · intro n hn
        exact (by fun_prop : Continuous (fun t : ℝ ↦ max (a n - t) 0)).integrableOn_Icc
    _ ≤ finiteEnergy a ε M := hmono

lemma summable_sq_of_not_energy {a : ℕ → ℝ} {ε : ℝ}
    (hε₀ : 0 < ε) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    (henergy : ¬ EnergyCondition a ε) : Summable (fun n ↦ (a n) ^ 2) := by
  have hmonoEnergy : Monotone (finiteEnergy a ε) := finiteEnergy_mono_nat ha₀ ε
  have hbounded : ∃ B : ℝ, ∀ M, finiteEnergy a ε M < B := by
    rw [EnergyCondition, hmonoEnergy.tendsto_atTop_atTop_iff] at henergy
    push_neg at henergy
    exact henergy
  obtain ⟨B, hB⟩ := hbounded
  apply summable_of_sum_le (fun n ↦ sq_nonneg (a n))
  intro s
  obtain ⟨M, hsM⟩ := s.exists_nat_subset_range
  calc
    ∑ n ∈ s, (a n) ^ 2 ≤ ∑ n ∈ Finset.range M, (a n) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsM
        (fun n hn hn' ↦ sq_nonneg (a n))
    _ = 2 * ∑ n ∈ Finset.range M, (a n) ^ 2 / 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 2 * finiteEnergy a ε M := by
      exact mul_le_mul_of_nonneg_left
        (finite_sum_sq_div_two_le_energy hε₀.le ha₀ haε M) (by norm_num)
    _ ≤ 2 * B := by
      exact mul_le_mul_of_nonneg_left (hB M).le (by norm_num)

lemma integral_finiteNormalizedKernel_le_exponential
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    (∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t) ≤
      Real.exp (4 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
        ∫ t in Icc (0 : ℝ) ε, finiteExponentialKernel a M t := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on
    (continuous_finiteNormalizedKernel a M).integrableOn_Icc
    ((continuous_const.mul
      (continuous_finiteExponentialKernel a M)).integrableOn_Icc)
    measurableSet_Icc
  intro t ht
  exact finiteNormalizedKernel_le_exponential M t ht.1 ha₀ ha

lemma integral_exponential_le_finiteNormalizedKernel
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    Real.exp (-10 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
        ∫ t in Icc (0 : ℝ) ε, finiteExponentialKernel a M t ≤
      ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on
    ((continuous_const.mul
      (continuous_finiteExponentialKernel a M)).integrableOn_Icc)
    (continuous_finiteNormalizedKernel a M).integrableOn_Icc
    measurableSet_Icc
  intro t ht
  exact exponential_le_finiteNormalizedKernel M t ht.1 ha₀ ha

lemma integral_finiteMissKernel_eq_mul_normalized
    {a : ℕ → ℝ} (M : ℕ) (ha : ∀ n, a n ≤ 1 / 4) (ε : ℝ) :
    (∫ t in Icc (0 : ℝ) ε, finiteMissKernel a M t) =
      (∏ n ∈ Finset.range M, (1 - a n)) ^ 2 *
        ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t := by
  simp_rw [finiteMissKernel_eq_mul_finiteNormalizedKernel M ha]
  exact integral_const_mul _ _

lemma integral_localUncoveredLength_sq_le
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    (∫ ω, localUncoveredLength a M ε ω ^ 2 ∂sampleMeasure) ≤
      2 * ε * ∫ t in Icc (0 : ℝ) ε, finiteMissKernel a M t := by
  rw [integral_localUncoveredLength_sq M ε hε₀ hε ha₀ ha]
  change (∫ x in Icc (0 : ℝ) ε, ∫ y in Icc (0 : ℝ) ε,
      finiteMissKernel a M |x - y|) ≤ _
  exact integral_Icc_integral_Icc_abs_sub_le (finiteMissKernel a M) ε hε₀
    (continuous_finiteMissKernel a M) (finiteMissKernel_nonneg M ha)

/-- Cauchy--Schwarz in the form used by the second-moment method. -/
lemma integral_localUncoveredLength_sq_le_measure_mul_secondMoment
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (∫ ω, localUncoveredLength a M ε ω ∂sampleMeasure) ^ 2 ≤
      sampleMeasure.real (localUncoveredPositive a M ε) *
        ∫ ω, localUncoveredLength a M ε ω ^ 2 ∂sampleMeasure := by
  let X : Sample → ℝ := localUncoveredLength a M ε
  let E : Set Sample := localUncoveredPositive a M ε
  let I : Sample → ℝ := E.indicator (fun _ ↦ (1 : ℝ))
  have hE : MeasurableSet E := measurableSet_localUncoveredPositive a M ε
  have hXnonneg : ∀ᵐ ω ∂sampleMeasure, 0 ≤ X ω :=
    ae_of_all _ fun ω ↦ localUncoveredLength_nonneg a M ε ω
  have hInonneg : ∀ᵐ ω ∂sampleMeasure, 0 ≤ I ω := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ E <;> simp [I, Set.indicator, hω]
  have hXmem : MemLp X (ENNReal.ofReal (2 : ℝ)) sampleMeasure := by
    apply MemLp.of_bound
      (stronglyMeasurable_localUncoveredLength a M ε).aestronglyMeasurable ε
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (localUncoveredLength_nonneg a M ε ω)]
    exact localUncoveredLength_le a M ε hε ω
  have hImem : MemLp I (ENNReal.ofReal (2 : ℝ)) sampleMeasure := by
    apply MemLp.of_bound (measurable_const.indicator hE).aestronglyMeasurable 1
    filter_upwards [] with ω
    by_cases hω : ω ∈ E <;> simp [I, Set.indicator, hω]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hXnonneg hInonneg hXmem hImem
  have hXI : (fun ω ↦ X ω * I ω) = X := by
    funext ω
    by_cases hpos : 0 < X ω
    · have hmem : ω ∈ E := hpos
      simp [I, Set.indicator_of_mem hmem]
    · have hzero : X ω = 0 := by
        apply le_antisymm (le_of_not_gt hpos)
        exact localUncoveredLength_nonneg a M ε ω
      simp [hzero]
  rw [hXI] at hholder
  simp_rw [Real.rpow_two] at hholder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hI2 : (∫ ω, I ω ^ 2 ∂sampleMeasure) = sampleMeasure.real E := by
    have hfun : (fun ω ↦ I ω ^ 2) = I := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [I, Set.indicator, hω]
    rw [hfun]
    change (∫ ω, E.indicator (fun _ ↦ (1 : ℝ)) ω ∂sampleMeasure) = _
    rw [integral_indicator_const]
    · simp only [smul_eq_mul, mul_one]
    · exact hE
  rw [hI2] at hholder
  have hmean : 0 ≤ ∫ ω, X ω ∂sampleMeasure := integral_nonneg_of_ae hXnonneg
  have hsecond : 0 ≤ ∫ ω, X ω ^ 2 ∂sampleMeasure :=
    integral_nonneg_of_ae (ae_of_all _ fun ω ↦ sq_nonneg (X ω))
  have hprob : 0 ≤ sampleMeasure.real E := measureReal_nonneg
  have hrhs : 0 ≤
      √(∫ ω, X ω ^ 2 ∂sampleMeasure) * √(sampleMeasure.real E) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare : (∫ ω, X ω ∂sampleMeasure) ^ 2 ≤
      (√(∫ ω, X ω ^ 2 ∂sampleMeasure) * √(sampleMeasure.real E)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hholder) (add_nonneg hrhs hmean)]
  rw [mul_pow, Real.sq_sqrt hsecond, Real.sq_sqrt hprob] at hsquare
  simpa only [X, E, mul_comm] using hsquare

lemma paleyZygmund_localUncovered
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    (ε * ∏ n ∈ Finset.range M, (1 - a n)) ^ 2 ≤
      sampleMeasure.real (localUncoveredPositive a M ε) *
        (2 * ε * ∫ t in Icc (0 : ℝ) ε, finiteMissKernel a M t) := by
  have hCS := integral_localUncoveredLength_sq_le_measure_mul_secondMoment a M ε hε₀
  rw [integral_localUncoveredLength M ε hε₀ ha₀
    (fun n ↦ (ha n).trans (by norm_num))] at hCS
  calc
    (ε * ∏ n ∈ Finset.range M, (1 - a n)) ^ 2 ≤
        sampleMeasure.real (localUncoveredPositive a M ε) *
          ∫ ω, localUncoveredLength a M ε ω ^ 2 ∂sampleMeasure := hCS
    _ ≤ sampleMeasure.real (localUncoveredPositive a M ε) *
        (2 * ε * ∫ t in Icc (0 : ℝ) ε, finiteMissKernel a M t) := by
      exact mul_le_mul_of_nonneg_left
        (integral_localUncoveredLength_sq_le M ε hε₀ hε ha₀ ha)
        measureReal_nonneg

lemma paleyZygmund_normalized
    {a : ℕ → ℝ} (M : ℕ) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 4)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    ε ≤ 2 * sampleMeasure.real (localUncoveredPositive a M ε) *
      ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t := by
  let P : ℝ := ∏ n ∈ Finset.range M, (1 - a n)
  let I : ℝ := ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t
  have hP : 0 < P := by
    dsimp only [P]
    apply Finset.prod_pos
    intro n hn
    linarith [ha n]
  have hpal := paleyZygmund_localUncovered M ε hε₀.le hε ha₀ ha
  rw [integral_finiteMissKernel_eq_mul_normalized M ha ε] at hpal
  change (ε * P) ^ 2 ≤
    sampleMeasure.real (localUncoveredPositive a M ε) * (2 * ε * (P ^ 2 * I)) at hpal
  have hc : 0 < ε * P ^ 2 := mul_pos hε₀ (sq_pos_of_pos hP)
  change ε ≤ 2 * sampleMeasure.real (localUncoveredPositive a M ε) * I
  apply le_of_mul_le_mul_left ?_ hc
  calc
    ε * P ^ 2 * ε = (ε * P) ^ 2 := by ring
    _ ≤ sampleMeasure.real (localUncoveredPositive a M ε) *
        (2 * ε * (P ^ 2 * I)) := hpal
    _ = ε * P ^ 2 *
        (2 * sampleMeasure.real (localUncoveredPositive a M ε) * I) := by ring

lemma localUncoveredPositive_subset_finiteCoverEvent_compl
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    localUncoveredPositive a M ε ⊆ (finiteCoverEvent a 0 M)ᶜ := by
  intro ω hpos hcover
  have hcover' : FiniteCovers a ω 0 M := hcover
  have hzero : localUncoveredLength a M ε ω = 0 := by
    unfold localUncoveredLength
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    obtain ⟨n, hn, ht⟩ := hcover' (t : Circle)
    have hn' : n ∈ Finset.range M := by simpa using hn
    have hnot : (ω, t) ∉ finiteUncoveredPairs a M := by
      intro hall
      simp only [finiteUncoveredPairs, mem_iInter] at hall
      have hj := hall n hn'
      change a n / 2 ≤ dist (ω n) (t : Circle) at hj
      change dist (t : Circle) (ω n) < a n / 2 at ht
      rw [dist_comm] at ht
      exact (not_lt_of_ge hj) ht
    simp [uncoveredIndicator, Set.indicator, hnot]
  exact (ne_of_gt hpos) hzero

lemma finiteCoverEvent_mono_right (a : ℕ → ℝ) (N : ℕ) :
    Monotone (finiteCoverEvent a N) := by
  intro M L hML ω hω x
  obtain ⟨n, hn, hx⟩ := hω x
  exact ⟨n, Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hn).1,
    (Finset.mem_Ico.1 hn).2.trans_le hML⟩, hx⟩

/-- If the square errors are summable but the overlap energy stays bounded,
the arcs cannot cover the circle with probability one.  This is the
necessity half of the kernel criterion. -/
theorem measure_onceCoverageEvent_ne_one_of_not_energy
    {a : ℕ → ℝ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 4)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hsq : Summable (fun n ↦ (a n) ^ 2)) (henergy : ¬ EnergyCondition a ε) :
    sampleMeasure (onceCoverageEvent a) ≠ 1 := by
  have hmonoEnergy : Monotone (finiteEnergy a ε) := finiteEnergy_mono_nat ha₀ ε
  have hbounded : ∃ B : ℝ, ∀ M, finiteEnergy a ε M < B := by
    rw [EnergyCondition, hmonoEnergy.tendsto_atTop_atTop_iff] at henergy
    push_neg at henergy
    exact henergy
  obtain ⟨B, hB⟩ := hbounded
  have hBpos : 0 < B := by
    have := hB 0
    rw [finiteEnergy_zero a hε₀.le] at this
    exact hε₀.trans this
  let S : ℝ := ∑' n, (a n) ^ 2
  let Q : ℝ := Real.exp (4 * S) * B
  have hSnonneg : 0 ≤ S := tsum_nonneg (fun n ↦ sq_nonneg (a n))
  have hQpos : 0 < Q := mul_pos (Real.exp_pos _) hBpos
  have hnorm (M : ℕ) :
      (∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t) ≤ Q := by
    have hpartial : (∑ n ∈ Finset.range M, (a n) ^ 2) ≤ S := by
      dsimp only [S]
      exact hsq.sum_le_tsum (Finset.range M) (fun n hn ↦ sq_nonneg (a n))
    calc
      (∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t) ≤
          Real.exp (4 * ∑ n ∈ Finset.range M, (a n) ^ 2) *
            finiteEnergy a ε M :=
        integral_finiteNormalizedKernel_le_exponential M ε ha₀ ha
      _ ≤ Real.exp (4 * S) * B := by
        apply mul_le_mul
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpartial (by norm_num))
        · exact (hB M).le
        · exact finiteEnergy_nonneg a M hε₀.le
        · exact (Real.exp_pos _).le
      _ = Q := rfl
  let δ : ℝ := ε / (2 * Q)
  have hδpos : 0 < δ := div_pos hε₀ (mul_pos (by norm_num) hQpos)
  have hlocal (M : ℕ) :
      δ ≤ sampleMeasure.real (localUncoveredPositive a M ε) := by
    have hpal := paleyZygmund_normalized M ε hε₀ hε ha₀ ha
    apply (div_le_iff₀ (mul_pos (by norm_num) hQpos)).2
    calc
      ε ≤ 2 * sampleMeasure.real (localUncoveredPositive a M ε) *
          ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel a M t := hpal
      _ ≤ 2 * sampleMeasure.real (localUncoveredPositive a M ε) * Q := by
        exact mul_le_mul_of_nonneg_left (hnorm M)
          (mul_nonneg (by norm_num) measureReal_nonneg)
      _ = sampleMeasure.real (localUncoveredPositive a M ε) * (2 * Q) := by ring
  have hfinite (M : ℕ) :
      sampleMeasure.real (finiteCoverEvent a 0 M) ≤ 1 - δ := by
    have hcomp : δ ≤ sampleMeasure.real (finiteCoverEvent a 0 M)ᶜ :=
      (hlocal M).trans (measureReal_mono
        (localUncoveredPositive_subset_finiteCoverEvent_compl a M ε))
    rw [measureReal_compl (measurableSet_finiteCoverEvent a 0 M)] at hcomp
    rw [probReal_univ] at hcomp
    linarith
  intro hcover
  have hmonoCover : Monotone (finiteCoverEvent a 0) :=
    finiteCoverEvent_mono_right a 0
  have ht := tendsto_measure_iUnion_atTop (μ := sampleMeasure) hmonoCover
  have hunion : (⋃ M : ℕ, finiteCoverEvent a 0 M) = onceCoverageEvent a := by
    rw [onceCoverageEvent_eq, coversFromEvent_eq_iUnion]
  rw [hunion, hcover] at ht
  have htreal : Tendsto
      (fun M ↦ sampleMeasure.real (finiteCoverEvent a 0 M)) atTop (nhds 1) := by
    change Tendsto
      (ENNReal.toReal ∘ (sampleMeasure ∘ finiteCoverEvent a 0)) atTop (nhds 1)
    exact (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp ht
  have hevent : ∀ᶠ M in atTop,
      1 - δ / 2 < sampleMeasure.real (finiteCoverEvent a 0 M) :=
    (tendsto_order.1 htreal).1 (1 - δ / 2) (by linarith)
  obtain ⟨M, hM⟩ := (eventually_atTop.1 hevent)
  have hlarge := hM M le_rfl
  have hsmall := hfinite M
  linarith

theorem measure_onceCoverageEvent_ne_one_of_not_energy'
    {a : ℕ → ℝ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 4)
    (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    (henergy : ¬ EnergyCondition a ε) :
    sampleMeasure (onceCoverageEvent a) ≠ 1 := by
  have ha : ∀ n, a n ≤ 1 / 4 := fun n ↦ (haε n).trans hε
  exact measure_onceCoverageEvent_ne_one_of_not_energy hε₀ hε ha₀ ha
    (summable_sq_of_not_energy hε₀ ha₀ haε henergy) henergy

lemma hitEvent_iIndep (a : ℕ → ℝ) (x : Circle) :
    iIndepSet (hitEvent a x) sampleMeasure := by
  rw [iIndepSet_iff_meas_biInter (measurableSet_hitEvent a x)]
  intro s
  exact center_iIndep.measure_inter_preimage_eq_mul s
    (sets := fun n ↦ Metric.ball x (a n / 2))
    (fun _ _ ↦ measurableSet_ball)

/-- Under the elementary divergence hypothesis, every fixed point is covered
infinitely often with probability one.  Shepp's theorem is stronger because
its exceptional null set must be independent of the point. -/
theorem measure_fixedPoint_limsup_eq_one (a : ℕ → ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (ha_diverges : ¬ Summable a) (x : Circle) :
    sampleMeasure (limsup (hitEvent a x) atTop) = 1 := by
  apply ProbabilityTheory.measure_limsup_eq_one
    (measurableSet_hitEvent a x) (hitEvent_iIndep a x)
  let b : ℕ → ℝ≥0 := fun n ↦ ⟨a n, ha₀ n⟩
  have hb : (∑' n, (b n : ℝ≥0∞)) = ∞ :=
    ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr (by
      change ¬ Summable a
      exact ha_diverges)
  simp_rw [measure_hitEvent x _ (ha₀ _) (ha₁ _)]
  calc
    (∑' n, ENNReal.ofReal (a n)) = ∑' n, (b n : ℝ≥0∞) := by
      apply tsum_congr
      intro n
      rw [ENNReal.coe_nnreal_eq]
      rfl
    _ = ∞ := hb

/-! ### The discrete Hardy estimate used in Shepp's analytic lemma -/

open Finset

lemma sum_sq_eq_weighted_differences (z : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, z n ^ 2) =
      (∑ n ∈ range N, (n + 1 : ℝ) * (z n ^ 2 - z (n + 1) ^ 2)) +
        (N : ℝ) * z N ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      push_cast
      ring

/-- Finite adjoint Hardy inequality, with the sharp-enough constant four. -/
lemma finite_adjoint_hardy (y z : ℕ → ℝ) (N : ℕ)
    (hy : ∀ n < N, 0 ≤ y n) (hz : ∀ n ≤ N, 0 ≤ z n)
    (hzmono : ∀ n < N, z (n + 1) ≤ z n) (hzN : z N = 0)
    (hrec : ∀ n < N, (n + 1 : ℝ) * (z n - z (n + 1)) = y n) :
    (∑ n ∈ range N, z n ^ 2) ≤ 4 * ∑ n ∈ range N, y n ^ 2 := by
  let Z : ℝ := ∑ n ∈ range N, z n ^ 2
  let Y : ℝ := ∑ n ∈ range N, y n ^ 2
  let C : ℝ := ∑ n ∈ range N, y n * z n
  have hZnonneg : 0 ≤ Z := sum_nonneg fun n hn ↦ sq_nonneg _
  have hYnonneg : 0 ≤ Y := sum_nonneg fun n hn ↦ sq_nonneg _
  have hCnonneg : 0 ≤ C := by
    apply sum_nonneg
    intro n hn
    exact mul_nonneg (hy n (mem_range.1 hn)) (hz n (Nat.le_of_lt (mem_range.1 hn)))
  have hZeq : Z = ∑ n ∈ range N,
      (n + 1 : ℝ) * (z n ^ 2 - z (n + 1) ^ 2) := by
    have h := sum_sq_eq_weighted_differences z N
    rw [hzN, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at h
    exact h
  have hZC : Z ≤ 2 * C := by
    rw [hZeq]
    calc
      (∑ n ∈ range N, (n + 1 : ℝ) * (z n ^ 2 - z (n + 1) ^ 2)) =
          ∑ n ∈ range N, y n * (z n + z (n + 1)) := by
        apply sum_congr rfl
        intro n hn
        rw [← hrec n (mem_range.1 hn)]
        ring
      _ ≤ ∑ n ∈ range N, 2 * (y n * z n) := by
        apply sum_le_sum
        intro n hn
        have hyn := hy n (mem_range.1 hn)
        have hzn := hzmono n (mem_range.1 hn)
        nlinarith
      _ = 2 * C := by
        dsimp only [C]
        rw [Finset.mul_sum]
  have hC : C ^ 2 ≤ Y * Z := by
    dsimp only [C, Y, Z]
    exact sum_mul_sq_le_sq_mul_sq (range N) y z
  by_cases hZzero : Z = 0
  · change Z ≤ 4 * Y
    rw [hZzero]
    positivity
  · have hZpos : 0 < Z := lt_of_le_of_ne hZnonneg (Ne.symm hZzero)
    have hsquare : Z ^ 2 ≤ 4 * C ^ 2 := by nlinarith
    have hZZ : Z * Z ≤ (4 * Y) * Z := by
      calc
        Z * Z = Z ^ 2 := by ring
        _ ≤ 4 * C ^ 2 := hsquare
        _ ≤ 4 * (Y * Z) := mul_le_mul_of_nonneg_left hC (by norm_num)
        _ = (4 * Y) * Z := by ring
    exact le_of_mul_le_mul_right hZZ hZpos

def hardyTail (y : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ k ∈ Ico n N, y k / (k + 1 : ℝ)

lemma hardyTail_zero (y : ℕ → ℝ) (N : ℕ) : hardyTail y N N = 0 := by
  simp [hardyTail]

lemma hardyTail_nonneg {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n) (N n : ℕ) :
    0 ≤ hardyTail y N n := by
  unfold hardyTail
  apply sum_nonneg
  intro k hk
  exact div_nonneg (hy k) (by positivity)

lemma hardyTail_antitone {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n) (N : ℕ) :
    Antitone (hardyTail y N) := by
  intro n m hnm
  unfold hardyTail
  apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left hnm)
  intro k hk hk'
  exact div_nonneg (hy k) (by positivity)

lemma hardyTail_recurrence (y : ℕ → ℝ) (N n : ℕ) (hn : n < N) :
    (n + 1 : ℝ) * (hardyTail y N n - hardyTail y N (n + 1)) = y n := by
  unfold hardyTail
  rw [sum_eq_sum_Ico_succ_bot hn]
  field_simp
  ring

lemma finite_adjoint_hardy_tail {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n) (N : ℕ) :
    (∑ n ∈ range N, hardyTail y N n ^ 2) ≤
      4 * ∑ n ∈ range N, y n ^ 2 := by
  apply finite_adjoint_hardy y (hardyTail y N) N
  · exact fun n hn ↦ hy n
  · exact fun n hn ↦ hardyTail_nonneg hy N n
  · intro n hn
    exact hardyTail_antitone hy N (Nat.le_succ n)
  · exact hardyTail_zero y N
  · exact hardyTail_recurrence y N

lemma summable_one_div_succ_sq :
    Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) := by
  have h : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h' := (summable_nat_add_iff 1).mpr h
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h'

lemma summable_div_succ_of_sq_summable {y : ℕ → ℝ}
    (hy : ∀ n, 0 ≤ y n) (hy2 : Summable (fun n ↦ y n ^ 2)) :
    Summable (fun n ↦ y n / (n + 1 : ℝ)) := by
  have hmajor : Summable
      (fun n : ℕ ↦ (1 / 2 : ℝ) * (y n ^ 2 + 1 / (n + 1 : ℝ) ^ 2)) :=
    (hy2.add summable_one_div_succ_sq).mul_left (1 / 2 : ℝ)
  refine Summable.of_nonneg_of_le (fun n ↦ div_nonneg (hy n) (by positivity))
    (fun n ↦ ?_) hmajor
  have hs := sq_nonneg (y n - 1 / (n + 1 : ℝ))
  have hn : 0 < (n + 1 : ℝ) := by positivity
  rw [div_eq_mul_inv]
  field_simp at hs ⊢
  nlinarith

/-- The infinite adjoint Hardy operator, represented as a convergent total
sum minus the finite prefix preceding `n`.  The definition is total; all
uses below establish the required summability explicitly. -/
def adjointHardy (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑' k, y k / (k + 1 : ℝ)) - ∑ k ∈ range n, y k / (k + 1 : ℝ)

lemma tendsto_hardyTail_adjointHardy {y : ℕ → ℝ}
    (hy : ∀ n, 0 ≤ y n) (hy2 : Summable (fun n ↦ y n ^ 2)) (n : ℕ) :
    Tendsto (fun N ↦ hardyTail y N n) atTop (nhds (adjointHardy y n)) := by
  have hsum := summable_div_succ_of_sq_summable hy hy2
  have ht := hsum.hasSum.tendsto_sum_nat.sub_const
    (∑ k ∈ range n, y k / (k + 1 : ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [hardyTail, sum_Ico_eq_sub _ hN]

/-- Infinite adjoint Hardy inequality obtained from the finite estimate by
monotone exhaustion. -/
lemma infinite_adjoint_hardy {y : ℕ → ℝ}
    (hy : ∀ n, 0 ≤ y n) (hy2 : Summable (fun n ↦ y n ^ 2)) :
    Summable (fun n ↦ adjointHardy y n ^ 2) ∧
      (∑' n, adjointHardy y n ^ 2) ≤ 4 * ∑' n, y n ^ 2 := by
  have hrange (L : ℕ) :
      (∑ n ∈ range L, adjointHardy y n ^ 2) ≤ 4 * ∑' n, y n ^ 2 := by
    have ht : Tendsto
        (fun N ↦ ∑ n ∈ range L, hardyTail y N n ^ 2) atTop
        (nhds (∑ n ∈ range L, adjointHardy y n ^ 2)) := by
      apply tendsto_finsetSum
      intro n hn
      exact (tendsto_hardyTail_adjointHardy hy hy2 n).pow 2
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop L] with N hLN
    calc
      (∑ n ∈ range L, hardyTail y N n ^ 2) ≤
          ∑ n ∈ range N, hardyTail y N n ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg (range_mono hLN)
        intro n hn hn'
        exact sq_nonneg _
      _ ≤ 4 * ∑ n ∈ range N, y n ^ 2 := finite_adjoint_hardy_tail hy N
      _ ≤ 4 * ∑' n, y n ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (hy2.sum_le_tsum (range N) (fun n hn ↦ sq_nonneg _)) (by norm_num)
  have hsum : Summable (fun n ↦ adjointHardy y n ^ 2) :=
    summable_of_sum_range_le (fun n ↦ sq_nonneg _) hrange
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hrange⟩

/-- Shepp's tilted prefix `Sₙ - n aₙ`, in zero-based notation. -/
def tiltedLength (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  prefixLength a (n + 1) - (n + 1 : ℝ) * a n

/-- The summand attached to the tilted prefix. -/
def tiltedTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (tiltedLength a n) / (n + 1 : ℝ) ^ 2

def tiltedRoot (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (tiltedLength a n / 2) / (n + 1 : ℝ)

def sheppRoot (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (prefixLength a (n + 1) / 2) / (n + 1 : ℝ)

lemma tiltedRoot_pos (a : ℕ → ℝ) (n : ℕ) : 0 < tiltedRoot a n := by
  unfold tiltedRoot
  positivity

lemma tiltedRoot_sq (a : ℕ → ℝ) (n : ℕ) :
    tiltedRoot a n ^ 2 = tiltedTerm a n := by
  unfold tiltedRoot tiltedTerm
  rw [div_pow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma tiltedLength_le_prefixLength {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (n : ℕ) :
    tiltedLength a n ≤ prefixLength a (n + 1) := by
  unfold tiltedLength
  exact sub_le_self _ (mul_nonneg (by positivity) (ha₀ n))

lemma tiltedTerm_le_sheppTerm {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (n : ℕ) :
    tiltedTerm a n ≤ sheppTerm a n := by
  unfold tiltedTerm sheppTerm
  simp only [Nat.cast_add, Nat.cast_one]
  exact div_le_div_of_nonneg_right
    (Real.exp_le_exp.mpr (tiltedLength_le_prefixLength ha₀ n)) (sq_nonneg _)

lemma summable_tiltedTerm_of_summable_sheppTerm {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (h : Summable (sheppTerm a)) :
    Summable (tiltedTerm a) := by
  exact Summable.of_nonneg_of_le
    (fun n ↦ (sq_nonneg (tiltedRoot a n)).trans_eq (tiltedRoot_sq a n))
    (tiltedTerm_le_sheppTerm ha₀) h

def prefixAverage (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  prefixLength a n / (n : ℝ)

lemma tendsto_prefixAverage_zero {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (prefixAverage a) atTop (nhds 0) := by
  change Tendsto (fun n ↦ prefixLength a n / (n : ℝ)) atTop (nhds 0)
  have h := ha.cesaro
  simpa [prefixLength, div_eq_mul_inv, mul_comm] using h

lemma tilted_div_eq_prefixAverage_sub (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    tiltedLength a n / ((n : ℝ) * (n + 1 : ℝ)) =
      prefixAverage a n - prefixAverage a (n + 1) := by
  have hnℝ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnsℝ : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold tiltedLength prefixAverage prefixLength
  rw [sum_range_succ]
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma sum_tilted_div_eq_prefixAverage_sub (a : ℕ → ℝ)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (∑ n ∈ Ico m N, tiltedLength a n / ((n : ℝ) * (n + 1 : ℝ))) =
      prefixAverage a m - prefixAverage a N := by
  calc
    (∑ n ∈ Ico m N, tiltedLength a n / ((n : ℝ) * (n + 1 : ℝ))) =
        ∑ n ∈ Ico m N, (prefixAverage a n - prefixAverage a (n + 1)) := by
      apply sum_congr rfl
      intro n hn
      exact tilted_div_eq_prefixAverage_sub a n
        (hm.trans_le (mem_Ico.1 hn).1)
    _ = prefixAverage a m - prefixAverage a N := by
      have htel := sum_Ico_sub (prefixAverage a) hmN
      calc
        (∑ n ∈ Ico m N, (prefixAverage a n - prefixAverage a (n + 1))) =
            -(∑ n ∈ Ico m N,
              (prefixAverage a (n + 1) - prefixAverage a n)) := by
          rw [← Finset.sum_neg_distrib]
          apply sum_congr rfl
          intro n hn
          ring
        _ = prefixAverage a m - prefixAverage a N := by
          rw [htel]
          ring

def sheppWeight (m N r : ℕ) : ℝ :=
  if r = N then (m : ℝ) / N else
    (m : ℝ) / ((r : ℝ) * (r + 1 : ℝ))

def sheppJensenPoint (a : ℕ → ℝ) (N r : ℕ) : ℝ :=
  if r = N then 0 else tiltedLength a r / 2

lemma sum_sheppWeight {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (∑ r ∈ Icc m N, sheppWeight m N r) = 1 := by
  have hN : 0 < N := hm.trans_le hmN
  have hsum :
      (∑ r ∈ Ico m N,
        (1 / (r : ℝ) - 1 / (r + 1 : ℝ))) =
          1 / (m : ℝ) - 1 / (N : ℝ) := by
    have htel := sum_Ico_sub (fun r : ℕ ↦ 1 / (r : ℝ)) hmN
    norm_num only [Nat.cast_add, Nat.cast_one] at htel
    calc
      (∑ r ∈ Ico m N, (1 / (r : ℝ) - 1 / (r + 1 : ℝ))) =
          -(∑ r ∈ Ico m N,
            (1 / (r + 1 : ℝ) - 1 / (r : ℝ))) := by
        rw [← Finset.sum_neg_distrib]
        apply sum_congr rfl
        intro r hr
        ring
      _ = 1 / (m : ℝ) - 1 / (N : ℝ) := by
        rw [htel]
        ring
  rw [← Finset.Ico_insert_right hmN, sum_insert (by simp)]
  simp only [sheppWeight, if_pos]
  have hterms :
      (∑ r ∈ Ico m N,
        (if r = N then (m : ℝ) / N else
          (m : ℝ) / ((r : ℝ) * (r + 1 : ℝ)))) =
        (m : ℝ) * ∑ r ∈ Ico m N,
          (1 / (r : ℝ) - 1 / (r + 1 : ℝ)) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [if_neg (ne_of_lt (mem_Ico.1 hr).2)]
    have hr₀ : (r : ℝ) ≠ 0 := by
      exact_mod_cast (hm.trans_le (mem_Ico.1 hr).1).ne'
    have hrs : (r + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hterms, hsum]
  have hmℝ : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hNℝ : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

lemma sheppWeight_nonneg {m N r : ℕ} (hm : 0 < m)
    (hr : r ∈ Finset.Icc m N) : 0 ≤ sheppWeight m N r := by
  unfold sheppWeight
  split_ifs with h
  · subst r
    exact div_nonneg (by positivity) (by
      exact_mod_cast (hm.trans_le (Finset.mem_Icc.1 hr).1).le)
  · exact div_nonneg (by positivity)
      (mul_nonneg (by positivity) (by positivity))

lemma sum_sheppWeight_smul_point (a : ℕ → ℝ)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (∑ r ∈ Icc m N, sheppWeight m N r • sheppJensenPoint a N r) =
      (m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N) := by
  rw [← Finset.Ico_insert_right hmN, sum_insert (by simp)]
  simp only [sheppWeight, sheppJensenPoint, if_pos, smul_eq_mul, mul_zero, zero_add]
  calc
    (∑ r ∈ Ico m N,
        (if r = N then (m : ℝ) / N else
          (m : ℝ) / ((r : ℝ) * (r + 1 : ℝ))) *
        (if r = N then 0 else tiltedLength a r / 2)) =
        (m : ℝ) / 2 *
          ∑ r ∈ Ico m N,
            tiltedLength a r / ((r : ℝ) * (r + 1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro r hr
      simp only [if_neg (ne_of_lt (mem_Ico.1 hr).2)]
      ring
    _ = (m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N) := by
      rw [sum_tilted_div_eq_prefixAverage_sub a hm hmN]

lemma finite_shepp_jensen (a : ℕ → ℝ)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    Real.exp ((m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N)) ≤
      ∑ r ∈ Icc m N,
        sheppWeight m N r * Real.exp (sheppJensenPoint a N r) := by
  have h := convexOn_exp.map_sum_le
    (t := Icc m N) (w := sheppWeight m N)
    (p := sheppJensenPoint a N)
    (fun r hr ↦ sheppWeight_nonneg hm hr) (sum_sheppWeight hm hmN)
    (fun r hr ↦ mem_univ _)
  rw [sum_sheppWeight_smul_point a hm hmN] at h
  simpa only [smul_eq_mul] using h

lemma finite_shepp_root_le_hardy (a : ℕ → ℝ)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    Real.exp ((m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N)) /
        (m : ℝ) ≤
      1 / (N : ℝ) + 2 * hardyTail (tiltedRoot a) N m := by
  have hmℝ : 0 < (m : ℝ) := by exact_mod_cast hm
  apply (div_le_iff₀ hmℝ).2
  calc
    Real.exp ((m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N)) ≤
        ∑ r ∈ Finset.Icc m N,
          sheppWeight m N r * Real.exp (sheppJensenPoint a N r) :=
      finite_shepp_jensen a hm hmN
    _ ≤ (m : ℝ) * (1 / (N : ℝ) +
          2 * hardyTail (tiltedRoot a) N m) := by
      rw [← Finset.Ico_insert_right hmN, sum_insert (by simp)]
      simp only [sheppWeight, sheppJensenPoint, if_pos, Real.exp_zero,
        mul_one, hardyTail]
      rw [mul_add, mul_one_div, ← mul_assoc, Finset.mul_sum]
      apply add_le_add (le_refl _)
      apply sum_le_sum
      intro r hr
      simp only [if_neg (ne_of_lt (mem_Ico.1 hr).2)]
      have hrnat : 0 < r := hm.trans_le (mem_Ico.1 hr).1
      have hrℝ : 0 < (r : ℝ) := by exact_mod_cast hrnat
      have hrone : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrnat
      have hrsℝ : 0 < (r + 1 : ℝ) := by positivity
      have hfrac :
          1 / ((r : ℝ) * (r + 1 : ℝ)) ≤
            2 / (r + 1 : ℝ) ^ 2 := by
        field_simp
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith
      unfold tiltedRoot
      calc
        (m : ℝ) / ((r : ℝ) * (r + 1 : ℝ)) *
            Real.exp (tiltedLength a r / 2) =
            ((m : ℝ) * Real.exp (tiltedLength a r / 2)) *
              (1 / ((r : ℝ) * (r + 1 : ℝ))) := by ring
        _ ≤ ((m : ℝ) * Real.exp (tiltedLength a r / 2)) *
              (2 / (r + 1 : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac
            (mul_nonneg (Nat.cast_nonneg m) (Real.exp_pos _).le)
        _ = (m : ℝ) * 2 *
              (Real.exp (tiltedLength a r / 2) / (r + 1 : ℝ) /
                (r + 1 : ℝ)) := by
          field_simp
    _ = (1 / (N : ℝ) + 2 * hardyTail (tiltedRoot a) N m) * (m : ℝ) := by
      ring

lemma sheppRoot_le_two_adjointHardy {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0))
    (htilt : Summable (tiltedTerm a)) (n : ℕ) :
    sheppRoot a n ≤ 2 * adjointHardy (tiltedRoot a) (n + 1) := by
  let m := n + 1
  have hm : 0 < m := by simp [m]
  have hy : ∀ r, 0 ≤ tiltedRoot a r := fun r ↦ (tiltedRoot_pos a r).le
  have hy2 : Summable (fun r ↦ tiltedRoot a r ^ 2) :=
    htilt.congr (fun r ↦ (tiltedRoot_sq a r).symm)
  have havg := tendsto_prefixAverage_zero ha
  have hcenter : Tendsto
      (fun N ↦ (m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N))
      atTop (nhds ((m : ℝ) / 2 * (prefixAverage a m - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub havg)
  have hleft : Tendsto
      (fun N ↦ Real.exp ((m : ℝ) / 2 *
        (prefixAverage a m - prefixAverage a N)) / (m : ℝ))
      atTop
      (nhds (Real.exp (prefixLength a m / 2) / (m : ℝ))) := by
    have he := (Real.continuous_exp.tendsto _).comp hcenter
    have hed := he.div_const (m : ℝ)
    have hlimit : (m : ℝ) / 2 * (prefixAverage a m - 0) =
        prefixLength a m / 2 := by
      have hmℝ : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      unfold prefixAverage
      field_simp
      ring
    rw [hlimit] at hed
    simpa only [Function.comp_apply] using hed
  have hinv : Tendsto (fun N : ℕ ↦ 1 / (N : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have htail := tendsto_hardyTail_adjointHardy hy hy2 m
  have hright : Tendsto
      (fun N : ℕ ↦ 1 / (N : ℝ) + 2 * hardyTail (tiltedRoot a) N m)
      atTop (nhds (2 * adjointHardy (tiltedRoot a) m)) := by
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa only [zero_add] using hinv.add (htwo.mul htail)
  have hle : ∀ᶠ N in atTop,
      Real.exp ((m : ℝ) / 2 * (prefixAverage a m - prefixAverage a N)) /
          (m : ℝ) ≤
        1 / (N : ℝ) + 2 * hardyTail (tiltedRoot a) N m := by
    filter_upwards [eventually_ge_atTop m] with N hN
    exact finite_shepp_root_le_hardy a hm hN
  have hlim := le_of_tendsto_of_tendsto hleft hright hle
  simpa only [sheppRoot, m, Nat.cast_add, Nat.cast_one] using hlim

lemma sheppRoot_pos (a : ℕ → ℝ) (n : ℕ) : 0 < sheppRoot a n := by
  unfold sheppRoot
  positivity

lemma sheppRoot_sq (a : ℕ → ℝ) (n : ℕ) :
    sheppRoot a n ^ 2 = sheppTerm a n := by
  unfold sheppRoot sheppTerm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [div_pow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma summable_sheppTerm_of_summable_tiltedTerm {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0)) (htilt : Summable (tiltedTerm a)) :
    Summable (sheppTerm a) := by
  have hy : ∀ r, 0 ≤ tiltedRoot a r := fun r ↦ (tiltedRoot_pos a r).le
  have hy2 : Summable (fun r ↦ tiltedRoot a r ^ 2) :=
    htilt.congr (fun r ↦ (tiltedRoot_sq a r).symm)
  obtain ⟨hHardy, hHardyBound⟩ := infinite_adjoint_hardy hy hy2
  have hrootSq : Summable (fun n ↦ sheppRoot a n ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) (fun n ↦ ?_)
      (hHardy.mul_left 4)
    have hle := sheppRoot_le_two_adjointHardy ha htilt n
    have hpos := (sheppRoot_pos a n).le
    have hz : 0 ≤ adjointHardy (tiltedRoot a) (n + 1) := by linarith
    have hsq : sheppRoot a n ^ 2 ≤
        4 * adjointHardy (tiltedRoot a) (n + 1) ^ 2 := by nlinarith
    calc
      sheppRoot a n ^ 2 ≤
          4 * adjointHardy (tiltedRoot a) (n + 1) ^ 2 := hsq
      _ ≤ 4 * adjointHardy (tiltedRoot a) n ^ 2 := by
        have hmono := hardyTail_antitone hy
        have htailn := tendsto_hardyTail_adjointHardy hy hy2 n
        have htailns := tendsto_hardyTail_adjointHardy hy hy2 (n + 1)
        have horder : adjointHardy (tiltedRoot a) (n + 1) ≤
            adjointHardy (tiltedRoot a) n := by
          apply le_of_tendsto_of_tendsto htailns htailn
          filter_upwards with N
          exact hmono N (Nat.le_succ n)
        have hzn : 0 ≤ adjointHardy (tiltedRoot a) n := hz.trans horder
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hz hzn).2 horder) (by norm_num)
  exact hrootSq.congr (fun n ↦ sheppRoot_sq a n)

lemma summable_sheppTerm_iff_tiltedTerm {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (ha : Tendsto a atTop (nhds 0)) :
    Summable (sheppTerm a) ↔ Summable (tiltedTerm a) := by
  exact ⟨summable_tiltedTerm_of_summable_sheppTerm ha₀,
    summable_sheppTerm_of_summable_tiltedTerm ha⟩

/-! ### Evaluation of the finite overlap energy -/

lemma intervalIntegral_exp_sub_mul (S c u v : ℝ) (hc : c ≠ 0) :
    (∫ t in u..v, Real.exp (S - c * t)) =
      (Real.exp (S - c * u) - Real.exp (S - c * v)) / c := by
  have hderiv (t : ℝ) : HasDerivAt
      (fun x : ℝ ↦ -Real.exp (S - c * x) / c)
      (Real.exp (S - c * t)) t := by
    have hinner : HasDerivAt (fun x : ℝ ↦ S - c * x) (-c) t := by
      exact (hasDerivAt_const_mul c).const_sub S
    have h := hinner.exp.neg.div_const c
    apply h.congr_deriv
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ ↦ Real.exp (S - c * t)) volume u v :=
    (by fun_prop : Continuous (fun t : ℝ ↦ Real.exp (S - c * t))).intervalIntegrable u v
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t) hint]
  field_simp
  ring

lemma finiteOverlapSum_succ_eq_linear_of_le {a : ℕ → ℝ}
    (hanti : Antitone a) (M : ℕ) {t : ℝ} (ht : t ≤ a M) :
    finiteOverlapSum a (M + 1) t =
      prefixLength a (M + 1) - (M + 1 : ℝ) * t := by
  unfold finiteOverlapSum prefixLength
  calc
    (∑ n ∈ range (M + 1), max (a n - t) 0) =
        ∑ n ∈ range (M + 1), (a n - t) := by
      apply sum_congr rfl
      intro n hn
      rw [max_eq_left]
      exact sub_nonneg.mpr
        (ht.trans (hanti (Nat.le_of_lt_succ (mem_range.1 hn))))
    _ = (∑ n ∈ range (M + 1), a n) - (M + 1 : ℝ) * t := by
      rw [Finset.sum_sub_distrib]
      simp only [sum_const, card_range, nsmul_eq_mul]
      norm_num only [Nat.cast_add, Nat.cast_one]

lemma finiteOverlapSum_succ_eq_of_ge {a : ℕ → ℝ}
    (M : ℕ) {t : ℝ} (ht : a M ≤ t) :
    finiteOverlapSum a (M + 1) t = finiteOverlapSum a M t := by
  unfold finiteOverlapSum
  rw [sum_range_succ, max_eq_right (sub_nonpos.mpr ht), add_zero]

lemma finiteOverlapSum_eq_linear_of_le_next {a : ℕ → ℝ}
    (hanti : Antitone a) (M : ℕ) {t : ℝ} (ht : t ≤ a M) :
    finiteOverlapSum a M t = prefixLength a M - (M : ℝ) * t := by
  unfold finiteOverlapSum prefixLength
  calc
    (∑ n ∈ range M, max (a n - t) 0) =
        ∑ n ∈ range M, (a n - t) := by
      apply sum_congr rfl
      intro n hn
      rw [max_eq_left]
      exact sub_nonneg.mpr
        (ht.trans (hanti (Nat.le_of_lt (mem_range.1 hn))))
    _ = (∑ n ∈ range M, a n) - (M : ℝ) * t := by
      rw [Finset.sum_sub_distrib]
      simp only [sum_const, card_range, nsmul_eq_mul]

lemma finiteEnergy_eq_intervalIntegral (a : ℕ → ℝ) (M : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEnergy a ε M = ∫ t in (0 : ℝ)..ε, finiteExponentialKernel a M t := by
  unfold finiteEnergy
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε]

lemma finiteEnergy_succ_recurrence_integral {a : ℕ → ℝ} {ε : ℝ}
    (hanti : Antitone a) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    (M : ℕ) :
    finiteEnergy a ε (M + 1) = finiteEnergy a ε M +
      (∫ t in (0 : ℝ)..a M,
        Real.exp (prefixLength a (M + 1) - (M + 1 : ℝ) * t)) -
      ∫ t in (0 : ℝ)..a M,
        Real.exp (prefixLength a M - (M : ℝ) * t) := by
  have hε₀ : 0 ≤ ε := (ha₀ M).trans (haε M)
  rw [finiteEnergy_eq_intervalIntegral a (M + 1) hε₀,
    finiteEnergy_eq_intervalIntegral a M hε₀]
  have hfint₁ : IntervalIntegrable (finiteExponentialKernel a (M + 1)) volume 0 (a M) :=
    (continuous_finiteExponentialKernel a (M + 1)).intervalIntegrable 0 (a M)
  have hfint₂ : IntervalIntegrable (finiteExponentialKernel a (M + 1)) volume (a M) ε :=
    (continuous_finiteExponentialKernel a (M + 1)).intervalIntegrable (a M) ε
  have hgint₁ : IntervalIntegrable (finiteExponentialKernel a M) volume 0 (a M) :=
    (continuous_finiteExponentialKernel a M).intervalIntegrable 0 (a M)
  have hgint₂ : IntervalIntegrable (finiteExponentialKernel a M) volume (a M) ε :=
    (continuous_finiteExponentialKernel a M).intervalIntegrable (a M) ε
  calc
    (∫ t in (0 : ℝ)..ε, finiteExponentialKernel a (M + 1) t) =
        (∫ t in (0 : ℝ)..a M, finiteExponentialKernel a (M + 1) t) +
          ∫ t in a M..ε, finiteExponentialKernel a (M + 1) t := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals hfint₁ hfint₂
    _ = (∫ t in (0 : ℝ)..a M,
          Real.exp (prefixLength a (M + 1) - (M + 1 : ℝ) * t)) +
          ∫ t in a M..ε, finiteExponentialKernel a M t := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (ha₀ M)] at ht
        unfold finiteExponentialKernel
        rw [finiteOverlapSum_succ_eq_linear_of_le hanti M ht.2]
      · apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (haε M)] at ht
        unfold finiteExponentialKernel
        rw [finiteOverlapSum_succ_eq_of_ge M ht.1]
    _ = ((∫ t in (0 : ℝ)..a M, finiteExponentialKernel a M t) +
          ∫ t in a M..ε, finiteExponentialKernel a M t) +
          (∫ t in (0 : ℝ)..a M,
            Real.exp (prefixLength a (M + 1) - (M + 1 : ℝ) * t)) -
          ∫ t in (0 : ℝ)..a M,
            Real.exp (prefixLength a M - (M : ℝ) * t) := by
      have hold : (∫ t in (0 : ℝ)..a M, finiteExponentialKernel a M t) =
          ∫ t in (0 : ℝ)..a M,
            Real.exp (prefixLength a M - (M : ℝ) * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (ha₀ M)] at ht
        unfold finiteExponentialKernel
        rw [finiteOverlapSum_eq_linear_of_le_next hanti M ht.2]
      rw [hold]
      ring
    _ = (∫ t in (0 : ℝ)..ε, finiteExponentialKernel a M t) +
          (∫ t in (0 : ℝ)..a M,
            Real.exp (prefixLength a (M + 1) - (M + 1 : ℝ) * t)) -
          ∫ t in (0 : ℝ)..a M,
            Real.exp (prefixLength a M - (M : ℝ) * t) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hgint₁ hgint₂]

lemma finiteEnergy_succ_recurrence {a : ℕ → ℝ} {ε : ℝ}
    (hanti : Antitone a) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    {M : ℕ} (hM : 0 < M) :
    finiteEnergy a ε (M + 1) = finiteEnergy a ε M +
      (Real.exp (prefixLength a (M + 1)) - Real.exp (tiltedLength a M)) /
        (M + 1 : ℝ) -
      (Real.exp (prefixLength a M) - Real.exp (tiltedLength a M)) /
        (M : ℝ) := by
  rw [finiteEnergy_succ_recurrence_integral hanti ha₀ haε M,
    intervalIntegral_exp_sub_mul _ (M + 1 : ℝ) _ _ (by positivity),
    intervalIntegral_exp_sub_mul _ (M : ℝ) _ _ (by exact_mod_cast hM.ne')]
  unfold tiltedLength prefixLength
  rw [sum_range_succ]
  norm_num only [Nat.cast_add, Nat.cast_one, mul_zero, sub_zero]
  congr 3
  · ring_nf

lemma finiteEnergy_one {a : ℕ → ℝ} {ε : ℝ}
    (hanti : Antitone a) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε) :
    finiteEnergy a ε 1 = ε - a 0 - 1 + Real.exp (prefixLength a 1) := by
  rw [show (1 : ℕ) = 0 + 1 by omega,
    finiteEnergy_succ_recurrence_integral hanti ha₀ haε 0,
    finiteEnergy_zero a ((ha₀ 0).trans (haε 0))]
  simp only [zero_add, Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero]
  rw [intervalIntegral_exp_sub_mul _ (1 : ℝ) _ _ (by norm_num)]
  unfold prefixLength
  simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul, sub_zero,
    Real.exp_zero, range_one, sum_singleton, Nat.cast_one, one_mul]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_one]
  simp only [sub_self, Real.exp_zero, div_one]
  ring

lemma finiteEnergy_formula {a : ℕ → ℝ} {ε : ℝ}
    (hanti : Antitone a) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    {M : ℕ} (hM : 1 ≤ M) :
    finiteEnergy a ε M =
      ε - a 0 - 1 + Real.exp (prefixLength a M) / (M : ℝ) +
        ∑ k ∈ Ico 1 M,
          Real.exp (tiltedLength a k) / ((k : ℝ) * (k + 1 : ℝ)) := by
  induction M, hM using Nat.le_induction with
  | base =>
      rw [finiteEnergy_one hanti ha₀ haε]
      simp
  | succ M hM ih =>
      rw [finiteEnergy_succ_recurrence hanti ha₀ haε (by omega), ih,
        Finset.sum_Ico_succ_top hM]
      have hMℝ : (M : ℝ) ≠ 0 := by positivity
      have hMsℝ : (M + 1 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

lemma sum_Ico_one_div_succ_sq_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (∑ r ∈ Ico m N, (1 / (r + 1 : ℝ)) ^ 2) ≤ 1 / (m : ℝ) := by
  have hterm (r : ℕ) (hr : 0 < r) :
      (1 / (r + 1 : ℝ)) ^ 2 ≤
        1 / (r : ℝ) - 1 / (r + 1 : ℝ) := by
    have hrℝ : (0 : ℝ) < r := by exact_mod_cast hr
    have hrone : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hrsℝ : (0 : ℝ) < r + 1 := by positivity
    field_simp
    nlinarith
  calc
    (∑ r ∈ Ico m N, (1 / (r + 1 : ℝ)) ^ 2) ≤
        ∑ r ∈ Ico m N,
          (1 / (r : ℝ) - 1 / (r + 1 : ℝ)) := by
      apply sum_le_sum
      intro r hr
      exact hterm r (hm.trans_le (mem_Ico.1 hr).1)
    _ = 1 / (m : ℝ) - 1 / (N : ℝ) := by
      have htel := sum_Ico_sub (fun r : ℕ ↦ 1 / (r : ℝ)) hmN
      norm_num only [Nat.cast_add, Nat.cast_one] at htel
      have hneg := congrArg Neg.neg htel
      rw [← Finset.sum_neg_distrib] at hneg
      simpa only [neg_sub] using hneg
    _ ≤ 1 / (m : ℝ) := sub_le_self _ (by positivity)

lemma adjointHardy_sq_le_tsum_div {y : ℕ → ℝ}
    (hy : ∀ n, 0 ≤ y n) (hy2 : Summable (fun n ↦ y n ^ 2))
    {m : ℕ} (hm : 0 < m) :
    adjointHardy y m ^ 2 ≤ (∑' n, y n ^ 2) / (m : ℝ) := by
  have ht := (tendsto_hardyTail_adjointHardy hy hy2 m).pow 2
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop m] with N hmN
  have hcs : hardyTail y N m ^ 2 ≤
      (∑ r ∈ Ico m N, y r ^ 2) *
        ∑ r ∈ Ico m N, (1 / (r + 1 : ℝ)) ^ 2 := by
    unfold hardyTail
    have h := sum_mul_sq_le_sq_mul_sq (Ico m N) y
      (fun r ↦ 1 / (r + 1 : ℝ))
    simpa only [div_eq_mul_inv, one_mul] using h
  calc
    hardyTail y N m ^ 2 ≤
        (∑ r ∈ Ico m N, y r ^ 2) *
          ∑ r ∈ Ico m N, (1 / (r + 1 : ℝ)) ^ 2 := hcs
    _ ≤ (∑' r, y r ^ 2) * (1 / (m : ℝ)) := by
      apply mul_le_mul
      · exact hy2.sum_le_tsum (Ico m N) (fun r hr ↦ sq_nonneg _)
      · exact sum_Ico_one_div_succ_sq_le hm hmN
      · exact sum_nonneg (fun r hr ↦ sq_nonneg _)
      · exact tsum_nonneg (fun r ↦ sq_nonneg _)
    _ = (∑' r, y r ^ 2) / (m : ℝ) := by ring

lemma exp_prefix_div_le_four_tsum_tilted {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0)) (htilt : Summable (tiltedTerm a)) (n : ℕ) :
    Real.exp (prefixLength a (n + 1)) / (n + 1 : ℝ) ≤
      4 * ∑' r, tiltedTerm a r := by
  have hy : ∀ r, 0 ≤ tiltedRoot a r := fun r ↦ (tiltedRoot_pos a r).le
  have hy2 : Summable (fun r ↦ tiltedRoot a r ^ 2) :=
    htilt.congr (fun r ↦ (tiltedRoot_sq a r).symm)
  let z := adjointHardy (tiltedRoot a) (n + 1)
  have hroot := sheppRoot_le_two_adjointHardy ha htilt n
  have hz : 0 ≤ z := by
    have hp := (sheppRoot_pos a n).le
    dsimp only [z]
    linarith
  have hsq : sheppRoot a n ^ 2 ≤ 4 * z ^ 2 := by
    have hp := (sheppRoot_pos a n).le
    nlinarith
  have htail : z ^ 2 ≤ (∑' r, tiltedRoot a r ^ 2) / (n + 1 : ℝ) := by
    dsimp only [z]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (adjointHardy_sq_le_tsum_div hy hy2
        (m := n + 1) (Nat.zero_lt_succ n))
  have hterm : (∑' r, tiltedRoot a r ^ 2) = ∑' r, tiltedTerm a r := by
    apply tsum_congr
    exact tiltedRoot_sq a
  rw [hterm] at htail
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  calc
    Real.exp (prefixLength a (n + 1)) / (n + 1 : ℝ) =
        (Real.exp (prefixLength a (n + 1) / 2) / (n + 1 : ℝ)) ^ 2 *
          (n + 1 : ℝ) := by
      rw [div_pow, ← Real.exp_nat_mul]
      field_simp
      congr 1
      ring
    _ ≤ 4 * z ^ 2 * (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_right hsq hnpos.le
    _ ≤ 4 * ((∑' r, tiltedTerm a r) / (n + 1 : ℝ)) *
          (n + 1 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (by norm_num)) hnpos.le
    _ = 4 * ∑' r, tiltedTerm a r := by field_simp

def energySeriesTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (tiltedLength a n) / ((n : ℝ) * (n + 1 : ℝ))

lemma tiltedTerm_le_energySeriesTerm (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    tiltedTerm a n ≤ energySeriesTerm a n := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hnsℝ : (0 : ℝ) < n + 1 := by positivity
  have hfrac : 1 / (n + 1 : ℝ) ^ 2 ≤
      1 / ((n : ℝ) * (n + 1 : ℝ)) := by
    field_simp
    nlinarith
  unfold tiltedTerm energySeriesTerm
  have h := mul_le_mul_of_nonneg_left hfrac
    (Real.exp_pos (tiltedLength a n)).le
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

lemma energySeriesTerm_le_two_tiltedTerm (a : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) :
    energySeriesTerm a n ≤ 2 * tiltedTerm a n := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsℝ : (0 : ℝ) < n + 1 := by positivity
  have hfrac : 1 / ((n : ℝ) * (n + 1 : ℝ)) ≤
      2 / (n + 1 : ℝ) ^ 2 := by
    field_simp
    nlinarith
  unfold tiltedTerm energySeriesTerm
  have h := mul_le_mul_of_nonneg_left hfrac
    (Real.exp_pos (tiltedLength a n)).le
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

lemma tiltedTerm_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ tiltedTerm a n :=
  (sq_nonneg (tiltedRoot a n)).trans_eq (tiltedRoot_sq a n)

/-- For a decreasing sequence, the permutation-invariant overlap energy and
Shepp's tilted series diverge together. -/
theorem energyCondition_iff_not_summable_tilted {a : ℕ → ℝ} {ε : ℝ}
    (hanti : Antitone a) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    (ha : Tendsto a atTop (nhds 0)) :
    EnergyCondition a ε ↔ ¬ Summable (tiltedTerm a) := by
  constructor
  · intro henergy htilt
    let T : ℝ := ∑' n, tiltedTerm a n
    let C : ℝ := ε - a 0 - 1
    have hT₀ : 0 ≤ T := tsum_nonneg (tiltedTerm_nonneg a)
    have hbound (M : ℕ) (hM : 1 ≤ M) :
        finiteEnergy a ε M ≤ C + 6 * T := by
      rw [finiteEnergy_formula hanti ha₀ haε hM]
      dsimp only [C]
      have hboundary : Real.exp (prefixLength a M) / (M : ℝ) ≤ 4 * T := by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
        dsimp only [T]
        simpa [Nat.succ_eq_add_one] using
          (exp_prefix_div_le_four_tsum_tilted ha htilt n)
      have hsum : (∑ k ∈ Ico 1 M, energySeriesTerm a k) ≤ 2 * T := by
        calc
          (∑ k ∈ Ico 1 M, energySeriesTerm a k) ≤
              ∑ k ∈ Ico 1 M, 2 * tiltedTerm a k := by
            apply sum_le_sum
            intro k hk
            exact energySeriesTerm_le_two_tiltedTerm a
              (mem_Ico.1 hk).1
          _ = 2 * ∑ k ∈ Ico 1 M, tiltedTerm a k := by
            rw [Finset.mul_sum]
          _ ≤ 2 * T := by
            exact mul_le_mul_of_nonneg_left
              (htilt.sum_le_tsum (Ico 1 M) (fun k hk ↦ tiltedTerm_nonneg a k))
              (by norm_num)
      change C + Real.exp (prefixLength a M) / (M : ℝ) +
          ∑ k ∈ Ico 1 M, energySeriesTerm a k ≤ C + 6 * T
      linarith
    obtain ⟨M, hM, hlarge⟩ := exists_lt_of_tendsto_atTop henergy 1 (C + 6 * T)
    exact (not_lt_of_ge (hbound M hM)) hlarge
  · intro htilt
    have hdiv : Tendsto
        (fun M ↦ ∑ k ∈ range M, tiltedTerm a k) atTop atTop :=
      not_summable_iff_tendsto_nat_atTop_of_nonneg (tiltedTerm_nonneg a) |>.1 htilt
    let D : ℝ := ε - a 0 - 1 - tiltedTerm a 0
    have hlower : ∀ᶠ M in atTop,
        D + ∑ k ∈ range M, tiltedTerm a k ≤ finiteEnergy a ε M := by
      filter_upwards [eventually_ge_atTop 1] with M hM
      rw [finiteEnergy_formula hanti ha₀ haε hM]
      have hsum : (∑ k ∈ Ico 1 M, tiltedTerm a k) ≤
          ∑ k ∈ Ico 1 M, energySeriesTerm a k := by
        apply sum_le_sum
        intro k hk
        exact tiltedTerm_le_energySeriesTerm a
          (mem_Ico.1 hk).1
      have hrange : (∑ k ∈ range M, tiltedTerm a k) =
          tiltedTerm a 0 + ∑ k ∈ Ico 1 M, tiltedTerm a k := by
        rw [← sum_range_add_sum_Ico (f := tiltedTerm a) hM]
        simp
      rw [hrange]
      dsimp only [D]
      have hboundary : 0 ≤ Real.exp (prefixLength a M) / (M : ℝ) := by
        positivity
      change ε - a 0 - 1 - tiltedTerm a 0 +
          (tiltedTerm a 0 + ∑ k ∈ Ico 1 M, tiltedTerm a k) ≤
        ε - a 0 - 1 + Real.exp (prefixLength a M) / (M : ℝ) +
          ∑ k ∈ Ico 1 M, energySeriesTerm a k
      linarith
    have hD : Tendsto
        (fun M ↦ D + ∑ k ∈ range M, tiltedTerm a k) atTop atTop := by
      have hc : Tendsto (fun _ : ℕ ↦ D) atTop (nhds D) := tendsto_const_nhds
      simpa only [add_comm] using hdiv.atTop_add hc
    exact tendsto_atTop_mono' atTop hlower hD

theorem energyCondition_iff_sheppCondition {a : ℕ → ℝ} {ε : ℝ}
    (hanti : Antitone a) (ha₀ : ∀ n, 0 ≤ a n) (haε : ∀ n, a n ≤ ε)
    (ha : Tendsto a atTop (nhds 0)) :
    EnergyCondition a ε ↔ SheppCondition a := by
  rw [energyCondition_iff_not_summable_tilted hanti ha₀ haε ha,
    SheppCondition, ← not_congr (summable_sheppTerm_iff_tiltedTerm ha₀ ha)]

lemma sheppTerm_pos (a : ℕ → ℝ) (n : ℕ) : 0 < sheppTerm a n := by
  unfold sheppTerm
  positivity

lemma sheppTerm_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ sheppTerm a n :=
  (sheppTerm_pos a n).le

lemma sheppCondition_iff_tendsto (a : ℕ → ℝ) :
    SheppCondition a ↔
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N, sheppTerm a n) atTop atTop := by
  exact not_summable_iff_tendsto_nat_atTop_of_nonneg (sheppTerm_nonneg a)

end

end Erdos526
