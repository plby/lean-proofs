/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 533.
https://www.erdosproblems.com/forum/thread/533

Informal authors:
- József Balogh
- John Lenz
- Hong Liu
- Christian Reiher
- Maryam Sharifzadeh
- Katherine Staden

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos533.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/533.lean
-/
/-
Formalization of the negative answer to Erdős Problem 533.

The mathematical construction is the `p = 3`, `ℓ = 1` specialization of
the complex Bollobás--Erdős graph of Liu, Reiher, Sharifzadeh, and Staden.
-/

import ErdosProblems.Erdos615.Erdos615Construction

open Filter SimpleGraph
open Set MeasureTheory
open scoped Classical ENNReal NNReal Pointwise Topology BigOperators

namespace Erdos533

/-! ## The complex sphere used by the LRSS construction -/

/-- The unit sphere in a nonzero finite-dimensional complex Euclidean space.
The parameter is shifted by one so that the sphere is nonempty also at `k = 0`. -/
abbrev ComplexSphere (k : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1

instance complexSphereNonempty (k : ℕ) : Nonempty (ComplexSphere k) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp [ComplexSphere, Metric.mem_sphere]⟩⟩

/-- Surface measure on `ComplexSphere k`, regarded as a bundled finite measure. -/
noncomputable def complexSphereFiniteMeasure (k : ℕ) :
    MeasureTheory.FiniteMeasure (ComplexSphere k) :=
  ⟨MeasureTheory.Measure.toSphere MeasureTheory.volume, inferInstance⟩

/-- Normalized surface measure on the complex unit sphere. -/
noncomputable def complexSphereProbability (k : ℕ) :
    MeasureTheory.ProbabilityMeasure (ComplexSphere k) :=
  (complexSphereFiniteMeasure k).normalize

@[simp] theorem complexSphereProbability_univ (k : ℕ) :
    (complexSphereProbability k : MeasureTheory.Measure (ComplexSphere k)) Set.univ = 1 := by
  exact MeasureTheory.measure_univ

/-! ## A two-set concentration lemma on a real sphere -/

/-- Brunn--Minkowski applied to the two truncated cones over `A` and `-B`.
If both sets have more than `(d / 2)^h` of the spherical surface measure,
then some pair has distance greater than `d`.  This two-set form is the
concentration input used to find the three approximate rotations. -/
theorem realSphere_two_set_far (h : ℕ) (hh : 0 < h)
    (A B : Set (Erdos615.Construction.Sphere h))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (d : ℝ) (hd : 1 ≤ d) (q : ℝ≥0∞)
    (hq : ENNReal.ofReal ((d / 2) ^ h) < q)
    (hAq : q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere A)
    (hBq : q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere B) :
    ∃ a ∈ A, ∃ b ∈ B, d < dist a b := by
  let E := EuclideanSpace ℝ (Fin h)
  let V : ℝ≥0∞ := volume (Metric.ball (0 : E) 1)
  obtain ⟨KA, hKAA, hKA, hKAq⟩ := hA.exists_lt_isCompact hAq
  obtain ⟨KB, hKBB, hKB, hKBq⟩ := hB.exists_lt_isCompact hBq
  let OA : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' KA)
  let OB : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' KB)
  let CA : Set E := Set.Icc (0 : ℝ) 1 • ((↑) '' KA)
  let CB : Set E := Set.Icc (0 : ℝ) 1 • ((↑) '' KB)
  have hCA : IsCompact CA :=
    isCompact_Icc.smul_set (hKA.image continuous_subtype_val)
  have hCB : IsCompact CB :=
    isCompact_Icc.smul_set (hKB.image continuous_subtype_val)
  have hh0 : (h : ℝ≥0∞) ≠ 0 := by simp [hh.ne']
  have hhtop : (h : ℝ≥0∞) ≠ ∞ := by simp
  have htotal : volume.toSphere
      (Set.univ : Set (Metric.sphere (0 : E) 1)) = (h : ℝ≥0∞) * V := by
    simp [E, V, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  have hOAK : volume.toSphere KA = (h : ℝ≥0∞) * volume OA := by
    rw [Measure.toSphere_apply' volume hKA.measurableSet]
    simp only [OA, E, finrank_euclideanSpace_fin]
  have hOBK : volume.toSphere KB = (h : ℝ≥0∞) * volume OB := by
    rw [Measure.toSphere_apply' volume hKB.measurableSet]
    simp only [OB, E, finrank_euclideanSpace_fin]
  have hOA_lower : q * V < volume OA := by
    by_contra hn
    have hle : volume OA ≤ q * V := not_lt.mp hn
    have hmul := mul_le_mul_right hle (h : ℝ≥0∞)
    apply not_lt_of_ge hmul
    simpa [htotal, hOAK, mul_assoc, mul_left_comm, mul_comm] using hKAq
  have hOB_lower : q * V < volume OB := by
    by_contra hn
    have hle : volume OB ≤ q * V := not_lt.mp hn
    have hmul := mul_le_mul_right hle (h : ℝ≥0∞)
    apply not_lt_of_ge hmul
    simpa [htotal, hOBK, mul_assoc, mul_left_comm, mul_comm] using hKBq
  have hOA_CA : OA ⊆ CA := by
    rintro x ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩, y, hy, rfl⟩
  have hOB_CB : OB ⊆ CB := by
    rintro x ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩, y, hy, rfl⟩
  have hCA_lower : q * V < volume CA :=
    hOA_lower.trans_le (measure_mono hOA_CA)
  have hCB_lower : q * V < volume CB :=
    hOB_lower.trans_le (measure_mono hOB_CB)
  by_contra hfar
  push Not at hfar
  let M : Set E := ((2 : ℝ)⁻¹ • CA) + ((2 : ℝ)⁻¹ • (-CB))
  have hBM : volume M ≥
      volume CA ^ (2 : ℝ)⁻¹ * volume (-CB) ^ (2 : ℝ)⁻¹ := by
    exact Erdos615.BrunnMinkowski.brunnMinkowski_multiplicative_of_hasPrekopaLeindler
      (Erdos615.BrunnMinkowski.hasPrekopaLeindler_euclidean h)
      CA (-CB) hCA.measurableSet hCB.neg.measurableSet
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num) (by norm_num)
  have hneg : volume (-CB) = volume CB := Measure.measure_neg volume CB
  have hM_lower : q * V < volume M := by
    have hca := ENNReal.rpow_lt_rpow hCA_lower
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    have hcb := ENNReal.rpow_lt_rpow hCB_lower
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    have hCApos : 0 < volume CA := bot_le.trans_lt hCA_lower
    have hCArpow0 : volume CA ^ (2 : ℝ)⁻¹ ≠ 0 :=
      (ENNReal.rpow_pos hCApos hCA.measure_lt_top.ne).ne'
    have hCArpowTop : volume CA ^ (2 : ℝ)⁻¹ ≠ ∞ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCA.measure_lt_top.ne).ne
    calc
      q * V = (q * V) ^ (2 : ℝ)⁻¹ * (q * V) ^ (2 : ℝ)⁻¹ := by
        rw [← ENNReal.rpow_add_of_nonneg] <;> norm_num
      _ ≤ volume CA ^ (2 : ℝ)⁻¹ * (q * V) ^ (2 : ℝ)⁻¹ :=
        mul_le_mul_left hca.le _
      _ < volume CA ^ (2 : ℝ)⁻¹ * volume CB ^ (2 : ℝ)⁻¹ := by
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_left hCArpow0 hCArpowTop hcb
      _ = volume CA ^ (2 : ℝ)⁻¹ * volume (-CB) ^ (2 : ℝ)⁻¹ := by rw [hneg]
      _ ≤ volume M := hBM
  have hnorm (x : Metric.sphere (0 : E) 1) : ‖(x : E)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hMball : M ⊆ Metric.closedBall (0 : E) (d / 2) := by
    intro z hz
    rcases hz with ⟨u, hu, v, hv, rfl⟩
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨nb, hnb, rfl⟩
    have hnb' : -nb ∈ CB := Set.mem_neg.mp hnb
    rcases ha with ⟨r, hr, ar, har, rfl⟩
    rcases har with ⟨a, haK, rfl⟩
    rcases hnb' with ⟨s, hs, br, hbr, hsbr⟩
    rcases hbr with ⟨b, hbK, rfl⟩
    have hnb_eq : nb = -(s • (b : E)) := by
      have hn := congrArg Neg.neg hsbr
      exact (neg_neg nb).symm.trans hn.symm
    subst nb
    rw [Metric.mem_closedBall, dist_zero_right]
    have hab : dist (a : E) b ≤ d := hfar a (hKAA haK) b (hKBB hbK)
    have aux (hrs : r ≤ s) : ‖r • (a : E) - s • (b : E)‖ ≤ d := by
      calc
        ‖r • (a : E) - s • (b : E)‖ =
            ‖r • ((a : E) - b) + (r - s) • (b : E)‖ := by
          congr 1
          simp only [smul_sub, sub_smul]
          abel
        _ ≤ ‖r • ((a : E) - b)‖ + ‖(r - s) • (b : E)‖ := norm_add_le _ _
        _ = r * dist (a : E) b + (s - r) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hr.1, abs_of_nonpos (sub_nonpos.mpr hrs), hnorm b,
            mul_one, dist_eq_norm]
          ring
        _ ≤ r * d + (s - r) := by
          simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hab hr.1) (s - r)
        _ ≤ d := by nlinarith [hr.2, hs.2]
    have hrsnorm : ‖r • (a : E) - s • (b : E)‖ ≤ d := by
      rcases le_total r s with hrs | hsr
      · exact aux hrs
      · rw [norm_sub_rev]
        have hba : dist (b : E) (a : E) ≤ d := by
          calc
            dist (b : E) (a : E) = dist (a : E) (b : E) := dist_comm _ _
            _ ≤ d := hab
        calc
          ‖s • (b : E) - r • (a : E)‖ =
              ‖s • ((b : E) - a) + (s - r) • (a : E)‖ := by
            congr 1
            simp only [smul_sub, sub_smul]
            abel
          _ ≤ ‖s • ((b : E) - a)‖ + ‖(s - r) • (a : E)‖ := norm_add_le _ _
          _ = s * dist (b : E) a + (r - s) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hs.1, abs_of_nonpos (sub_nonpos.mpr hsr), hnorm a,
              mul_one, dist_eq_norm]
            ring
          _ ≤ s * d + (r - s) := by
            simpa [add_comm] using
              add_le_add_right (mul_le_mul_of_nonneg_left hba hs.1) (r - s)
          _ ≤ d := by nlinarith [hr.2, hs.2]
    exact (show
      ‖(2 : ℝ)⁻¹ • (r • (a : E)) + (2 : ℝ)⁻¹ • (-(s • (b : E)))‖ ≤ d / 2 from
      calc
        ‖(2 : ℝ)⁻¹ • (r • (a : E)) + (2 : ℝ)⁻¹ • (-(s • (b : E)))‖ =
            ‖(2 : ℝ)⁻¹ • (r • (a : E) - s • (b : E))‖ := by
          congr 1
          simp only [smul_neg, smul_sub, smul_smul]
          abel
        _ = (2 : ℝ)⁻¹ * ‖r • (a : E) - s • (b : E)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          norm_num
        _ ≤ (2 : ℝ)⁻¹ * d := mul_le_mul_of_nonneg_left hrsnorm (by norm_num)
        _ = d / 2 := inv_mul_eq_div 2 d)
  have hball : volume (Metric.closedBall (0 : E) (d / 2)) =
      ENNReal.ofReal ((d / 2) ^ h) * V := by
    rw [Measure.addHaar_closedBall' volume (0 : E) (by linarith)]
    simp [E, V, finrank_euclideanSpace_fin,
      Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
  have hV0 : V ≠ 0 := by
    exact ne_of_gt (by simpa [V] using
      Metric.measure_ball_pos (volume : Measure E) (0 : E) zero_lt_one)
  have hVtop : V ≠ ∞ := by
    exact ne_of_lt (by simpa [V] using
      (measure_ball_lt_top : volume (Metric.ball (0 : E) 1) < ∞))
  have hpqV : ENNReal.ofReal ((d / 2) ^ h) * V < q * V :=
    ENNReal.mul_lt_mul_left hV0 hVtop hq
  exact (not_lt_of_ge ((measure_mono hMball).trans_eq hball))
    (hpqV.trans hM_lower)

/-- Probability-normalized version of `realSphere_two_set_far`, phrased in
the normalization used by the finite partition from Problem 615. -/
theorem sphereProbability_two_set_far (h : ℕ) (hh : 0 < h)
    (A B : Set (Erdos615.Construction.Sphere h))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (d q : ℝ) (hd : 1 ≤ d) (hq0 : 0 ≤ q)
    (hpow : (d / 2) ^ h < q)
    (hAq : q < (Erdos615.Construction.sphereProbability h hh A : ℝ))
    (hBq : q < (Erdos615.Construction.sphereProbability h hh B : ℝ)) :
    ∃ a ∈ A, ∃ b ∈ B, d < dist a b := by
  have hAun : ENNReal.ofReal q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere A := by
    apply lt_of_not_ge
    intro hle
    have hp := Erdos615.Construction.sphereProbability_le_of_toSphere_le
      h hh A q hq0 hle
    linarith
  have hBun : ENNReal.ofReal q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere B := by
    apply lt_of_not_ge
    intro hle
    have hp := Erdos615.Construction.sphereProbability_le_of_toSphere_le
      h hh B q hq0 hle
    linarith
  apply realSphere_two_set_far h hh A B hA hB d hd (ENNReal.ofReal q)
  · have hqpos : 0 < q :=
      (pow_nonneg (by linarith : 0 ≤ d / 2) h).trans_lt hpow
    exact (ENNReal.ofReal_lt_ofReal_iff hqpos).mpr hpow
  · exact hAun
  · exact hBun

/-! ## The order-three complex rotation -/

/-- The primitive cube root of unity used by the `p = 3` construction. -/
noncomputable def rho : ℂ :=
  (-1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I

private lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  norm_num

@[simp] theorem rho_re : rho.re = -1 / 2 := by
  simp [rho]

@[simp] theorem rho_im : rho.im = Real.sqrt 3 / 2 := by
  simp [rho]

theorem rho_sq : rho ^ 2 =
    (-1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [rho, pow_two]
  · nlinarith [sqrt_three_sq]
  · ring

@[simp] theorem rho_cube : rho ^ 3 = 1 := by
  rw [show rho ^ 3 = rho ^ 2 * rho by ring, rho_sq]
  apply Complex.ext <;> simp [rho]
  · nlinarith [sqrt_three_sq]
  · ring

theorem one_add_rho_add_sq : 1 + rho + rho ^ 2 = 0 := by
  rw [rho_sq]
  apply Complex.ext <;> simp [rho]
  <;> ring

@[simp] theorem norm_rho : ‖rho‖ = 1 := by
  rw [Complex.norm_def]
  rw [show Complex.normSq rho = 1 by
    simp [rho, Complex.normSq_apply]
    nlinarith [sqrt_three_sq]]
  norm_num

/-- A real orthonormal basis identifying `ℂ^(k+1)` with `ℝ^(2(k+1))`. -/
noncomputable def complexRealBasis (k : ℕ) :
    OrthonormalBasis (Fin ((k + 1) * 2)) ℝ
      (EuclideanSpace ℂ (Fin (k + 1))) :=
  (Pi.orthonormalBasis fun _ : Fin (k + 1) =>
    Complex.orthonormalBasisOneI).reindex
      ((Equiv.sigmaEquivProd (Fin (k + 1)) (Fin 2)).trans finProdFinEquiv)

/-- Coordinatewise multiplication by a unit complex number, as a real
linear isometry of complex Euclidean space. -/
noncomputable def complexScalarIsometry (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℂ (Fin (k + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℂ (Fin (k + 1)) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin (k + 1) => rotation
      ⟨u, by
        simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hu⟩)

@[simp] theorem complexScalarIsometry_apply (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℂ (Fin (k + 1))) :
    complexScalarIsometry k u hu x = u • x := by
  ext i
  rfl

/-- The same complex rotation transported to the real coordinate sphere. -/
noncomputable def realCoordinateRotation (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℝ (Fin ((k + 1) * 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  (complexRealBasis k).repr.symm.trans
    ((complexScalarIsometry k u hu).trans (complexRealBasis k).repr)

@[simp] theorem realCoordinateRotation_apply (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℝ (Fin ((k + 1) * 2))) :
    (complexRealBasis k).repr.symm (realCoordinateRotation k u hu x) =
      u • (complexRealBasis k).repr.symm x := by
  simp [realCoordinateRotation]

/-- A real linear isometry restricts to an equivalence of the unit sphere. -/
noncomputable def realSphereEquiv {h : ℕ}
    (e : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h)) :
    Erdos615.Construction.Sphere h ≃ Erdos615.Construction.Sphere h where
  toFun x := ⟨e x, by
    simpa [Erdos615.Construction.Sphere, Metric.mem_sphere, dist_zero_right]
      using x.property⟩
  invFun x := ⟨e.symm x, by
    simpa [Erdos615.Construction.Sphere, Metric.mem_sphere, dist_zero_right]
      using x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

@[simp] theorem realSphereEquiv_coe {h : ℕ}
    (e : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (x : Erdos615.Construction.Sphere h) :
    ((realSphereEquiv e x : Erdos615.Construction.Sphere h) :
      EuclideanSpace ℝ (Fin h)) = e x := rfl

/-- Normalized spherical measure is invariant under every ambient real linear
isometry.  The proof compares the truncated cones in the definition of
`Measure.toSphere`. -/
theorem sphereProbability_preimage_linearIsometry (h : ℕ) (hh : 0 < h)
    (e : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (A : Set (Erdos615.Construction.Sphere h)) (hA : MeasurableSet A) :
    Erdos615.Construction.sphereProbability h hh
        ((realSphereEquiv e) ⁻¹' A) =
      Erdos615.Construction.sphereProbability h hh A := by
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  letI : Nonempty (Erdos615.Construction.Sphere h) :=
    Erdos615.Construction.sphereNonempty h hh
  let M := Erdos615.Construction.sphereFiniteMeasure h
  let P := Erdos615.Construction.sphereProbability h hh
  let eS := realSphereEquiv e
  have hpreMeas : MeasurableSet (eS ⁻¹' A) := by
    apply hA.preimage
    exact ((e.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hcone : Set.Ioo (0 : ℝ) 1 • ((↑) '' (eS ⁻¹' A)) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' A)) := by
    ext z
    constructor
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨r, hr, e (w : EuclideanSpace ℝ (Fin h)),
        ⟨eS w, hw, rfl⟩, ?_⟩
      simp [eS, realSphereEquiv]
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, hzw⟩
      let w' : Erdos615.Construction.Sphere h :=
        ⟨e.symm w, by
          simpa [Erdos615.Construction.Sphere, Metric.mem_sphere, dist_zero_right]
            using w.property⟩
      refine ⟨r, hr, (w' : EuclideanSpace ℝ (Fin h)), ⟨w', ?_, rfl⟩, ?_⟩
      · change eS w' ∈ A
        simpa [eS, w', realSphereEquiv] using hw
      · apply e.injective
        simpa [w'] using hzw
  have Henn : (M : Measure (Erdos615.Construction.Sphere h)) (eS ⁻¹' A) =
      (M : Measure (Erdos615.Construction.Sphere h)) A := by
    rw [show (M : Measure (Erdos615.Construction.Sphere h)) =
      (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere by rfl]
    rw [Measure.toSphere_apply' volume hpreMeas,
      Measure.toSphere_apply' volume hA, hcone]
    congr 1
    have hvol : MeasurePreserving
        (⇑e.toHomeomorph.toMeasurableEquiv) volume volume := by
      simpa using e.measurePreserving
    exact hvol.measure_preimage_equiv _
  have H : M (eS ⁻¹' A) = M A := by
    exact congrArg ENNReal.toNNReal Henn
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg
      (fun N : FiniteMeasure (Erdos615.Construction.Sphere h) =>
        (N : Measure (Erdos615.Construction.Sphere h))) hzero
    exact hμ (by simpa [M, Erdos615.Construction.sphereFiniteMeasure] using hcoe)
  have hmass : M.mass ≠ 0 := M.mass_nonzero_iff.mpr hMne
  apply mul_left_cancel₀ hmass
  calc
    M.mass * P (eS ⁻¹' A) = M (eS ⁻¹' A) :=
      (M.self_eq_mass_mul_normalize _).symm
    _ = M A := H
    _ = M.mass * P A := M.self_eq_mass_mul_normalize A

/-- If a measurable set has probability greater than twice the two-set
concentration threshold, one point of the set is far from one transformed
copy in each of two prescribed orthogonal directions. -/
theorem three_far_transforms (h : ℕ) (hh : 0 < h)
    (A : Set (Erdos615.Construction.Sphere h)) (hA : MeasurableSet A)
    (q D : ℝ) (hq0 : 0 ≤ q) (hD : 1 ≤ D)
    (hpow : (D / 2) ^ h < q)
    (hlarge : 2 * q <
      (Erdos615.Construction.sphereProbability h hh A : ℝ))
    (e₁ e₂ : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin h)) :
    ∃ a₀ ∈ A, ∃ a₁ ∈ A, ∃ a₂ ∈ A,
      D < dist a₀ (realSphereEquiv e₁ a₁) ∧
      D < dist a₀ (realSphereEquiv e₂ a₂) := by
  let P := Erdos615.Construction.sphereProbability h hh
  let B₁ : Set (Erdos615.Construction.Sphere h) :=
    (realSphereEquiv e₁.symm) ⁻¹' A
  let B₂ : Set (Erdos615.Construction.Sphere h) :=
    (realSphereEquiv e₂.symm) ⁻¹' A
  have hB₁ : MeasurableSet B₁ := by
    apply hA.preimage
    exact ((e₁.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hB₂ : MeasurableSet B₂ := by
    apply hA.preimage
    exact ((e₂.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hPB₁ : P B₁ = P A := by
    exact sphereProbability_preimage_linearIsometry h hh e₁.symm A hA
  have hPB₂ : P B₂ = P A := by
    exact sphereProbability_preimage_linearIsometry h hh e₂.symm A hA
  let Bad₁ : Set (Erdos615.Construction.Sphere h) :=
    A ∩ ⋂ b : B₁, Metric.closedBall (b : Erdos615.Construction.Sphere h) D
  let Bad₂ : Set (Erdos615.Construction.Sphere h) :=
    A ∩ ⋂ b : B₂, Metric.closedBall (b : Erdos615.Construction.Sphere h) D
  have hBad₁ : MeasurableSet Bad₁ := by
    exact hA.inter (isClosed_iInter fun _ => Metric.isClosed_closedBall).measurableSet
  have hBad₂ : MeasurableSet Bad₂ := by
    exact hA.inter (isClosed_iInter fun _ => Metric.isClosed_closedBall).measurableSet
  have hqA : q < (P A : ℝ) := by linarith
  have hBad₁q : (P Bad₁ : ℝ) ≤ q := by
    by_contra hn
    have hqBad : q < (P Bad₁ : ℝ) := lt_of_not_ge hn
    have hqB₁ : q < (P B₁ : ℝ) := by
      rw [hPB₁]
      exact hqA
    obtain ⟨a, haBad, b, hbB, hab⟩ := sphereProbability_two_set_far
      h hh Bad₁ B₁ hBad₁ hB₁ D q hD hq0 hpow hqBad hqB₁
    have hle : dist a b ≤ D := by
      exact Metric.mem_closedBall.mp
        (Set.mem_iInter.mp haBad.2 ⟨b, hbB⟩)
    exact (not_lt_of_ge hle) hab
  have hBad₂q : (P Bad₂ : ℝ) ≤ q := by
    by_contra hn
    have hqBad : q < (P Bad₂ : ℝ) := lt_of_not_ge hn
    have hqB₂ : q < (P B₂ : ℝ) := by
      rw [hPB₂]
      exact hqA
    obtain ⟨a, haBad, b, hbB, hab⟩ := sphereProbability_two_set_far
      h hh Bad₂ B₂ hBad₂ hB₂ D q hD hq0 hpow hqBad hqB₂
    have hle : dist a b ≤ D := by
      exact Metric.mem_closedBall.mp
        (Set.mem_iInter.mp haBad.2 ⟨b, hbB⟩)
    exact (not_lt_of_ge hle) hab
  have hnot : ¬A ⊆ Bad₁ ∪ Bad₂ := by
    intro hsub
    have hmono : P A ≤ P (Bad₁ ∪ Bad₂) := P.apply_mono hsub
    have hunion : P (Bad₁ ∪ Bad₂) ≤ P Bad₁ + P Bad₂ := P.apply_union_le
    have hmonoR : (P A : ℝ) ≤ (P (Bad₁ ∪ Bad₂) : ℝ) := by exact_mod_cast hmono
    have hunionR : (P (Bad₁ ∪ Bad₂) : ℝ) ≤
        (P Bad₁ : ℝ) + (P Bad₂ : ℝ) := by exact_mod_cast hunion
    linarith
  obtain ⟨a₀, ha₀A, ha₀bad⟩ := Set.not_subset.mp hnot
  have ha₀bad₁ : a₀ ∉ Bad₁ := by
    intro ha
    exact ha₀bad (Or.inl ha)
  have ha₀bad₂ : a₀ ∉ Bad₂ := by
    intro ha
    exact ha₀bad (Or.inr ha)
  have hex₁ : ∃ b : B₁, D < dist a₀ (b : Erdos615.Construction.Sphere h) := by
    by_contra hn
    push Not at hn
    apply ha₀bad₁
    refine ⟨ha₀A, Set.mem_iInter.mpr ?_⟩
    intro b
    exact Metric.mem_closedBall.mpr (hn b)
  have hex₂ : ∃ b : B₂, D < dist a₀ (b : Erdos615.Construction.Sphere h) := by
    by_contra hn
    push Not at hn
    apply ha₀bad₂
    refine ⟨ha₀A, Set.mem_iInter.mpr ?_⟩
    intro b
    exact Metric.mem_closedBall.mpr (hn b)
  obtain ⟨b₁, hb₁⟩ := hex₁
  obtain ⟨b₂, hb₂⟩ := hex₂
  let a₁ : Erdos615.Construction.Sphere h := realSphereEquiv e₁.symm b₁
  let a₂ : Erdos615.Construction.Sphere h := realSphereEquiv e₂.symm b₂
  have ha₁A : a₁ ∈ A := b₁.property
  have ha₂A : a₂ ∈ A := b₂.property
  refine ⟨a₀, ha₀A, a₁, ha₁A, a₂, ha₂A, ?_, ?_⟩
  · have heq : realSphereEquiv e₁ a₁ = b₁ := by
      simp [a₁, realSphereEquiv]
    simpa [heq] using hb₁
  · have heq : realSphereEquiv e₂ a₂ = b₂ := by
      simp [a₂, realSphereEquiv]
    simpa [heq] using hb₂

/-! ## Transporting the concentration output back to the complex sphere -/

/-- The real coordinate sphere associated with `complexRealBasis` is
isometric to the complex sphere used by the graph construction. -/
noncomputable def complexOfRealSphere (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) : ComplexSphere k :=
  ⟨(complexRealBasis k).repr.symm x, by
    simpa [ComplexSphere, Erdos615.Construction.Sphere, Metric.mem_sphere,
      dist_zero_right] using x.property⟩

@[simp] theorem complexOfRealSphere_coe (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    ((complexOfRealSphere k x : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) = (complexRealBasis k).repr.symm x := rfl

theorem dist_complexOfRealSphere (k : ℕ)
    (x y : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    dist (complexOfRealSphere k x) (complexOfRealSphere k y) = dist x y := by
  change dist ((complexRealBasis k).repr.symm (x :
      EuclideanSpace ℝ (Fin ((k + 1) * 2))))
    ((complexRealBasis k).repr.symm (y :
      EuclideanSpace ℝ (Fin ((k + 1) * 2)))) = dist x y
  simp [dist_eq_norm, Subtype.dist_eq, ← map_sub]

/-- On a unit sphere, being very close to the antipode of `y` forces being
close to `y` itself after the sign is removed. -/
theorem close_of_far_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {D e : ℝ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hD : 0 ≤ D) (he : 0 ≤ e) (hgap : 4 - D ^ 2 < e ^ 2)
    (hfar : D < dist x (-y)) : dist x y < e := by
  have hfar' : D < ‖x + y‖ := by
    simpa [dist_eq_norm] using hfar
  have hfarSq : D ^ 2 < ‖x + y‖ ^ 2 :=
    (sq_lt_sq₀ hD (norm_nonneg _)).2 hfar'
  have hpar : ‖x - y‖ ^ 2 + ‖x + y‖ ^ 2 = 4 := by
    rw [norm_sub_sq_real, norm_add_sq_real, hx, hy]
    ring
  have hcloseSq : ‖x - y‖ ^ 2 < e ^ 2 := by
    nlinarith
  have hclose : ‖x - y‖ < e :=
    (sq_lt_sq₀ (norm_nonneg _) he).1 hcloseSq
  simpa [dist_eq_norm] using hclose

@[simp] theorem norm_neg_rho : ‖-rho‖ = 1 := by simp

@[simp] theorem norm_neg_rho_sq : ‖-(rho ^ 2)‖ = 1 := by simp [norm_rho]

/-- The two negative order-three rotations used by the antipodal
concentration argument. -/
noncomputable def negRhoRotation (k : ℕ) :
    EuclideanSpace ℝ (Fin ((k + 1) * 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  realCoordinateRotation k (-rho) norm_neg_rho

noncomputable def negRhoSqRotation (k : ℕ) :
    EuclideanSpace ℝ (Fin ((k + 1) * 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  realCoordinateRotation k (-(rho ^ 2)) norm_neg_rho_sq

@[simp] theorem complexOfRealSphere_negRhoRotation (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    ((complexOfRealSphere k
        (realSphereEquiv (negRhoRotation k) x) : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) =
      -(rho • ((complexOfRealSphere k x : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))) := by
  simp [negRhoRotation, complexOfRealSphere]

@[simp] theorem complexOfRealSphere_negRhoSqRotation (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    ((complexOfRealSphere k
        (realSphereEquiv (negRhoSqRotation k) x) : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) =
      -(rho ^ 2 • ((complexOfRealSphere k x : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))) := by
  simp [negRhoSqRotation, complexOfRealSphere]

theorem norm_one_sub_rho : ‖(1 : ℂ) - rho‖ = Real.sqrt 3 := by
  rw [Complex.norm_def]
  congr 1
  simp [rho, Complex.normSq_apply]
  nlinarith [sqrt_three_sq]

theorem norm_one_sub_rho_sq : ‖(1 : ℂ) - rho ^ 2‖ = Real.sqrt 3 := by
  rw [rho_sq, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  nlinarith [sqrt_three_sq]

/-! ## Geometric graph definitions -/

/-- Two sphere points are inner-adjacent in the oriented relation when one
is close to one of the two nontrivial order-three rotations of the other. -/
def approxRotation {k : ℕ} (d : ℝ) (h : Fin 2)
    (x y : ComplexSphere k) : Prop :=
  ‖(x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (h.1 + 1) • (y : EuclideanSpace ℂ (Fin (k + 1)))‖ ≤ d

def rotationClose {k : ℕ} (d : ℝ) (x y : ComplexSphere k) : Prop :=
  ∃ h : Fin 2, approxRotation d h x y

/-- The real partition centers, transported to the complex sphere. -/
noncomputable def complexCenter (k : ℕ) (r : ℝ) (hr : 0 < r)
    (i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :
    ComplexSphere k :=
  complexOfRealSphere k
    (Erdos615.Construction.center ((k + 1) * 2) r hr i)

/-- A unit real normal vector representing one of the three imaginary-part
functionals `Im (rho^j ⟨x,y⟩)`. -/
noncomputable def complexStripNormal (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k) : EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  (complexRealBasis k).repr
    ((Complex.I * star (rho ^ j.1)) •
      (x : EuclideanSpace ℂ (Fin (k + 1))))

theorem complexStripNormal_norm (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k) : ‖complexStripNormal k j x‖ = 1 := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin (k + 1)))‖ = 1 := by
    simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
  simp [complexStripNormal, norm_smul, norm_mul, norm_rho, hx]

theorem complexStripFunctional (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k)
    (y : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    inner ℝ (complexStripNormal k j x)
        (y : EuclideanSpace ℝ (Fin ((k + 1) * 2))) =
      (rho ^ j.1 * inner ℂ
        (x : EuclideanSpace ℂ (Fin (k + 1)))
        ((complexOfRealSphere k y : ComplexSphere k) :
          EuclideanSpace ℂ (Fin (k + 1)))).im := by
  calc
    inner ℝ (complexStripNormal k j x)
        (y : EuclideanSpace ℝ (Fin ((k + 1) * 2))) =
      inner ℝ
        ((Complex.I * star (rho ^ j.1)) •
          (x : EuclideanSpace ℂ (Fin (k + 1))))
        ((complexRealBasis k).repr.symm y) := by
          exact (complexRealBasis k).repr.inner_map_eq_flip _ _
    _ = (inner ℂ
        ((Complex.I * star (rho ^ j.1)) •
          (x : EuclideanSpace ℂ (Fin (k + 1))))
        ((complexRealBasis k).repr.symm y)).re :=
      by
        simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply]
        exact (map_sum Complex.reCLM (fun i : Fin (k + 1) =>
          ((complexRealBasis k).repr.symm y) i *
            star (((Complex.I * star (rho ^ j.1)) •
              (x : EuclideanSpace ℂ (Fin (k + 1)))) i)) Finset.univ).symm
    _ = _ := by
      rw [inner_smul_left]
      simp [Complex.mul_re, Complex.mul_im]

/-- Each complex strip has the same elementary spherical-measure bound as a
real equatorial strip. -/
theorem sphereProbability_complex_strip (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k) (s : ℝ) (hs : 0 ≤ s) :
    (Erdos615.Construction.sphereProbability ((k + 1) * 2) (by omega)
      {y | |(rho ^ j.1 * inner ℂ
        (x : EuclideanSpace ℂ (Fin (k + 1)))
        ((complexOfRealSphere k y : ComplexSphere k) :
          EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ s} : ℝ) ≤
      2 * s * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) := by
  simpa only [complexStripFunctional] using
    Erdos615.Construction.sphereProbability_strip_bound ((k + 1) * 2)
      (by omega) (complexStripNormal k j x)
      (complexStripNormal_norm k j x) s hs

/-! The cross-edge sector predicates are declared here because the strip
estimate and the subsequent finite averaging use them. -/

/-- The closed angular sector from angle `0` to angle `2π/3`, represented
as the intersection of two half-planes. -/
def inMainSector (a : ℂ) : Prop :=
  0 ≤ a.im ∧ 0 ≤ (-rho ^ 2 * a).im

/-- The inner product stays away from the three boundary lines of the
rotated sectors. -/
def awayFromStrips (t : ℝ) (a : ℂ) : Prop :=
  ∀ h : Fin 3, t ≤ |(rho ^ h.1 * a).im|

/-- Cross adjacency between one point in each tagged part. -/
def crossClose {k : ℕ} (t : ℝ) (x y : ComplexSphere k) : Prop :=
  inMainSector
      (inner ℂ (x : EuclideanSpace ℂ (Fin (k + 1)))
        (y : EuclideanSpace ℂ (Fin (k + 1)))) ∧
    awayFromStrips t
      (inner ℂ (x : EuclideanSpace ℂ (Fin (k + 1)))
        (y : EuclideanSpace ℂ (Fin (k + 1))))

/-- Cells whose centers avoid all three strips relative to a fixed first
center. -/
noncomputable def robustSecondCells (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :
    Finset (Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :=
  Finset.univ.filter fun j ↦ awayFromStrips t
    (inner ℂ
      ((complexCenter k r hr i : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))
      ((complexCenter k r hr j : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1))))

/-- For a fixed first center, almost all of the second-sphere weight avoids
the three strips.  The loss is the sum of the three real strip bounds. -/
theorem sum_robustSecondCells_weight_lower (k : ℕ) (r t : ℝ)
    (hr : 0 < r) (hrt : r < t)
    (i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :
    1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤
      ∑ j ∈ robustSecondCells k r hr t i,
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr j := by
  let h : ℕ := (k + 1) * 2
  have hh : 0 < h := by simp [h]
  let P := Erdos615.Construction.sphereProbability h hh
  let x : ComplexSphere k := complexCenter k r hr i
  let Strip (q : Fin 3) : Set (Erdos615.Construction.Sphere h) :=
    {y | |(rho ^ q.1 * inner ℂ
      (x : EuclideanSpace ℂ (Fin (k + 1)))
      ((complexOfRealSphere k y : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ 2 * t}
  let Bad : Set (Erdos615.Construction.Sphere h) :=
    Strip 0 ∪ Strip 1 ∪ Strip 2
  have ht : 0 < t := hr.trans hrt
  have hStrip (q : Fin 3) : MeasurableSet (Strip q) := by
    dsimp only [Strip]
    measurability
  have hBad : MeasurableSet Bad :=
    ((hStrip 0).union (hStrip 1)).union (hStrip 2)
  have hstripBound (q : Fin 3) :
      (P (Strip q) : ℝ) ≤ 4 * t * Real.sqrt h := by
    convert sphereProbability_complex_strip k q x (2 * t) (by positivity) using 1 <;>
      simp only [P, Strip, h, x] <;> ring
  have hBadNN : P Bad ≤ P (Strip 0) + P (Strip 1) + P (Strip 2) := by
    calc
      P Bad ≤ P (Strip 0 ∪ Strip 1) + P (Strip 2) := by
        simpa [Bad] using P.apply_union_le (s₁ := Strip 0 ∪ Strip 1)
          (s₂ := Strip 2)
      _ ≤ (P (Strip 0) + P (Strip 1)) + P (Strip 2) := by
        gcongr
        exact P.apply_union_le
      _ = P (Strip 0) + P (Strip 1) + P (Strip 2) := by ring
  have hBadReal : (P Bad : ℝ) ≤ 12 * t * Real.sqrt h := by
    have H : (P Bad : ℝ) ≤
        (P (Strip 0) : ℝ) + (P (Strip 1) : ℝ) + (P (Strip 2) : ℝ) := by
      exact_mod_cast hBadNN
    linarith [hstripBound 0, hstripBound 1, hstripBound 2]
  have hcompENN : (P : Measure (Erdos615.Construction.Sphere h)) Bad +
      (P : Measure (Erdos615.Construction.Sphere h)) Badᶜ = 1 := by
    simpa using
      (measure_add_measure_compl (μ := (P : Measure (Erdos615.Construction.Sphere h))) hBad)
  have hcompNN : P Bad + P Badᶜ = 1 := by
    apply ENNReal.coe_injective
    simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hcompENN
  have hcompReal : (P Bad : ℝ) + (P Badᶜ : ℝ) = 1 := by
    exact_mod_cast hcompNN
  have hgoodProb : 1 - 12 * t * Real.sqrt h ≤ (P Badᶜ : ℝ) := by
    linarith
  have hsubset : Badᶜ ⊆ Erdos615.Construction.cellUnion h r hr
      (robustSecondCells k r hr t i) := by
    intro y hy
    have hyBad : y ∉ Bad := hy
    have hyall : y ∈ ⋃ j : Fin (Erdos615.Construction.netCard h r hr),
        Erdos615.Construction.cell h r hr j := by
      rw [Erdos615.Construction.iUnion_cell h r hr]
      trivial
    rcases Set.mem_iUnion.mp hyall with ⟨j, hycell⟩
    have hycenter := Erdos615.Construction.cell_subset_ball h r hr j hycell
    rw [Metric.mem_closedBall] at hycenter
    have haway : awayFromStrips t
        (inner ℂ
          ((complexCenter k r hr i : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))) := by
      intro q
      have hyNot : ¬|(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ 2 * t := by
        intro H
        apply hyBad
        fin_cases q
        · exact Or.inl (Or.inl H)
        · exact Or.inl (Or.inr H)
        · exact Or.inr H
      have hyLarge : 2 * t < |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| := lt_of_not_ge hyNot
      have hproj : |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im -
          (rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ r := by
        have hc := complexStripFunctional k q x
          (Erdos615.Construction.center h r hr j)
        have hyf := complexStripFunctional k q x y
        change inner ℝ (complexStripNormal k q x)
            (Erdos615.Construction.center h r hr j :
              EuclideanSpace ℝ (Fin h)) = _ at hc
        change |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k (Erdos615.Construction.center h r hr j) :
            ComplexSphere k) : EuclideanSpace ℂ (Fin (k + 1)))).im -
          (rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ r
        rw [← hc, ← hyf]
        have H := abs_real_inner_le_norm (complexStripNormal k q x)
          ((Erdos615.Construction.center h r hr j :
              EuclideanSpace ℝ (Fin h)) - (y : EuclideanSpace ℝ (Fin h)))
        rw [inner_sub_right, complexStripNormal_norm, one_mul] at H
        exact H.trans (by
          simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hycenter)
      have habs := abs_sub_abs_le_abs_sub
        ((rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im)
        ((rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im)
      have hdiff : |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| -
          |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ r :=
        habs.trans (by simpa [abs_sub_comm] using hproj)
      dsimp only [x] at hyLarge hdiff ⊢
      linarith
    have hj : j ∈ robustSecondCells k r hr t i := by
      simp [robustSecondCells, haway]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hycell⟩⟩
  have hmonoNN : P Badᶜ ≤
      P (Erdos615.Construction.cellUnion h r hr
        (robustSecondCells k r hr t i)) := P.apply_mono hsubset
  have hmonoReal : (P Badᶜ : ℝ) ≤
      (P (Erdos615.Construction.cellUnion h r hr
        (robustSecondCells k r hr t i)) : ℝ) := by
    exact_mod_cast hmonoNN
  have hw := Erdos615.Construction.sum_weight_finset_eq_probability
    h r hh hr (robustSecondCells k r hr t i)
  calc
    1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) =
        1 - 12 * t * Real.sqrt h := by simp [h]
    _ ≤ (P Badᶜ : ℝ) := hgoodProb
    _ ≤ (P (Erdos615.Construction.cellUnion h r hr
        (robustSecondCells k r hr t i)) : ℝ) := hmonoReal
    _ = ∑ j ∈ robustSecondCells k r hr t i,
        Erdos615.Construction.weight h r hh hr j := hw.symm

/-- Coordinatewise multiplication by `rho^q` on the complex sphere. -/
noncomputable def rhoRotateSphere (k : ℕ) (q : Fin 3) (x : ComplexSphere k) :
    ComplexSphere k :=
  ⟨rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))), by
    have hx : ‖(x : EuclideanSpace ℂ (Fin (k + 1)))‖ = 1 := by
      simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
    simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right, norm_smul,
      norm_rho, hx]⟩

@[simp] theorem rhoRotateSphere_coe (k : ℕ) (q : Fin 3)
    (x : ComplexSphere k) :
    ((rhoRotateSphere k q x : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) =
      rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))) := rfl

theorem rotationClose_rhoRotate {k : ℕ} {d : ℝ} (q : Fin 3)
    {x y : ComplexSphere k} (hxy : rotationClose d x y) :
    rotationClose d (rhoRotateSphere k q x) (rhoRotateSphere k q y) := by
  obtain ⟨j, hj⟩ := hxy
  refine ⟨j, ?_⟩
  change ‖rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (j.1 + 1) •
        (rho ^ q.1 • (y : EuclideanSpace ℂ (Fin (k + 1))))‖ ≤ d
  rw [show rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (j.1 + 1) •
        (rho ^ q.1 • (y : EuclideanSpace ℂ (Fin (k + 1)))) =
      rho ^ q.1 • ((x : EuclideanSpace ℂ (Fin (k + 1))) -
        rho ^ (j.1 + 1) • (y : EuclideanSpace ℂ (Fin (k + 1)))) by
          rw [smul_sub, smul_smul, smul_smul]
          congr 2
          ring,
    norm_smul, norm_pow, norm_rho, one_pow, one_mul]
  exact hj

/-- The three closed sectors of angle `2π/3` cover the complex plane. -/
theorem three_main_sectors_cover (a : ℂ) :
    inMainSector a ∨ inMainSector (rho * a) ∨
      inMainSector (rho ^ 2 * a) := by
  have hsum : a.im + (rho * a).im + (rho ^ 2 * a).im = 0 := by
    have H := congrArg Complex.im
      (show (1 + rho + rho ^ 2) * a = 0 by rw [one_add_rho_add_sq, zero_mul])
    simpa [add_mul] using H
  have hsec₀ : (-rho ^ 2 * a).im = a.im + (rho * a).im := by
    have hc : -rho ^ 2 = 1 + rho := by
      linear_combination -one_add_rho_add_sq
    rw [hc, add_mul]
    simp
  have hsec₁ : (-rho ^ 2 * (rho * a)).im = -a.im := by
    have hc : (-rho ^ 2) * rho = -1 := by
      rw [neg_mul, show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
    rw [← mul_assoc, hc]
    simp
  have hsec₂ : (-rho ^ 2 * (rho ^ 2 * a)).im = -(rho * a).im := by
    have hc : (-rho ^ 2) * rho ^ 2 = -rho := by
      rw [neg_mul, show rho ^ 2 * rho ^ 2 = rho ^ 3 * rho by ring, rho_cube,
        one_mul]
    rw [← mul_assoc, hc]
    simp
  by_cases ha : 0 ≤ a.im
  · by_cases hs : 0 ≤ (-rho ^ 2 * a).im
    · exact Or.inl ⟨ha, hs⟩
    · right
      right
      rw [inMainSector, hsec₂]
      rw [hsec₀] at hs
      constructor <;> linarith
  · have ha' : a.im < 0 := lt_of_not_ge ha
    by_cases hr : 0 ≤ (rho * a).im
    · right
      left
      rw [inMainSector, hsec₁]
      exact ⟨hr, by linarith⟩
    · right
      right
      have hr' : (rho * a).im < 0 := lt_of_not_ge hr
      rw [inMainSector, hsec₂]
      constructor <;> linarith

/-- Avoiding the three boundary strips is invariant under the three rotations. -/
theorem awayFromStrips_rho_pow {t : ℝ} {a : ℂ} (q : Fin 3)
    (ha : awayFromStrips t a) : awayFromStrips t (rho ^ q.1 * a) := by
  intro j
  fin_cases q <;> fin_cases j
  · simpa using ha 0
  · simpa using ha 1
  · simpa using ha 2
  · simpa [mul_assoc] using ha 1
  · norm_num only [pow_one] at ⊢
    change t ≤ |(rho * (rho * a)).im|
    rw [show rho * (rho * a) = rho ^ 2 * a by ring]
    exact ha 2
  · norm_num only [pow_one] at ⊢
    change t ≤ |(rho ^ 2 * (rho * a)).im|
    rw [show rho ^ 2 * (rho * a) = a by
      calc
        rho ^ 2 * (rho * a) = rho ^ 3 * a := by ring
        _ = a := by rw [rho_cube, one_mul]]
    simpa only [Fin.val_zero 3, pow_zero, one_mul] using ha 0
  · simpa [mul_assoc] using ha 2
  · norm_num only [pow_one] at ⊢
    change t ≤ |(rho * (rho ^ 2 * a)).im|
    rw [show rho * (rho ^ 2 * a) = a by
      calc
        rho * (rho ^ 2 * a) = rho ^ 3 * a := by ring
        _ = a := by rw [rho_cube, one_mul]]
    simpa only [Fin.val_zero 3, pow_zero, one_mul] using ha 0
  · change t ≤ |(rho ^ 2 * (rho ^ 2 * a)).im|
    rw [show rho ^ 2 * (rho ^ 2 * a) = rho * a by
      calc
        rho ^ 2 * (rho ^ 2 * a) = rho ^ 3 * (rho * a) := by ring
        _ = rho * a := by rw [rho_cube, one_mul]]
    simpa only [Fin.val_one 1, pow_one] using ha 1

/-- The weighted fraction of cross pairs selected by a fixed global rotation
of the second part. -/
noncomputable def crossWeight (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (q : Fin 3) : ℝ :=
  ∑ i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr),
    Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr i *
      ∑ j : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr),
        if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k q (complexCenter k r hr j)) then
          Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr j
        else 0

/-- One of the three global rotations supplies at least one quarter of all
weighted cross pairs, provided the three strip losses total at most `1/4`. -/
theorem exists_crossWeight_ge_quarter (k : ℕ) (r t : ℝ)
    (hr : 0 < r) (hrt : r < t)
    (hstrip : 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤ 1 / 4) :
    ∃ q : Fin 3, 1 / 4 ≤ crossWeight k r hr t q := by
  let I := Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)
  let wt : I → ℝ := fun i ↦
    Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr i
  have hwt (i : I) : 0 ≤ wt i :=
    Erdos615.Construction.weight_nonneg ((k + 1) * 2) r (by omega) hr i
  have hwtsum : ∑ i : I, wt i = 1 :=
    Erdos615.Construction.sum_weight ((k + 1) * 2) r (by omega) hr
  let robust : ℝ := ∑ i : I, wt i *
    ∑ j ∈ robustSecondCells k r hr t i, wt j
  have hrobust : 3 / 4 ≤ robust := by
    have H : 1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤ robust := by
      calc
        1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) =
            ∑ i : I, wt i *
              (1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ))) := by
                rw [← Finset.sum_mul, hwtsum, one_mul]
        _ ≤ ∑ i : I, wt i *
            ∑ j ∈ robustSecondCells k r hr t i, wt j := by
              exact Finset.sum_le_sum fun i _ ↦
                mul_le_mul_of_nonneg_left
                  (sum_robustSecondCells_weight_lower k r t hr hrt i) (hwt i)
        _ = robust := rfl
    linarith
  have hpair (i j : I)
      (hj : j ∈ robustSecondCells k r hr t i) :
      wt i * wt j ≤ ∑ q : Fin 3,
        if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k q (complexCenter k r hr j)) then
          wt i * wt j else 0 := by
    have haway : awayFromStrips t
        (inner ℂ
          ((complexCenter k r hr i : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))) := by
      simpa [robustSecondCells] using (Finset.mem_filter.mp hj).2
    let a : ℂ := inner ℂ
      ((complexCenter k r hr i : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))
      ((complexCenter k r hr j : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))
    obtain hsector | hsector | hsector := three_main_sectors_cover a
    · have hc : crossClose t (complexCenter k r hr i)
          (rhoRotateSphere k 0 (complexCenter k r hr j)) := by
        refine ⟨?_, ?_⟩
        · simpa [a, inner_smul_right]
        · simpa [a, inner_smul_right] using awayFromStrips_rho_pow 0 haway
      have hnonneg : 0 ≤ wt i * wt j := mul_nonneg (hwt i) (hwt j)
      calc
        wt i * wt j = if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k 0 (complexCenter k r hr j)) then
          wt i * wt j else 0 := (if_pos hc).symm
        _ ≤ ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := Finset.single_le_sum
              (s := Finset.univ) (a := (0 : Fin 3))
              (f := fun q : Fin 3 ↦ if crossClose t (complexCenter k r hr i)
                (rhoRotateSphere k q (complexCenter k r hr j)) then
                  wt i * wt j else 0)
              (fun q _ ↦ by
                by_cases hq : crossClose t (complexCenter k r hr i)
                  (rhoRotateSphere k q (complexCenter k r hr j))
                · rw [if_pos hq]
                  exact hnonneg
                · rw [if_neg hq]) (Finset.mem_univ 0)
    · have hc : crossClose t (complexCenter k r hr i)
          (rhoRotateSphere k 1 (complexCenter k r hr j)) := by
        refine ⟨?_, ?_⟩
        · simpa [a, inner_smul_right]
        · simpa [a, inner_smul_right] using awayFromStrips_rho_pow 1 haway
      have hnonneg : 0 ≤ wt i * wt j := mul_nonneg (hwt i) (hwt j)
      calc
        wt i * wt j = if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k 1 (complexCenter k r hr j)) then
          wt i * wt j else 0 := (if_pos hc).symm
        _ ≤ ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := Finset.single_le_sum
              (s := Finset.univ) (a := (1 : Fin 3))
              (f := fun q : Fin 3 ↦ if crossClose t (complexCenter k r hr i)
                (rhoRotateSphere k q (complexCenter k r hr j)) then
                  wt i * wt j else 0)
              (fun q _ ↦ by
                by_cases hq : crossClose t (complexCenter k r hr i)
                  (rhoRotateSphere k q (complexCenter k r hr j))
                · rw [if_pos hq]
                  exact hnonneg
                · rw [if_neg hq]) (Finset.mem_univ 1)
    · have hc : crossClose t (complexCenter k r hr i)
          (rhoRotateSphere k 2 (complexCenter k r hr j)) := by
        refine ⟨?_, ?_⟩
        · simpa [a, inner_smul_right]
        · simpa [a, inner_smul_right] using awayFromStrips_rho_pow 2 haway
      have hnonneg : 0 ≤ wt i * wt j := mul_nonneg (hwt i) (hwt j)
      calc
        wt i * wt j = if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k 2 (complexCenter k r hr j)) then
          wt i * wt j else 0 := (if_pos hc).symm
        _ ≤ ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := Finset.single_le_sum
              (s := Finset.univ) (a := (2 : Fin 3))
              (f := fun q : Fin 3 ↦ if crossClose t (complexCenter k r hr i)
                (rhoRotateSphere k q (complexCenter k r hr j)) then
                  wt i * wt j else 0)
              (fun q _ ↦ by
                by_cases hq : crossClose t (complexCenter k r hr i)
                  (rhoRotateSphere k q (complexCenter k r hr j))
                · rw [if_pos hq]
                  exact hnonneg
                · rw [if_neg hq]) (Finset.mem_univ 2)
  have hrobustCross : robust ≤ ∑ q : Fin 3, crossWeight k r hr t q := by
    calc
      robust = ∑ i : I, ∑ j ∈ robustSecondCells k r hr t i,
          wt i * wt j := by
            simp only [robust, Finset.mul_sum]
      _ ≤ ∑ i : I, ∑ j ∈ robustSecondCells k r hr t i,
          ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := by
              exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ hpair i j hj
      _ ≤ ∑ i : I, ∑ j : I,
          ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_univ_sum_of_nonneg
              intro j
              exact Finset.sum_nonneg fun q _ ↦ by
                split_ifs <;> simp_all [mul_nonneg (hwt i) (hwt j)]
      _ = ∑ q : Fin 3, crossWeight k r hr t q := by
              simp only [crossWeight, wt, I]
              rw [show (∑ i : I, ∑ j : I,
                  ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
                      (rhoRotateSphere k q (complexCenter k r hr j)) then
                    wt i * wt j else 0) =
                  ∑ q : Fin 3, ∑ i : I, ∑ j : I,
                    if crossClose t (complexCenter k r hr i)
                        (rhoRotateSphere k q (complexCenter k r hr j)) then
                      wt i * wt j else 0 by
                calc
                  _ = ∑ i : I, ∑ q : Fin 3, ∑ j : I,
                      if crossClose t (complexCenter k r hr i)
                          (rhoRotateSphere k q (complexCenter k r hr j)) then
                        wt i * wt j else 0 := by
                          apply Finset.sum_congr rfl
                          intro i hi
                          rw [Finset.sum_comm]
                  _ = _ := by rw [Finset.sum_comm]]
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> ring
  by_contra hn
  push Not at hn
  have hsumlt : (∑ q : Fin 3, crossWeight k r hr t q) < 3 / 4 := by
    rw [Fin.sum_univ_succ]
    norm_num [Fin.sum_univ_succ]
    linarith [hn 0, hn 1, hn 2]
  linarith

theorem rotationClose_irrefl {k : ℕ} {d : ℝ} (hd : d < Real.sqrt 3)
    (x : ComplexSphere k) : ¬rotationClose d x x := by
  rintro ⟨j, hj⟩
  have hxnorm : ‖(x : EuclideanSpace ℂ (Fin (k + 1)))‖ = 1 := by
    simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
  have hnorm :
      ‖(x : EuclideanSpace ℂ (Fin (k + 1))) -
          rho ^ (j.1 + 1) • (x : EuclideanSpace ℂ (Fin (k + 1)))‖ =
        Real.sqrt 3 := by
    rw [show
      (x : EuclideanSpace ℂ (Fin (k + 1))) -
          rho ^ (j.1 + 1) • (x : EuclideanSpace ℂ (Fin (k + 1))) =
        ((1 : ℂ) - rho ^ (j.1 + 1)) •
          (x : EuclideanSpace ℂ (Fin (k + 1))) by module,
      norm_smul, hxnorm, mul_one]
    fin_cases j
    · norm_num
      exact norm_one_sub_rho
    · norm_num
      exact norm_one_sub_rho_sq
  change ‖(x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (j.1 + 1) • (x : EuclideanSpace ℂ (Fin (k + 1)))‖ ≤ d at hj
  rw [hnorm] at hj
  linarith

theorem rotationClose_symm {k : ℕ} {d : ℝ} {x y : ComplexSphere k} :
    rotationClose d x y → rotationClose d y x := by
  rintro ⟨h, hh⟩
  fin_cases h
  · refine ⟨1, ?_⟩
    norm_num [approxRotation] at hh ⊢
    rw [show
      (y : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
          (x : EuclideanSpace ℂ (Fin (k + 1))) =
        (-rho ^ 2) •
          ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho •
            (y : EuclideanSpace ℂ (Fin (k + 1)))) by
      have hcoef : (-rho ^ 2) * rho = -1 := by
        rw [neg_mul, show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
      rw [smul_sub, smul_smul, hcoef]
      simp [sub_eq_add_neg, add_comm]]
    simpa [norm_smul, norm_rho] using hh

  · refine ⟨0, ?_⟩
    norm_num [approxRotation] at hh ⊢
    rw [show
      (y : EuclideanSpace ℂ (Fin (k + 1))) - rho •
          (x : EuclideanSpace ℂ (Fin (k + 1))) =
        (-rho) •
          ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
            (y : EuclideanSpace ℂ (Fin (k + 1)))) by
      have hcoef : (-rho) * rho ^ 2 = -1 := by
        rw [neg_mul, show rho * rho ^ 2 = rho ^ 3 by ring, rho_cube]
      rw [smul_sub, smul_smul, hcoef]
      simp [sub_eq_add_neg, add_comm]]
    simpa [norm_smul, norm_rho] using hh

theorem approxRotation_zero_flip_one {k : ℕ} {d : ℝ}
    {x y : ComplexSphere k} (h : approxRotation d 0 x y) :
    approxRotation d 1 y x := by
  norm_num [approxRotation] at h ⊢
  rw [show
    (y : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
        (x : EuclideanSpace ℂ (Fin (k + 1))) =
      (-rho ^ 2) •
        ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho •
          (y : EuclideanSpace ℂ (Fin (k + 1)))) by
    have hcoef : (-rho ^ 2) * rho = -1 := by
      rw [neg_mul, show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
    rw [smul_sub, smul_smul, hcoef]
    simp [sub_eq_add_neg, add_comm]]
  simpa [norm_smul, norm_rho] using h

theorem approxRotation_one_flip_zero {k : ℕ} {d : ℝ}
    {x y : ComplexSphere k} (h : approxRotation d 1 x y) :
    approxRotation d 0 y x := by
  norm_num [approxRotation] at h ⊢
  rw [show
    (y : EuclideanSpace ℂ (Fin (k + 1))) - rho •
        (x : EuclideanSpace ℂ (Fin (k + 1))) =
      (-rho) •
        ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
          (y : EuclideanSpace ℂ (Fin (k + 1)))) by
    have hcoef : (-rho) * rho ^ 2 = -1 := by
      rw [neg_mul, show rho * rho ^ 2 = rho ^ 3 by ring, rho_cube]
    rw [smul_sub, smul_smul, hcoef]
    simp [sub_eq_add_neg, add_comm]]
  simpa [norm_smul, norm_rho] using h

/-- If a union of partition cells has more than four times the spherical
concentration threshold, three of its cells have centers spanning an inner
triangle.  This is the analytic heart of the bound on triangle-free sets. -/
theorem large_cells_give_inner_triangle (k : ℕ) (r d e D : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3)
    (J : Finset (Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)))
    (hlarge :
      4 * (D / 2) ^ ((k + 1) * 2) <
        ∑ i ∈ J, Erdos615.Construction.weight ((k + 1) * 2) r
          (by omega) hr i) :
    ∃ i₀ ∈ J, ∃ i₁ ∈ J, ∃ i₂ ∈ J,
      i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₁ ≠ i₂ ∧
      rotationClose d (complexCenter k r hr i₀) (complexCenter k r hr i₁) ∧
      rotationClose d (complexCenter k r hr i₀) (complexCenter k r hr i₂) ∧
      rotationClose d (complexCenter k r hr i₁) (complexCenter k r hr i₂) := by
  let h : ℕ := (k + 1) * 2
  have hh : 0 < h := by simp [h]
  let P := Erdos615.Construction.sphereProbability h hh
  let A : Set (Erdos615.Construction.Sphere h) :=
    Erdos615.Construction.cellUnion h r hr J
  have hA : MeasurableSet A :=
    Erdos615.Construction.cellUnion_measurable h r hr J
  let b : ℝ := (D / 2) ^ h
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hbpos : 0 < b := pow_pos (by positivity) _
  have hPA : 4 * b < (P A : ℝ) := by
    have hw := Erdos615.Construction.sum_weight_finset_eq_probability
      h r hh hr J
    simpa [h, b, P, A] using hlarge.trans_eq hw
  obtain ⟨a₀, ha₀A, a₁, ha₁A, a₂, ha₂A, hfar₁, hfar₂⟩ :=
    three_far_transforms h hh A hA (2 * b) D (by positivity) hD
      (by simpa [b] using (show b < 2 * b by linarith))
      (by simpa [P] using (show 2 * (2 * b) < (P A : ℝ) by nlinarith [hPA]))
      (negRhoRotation k) (negRhoSqRotation k)
  have ha₀mem := ha₀A
  have ha₁mem := ha₁A
  have ha₂mem := ha₂A
  simp only [A, Erdos615.Construction.cellUnion, Set.mem_iUnion] at ha₀mem ha₁mem ha₂mem
  rcases ha₀mem with ⟨i₀, hi₀J, ha₀cell⟩
  rcases ha₁mem with ⟨i₁, hi₁J, ha₁cell⟩
  rcases ha₂mem with ⟨i₂, hi₂J, ha₂cell⟩
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let x₀ : ComplexSphere k := complexOfRealSphere k a₀
  let x₁ : ComplexSphere k := complexOfRealSphere k a₁
  let x₂ : ComplexSphere k := complexOfRealSphere k a₂
  let c₀ : ComplexSphere k := complexCenter k r hr i₀
  let c₁ : ComplexSphere k := complexCenter k r hr i₁
  let c₂ : ComplexSphere k := complexCenter k r hr i₂
  have sphereNorm (x : ComplexSphere k) : ‖(x : E)‖ = 1 := by
    simpa [E, ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
  have hfar₁' : D < dist (x₀ : E) (-(rho • (x₁ : E))) := by
    have H : D < dist (complexOfRealSphere k a₀)
        (complexOfRealSphere k (realSphereEquiv (negRhoRotation k) a₁)) := by
      rw [dist_complexOfRealSphere]
      exact hfar₁
    change D < dist
      (((complexOfRealSphere k a₀ : ComplexSphere k) : E))
      (((complexOfRealSphere k (realSphereEquiv (negRhoRotation k) a₁) :
        ComplexSphere k) : E)) at H
    simpa only [x₀, x₁, complexOfRealSphere_negRhoRotation] using H
  have hfar₂' : D < dist (x₀ : E) (-(rho ^ 2 • (x₂ : E))) := by
    have H : D < dist (complexOfRealSphere k a₀)
        (complexOfRealSphere k (realSphereEquiv (negRhoSqRotation k) a₂)) := by
      rw [dist_complexOfRealSphere]
      exact hfar₂
    change D < dist
      (((complexOfRealSphere k a₀ : ComplexSphere k) : E))
      (((complexOfRealSphere k (realSphereEquiv (negRhoSqRotation k) a₂) :
        ComplexSphere k) : E)) at H
    simpa only [x₀, x₂, complexOfRealSphere_negRhoSqRotation] using H
  have hrotNorm₁ : ‖rho • (x₁ : E)‖ = 1 := by
    rw [norm_smul, norm_rho, sphereNorm x₁]
    norm_num
  have hrotNorm₂ : ‖rho ^ 2 • (x₂ : E)‖ = 1 := by
    rw [norm_smul, norm_pow, norm_rho, sphereNorm x₂]
    norm_num
  have hx₀₁ : dist (x₀ : E) (rho • (x₁ : E)) < e :=
    close_of_far_neg (sphereNorm x₀) hrotNorm₁ (by linarith) he hgap hfar₁'
  have hx₀₂ : dist (x₀ : E) (rho ^ 2 • (x₂ : E)) < e :=
    close_of_far_neg (sphereNorm x₀) hrotNorm₂ (by linarith) he hgap hfar₂'
  have hc₀x₀ : dist (c₀ : E) (x₀ : E) ≤ r := by
    have H := Erdos615.Construction.cell_subset_ball h r hr i₀ ha₀cell
    rw [Metric.mem_closedBall] at H
    have H' : dist (complexOfRealSphere k a₀)
        (complexOfRealSphere k (Erdos615.Construction.center h r hr i₀)) ≤ r := by
      rw [dist_complexOfRealSphere]
      exact H
    rw [_root_.dist_comm] at H'
    change dist (c₀ : E) (x₀ : E) ≤ r at H'
    exact H'
  have hc₁x₁ : dist (c₁ : E) (x₁ : E) ≤ r := by
    have H := Erdos615.Construction.cell_subset_ball h r hr i₁ ha₁cell
    rw [Metric.mem_closedBall] at H
    have H' : dist (complexOfRealSphere k a₁)
        (complexOfRealSphere k (Erdos615.Construction.center h r hr i₁)) ≤ r := by
      rw [dist_complexOfRealSphere]
      exact H
    rw [_root_.dist_comm] at H'
    change dist (c₁ : E) (x₁ : E) ≤ r at H'
    exact H'
  have hc₂x₂ : dist (c₂ : E) (x₂ : E) ≤ r := by
    have H := Erdos615.Construction.cell_subset_ball h r hr i₂ ha₂cell
    rw [Metric.mem_closedBall] at H
    have H' : dist (complexOfRealSphere k a₂)
        (complexOfRealSphere k (Erdos615.Construction.center h r hr i₂)) ≤ r := by
      rw [dist_complexOfRealSphere]
      exact H
    rw [_root_.dist_comm] at H'
    change dist (c₂ : E) (x₂ : E) ≤ r at H'
    exact H'
  have rhoDist (u v : E) : dist (rho • u) (rho • v) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, norm_rho, one_mul]
  have rhoSqDist (u v : E) : dist (rho ^ 2 • u) (rho ^ 2 • v) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, norm_pow, norm_rho,
      one_pow, one_mul]
  have hc₀₁ : dist (c₀ : E) (rho • (c₁ : E)) < d := by
    calc
      dist (c₀ : E) (rho • (c₁ : E)) ≤
          dist (c₀ : E) (x₀ : E) +
            dist (x₀ : E) (rho • (x₁ : E)) +
            dist (rho • (x₁ : E)) (rho • (c₁ : E)) :=
        dist_triangle4 _ _ _ _
      _ < r + e + r := by
        have hlast : dist (rho • (x₁ : E)) (rho • (c₁ : E)) ≤ r := by
          rw [rhoDist]
          rw [_root_.dist_comm]
          exact hc₁x₁
        linarith
      _ < d := by linarith
  have hc₀₂ : dist (c₀ : E) (rho ^ 2 • (c₂ : E)) < d := by
    calc
      dist (c₀ : E) (rho ^ 2 • (c₂ : E)) ≤
          dist (c₀ : E) (x₀ : E) +
            dist (x₀ : E) (rho ^ 2 • (x₂ : E)) +
            dist (rho ^ 2 • (x₂ : E)) (rho ^ 2 • (c₂ : E)) :=
        dist_triangle4 _ _ _ _
      _ < r + e + r := by
        have hlast : dist (rho ^ 2 • (x₂ : E)) (rho ^ 2 • (c₂ : E)) ≤ r := by
          rw [rhoSqDist]
          rw [_root_.dist_comm]
          exact hc₂x₂
        linarith
      _ < d := by linarith
  have hrho21 : rho ^ 2 * rho = 1 := by
    rw [show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
  have hrho22 : rho ^ 2 * rho ^ 2 = rho := by
    calc
      rho ^ 2 * rho ^ 2 = rho ^ 3 * rho := by ring
      _ = rho := by rw [rho_cube, one_mul]
  have hx₁₂ : dist (x₁ : E) (rho • (x₂ : E)) < 2 * e := by
    have H : dist (rho • (x₁ : E)) (rho ^ 2 • (x₂ : E)) < 2 * e := by
      calc
        dist (rho • (x₁ : E)) (rho ^ 2 • (x₂ : E)) ≤
            dist (rho • (x₁ : E)) (x₀ : E) +
              dist (x₀ : E) (rho ^ 2 • (x₂ : E)) := dist_triangle _ _ _
        _ < e + e := add_lt_add (by simpa only [_root_.dist_comm] using hx₀₁) hx₀₂
        _ = 2 * e := by ring
    rw [dist_eq_norm, show
      (x₁ : E) - rho • (x₂ : E) =
        rho ^ 2 • (rho • (x₁ : E) - rho ^ 2 • (x₂ : E)) by
          rw [smul_sub, smul_smul, smul_smul, hrho21, hrho22, one_smul],
      norm_smul, norm_pow, norm_rho]
    simpa [dist_eq_norm] using H
  have hc₁₂ : dist (c₁ : E) (rho • (c₂ : E)) < d := by
    calc
      dist (c₁ : E) (rho • (c₂ : E)) ≤
          dist (c₁ : E) (x₁ : E) +
            dist (x₁ : E) (rho • (x₂ : E)) +
            dist (rho • (x₂ : E)) (rho • (c₂ : E)) :=
        dist_triangle4 _ _ _ _
      _ < r + 2 * e + r := by
        have hlast : dist (rho • (x₂ : E)) (rho • (c₂ : E)) ≤ r := by
          rw [rhoDist]
          rw [_root_.dist_comm]
          exact hc₂x₂
        linarith
      _ < d := by linarith
  have hrot₀₁ : rotationClose d c₀ c₁ := by
    refine ⟨0, ?_⟩
    norm_num [approxRotation]
    simpa [dist_eq_norm] using hc₀₁.le
  have hrot₀₂ : rotationClose d c₀ c₂ := by
    refine ⟨1, ?_⟩
    norm_num [approxRotation]
    simpa [dist_eq_norm] using hc₀₂.le
  have hrot₁₂ : rotationClose d c₁ c₂ := by
    refine ⟨0, ?_⟩
    norm_num [approxRotation]
    simpa [dist_eq_norm] using hc₁₂.le
  have hi₀₁ : i₀ ≠ i₁ := by
    intro hij
    subst i₁
    exact rotationClose_irrefl hdroot c₀ hrot₀₁
  have hi₀₂ : i₀ ≠ i₂ := by
    intro hij
    subst i₂
    exact rotationClose_irrefl hdroot c₀ hrot₀₂
  have hi₁₂ : i₁ ≠ i₂ := by
    intro hij
    subst i₂
    exact rotationClose_irrefl hdroot c₁ hrot₁₂
  exact ⟨i₀, hi₀J, i₁, hi₁J, i₂, hi₂J, hi₀₁, hi₀₂, hi₁₂,
    hrot₀₁, hrot₀₂, hrot₁₂⟩

/-- In an inner triangle, two vertices cannot use the same rotation label
relative to the third vertex once the approximation radius is small. -/
theorem same_rotation_not_adjacent {k : ℕ} {d : ℝ} {u v x : ComplexSphere k}
    {h : Fin 2} (hd : 3 * d < Real.sqrt 3)
    (hu : approxRotation d h u x) (hv : approxRotation d h v x) :
    ¬ rotationClose d u v := by
  intro huv
  obtain ⟨j, huv⟩ := huv
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let a : E := rho ^ (h.1 + 1) • (x : E)
  change ‖(u : E) - a‖ ≤ d at hu
  change ‖(v : E) - a‖ ≤ d at hv
  change ‖(u : E) - rho ^ (j.1 + 1) • (v : E)‖ ≤ d at huv
  have huv_dist : ‖(u : E) - (v : E)‖ ≤ 2 * d := by
    calc
      ‖(u : E) - (v : E)‖ = ‖((u : E) - a) - ((v : E) - a)‖ := by
        congr 1
        module
      _ ≤ ‖(u : E) - a‖ + ‖(v : E) - a‖ := norm_sub_le _ _
      _ ≤ d + d := add_le_add hu hv
      _ = 2 * d := by ring
  have hfar :
      ‖(v : E) - rho ^ (j.1 + 1) • (v : E)‖ ≤ 3 * d := by
    calc
      ‖(v : E) - rho ^ (j.1 + 1) • (v : E)‖ =
          ‖((v : E) - (u : E)) +
            ((u : E) - rho ^ (j.1 + 1) • (v : E))‖ := by
        congr 1
        module
      _ ≤ ‖(v : E) - (u : E)‖ +
          ‖(u : E) - rho ^ (j.1 + 1) • (v : E)‖ := norm_add_le _ _
      _ ≤ 2 * d + d := add_le_add (by simpa [norm_sub_rev] using huv_dist) huv
      _ = 3 * d := by ring
  have hvnorm : ‖(v : E)‖ = 1 := by
    simpa [ComplexSphere] using v.property
  have hnorm :
      ‖(v : E) - rho ^ (j.1 + 1) • (v : E)‖ = Real.sqrt 3 := by
    rw [show
      (v : E) - rho ^ (j.1 + 1) • (v : E) =
        ((1 : ℂ) - rho ^ (j.1 + 1)) • (v : E) by module, norm_smul, hvnorm, mul_one]
    fin_cases j
    · norm_num
      exact norm_one_sub_rho
    · norm_num
      exact norm_one_sub_rho_sq
  rw [hnorm] at hfar
  linarith

/-- The graph induced by the inner-edge rule on one tagged part. -/
def innerGraph {k m : ℕ} (d : ℝ) (w : Fin m → ComplexSphere k) :
    SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j ↦ rotationClose d (w i) (w j)

theorem innerGraph_adj_iff {k m : ℕ} (d : ℝ)
    (w : Fin m → ComplexSphere k) (i j : Fin m) :
    (innerGraph d w).Adj i j ↔ i ≠ j ∧ rotationClose d (w i) (w j) := by
  rw [innerGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, rotationClose_symm h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

/-- The inner graph is `K₄`-free.  This is the label-pigeonhole part of
the LRSS construction and uses no measure theory. -/
theorem innerGraph_cliqueFree_four {k m : ℕ} {d : ℝ}
    (w : Fin m → ComplexSphere k) (hd : 3 * d < Real.sqrt 3) :
    (innerGraph d w).CliqueFree 4 := by
  intro s hs
  obtain ⟨a, b, c, x, hab, hac, hax, hbc, hbx, hcx, rfl⟩ :=
    Finset.card_eq_four.mp hs.card_eq
  have hcl := hs.isClique
  have hab_adj : rotationClose d (w a) (w b) :=
    ((innerGraph_adj_iff d w a b).mp (hcl (by solve | simp) (by solve | simp) hab)).2
  have hac_adj : rotationClose d (w a) (w c) :=
    ((innerGraph_adj_iff d w a c).mp (hcl (by solve | simp) (by solve | simp) hac)).2
  have hbc_adj : rotationClose d (w b) (w c) :=
    ((innerGraph_adj_iff d w b c).mp (hcl (by solve | simp) (by solve | simp) hbc)).2
  obtain ⟨ha, ha_rot⟩ : rotationClose d (w a) (w x) :=
    (innerGraph_adj_iff d w a x).mp (hcl (by solve | simp) (by solve | simp) hax) |>.2
  obtain ⟨hb, hb_rot⟩ : rotationClose d (w b) (w x) :=
    (innerGraph_adj_iff d w b x).mp (hcl (by solve | simp) (by solve | simp) hbx) |>.2
  obtain ⟨hc, hc_rot⟩ : rotationClose d (w c) (w x) :=
    (innerGraph_adj_iff d w c x).mp (hcl (by solve | simp) (by solve | simp) hcx) |>.2
  have hpigeon : ha = hb ∨ ha = hc ∨ hb = hc := by
    fin_cases ha <;> fin_cases hb <;> fin_cases hc <;> simp
  rcases hpigeon with hab_label | hac_label | hbc_label
  · subst hb
    exact same_rotation_not_adjacent hd ha_rot hb_rot hab_adj
  · subst hc
    exact same_rotation_not_adjacent hd ha_rot hc_rot hac_adj
  · subst hc
    exact same_rotation_not_adjacent hd hb_rot hc_rot hbc_adj

/-- The centroid of three sphere points, regarded as a vector in the ambient
complex Euclidean space. -/
noncomputable def triangleAverage {k : ℕ} (x₀ x₁ x₂ : ComplexSphere k) :
    EuclideanSpace ℂ (Fin (k + 1)) :=
  (3 : ℝ)⁻¹ •
    ((x₀ : EuclideanSpace ℂ (Fin (k + 1))) +
      (x₁ : EuclideanSpace ℂ (Fin (k + 1))) +
      (x₂ : EuclideanSpace ℂ (Fin (k + 1))))

private theorem triangleAverage_norm_le_aux {k : ℕ} {d : ℝ}
    {x₀ x₁ x₂ : ComplexSphere k}
    (h₁ : approxRotation d 0 x₁ x₀) (h₂ : approxRotation d 1 x₂ x₀) :
    ‖triangleAverage x₀ x₁ x₂‖ ≤ 2 * d / 3 := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  norm_num [approxRotation] at h₁ h₂
  have hrho : -(rho + rho ^ 2) = 1 := by
    linear_combination -one_add_rho_add_sq
  have hsum :
      (x₀ : E) + (x₁ : E) + (x₂ : E) =
        ((x₁ : E) - rho • (x₀ : E)) +
          ((x₂ : E) - rho ^ 2 • (x₀ : E)) := by
    calc
      _ = (x₁ : E) + (x₂ : E) + (x₀ : E) := by module
      _ = (x₁ : E) + (x₂ : E) + (-(rho + rho ^ 2)) • (x₀ : E) := by
        rw [hrho, one_smul]
      _ = _ := by module
  calc
    ‖triangleAverage x₀ x₁ x₂‖ =
        (1 / 3 : ℝ) * ‖(x₀ : E) + (x₁ : E) + (x₂ : E)‖ := by
      rw [triangleAverage, norm_smul]
      norm_num
    _ = (1 / 3 : ℝ) *
        ‖((x₁ : E) - rho • (x₀ : E)) +
          ((x₂ : E) - rho ^ 2 • (x₀ : E))‖ := by rw [hsum]
    _ ≤ (1 / 3 : ℝ) *
        (‖(x₁ : E) - rho • (x₀ : E)‖ +
          ‖(x₂ : E) - rho ^ 2 • (x₀ : E)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (1 / 3 : ℝ) * (d + d) := by gcongr
    _ = 2 * d / 3 := by ring

/-- The centroid of an inner triangle is small. -/
theorem inner_triangle_average_norm_le {k : ℕ} {d : ℝ}
    {x₀ x₁ x₂ : ComplexSphere k} (hd : 3 * d < Real.sqrt 3)
    (h₁₀ : rotationClose d x₁ x₀) (h₂₀ : rotationClose d x₂ x₀)
    (h₁₂ : rotationClose d x₁ x₂) :
    ‖triangleAverage x₀ x₁ x₂‖ ≤ 2 * d / 3 := by
  obtain ⟨a, ha⟩ := h₁₀
  obtain ⟨b, hb⟩ := h₂₀
  have hab : a ≠ b := by
    intro heq
    subst b
    exact same_rotation_not_adjacent hd ha hb h₁₂
  fin_cases a <;> fin_cases b
  · simp at hab
  · exact triangleAverage_norm_le_aux ha hb
  · simpa [triangleAverage, add_left_comm, add_comm] using
      (triangleAverage_norm_le_aux (x₁ := x₂) (x₂ := x₁) hb ha)
  · simp at hab

/-- The sector and strip conditions force a uniform positive imaginary part
after subtracting a `rho²`-rotate of a second cross neighbor. -/
theorem crossClose_im_inner_sub_rhoSq {k : ℕ} {t : ℝ}
    {x y y' : ComplexSphere k} (hxy : crossClose t x y)
    (hxy' : crossClose t x y') :
    2 * t ≤
      (inner ℂ (x : EuclideanSpace ℂ (Fin (k + 1)))
        ((y : EuclideanSpace ℂ (Fin (k + 1))) -
          rho ^ 2 • (y' : EuclideanSpace ℂ (Fin (k + 1))))).im := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let a : ℂ := inner ℂ (x : E) (y : E)
  let b : ℂ := inner ℂ (x : E) (y' : E)
  have ha_nonneg : 0 ≤ a.im := hxy.1.1
  have hb_nonneg : 0 ≤ (-rho ^ 2 * b).im := hxy'.1.2
  have ha_strip := hxy.2 (0 : Fin 3)
  have hb_strip := hxy'.2 (2 : Fin 3)
  norm_num at ha_strip hb_strip
  change t ≤ |a.im| at ha_strip
  change t ≤ |(rho ^ 2 * b).im| at hb_strip
  have ha_lower : t ≤ a.im := by
    rwa [abs_of_nonneg ha_nonneg] at ha_strip
  have hb_abs : |(-rho ^ 2 * b).im| = |(rho ^ 2 * b).im| := by
    rw [neg_mul, Complex.neg_im, abs_neg]
  have hb_mag : t ≤ |(-rho ^ 2 * b).im| := by
    rwa [hb_abs]
  have hb_lower : t ≤ (-rho ^ 2 * b).im := by
    rwa [abs_of_nonneg hb_nonneg] at hb_mag
  rw [inner_sub_right, inner_smul_right]
  change 2 * t ≤ (a - rho ^ 2 * b).im
  calc
    2 * t = t + t := by ring
    _ ≤ a.im + (-rho ^ 2 * b).im := add_le_add ha_lower hb_lower
    _ = (a - rho ^ 2 * b).im := by simp [sub_eq_add_neg]

/-- The local `3 + 2` obstruction.  An inner triangle in the left part and
an inner edge in the right part cannot have all six cross edges. -/
theorem no_oriented_three_two_configuration {k : ℕ} {d t : ℝ}
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t)
    {x₀ x₁ x₂ y y' : ComplexSphere k}
    (hx₁₀ : rotationClose d x₁ x₀) (hx₂₀ : rotationClose d x₂ x₀)
    (hx₁₂ : rotationClose d x₁ x₂)
    (hyy' : approxRotation d 1 y y')
    (hx₀y : crossClose t x₀ y) (hx₀y' : crossClose t x₀ y')
    (hx₁y : crossClose t x₁ y) (hx₁y' : crossClose t x₁ y')
    (hx₂y : crossClose t x₂ y) (hx₂y' : crossClose t x₂ y') : False := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let e : E := (y : E) - rho ^ 2 • (y' : E)
  have he : ‖e‖ ≤ d := by
    norm_num [approxRotation] at hyy'
    exact hyy'
  have havg : ‖triangleAverage x₀ x₁ x₂‖ ≤ 2 * d / 3 :=
    inner_triangle_average_norm_le hdsmall hx₁₀ hx₂₀ hx₁₂
  have h₀ : 2 * t ≤ (inner ℂ (x₀ : E) e).im :=
    crossClose_im_inner_sub_rhoSq hx₀y hx₀y'
  have h₁ : 2 * t ≤ (inner ℂ (x₁ : E) e).im :=
    crossClose_im_inner_sub_rhoSq hx₁y hx₁y'
  have h₂ : 2 * t ≤ (inner ℂ (x₂ : E) e).im :=
    crossClose_im_inner_sub_rhoSq hx₂y hx₂y'
  have hlower : 2 * t ≤ (inner ℂ (triangleAverage x₀ x₁ x₂) e).im := by
    have hsum : 6 * t ≤
        (inner ℂ (x₀ : E) e).im + (inner ℂ (x₁ : E) e).im +
          (inner ℂ (x₂ : E) e).im := by linarith
    simp only [triangleAverage, inner_smul_real_left, inner_add_left]
    norm_num
    linarith
  have him_le_norm :
      (inner ℂ (triangleAverage x₀ x₁ x₂) e).im ≤
        ‖inner ℂ (triangleAverage x₀ x₁ x₂) e‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have hinner :
      ‖inner ℂ (triangleAverage x₀ x₁ x₂) e‖ ≤
        ‖triangleAverage x₀ x₁ x₂‖ * ‖e‖ :=
    norm_inner_le_norm _ _
  have hproduct :
      ‖triangleAverage x₀ x₁ x₂‖ * ‖e‖ ≤ (2 * d / 3) * d := by
    exact mul_le_mul havg he (norm_nonneg _) (by positivity)
  have hupper :
      (inner ℂ (triangleAverage x₀ x₁ x₂) e).im ≤ 2 * d ^ 2 / 3 := by
    calc
      _ ≤ ‖inner ℂ (triangleAverage x₀ x₁ x₂) e‖ := him_le_norm
      _ ≤ ‖triangleAverage x₀ x₁ x₂‖ * ‖e‖ := hinner
      _ ≤ (2 * d / 3) * d := hproduct
      _ = 2 * d ^ 2 / 3 := by ring
  nlinarith

/-- Companion cross-edge inequality with the approximate edge in the first
argument of the inner product. -/
theorem crossClose_im_inner_sub_left_rho {k : ℕ} {t : ℝ}
    {x x' y : ComplexSphere k} (hxy : crossClose t x y)
    (hx'y : crossClose t x' y) :
    2 * t ≤
      (inner ℂ
        ((x : EuclideanSpace ℂ (Fin (k + 1))) -
          rho • (x' : EuclideanSpace ℂ (Fin (k + 1))))
        (y : EuclideanSpace ℂ (Fin (k + 1)))).im := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let a : ℂ := inner ℂ (x : E) (y : E)
  let b : ℂ := inner ℂ (x' : E) (y : E)
  have ha_nonneg : 0 ≤ a.im := hxy.1.1
  have hb_nonneg : 0 ≤ (-rho ^ 2 * b).im := hx'y.1.2
  have ha_strip := hxy.2 (0 : Fin 3)
  have hb_strip := hx'y.2 (2 : Fin 3)
  norm_num at ha_strip hb_strip
  change t ≤ |a.im| at ha_strip
  change t ≤ |(rho ^ 2 * b).im| at hb_strip
  have ha_lower : t ≤ a.im := by
    rwa [abs_of_nonneg ha_nonneg] at ha_strip
  have hb_abs : |(-rho ^ 2 * b).im| = |(rho ^ 2 * b).im| := by
    rw [neg_mul, Complex.neg_im, abs_neg]
  have hb_mag : t ≤ |(-rho ^ 2 * b).im| := by rwa [hb_abs]
  have hb_lower : t ≤ (-rho ^ 2 * b).im := by
    rwa [abs_of_nonneg hb_nonneg] at hb_mag
  rw [inner_sub_left, inner_smul_left]
  change 2 * t ≤ (a - starRingEnd ℂ rho * b).im
  have hrho_star : starRingEnd ℂ rho = rho ^ 2 := by
    change star rho = rho ^ 2
    rw [Complex.star_def]
    have hrho_ne : rho ≠ 0 := by
      intro h
      have := norm_rho
      rw [h, norm_zero] at this
      norm_num at this
    apply mul_right_cancel₀ hrho_ne
    rw [← Complex.normSq_eq_conj_mul_self,
      show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube,
      Complex.normSq_eq_norm_sq, norm_rho]
    norm_num
  rw [hrho_star]
  calc
    2 * t = t + t := by ring
    _ ≤ a.im + (-rho ^ 2 * b).im := add_le_add ha_lower hb_lower
    _ = (a - rho ^ 2 * b).im := by simp [sub_eq_add_neg]

/-- The local `2 + 3` obstruction, obtained by putting the inner triangle in
the second part. -/
theorem no_oriented_two_three_configuration {k : ℕ} {d t : ℝ}
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t)
    {x x' y₀ y₁ y₂ : ComplexSphere k}
    (hxx' : approxRotation d 0 x x')
    (hy₁₀ : rotationClose d y₁ y₀) (hy₂₀ : rotationClose d y₂ y₀)
    (hy₁₂ : rotationClose d y₁ y₂)
    (hxy₀ : crossClose t x y₀) (hx'y₀ : crossClose t x' y₀)
    (hxy₁ : crossClose t x y₁) (hx'y₁ : crossClose t x' y₁)
    (hxy₂ : crossClose t x y₂) (hx'y₂ : crossClose t x' y₂) : False := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let e : E := (x : E) - rho • (x' : E)
  have he : ‖e‖ ≤ d := by
    norm_num [approxRotation] at hxx'
    exact hxx'
  have havg : ‖triangleAverage y₀ y₁ y₂‖ ≤ 2 * d / 3 :=
    inner_triangle_average_norm_le hdsmall hy₁₀ hy₂₀ hy₁₂
  have h₀ : 2 * t ≤ (inner ℂ e (y₀ : E)).im :=
    crossClose_im_inner_sub_left_rho hxy₀ hx'y₀
  have h₁ : 2 * t ≤ (inner ℂ e (y₁ : E)).im :=
    crossClose_im_inner_sub_left_rho hxy₁ hx'y₁
  have h₂ : 2 * t ≤ (inner ℂ e (y₂ : E)).im :=
    crossClose_im_inner_sub_left_rho hxy₂ hx'y₂
  have hlower : 2 * t ≤ (inner ℂ e (triangleAverage y₀ y₁ y₂)).im := by
    have hsum : 6 * t ≤
        (inner ℂ e (y₀ : E)).im + (inner ℂ e (y₁ : E)).im +
          (inner ℂ e (y₂ : E)).im := by linarith
    simp only [triangleAverage, inner_smul_real_right, inner_add_right]
    norm_num
    linarith
  have him_le_norm :
      (inner ℂ e (triangleAverage y₀ y₁ y₂)).im ≤
        ‖inner ℂ e (triangleAverage y₀ y₁ y₂)‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have hinner :
      ‖inner ℂ e (triangleAverage y₀ y₁ y₂)‖ ≤
        ‖e‖ * ‖triangleAverage y₀ y₁ y₂‖ :=
    norm_inner_le_norm _ _
  have hproduct :
      ‖e‖ * ‖triangleAverage y₀ y₁ y₂‖ ≤ d * (2 * d / 3) := by
    exact mul_le_mul he havg (norm_nonneg _) hd0
  have hupper :
      (inner ℂ e (triangleAverage y₀ y₁ y₂)).im ≤ 2 * d ^ 2 / 3 := by
    calc
      _ ≤ ‖inner ℂ e (triangleAverage y₀ y₁ y₂)‖ := him_le_norm
      _ ≤ ‖e‖ * ‖triangleAverage y₀ y₁ y₂‖ := hinner
      _ ≤ d * (2 * d / 3) := hproduct
      _ = 2 * d ^ 2 / 3 := by ring
  nlinarith

/-- The oriented relation whose symmetric, irreflexive closure is the finite
two-part complex Bollobás--Erdős graph. -/
def geometricRel {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) :
    (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) → Prop
  | .inl i, .inl j => rotationClose d (w i) (w j)
  | .inr i, .inr j => rotationClose d (z i) (z j)
  | .inl i, .inr j => crossClose t (w i) (z j)
  | _, _ => False

/-- The finite graph before transport from `Fin m ⊕ Fin m` to `Fin (2*m)`. -/
def geometricGraph {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) : SimpleGraph (Fin m ⊕ Fin m) :=
  SimpleGraph.fromRel (geometricRel d t w z)

theorem geometricGraph_left_adj {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inl i) (.inl j) ↔
      i ≠ j ∧
        (rotationClose d (w i) (w j) ∨ rotationClose d (w j) (w i)) := by
  simp [geometricGraph, geometricRel]

theorem geometricGraph_left_adj_iff {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inl i) (.inl j) ↔
      i ≠ j ∧ rotationClose d (w i) (w j) := by
  rw [geometricGraph_left_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, rotationClose_symm h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

theorem geometricGraph_right_adj {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inr i) (.inr j) ↔
      i ≠ j ∧
        (rotationClose d (z i) (z j) ∨ rotationClose d (z j) (z i)) := by
  simp [geometricGraph, geometricRel]

theorem geometricGraph_right_adj_iff {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inr i) (.inr j) ↔
      i ≠ j ∧ rotationClose d (z i) (z j) := by
  rw [geometricGraph_right_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, rotationClose_symm h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

theorem geometricGraph_cross_adj {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inl i) (.inr j) ↔
      crossClose t (w i) (z j) := by
  simp [geometricGraph, geometricRel]

private theorem no_four_left_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k) (hdsmall : 3 * d < Real.sqrt 3)
    {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {a b c e : Fin m}
    (ha : Sum.inl a ∈ s) (hb : Sum.inl b ∈ s)
    (hc : Sum.inl c ∈ s) (he : Sum.inl e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : False := by
  apply (innerGraph_cliqueFree_four w hdsmall) {a, b, c, e}
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    have hus : Sum.inl u ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    have hvs : Sum.inl v ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    exact (innerGraph_adj_iff d w u v).2
      ⟨huv, (geometricGraph_left_adj_iff d t w z u v).1
        (hs hus hvs (by simpa using huv)) |>.2⟩
  · simp [hab, hac, hae, hbc, hbe, hce]

private theorem no_four_right_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k) (hdsmall : 3 * d < Real.sqrt 3)
    {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {a b c e : Fin m}
    (ha : Sum.inr a ∈ s) (hb : Sum.inr b ∈ s)
    (hc : Sum.inr c ∈ s) (he : Sum.inr e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : False := by
  apply (innerGraph_cliqueFree_four z hdsmall) {a, b, c, e}
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    have hus : Sum.inr u ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    have hvs : Sum.inr v ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    exact (innerGraph_adj_iff d z u v).2
      ⟨huv, (geometricGraph_right_adj_iff d t w z u v).1
        (hs hus hvs (by simpa using huv)) |>.2⟩
  · simp [hab, hac, hae, hbc, hbe, hce]

private theorem no_three_left_two_right_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t) {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {a b c p q : Fin m}
    (ha : Sum.inl a ∈ s) (hb : Sum.inl b ∈ s) (hc : Sum.inl c ∈ s)
    (hp : Sum.inr p ∈ s) (hq : Sum.inr q ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hpq : p ≠ q) : False := by
  have hx₁₀ : rotationClose d (w b) (w a) :=
    (geometricGraph_left_adj_iff d t w z b a).1
      (hs hb ha (by simpa using hab.symm)) |>.2
  have hx₂₀ : rotationClose d (w c) (w a) :=
    (geometricGraph_left_adj_iff d t w z c a).1
      (hs hc ha (by simpa using hac.symm)) |>.2
  have hx₁₂ : rotationClose d (w b) (w c) :=
    (geometricGraph_left_adj_iff d t w z b c).1
      (hs hb hc (by simpa using hbc)) |>.2
  have hpqrot : rotationClose d (z p) (z q) :=
    (geometricGraph_right_adj_iff d t w z p q).1
      (hs hp hq (by simpa using hpq)) |>.2
  have cross (i : Fin m) (hi : Sum.inl i ∈ s) (j : Fin m)
      (hj : Sum.inr j ∈ s) : crossClose t (w i) (z j) :=
    (geometricGraph_cross_adj d t w z i j).1 (hs hi hj (by solve | simp))
  obtain ⟨r, hr⟩ := hpqrot
  fin_cases r
  · exact no_oriented_three_two_configuration hd0 ht hdsmall hdt hx₁₀ hx₂₀ hx₁₂
      (approxRotation_zero_flip_one hr)
      (cross a ha q hq) (cross a ha p hp)
      (cross b hb q hq) (cross b hb p hp)
      (cross c hc q hq) (cross c hc p hp)
  · exact no_oriented_three_two_configuration hd0 ht hdsmall hdt hx₁₀ hx₂₀ hx₁₂ hr
      (cross a ha p hp) (cross a ha q hq)
      (cross b hb p hp) (cross b hb q hq)
      (cross c hc p hp) (cross c hc q hq)

private theorem no_two_left_three_right_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t) {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {p q a b c : Fin m}
    (hp : Sum.inl p ∈ s) (hq : Sum.inl q ∈ s)
    (ha : Sum.inr a ∈ s) (hb : Sum.inr b ∈ s) (hc : Sum.inr c ∈ s)
    (hpq : p ≠ q) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have hpqrot : rotationClose d (w p) (w q) :=
    (geometricGraph_left_adj_iff d t w z p q).1
      (hs hp hq (by simpa using hpq)) |>.2
  have hy₁₀ : rotationClose d (z b) (z a) :=
    (geometricGraph_right_adj_iff d t w z b a).1
      (hs hb ha (by simpa using hab.symm)) |>.2
  have hy₂₀ : rotationClose d (z c) (z a) :=
    (geometricGraph_right_adj_iff d t w z c a).1
      (hs hc ha (by simpa using hac.symm)) |>.2
  have hy₁₂ : rotationClose d (z b) (z c) :=
    (geometricGraph_right_adj_iff d t w z b c).1
      (hs hb hc (by simpa using hbc)) |>.2
  have cross (i : Fin m) (hi : Sum.inl i ∈ s) (j : Fin m)
      (hj : Sum.inr j ∈ s) : crossClose t (w i) (z j) :=
    (geometricGraph_cross_adj d t w z i j).1 (hs hi hj (by solve | simp))
  obtain ⟨r, hr⟩ := hpqrot
  fin_cases r
  · exact no_oriented_two_three_configuration hd0 ht hdsmall hdt hr hy₁₀ hy₂₀ hy₁₂
      (cross p hp a ha) (cross q hq a ha)
      (cross p hp b hb) (cross q hq b hb)
      (cross p hp c hc) (cross q hq c hc)
  · exact no_oriented_two_three_configuration hd0 ht hdsmall hdt
      (approxRotation_one_flip_zero hr) hy₁₀ hy₂₀ hy₁₂
      (cross q hq a ha) (cross p hp a ha)
      (cross q hq b hb) (cross p hp b hb)
      (cross q hq c hc) (cross p hp c hc)

/-- The complete geometric graph is `K₅`-free whenever the two numerical
separation inequalities used above hold. -/
theorem geometricGraph_cliqueFree_five {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t) : (geometricGraph d t w z).CliqueFree 5 := by
  intro s hs
  have hcard : s.card = 4 + 1 := by simpa using hs.card_eq
  obtain ⟨v₀, u, hv₀u, hus, hu_card⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨v₁, v₂, v₃, v₄, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄, rfl⟩ :=
    Finset.card_eq_four.mp hu_card
  have h₀₁ : v₀ ≠ v₁ := by
    intro h
    apply hv₀u
    simp [h]
  have h₀₂ : v₀ ≠ v₂ := by
    intro h
    apply hv₀u
    simp [h]
  have h₀₃ : v₀ ≠ v₃ := by
    intro h
    apply hv₀u
    simp [h]
  have h₀₄ : v₀ ≠ v₄ := by
    intro h
    apply hv₀u
    simp [h]
  subst s
  rcases v₀ with v₀ | v₀ <;> rcases v₁ with v₁ | v₁ <;>
    rcases v₂ with v₂ | v₂ <;> rcases v₃ with v₃ | v₃ <;>
    rcases v₄ with v₄ | v₄
  all_goals simp at h₀₁ h₀₂ h₀₃ h₀₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (p := v₃) (q := v₄) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₁) (c := v₃) (p := v₂) (q := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₁) (c := v₄) (p := v₂) (q := v₃) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₁) (a := v₂) (b := v₃) (c := v₄) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₂) (c := v₃) (p := v₁) (q := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₂) (c := v₄) (p := v₁) (q := v₃) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₂) (a := v₁) (b := v₃) (c := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₃) (c := v₄) (p := v₁) (q := v₂) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₃) (a := v₁) (b := v₂) (c := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₄) (a := v₁) (b := v₂) (c := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₁) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₁) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₁) (b := v₂) (c := v₃) (p := v₀) (q := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₁) (b := v₂) (c := v₄) (p := v₀) (q := v₃) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₁) (q := v₂) (a := v₀) (b := v₃) (c := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₁) (b := v₃) (c := v₄) (p := v₀) (q := v₂) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₁) (q := v₃) (a := v₀) (b := v₂) (c := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₁) (q := v₄) (a := v₀) (b := v₂) (c := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₂) (b := v₃) (c := v₄) (p := v₀) (q := v₁) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₂) (q := v₃) (a := v₀) (b := v₁) (c := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₂) (q := v₄) (a := v₀) (b := v₁) (c := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₃) (q := v₄) (a := v₀) (b := v₁) (c := v₂) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₄) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption

/-! ## The finite construction interface -/

/-- Transport the two tagged parts of the geometric construction to the
standard vertex type `Fin (m + m)` used by the statement of the problem. -/
def finiteGeometricGraph {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) : SimpleGraph (Fin (m + m)) :=
  (geometricGraph d t w z).map finSumFinEquiv.toEmbedding

/-! ### Rounding the spherical weights -/

noncomputable def copyVertexEquivFin (h : ℕ) (r : ℝ)
    (hh : 0 < h) (hr : 0 < r) (L : ℕ) :
    Erdos615.Construction.CopyVertex h r hh hr L ≃
      Fin (Erdos615.Construction.copyCard h r hh hr L) :=
  Fintype.equivFin _

noncomputable def roundedLeftPosition (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (v : Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)) : ComplexSphere k :=
  complexCenter k r hr
    ((copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).symm v).1

noncomputable def roundedRightPosition (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (q : Fin 3)
    (v : Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)) : ComplexSphere k :=
  rhoRotateSphere k q (roundedLeftPosition k r hr L v)

/-- The standard finite vertex type, decoded as a Boolean part tag and a
rounded copy of a partition cell. -/
noncomputable def roundedVertexEquiv (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) :
    Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L +
      Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L) ≃
      Bool × Erdos615.Construction.CopyVertex ((k + 1) * 2) r (by omega) hr L :=
  finSumFinEquiv.symm |>.trans
    ((Equiv.sumCongr
      (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).symm
      (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).symm).trans
      (Equiv.boolProdEquivSum _).symm)

theorem rounded_adj_of_same_part {k L : ℕ} {r d t : ℝ} (hr : 0 < r)
    (q : Fin 3)
    (u v : Bool × Erdos615.Construction.CopyVertex ((k + 1) * 2) r
      (by omega) hr L) (huv : u ≠ v) (hpart : u.1 = v.1)
    (hrot : rotationClose d (complexCenter k r hr u.2.1)
      (complexCenter k r hr v.2.1)) :
    (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj
        ((roundedVertexEquiv k r hr L).symm u)
        ((roundedVertexEquiv k r hr L).symm v) := by
  rcases u with ⟨bu, u⟩
  rcases v with ⟨bv, v⟩
  simp only at hpart
  subst bv
  cases bu
  · rw [finiteGeometricGraph, SimpleGraph.map_adj]
    refine ⟨Sum.inl (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L u),
      Sum.inl (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L v), ?_, by
        rfl, by rfl⟩
    rw [geometricGraph_left_adj_iff]
    refine ⟨?_, ?_⟩
    · intro huvFin
      apply huv
      simp only [Prod.mk.injEq, true_and]
      exact (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective huvFin
    · simpa [roundedLeftPosition] using hrot
  · rw [finiteGeometricGraph, SimpleGraph.map_adj]
    refine ⟨Sum.inr (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L u),
      Sum.inr (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L v), ?_, by
        rfl, by rfl⟩
    rw [geometricGraph_right_adj_iff]
    refine ⟨?_, ?_⟩
    · intro huvFin
      apply huv
      simp only [Prod.mk.injEq, true_and]
      exact (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective huvFin
    · simpa [roundedRightPosition, roundedLeftPosition] using
        rotationClose_rhoRotate q hrot

abbrev CrossIndexPair (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (q : Fin 3) :=
  {p : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr) ×
      Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr) //
    crossClose t (complexCenter k r hr p.1)
      (rhoRotateSphere k q (complexCenter k r hr p.2))}

abbrev WeightedCrossCopyPair (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3) :=
  Σ p : CrossIndexPair k r hr t q,
    Fin (Erdos615.Construction.multiplicity ((k + 1) * 2) r (by omega) hr L p.1.1) ×
      Fin (Erdos615.Construction.multiplicity ((k + 1) * 2) r (by omega) hr L p.1.2)

theorem crossWeight_eq_sum (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (q : Fin 3) :
    crossWeight k r hr t q =
      ∑ p : CrossIndexPair k r hr t q,
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.1 *
          Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.2 := by
  classical
  rw [crossWeight]
  let I := Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)
  let good : I × I → Prop := fun p ↦
    crossClose t (complexCenter k r hr p.1)
      (rhoRotateSphere k q (complexCenter k r hr p.2))
  let f : I × I → ℝ := fun p ↦
    Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1 *
      Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.2
  rw [show (∑ i : I, Erdos615.Construction.weight ((k + 1) * 2) r
      (by omega) hr i * ∑ j : I, if good (i, j) then
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr j else 0) =
      ∑ p : I × I, if good p then f p else 0 by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> simp_all [f]]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter good) (by simp [good]) f

theorem weightedCrossCopyPair_card_lower (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3) :
    (L : ℝ) ^ 2 * crossWeight k r hr t q ≤
      Fintype.card (WeightedCrossCopyPair k r hr L t q) := by
  rw [crossWeight_eq_sum]
  change (L : ℝ) ^ 2 * (∑ p : CrossIndexPair k r hr t q,
      Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.1 *
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.2) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hi := Erdos615.Construction.multiplicity_lower ((k + 1) * 2) r
    (by omega) hr L p.1.1
  have hj := Erdos615.Construction.multiplicity_lower ((k + 1) * 2) r
    (by omega) hr L p.1.2
  calc
    (L : ℝ) ^ 2 *
        (Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.1 *
          Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.2) =
      ((L : ℝ) * Erdos615.Construction.weight ((k + 1) * 2) r
        (by omega) hr p.1.1) *
      ((L : ℝ) * Erdos615.Construction.weight ((k + 1) * 2) r
        (by omega) hr p.1.2) := by ring
    _ ≤ Erdos615.Construction.multiplicity ((k + 1) * 2) r
        (by omega) hr L p.1.1 *
      Erdos615.Construction.multiplicity ((k + 1) * 2) r
        (by omega) hr L p.1.2 := by
      exact mul_le_mul hi hj
        (mul_nonneg (Nat.cast_nonneg L)
          (Erdos615.Construction.weight_nonneg _ _ _ _ _)) (Nat.cast_nonneg _)

noncomputable def weightedCrossLeftFin (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3)
    (p : WeightedCrossCopyPair k r hr L t q) :
    Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L) :=
  copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L ⟨p.1.1.1, p.2.1⟩

noncomputable def weightedCrossRightFin (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3)
    (p : WeightedCrossCopyPair k r hr L t q) :
    Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L) :=
  copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L ⟨p.1.1.2, p.2.2⟩

noncomputable def weightedCrossPairToEdge (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (d t : ℝ) (q : Fin 3)
    (p : WeightedCrossCopyPair k r hr L t q) :
    (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).edgeFinset := by
  let m := Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L
  let u : Fin (m + m) := finSumFinEquiv
    (Sum.inl (weightedCrossLeftFin k r hr L t q p) : Fin m ⊕ Fin m)
  let v : Fin (m + m) := finSumFinEquiv
    (Sum.inr (weightedCrossRightFin k r hr L t q p) : Fin m ⊕ Fin m)
  refine ⟨s(u, v), ?_⟩
  rw [SimpleGraph.mem_edgeFinset]
  change (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
    (roundedRightPosition k r hr L q)).Adj u v
  rw [finiteGeometricGraph, SimpleGraph.map_adj]
  refine ⟨Sum.inl (weightedCrossLeftFin k r hr L t q p),
    Sum.inr (weightedCrossRightFin k r hr L t q p), ?_, rfl, rfl⟩
  rw [geometricGraph_cross_adj]
  simpa [roundedLeftPosition, roundedRightPosition, weightedCrossLeftFin,
    weightedCrossRightFin] using p.1.property

theorem weightedCrossPairToEdge_injective (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (d t : ℝ) (q : Fin 3) :
    Function.Injective (weightedCrossPairToEdge k r hr L d t q) := by
  intro p p' hpp'
  have hs := congrArg Subtype.val hpp'
  dsimp only [weightedCrossPairToEdge] at hs
  change s(finSumFinEquiv (Sum.inl (weightedCrossLeftFin k r hr L t q p)),
      finSumFinEquiv (Sum.inr (weightedCrossRightFin k r hr L t q p))) =
    s(finSumFinEquiv (Sum.inl (weightedCrossLeftFin k r hr L t q p')),
      finSumFinEquiv (Sum.inr (weightedCrossRightFin k r hr L t q p'))) at hs
  rw [Sym2.eq_iff] at hs
  have hends :
      weightedCrossLeftFin k r hr L t q p = weightedCrossLeftFin k r hr L t q p' ∧
      weightedCrossRightFin k r hr L t q p = weightedCrossRightFin k r hr L t q p' := by
    rcases hs with hs | hs
    · exact ⟨Sum.inl.inj (finSumFinEquiv.injective hs.1),
        Sum.inr.inj (finSumFinEquiv.injective hs.2)⟩
    · exfalso
      have := finSumFinEquiv.injective hs.1
      simp at this
  have hleft :=
    (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective hends.1
  have hright :=
    (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective hends.2
  rcases p with ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  rcases p' with ⟨⟨⟨i', j'⟩, hij'⟩, a', b'⟩
  dsimp only [weightedCrossLeftFin, weightedCrossRightFin] at hleft hright
  cases hleft
  cases hright
  rfl

/-- The rounded finite graph retains the weighted cross density. -/
theorem finiteGeometricGraph_edge_lower (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (d t : ℝ) (q : Fin 3) :
    (L : ℝ) ^ 2 * crossWeight k r hr t q ≤
      ((finiteGeometricGraph d t (roundedLeftPosition k r hr L)
        (roundedRightPosition k r hr L q)).edgeFinset.card : ℝ) := by
  have hcard : Fintype.card (WeightedCrossCopyPair k r hr L t q) ≤
      Fintype.card
        (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
          (roundedRightPosition k r hr L q)).edgeFinset :=
    Fintype.card_le_of_injective _
      (weightedCrossPairToEdge_injective k r hr L d t q)
  have hcard' : (Fintype.card (WeightedCrossCopyPair k r hr L t q) : ℝ) ≤
      ((finiteGeometricGraph d t (roundedLeftPosition k r hr L)
        (roundedRightPosition k r hr L q)).edgeFinset.card : ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_coe] using hcard)
  exact (weightedCrossCopyPair_card_lower k r hr L t q).trans hcard'

noncomputable def roundedDecodedSet (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L))) :
    Finset (Bool × Erdos615.Construction.CopyVertex ((k + 1) * 2) r
      (by omega) hr L) :=
  S.map (roundedVertexEquiv k r hr L).toEmbedding

/-- A triangle-free set cannot represent partition cells of total weight
above the three-point concentration threshold in either part. -/
theorem rounded_part_weight_bound (k L : ℕ) (r d e D t : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3) (q : Fin 3)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)))
    (hS : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).CliqueFreeOn S 3) (bpart : Bool) :
    ∑ i ∈ Erdos615.Construction.representedCells ((k + 1) * 2) r
        (by omega) hr L (roundedDecodedSet k r hr L S) bpart,
      Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr i ≤
        4 * (D / 2) ^ ((k + 1) * 2) := by
  let s := roundedDecodedSet k r hr L S
  let J := Erdos615.Construction.representedCells ((k + 1) * 2) r
    (by omega) hr L s bpart
  by_contra hn
  have hlarge : 4 * (D / 2) ^ ((k + 1) * 2) <
      ∑ i ∈ J, Erdos615.Construction.weight ((k + 1) * 2) r
        (by omega) hr i := lt_of_not_ge hn
  obtain ⟨i₀, hi₀J, i₁, hi₁J, i₂, hi₂J,
      hi₀₁, hi₀₂, hi₁₂, hrot₀₁, hrot₀₂, hrot₁₂⟩ :=
    large_cells_give_inner_triangle k r d e D hr he hD hgap hclose hdroot J hlarge
  rcases Finset.mem_image.mp hi₀J with ⟨u₀, hu₀part, hu₀cell⟩
  rcases Finset.mem_image.mp hi₁J with ⟨u₁, hu₁part, hu₁cell⟩
  rcases Finset.mem_image.mp hi₂J with ⟨u₂, hu₂part, hu₂cell⟩
  have hu₀s : u₀ ∈ s := (Finset.mem_filter.mp hu₀part).1
  have hu₁s : u₁ ∈ s := (Finset.mem_filter.mp hu₁part).1
  have hu₂s : u₂ ∈ s := (Finset.mem_filter.mp hu₂part).1
  have hu₀b : u₀.1 = bpart := (Finset.mem_filter.mp hu₀part).2
  have hu₁b : u₁.1 = bpart := (Finset.mem_filter.mp hu₁part).2
  have hu₂b : u₂.1 = bpart := (Finset.mem_filter.mp hu₂part).2
  have hcell₀ : u₀.2.1 = i₀ := hu₀cell
  have hcell₁ : u₁.2.1 = i₁ := hu₁cell
  have hcell₂ : u₂.2.1 = i₂ := hu₂cell
  have hu₀₁ : u₀ ≠ u₁ := by
    intro H
    apply hi₀₁
    rw [← hcell₀, ← hcell₁, H]
  have hu₀₂ : u₀ ≠ u₂ := by
    intro H
    apply hi₀₂
    rw [← hcell₀, ← hcell₂, H]
  have hu₁₂ : u₁ ≠ u₂ := by
    intro H
    apply hi₁₂
    rw [← hcell₁, ← hcell₂, H]
  let v₀ := (roundedVertexEquiv k r hr L).symm u₀
  let v₁ := (roundedVertexEquiv k r hr L).symm u₁
  let v₂ := (roundedVertexEquiv k r hr L).symm u₂
  have hv₀S : v₀ ∈ S := by
    simpa [s, roundedDecodedSet, v₀] using hu₀s
  have hv₁S : v₁ ∈ S := by
    simpa [s, roundedDecodedSet, v₁] using hu₁s
  have hv₂S : v₂ ∈ S := by
    simpa [s, roundedDecodedSet, v₂] using hu₂s
  have hv₀₁ : v₀ ≠ v₁ := (roundedVertexEquiv k r hr L).symm.injective.ne hu₀₁
  have hv₀₂ : v₀ ≠ v₂ := (roundedVertexEquiv k r hr L).symm.injective.ne hu₀₂
  have hv₁₂ : v₁ ≠ v₂ := (roundedVertexEquiv k r hr L).symm.injective.ne hu₁₂
  have hadj₀₁ : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj v₀ v₁ := by
    apply rounded_adj_of_same_part hr q u₀ u₁ hu₀₁
      (hu₀b.trans hu₁b.symm)
    simpa [hcell₀, hcell₁] using hrot₀₁
  have hadj₀₂ : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj v₀ v₂ := by
    apply rounded_adj_of_same_part hr q u₀ u₂ hu₀₂
      (hu₀b.trans hu₂b.symm)
    simpa [hcell₀, hcell₂] using hrot₀₂
  have hadj₁₂ : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj v₁ v₂ := by
    apply rounded_adj_of_same_part hr q u₁ u₂ hu₁₂
      (hu₁b.trans hu₂b.symm)
    simpa [hcell₁, hcell₂] using hrot₁₂
  apply hS (t := {v₀, v₁, v₂})
  · intro v hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hv₀S
    · exact hv₁S
    · exact hv₂S
  · refine ⟨?_, ?_⟩
    · intro v hv w hw hvw
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      all_goals simp_all only [ne_eq, not_true_eq_false]
      all_goals first | exact hadj₀₁ | exact hadj₀₂ | exact hadj₁₂ |
        exact hadj₀₁.symm | exact hadj₀₂.symm | exact hadj₁₂.symm
    · simp [hv₀₁, hv₀₂, hv₁₂]

theorem rounded_part_card_bound (k L : ℕ) (r d e D t : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3) (q : Fin 3)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)))
    (hS : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).CliqueFreeOn S 3) (bpart : Bool) :
    ((Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L
      (roundedDecodedSet k r hr L S) bpart).card : ℝ) ≤
      (L : ℝ) * (4 * (D / 2) ^ ((k + 1) * 2)) +
        Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
  let s := roundedDecodedSet k r hr L S
  let J := Erdos615.Construction.representedCells ((k + 1) * 2) r
    (by omega) hr L s bpart
  have hcard := Erdos615.Construction.partSet_card_le_sum_multiplicity
    ((k + 1) * 2) r (by omega) hr L s bpart
  have hweight := rounded_part_weight_bound k L r d e D t hr he hD hgap hclose
    hdroot q S hS bpart
  have hmult : (∑ i ∈ J, Erdos615.Construction.multiplicity
      ((k + 1) * 2) r (by omega) hr L i : ℝ) ≤
      (L : ℝ) * (∑ i ∈ J, Erdos615.Construction.weight
        ((k + 1) * 2) r (by omega) hr i) + J.card := by
    calc
      (∑ i ∈ J, Erdos615.Construction.multiplicity
          ((k + 1) * 2) r (by omega) hr L i : ℝ) ≤
        ∑ i ∈ J, ((L : ℝ) * Erdos615.Construction.weight
          ((k + 1) * 2) r (by omega) hr i + 1) := by
            exact Finset.sum_le_sum fun i _ ↦
              Erdos615.Construction.multiplicity_upper _ _ _ _ _ _
      _ = (L : ℝ) * (∑ i ∈ J, Erdos615.Construction.weight
          ((k + 1) * 2) r (by omega) hr i) + J.card := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp
  have hJ : (J.card : ℝ) ≤
      Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
    exact_mod_cast (by simpa using Finset.card_le_univ J)
  calc
    ((Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L
        s bpart).card : ℝ) ≤
      (∑ i ∈ J, Erdos615.Construction.multiplicity
        ((k + 1) * 2) r (by omega) hr L i : ℕ) := by exact_mod_cast hcard
    _ = ∑ i ∈ J, (Erdos615.Construction.multiplicity
        ((k + 1) * 2) r (by omega) hr L i : ℝ) := by norm_cast
    _ ≤ (L : ℝ) * (∑ i ∈ J, Erdos615.Construction.weight
        ((k + 1) * 2) r (by omega) hr i) + J.card := hmult
    _ ≤ (L : ℝ) * (4 * (D / 2) ^ ((k + 1) * 2)) +
        Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
      gcongr

theorem rounded_triangleFree_card_bound (k L : ℕ) (r d e D t : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3) (q : Fin 3)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)))
    (hS : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).CliqueFreeOn S 3) :
    (S.card : ℝ) ≤ 8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) +
      2 * Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
  let s := roundedDecodedSet k r hr L S
  have hfalse := rounded_part_card_bound k L r d e D t hr he hD hgap hclose
    hdroot q S hS false
  have htrue := rounded_part_card_bound k L r d e D t hr he hD hgap hclose
    hdroot q S hS true
  have hparts :
      (Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L s false).card +
      (Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L s true).card =
        s.card := by
    simpa [Erdos615.Construction.partSet] using
      (Finset.card_filter_add_card_filter_not (s := s) (fun v ↦ v.1 = false))
  have hScard : S.card = s.card := by simp [s, roundedDecodedSet]
  rw [hScard, ← hparts]
  push_cast
  nlinarith

/-! ### Choosing the dimension and the rounding scale -/

/-- An elementary Bernoulli bound, used instead of an asymptotic exponential
limit when selecting the sphere dimension. -/
theorem one_sub_pow_le_reciprocal (x : ℝ) (n : ℕ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (1 - x) ^ n ≤ 1 / (1 + (n : ℝ) * x) := by
  let p : ℝ := 1 - x
  have hp0 : 0 < p := by simp [p, hx1]
  have hp1 : p ≤ 1 := by simp [p, hx0.le]
  let a : ℝ := 1 / p - 1
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact sub_nonneg.mpr ((one_le_div hp0).2 hp1)
  have hbern : 1 + (n : ℝ) * a ≤ (1 + a) ^ n :=
    one_add_mul_le_pow (by linarith : -2 ≤ a) n
  have hax : x ≤ a := by
    dsimp [a, p]
    rw [le_sub_iff_add_le, le_div_iff₀ hp0]
    nlinarith
  have hrecip : 1 + (n : ℝ) * x ≤ (1 / p) ^ n := by
    calc
      1 + (n : ℝ) * x ≤ 1 + (n : ℝ) * a := by
        gcongr
      _ ≤ (1 + a) ^ n := hbern
      _ = (1 / p) ^ n := by simp [a]
  have hpPow : 0 < p ^ n := pow_pos hp0 _
  have hprod : p ^ n * (1 + (n : ℝ) * x) ≤ 1 := by
    calc
      p ^ n * (1 + (n : ℝ) * x) ≤ p ^ n * (1 / p) ^ n :=
        mul_le_mul_of_nonneg_left hrecip hpPow.le
      _ = 1 := by
        rw [← mul_pow]
        field_simp
        simp
  have hden : 0 < 1 + (n : ℝ) * x := by positivity
  rw [show (1 - x) ^ n = p ^ n by rfl, div_eq_mul_inv,
    le_mul_inv_iff₀ hden]
  simpa [mul_comm] using hprod

/-- There are dimensions of the special form `16 R⁴` for which the
three-point concentration threshold is arbitrarily small. -/
theorem exists_dimension_parameter (eta : ℝ) (heta : 0 < eta) :
    ∃ R : ℕ, 0 < R ∧
      8 * (1 - 1 / (102400 * (R : ℝ) ^ 2)) ^ (16 * R ^ 4) < eta := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max 1 (51200 / eta))
  have hR1 : 1 < (R : ℝ) := lt_of_le_of_lt (le_max_left _ _) hR
  have hR0 : 0 < R := by exact_mod_cast (by linarith : (0 : ℝ) < R)
  have hReta : 51200 / eta < (R : ℝ) :=
    (le_max_right _ _).trans_lt hR
  let x : ℝ := 1 / (102400 * (R : ℝ) ^ 2)
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg (R : ℝ)]
  have hpow := one_sub_pow_le_reciprocal x (16 * R ^ 4) hx0 hx1
  have hnx : ((16 * R ^ 4 : ℕ) : ℝ) * x = (R : ℝ) ^ 2 / 6400 := by
    dsimp [x]
    push_cast
    field_simp
    ring
  rw [hnx] at hpow
  have hfrac : 8 / eta < (R : ℝ) ^ 2 / 6400 := by
    rw [div_lt_div_iff₀ heta (by norm_num : (0 : ℝ) < 6400)]
    have hmul := mul_lt_mul_of_pos_left hReta heta
    field_simp at hmul ⊢
    nlinarith [hR1, sq_nonneg ((R : ℝ) - 1)]
  have hsmall : 8 * (1 / (1 + (R : ℝ) ^ 2 / 6400)) < eta := by
    rw [show 8 * (1 / (1 + (R : ℝ) ^ 2 / 6400)) =
      8 / (1 + (R : ℝ) ^ 2 / 6400) by ring,
      div_lt_iff₀ (by positivity)]
    have H : 8 < ((R : ℝ) ^ 2 / 6400) * eta :=
      (div_lt_iff₀ heta).mp hfrac
    nlinarith
  refine ⟨R, hR0, ?_⟩
  calc
    8 * (1 - 1 / (102400 * (R : ℝ) ^ 2)) ^ (16 * R ^ 4) =
        8 * (1 - x) ^ (16 * R ^ 4) := by rfl
    _ ≤ 8 * (1 / (1 + (R : ℝ) ^ 2 / 6400)) := by gcongr
    _ < eta := hsmall

/-- A finite counterexample at density `1 / 32`: every triangle-free vertex
set has fewer than `η n` vertices. -/
def IsCounterexample (η : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.CliqueFree 5 ∧
    (1 / 32 : ℝ) * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
    ∀ S : Finset (Fin n), G.CliqueFreeOn (S : Set (Fin n)) 3 →
      (S.card : ℝ) < η * n

/-- The precise finite output required from the analytic part of the LRSS
construction.  The numerical assumptions are kept in the package so that
`K₅`-freeness is obtained from `geometricGraph_cliqueFree_five`, rather than
being assumed as part of the analytic input. -/
def GeometricWitness (η : ℝ) (N : ℕ) : Prop :=
  ∃ (k m : ℕ) (d t : ℝ) (w z : Fin m → ComplexSphere k),
    0 < m ∧ N ≤ m + m ∧
    0 ≤ d ∧ 0 < t ∧ 3 * d < Real.sqrt 3 ∧ d ^ 2 < 3 * t ∧
    (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) ∧
    ∀ S : Finset (Fin (m + m)),
      (finiteGeometricGraph d t w z).CliqueFreeOn
          (S : Set (Fin (m + m))) 3 →
        (S.card : ℝ) < η * (m + m : ℕ)

/-- The complete finite complex Bollobás--Erdős construction.  All
parameters are explicit; only the final integer scale `L` is chosen large
enough to absorb rounding errors and the requested lower bound on the order. -/
theorem geometricWitness_exists (η : ℝ) (hη : 0 < η) (N : ℕ) :
    GeometricWitness η N := by
  obtain ⟨R, hR, hRsmall⟩ := exists_dimension_parameter η hη
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hRone : 1 ≤ (R : ℝ) := by exact_mod_cast hR
  let k : ℕ := 8 * R ^ 4 - 1
  have hEight : 0 < 8 * R ^ 4 := by positivity
  have hdim : (k + 1) * 2 = 16 * R ^ 4 := by
    dsimp [k]
    omega
  let d : ℝ := 1 / (20 * R)
  let t : ℝ := 1 / (400 * (R : ℝ) ^ 2)
  let e : ℝ := 1 / (80 * R)
  let D : ℝ := 2 - 1 / (51200 * (R : ℝ) ^ 2)
  let r : ℝ := 1 / (40000 * (R : ℝ) ^ 2)
  have hd : 0 < d := by positivity
  have ht : 0 < t := by positivity
  have he : 0 ≤ e := by positivity
  have hr : 0 < r := by positivity
  have hrt : r < t := by
    dsimp [r, t]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_pos_of_pos hRreal]
  have hD : 1 ≤ D := by
    have H : 1 / (51200 * (R : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg ((R : ℝ) - 1)]
    dsimp [D]
    linarith
  have hgap : 4 - D ^ 2 < e ^ 2 := by
    dsimp [D, e]
    field_simp
    nlinarith [sq_pos_of_pos hRreal, sq_nonneg ((R : ℝ) ^ 2)]
  have hclose : 2 * r + 2 * e < d := by
    dsimp [r, e, d]
    field_simp
    nlinarith [hRone, sq_pos_of_pos hRreal]
  have hdroot : d < Real.sqrt 3 := by
    have hsqrt : 1 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hd1 : d ≤ 1 / 20 := by
      dsimp [d]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdsmall : 3 * d < Real.sqrt 3 := by
    have hsqrt : 1 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hd1 : d ≤ 1 / 20 := by
      dsimp [d]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hdt : d ^ 2 < 3 * t := by
    dsimp [d, t]
    field_simp
    nlinarith [sq_pos_of_pos hRreal]
  have hstrip : 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤ 1 / 4 := by
    have hsqrt : Real.sqrt (((k + 1) * 2 : ℕ) : ℝ) = 4 * (R : ℝ) ^ 2 := by
      rw [hdim]
      push_cast
      rw [show (16 : ℝ) * (R : ℝ) ^ 4 = (4 * (R : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    rw [hsqrt]
    dsimp [t]
    field_simp
    nlinarith [sq_pos_of_pos hRreal]
  have hthreshold : 8 * (D / 2) ^ ((k + 1) * 2) < η := by
    rw [hdim]
    convert hRsmall using 1
    congr 2
    dsimp [D]
    field_simp
    ring
  obtain ⟨q, hq⟩ := exists_crossWeight_ge_quarter k r t hr hrt hstrip
  let K : ℕ := Erdos615.Construction.netCard ((k + 1) * 2) r hr
  have hK : 0 < K := Erdos615.Construction.netCard_pos ((k + 1) * 2) r
    (by omega) hr
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max ((3 * K : ℕ) : ℝ) (max (N : ℝ) (2 * (K : ℝ) / η)))
  have hLKreal : (3 * K : ℕ) < (L : ℝ) :=
    (le_max_left _ _).trans_lt hL
  have hNLreal : (N : ℝ) < (L : ℝ) :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans_lt hL
  have hKηreal : 2 * (K : ℝ) / η < (L : ℝ) :=
    (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hL
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by nlinarith [hK]
    exact_mod_cast this
  have hLK : 3 * K ≤ L := by exact_mod_cast hLKreal.le
  have hNL : N ≤ L := by exact_mod_cast hNLreal.le
  have hKη : 2 * (K : ℝ) < η * L := by
    rw [div_lt_iff₀ hη] at hKηreal
    simpa [mul_comm] using hKηreal
  let m : ℕ := Erdos615.Construction.copyCard ((k + 1) * 2) r
    (by omega) hr L
  let w : Fin m → ComplexSphere k := roundedLeftPosition k r hr L
  let z : Fin m → ComplexSphere k := roundedRightPosition k r hr L q
  have hLm : L ≤ m :=
    Erdos615.Construction.scale_le_copyCard ((k + 1) * 2) r (by omega) hr L
  have hmpos : 0 < m := hLpos.trans_le hLm
  have hmupper : m ≤ L + K :=
    Erdos615.Construction.copyCard_le_scale_add ((k + 1) * 2) r
      (by omega) hr L
  have hNorder : N ≤ m + m := by omega
  have hedgeL : (L : ℝ) ^ 2 / 4 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := by
    calc
      (L : ℝ) ^ 2 / 4 = (L : ℝ) ^ 2 * (1 / 4) := by ring
      _ ≤ (L : ℝ) ^ 2 * crossWeight k r hr t q := by
        gcongr
      _ ≤ ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := by
        simpa [w, z] using finiteGeometricGraph_edge_lower k r hr L d t q
  have hmupperReal : (m : ℝ) ≤ (L : ℝ) + K := by exact_mod_cast hmupper
  have hLKReal : 3 * (K : ℝ) ≤ L := by exact_mod_cast hLK
  have hedge : (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := by
    calc
      (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 / 4 := by
        push_cast
        nlinarith [sq_nonneg ((m : ℝ) - (L : ℝ)), sq_nonneg (L : ℝ)]
      _ ≤ ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := hedgeL
  refine ⟨k, m, d, t, w, z, hmpos, hNorder, hd.le, ht, hdsmall, hdt, hedge, ?_⟩
  intro S hS
  have hcard := rounded_triangleFree_card_bound k L r d e D t hr he hD hgap
    hclose hdroot q S (by simpa [w, z] using hS)
  have hLmReal : (L : ℝ) ≤ m := by exact_mod_cast hLm
  have hstrict : 8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) +
      2 * (K : ℝ) < η * (m + m : ℕ) := by
    push_cast
    have hfirst := mul_lt_mul_of_pos_right hthreshold (show (0 : ℝ) < L by exact_mod_cast hLpos)
    have hfirst' : 8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) < η * L := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hfirst
    calc
      8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) + 2 * (K : ℝ) <
          η * L + η * L := add_lt_add hfirst' hKη
      _ = η * (L + L) := by ring
      _ ≤ η * (m + m) := by
        gcongr
  exact hcard.trans_lt (by simpa [K] using hstrict)

/-- The deterministic geometric argument converts an analytic witness into
an ordinary finite counterexample. -/
theorem isCounterexample_finiteGeometricGraph {η : ℝ} {N k m : ℕ}
    {d t : ℝ} {w z : Fin m → ComplexSphere k}
    (hm : 0 < m) (hN : N ≤ m + m)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t)
    (hedge : (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ))
    (hsmall : ∀ S : Finset (Fin (m + m)),
      (finiteGeometricGraph d t w z).CliqueFreeOn
          (S : Set (Fin (m + m))) 3 →
        (S.card : ℝ) < η * (m + m : ℕ)) :
    N ≤ m + m ∧ IsCounterexample η (finiteGeometricGraph d t w z) := by
  refine ⟨hN, ?_, hedge, hsmall⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [finiteGeometricGraph, cliqueFree_map_iff]
  exact geometricGraph_cliqueFree_five w z hd0 ht hdsmall hdt

/-- The finite construction package needed to negate the eventual statement. -/
def CounterexamplePackage : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ ∃ G : SimpleGraph (Fin n), IsCounterexample η G

/-- The finite geometric witnesses, for arbitrary accuracy and lower bound on
the order, provide the counterexample package used by the quantifier layer. -/
theorem counterexamplePackage_of_geometricWitness
    (hgeom : ∀ η : ℝ, 0 < η → ∀ N : ℕ, GeometricWitness η N) :
    CounterexamplePackage := by
  intro η hη N
  obtain ⟨k, m, d, t, w, z, hm, hN, hd0, ht, hdsmall, hdt, hedge, hsmall⟩ :=
    hgeom η hη N
  refine ⟨m + m, hN, finiteGeometricGraph d t w z, ?_⟩
  exact (isCounterexample_finiteGeometricGraph hm hN hd0 ht hdsmall hdt hedge hsmall).2

/-- Pure quantifier conversion: arbitrarily large finite counterexamples at one
fixed positive density imply the exact negative answer in Problem 533. -/
theorem erdos_533_of_counterexamplePackage (hcounter : CounterexamplePackage) :
    ¬ ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 := by
  intro h
  obtain ⟨c, hc, h_eventual⟩ := h (1 / 32) (by norm_num)
  rw [eventually_atTop] at h_eventual
  obtain ⟨N, hN⟩ := h_eventual
  obtain ⟨n, hn, G, hG5, hGedge, hGsmall⟩ := hcounter (c / 2) (by positivity) N
  obtain ⟨S, hScard, hSfree⟩ := hN n hn G hG5 (by simpa using hGedge)
  have hsmall := hGsmall S hSfree
  have hn_pos : 0 < (n : ℝ) := by
    by_contra hn0
    have hn_eq : n = 0 := by
      exact Nat.eq_zero_of_not_pos fun hn_nat => hn0 (by exact_mod_cast hn_nat)
    subst n
    exact (not_lt_of_ge (Nat.cast_nonneg S.card)) (by simpa using hsmall)
  nlinarith

/-- Erdős Problem 533 has a negative answer.  The graph family above has
fixed edge density `1/32`, is `K₅`-free, and has triangle-independence
number `o(n)`. -/
theorem erdos_533 :
    ¬ ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 :=
  erdos_533_of_counterexamplePackage
    (counterexamplePackage_of_geometricWitness geometricWitness_exists)

#print axioms erdos_533

end Erdos533
