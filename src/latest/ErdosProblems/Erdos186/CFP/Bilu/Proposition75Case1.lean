import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2
import ErdosProblems.Erdos186.CFP.Bilu.OrthogonalTransport
import ErdosProblems.Erdos186.CFP.Bilu.CoordinateFlag

/-!
# The Case 1 branch of Bilu Proposition 7.5

This file proves the source's short Case 1 without assuming Lemma 6.5 as
an external statement.  It constructs an orthonormal ambient flag adapted
to the literal subspace `C₀`, applies the proved sharp cone-chain estimate,
and then performs the covolume-threshold arithmetic of equation (7.8).
-/

namespace Erdos186.CFP.Bilu.Proposition75Case1

open MeasureTheory Set Module Submodule
open scoped ENNReal Pointwise RealInnerProductSpace
open VolumeSections Proposition75Data Proposition75Case2

noncomputable section

structure AdaptedSectionFlag {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (d k : ℕ) (L : Submodule ℝ X) where
  f : (i : ℕ) → i ≤ k →
    EuclideanSpace ℝ (Fin (d + i)) →ₗᵢ[ℝ] X
  g : (i : ℕ) → i < k → ConeProduct (d + i) →ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (d + (i + 1)))
  compat : ∀ i (hi : i < k) x,
    f (i + 1) (Nat.succ_le_of_lt hi) (g i hi (conePair 0 x)) =
      f i hi.le x
  initial : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L
  initial_apply : ∀ x,
    f 0 (Nat.zero_le k) x = (initial x : X)

theorem exists_adaptedSectionFlag {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (d k : ℕ) (L : Submodule ℝ X)
    (hL : finrank ℝ L = d) (hX : finrank ℝ X = d + k) :
    Nonempty (AdaptedSectionFlag d k L) := by
  let j := canonicalCoordinateFlagF d k 0 (Nat.zero_le k)
  let q0 : EuclideanSpace ℝ (Fin (d + k)) ≃ₗᵢ[ℝ] X :=
    ((stdOrthonormalBasis ℝ X).reindex (finCongr hX)).repr.symm
  let jX : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] X :=
    q0.toLinearIsometry.comp j
  let S : Submodule ℝ X := LinearMap.range jX.toLinearMap
  have hS : finrank ℝ S = d := by
    dsimp only [S]
    rw [LinearMap.finrank_range_of_inj jX.injective]
    simp
  let eS : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] S :=
    euclideanEquivSubmoduleOfFinrankEq S hS
  let eL : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L :=
    euclideanEquivSubmoduleOfFinrankEq L hL
  let eSL : S ≃ₗᵢ[ℝ] L := eS.symm.trans eL
  let q : S →ₗᵢ[ℝ] X :=
    L.subtypeₗᵢ.comp eSL.toLinearIsometry
  let A : X →ₗᵢ[ℝ] X := q.extend
  let Ae : X ≃ₗᵢ[ℝ] X := A.toLinearIsometryEquiv rfl
  let jS : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] S :=
    { toLinearMap := jX.toLinearMap.codRestrict S fun x ↦
        LinearMap.mem_range_self jX.toLinearMap x
      norm_map' := jX.norm_map }
  let eJ : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] S :=
    jS.toLinearIsometryEquiv (by simp [hS])
  let initial : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L := eJ.trans eSL
  let u : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ] X :=
    Ae.toLinearIsometry.comp q0.toLinearIsometry
  let f := transportedCoordinateFlagF d k u
  refine ⟨⟨f, canonicalCoordinateFlagG d k,
    transportedCoordinateFlag_compat d k u,
    initial, ?_⟩⟩
  intro x
  change A (jX x) = (initial x : X)
  let sx : S := ⟨jX x, LinearMap.mem_range_self jX.toLinearMap x⟩
  rw [show jX x = (sx : X) from rfl,
    LinearIsometry.extend_apply q sx]
  change ((eSL sx : L) : X) = (initial x : X)
  apply congrArg Subtype.val
  change eSL sx = eSL (eJ x)
  apply congrArg eSL
  apply Subtype.ext
  rfl

theorem mem_coordinateB0_iff {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (z : coordinateC0 D) :
    z ∈ coordinateB0 D ↔
      (z : EuclideanSpace ℝ (Fin (m + r))) ∈
        coordinateDistortionBody B a := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (ambientEquiv m r).symm
      ((coordinateC0Equiv D x : coordinateC0 D) :
        EuclideanSpace ℝ (Fin (m + r))) ∈ distortionBody B a
    rw [show ((coordinateC0Equiv D x : coordinateC0 D) :
        EuclideanSpace ℝ (Fin (m + r))) =
          ambientEquiv m r (x : Ambient m r) from rfl,
      (ambientEquiv m r).symm_apply_apply]
    exact hx
  · intro hz
    let x : D.C0 :=
      ⟨(ambientEquiv m r).symm z, by
        have hzmem : (z : EuclideanSpace ℝ (Fin (m + r))) ∈
            D.C0.map (ambientEquiv m r).toLinearMap := z.property
        obtain ⟨y, hy, hzy⟩ := Submodule.mem_map.mp hzmem
        have : y = (ambientEquiv m r).symm z := by
          apply (ambientEquiv m r).injective
          simpa using hzy
        rwa [← this]⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [coordinateDistortionBody, GeometricData.B0] using hz
    apply Subtype.ext
    exact (ambientEquiv m r).apply_symm_apply z

/-- The geometric data used in Case 1 of Proposition 7.5.  Proposition
8.4 supplies the centered inball; no volume estimate is included as a
field. -/
structure Case1Witness {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (rho : ℝ) where
  measurable_B : MeasurableSet B
  convex_B : Convex ℝ B
  rho_pos : 0 < rho
  ambient_inball :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
      coordinateDistortionBody B a

/-- The norm-form core of Proposition 8.4.  A head inball and the displayed
operator bounds imply the same inball for the distortion body. -/
theorem closedBall_subset_distortionBody_of_norm_bounds {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)} {rho : ℝ}
    (_hrho : 0 ≤ rho)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rho ⊆
      (2 : ℝ) • B)
    (ha : ∀ i, rho * (‖a i‖ + 1) ≤ 1) :
    Metric.closedBall (0 : Ambient m r) rho ⊆ distortionBody B a := by
  intro z hz
  have hznorm : ‖z‖ ≤ rho := by
    simpa [Metric.mem_closedBall] using hz
  have hheadnorm : ‖head z‖ ≤ rho :=
    (WithLp.norm_fst_le (EuclideanSpace ℝ (Fin m)) z).trans hznorm
  refine ⟨hhead (by simpa [Metric.mem_closedBall] using hheadnorm), ?_⟩
  intro i
  have htailnorm : |tail z i| ≤ rho := by
    calc
      |tail z i| = ‖tail z i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖tail z‖ := PiLp.norm_apply_le (tail z) i
      _ ≤ ‖z‖ := WithLp.norm_snd_le (EuclideanSpace ℝ (Fin m)) z
      _ ≤ rho := hznorm
  calc
    |⟪head z, a i⟫ - tail z i| ≤
        |⟪head z, a i⟫| + |tail z i| := abs_sub _ _
    _ ≤ ‖head z‖ * ‖a i‖ + |tail z i| := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ rho * ‖a i‖ + rho := by gcongr
    _ = rho * (‖a i‖ + 1) := by ring
    _ ≤ 1 := ha i

/-- Coordinate form of the Proposition 8.4 inball. -/
theorem closedBall_subset_coordinateDistortionBody_of_norm_bounds {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)} {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rho ⊆
      (2 : ℝ) • B)
    (ha : ∀ i, rho * (‖a i‖ + 1) ≤ 1) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
      coordinateDistortionBody B a := by
  intro z hz
  change (ambientEquiv m r).symm z ∈ distortionBody B a
  apply closedBall_subset_distortionBody_of_norm_bounds hrho hhead ha
  simpa [Metric.mem_closedBall] using hz

/-- A real vector with all coordinates in the unit interval has Euclidean
norm at most the dimension.  This is the elementary estimate used in
Proposition 8.4. -/
theorem norm_le_dimension_of_abs_coord_le_one {m : ℕ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin m)) (hx : ∀ j, |x j| ≤ 1) :
    ‖x‖ ≤ m := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ m)).1
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ j, x j ^ 2 ≤ ∑ _j : Fin m, (1 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (x j)) zero_le_one).2 (hx j)
    _ = (m : ℝ) := by simp
    _ ≤ (m : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm]

/-- Proposition 8.4 with Bilu's explicit radius `1/(m+1)` and distorting
vectors in the unit cube. -/
theorem closedBall_subset_coordinateDistortionBody_of_unitCube {m r : ℕ}
    (hm : 0 < m) {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
        (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (ha : ∀ i j, |a i j| ≤ 1) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + r)))
        (((m : ℝ) + 1)⁻¹) ⊆ coordinateDistortionBody B a := by
  apply closedBall_subset_coordinateDistortionBody_of_norm_bounds
  · positivity
  · exact hhead
  · intro i
    have hainorm : ‖a i‖ ≤ (m : ℝ) :=
      norm_le_dimension_of_abs_coord_le_one hm (a i) (ha i)
    have hden : 0 < (m : ℝ) + 1 := by positivity
    calc
      ((m : ℝ) + 1)⁻¹ * (‖a i‖ + 1) ≤
          ((m : ℝ) + 1)⁻¹ * ((m : ℝ) + 1) := by gcongr
      _ = 1 := inv_mul_cancel₀ hden.ne'

/-- Source-data constructor for the Case 1 witness after Proposition 8.4. -/
theorem case1WitnessOfUnitCube {m r : ℕ} (hm : 0 < m)
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)} (D : GeometricData B a)
    (hmeas : MeasurableSet B) (hconv : Convex ℝ B)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
        (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (ha : ∀ i j, |a i j| ≤ 1) :
    Case1Witness D (((m : ℝ) + 1)⁻¹) where
  measurable_B := hmeas
  convex_B := hconv
  rho_pos := by positivity
  ambient_inball :=
    closedBall_subset_coordinateDistortionBody_of_unitCube hm hhead ha

/-- The output of Proposition 8.3 lies in the real unit cube, so it
automatically satisfies the coordinate premise of Proposition 8.4. -/
theorem case1WitnessOfUnitCubeIoc {m r : ℕ} (hm : 0 < m)
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)} (D : GeometricData B a)
    (hmeas : MeasurableSet B) (hconv : Convex ℝ B)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
        (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (ha : ∀ i, WithLp.ofLp (a i) ∈ Section8Synthesis.unitCubeIoc m) :
    Case1Witness D (((m : ℝ) + 1)⁻¹) := by
  apply case1WitnessOfUnitCube hm D hmeas hconv hhead
  intro i j
  have hij := ha i j
  rw [abs_of_nonneg hij.1.le]
  exact hij.2

/-- Proposition 8.5 applied to the literal section `B₀=C₀∩Ω`. -/
theorem raw_case1_bound {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {rho : ℝ} (X : Case1Witness D rho) :
    (((finrank ℝ D.C0).factorial : ENNReal) *
        ENNReal.ofReal (rho ^ (m + r - finrank ℝ D.C0))) *
        μHE[finrank ℝ D.C0] D.B0 ≤
      ((m + r).factorial : ENNReal) *
        ((2 : ENNReal) ^ (m + r) * volume B) := by
  let d := finrank ℝ D.C0
  let n := m + r
  let k := n - d
  have hdle : d ≤ n := by
    dsimp only [d, n]
    calc
      finrank ℝ D.C0 ≤ finrank ℝ (Ambient m r) := Submodule.finrank_le _
      _ = m + r := Proposition74Construction.finrank_ambient m r
  have hdadd : d + k = n := by
    dsimp only [k]
    exact Nat.add_sub_of_le hdle
  have hcoordinateRank : finrank ℝ (coordinateC0 D) = d := by
    simpa only [d] using finrank_coordinateC0 D
  have hambientRank :
      finrank ℝ (EuclideanSpace ℝ (Fin n)) = d + k := by
    simp only [finrank_euclideanSpace_fin, hdadd]
  obtain ⟨F⟩ := exists_adaptedSectionFlag d k (coordinateC0 D)
    hcoordinateRank hambientRank
  have hmain := origin_centered_linear_section_bound_of_isometric_flag
    X.rho_pos (measurableSet_coordinateDistortionBody X.measurable_B a)
    (convex_coordinateDistortionBody X.convex_B a) X.ambient_inball
    F.f F.g F.compat
  have hset :
      F.f 0 (Nat.zero_le k) ⁻¹' coordinateDistortionBody B a =
        F.initial ⁻¹' coordinateB0 D := by
    ext x
    change F.f 0 (Nat.zero_le k) x ∈ coordinateDistortionBody B a ↔
      F.initial x ∈ coordinateB0 D
    rw [F.initial_apply, mem_coordinateB0_iff]
  have himage :
      F.initial '' (F.initial ⁻¹' coordinateB0 D) = coordinateB0 D :=
    F.initial.image_preimage _
  have hinitialVolume :
      intrinsicVolume d
          (F.f 0 (Nat.zero_le k) ⁻¹' coordinateDistortionBody B a) =
        μHE[finrank ℝ D.C0] D.B0 := by
    rw [hset]
    calc
      intrinsicVolume d (F.initial ⁻¹' coordinateB0 D) =
          μHE[d] (F.initial ⁻¹' coordinateB0 D) := rfl
      _ = μHE[d] (F.initial '' (F.initial ⁻¹' coordinateB0 D)) :=
        (F.initial.isometry.euclideanHausdorffMeasure_image _).symm
      _ = μHE[d] (coordinateB0 D) := by rw [himage]
      _ = volume (coordinateB0 D) := by
        rw [← hcoordinateRank]
        rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := coordinateC0 D)]
      _ = μHE[finrank ℝ D.C0] D.B0 := volume_coordinateB0 D
  have hambientVolume :
      intrinsicVolume (d + k) (coordinateDistortionBody B a) =
        (2 : ENNReal) ^ (m + r) * volume B := by
    rw [intrinsicVolume,
      show (μHE[d + k] : Measure (EuclideanSpace ℝ (Fin n))) = volume by
        rw [← hambientRank]
        exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      volume_coordinateDistortionBody_eq X.measurable_B]
  rw [hinitialVolume, hambientVolume, hdadd] at hmain
  simpa only [d, k, n] using hmain

/-- The exact dimension/inradius factor furnished by Proposition 8.5. -/
noncomputable def case1GeometryFactor {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (rho : ℝ) : ENNReal :=
  (((finrank ℝ D.C0).factorial : ENNReal) *
      ENNReal.ofReal (rho ^ (m + r - finrank ℝ D.C0)))⁻¹ *
    ((m + r).factorial : ENNReal) * (2 : ENNReal) ^ (m + r)

/-- Bilu's explicit dimension-only constant from Proposition 8.5,
`c₈₁ = 2^(m+r) (m+r)! (m+1)^(m+r)`. -/
noncomputable def case1SourceConstant (m r : ℕ) : ENNReal :=
  (2 : ENNReal) ^ (m + r) * ((m + r).factorial : ENNReal) *
    ENNReal.ofReal (((m : ℝ) + 1) ^ (m + r))

/-- The exact geometric factor in Proposition 8.5 is at most Bilu's
uniform source constant `c₈₁`. -/
theorem case1GeometryFactor_le_sourceConstant {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    case1GeometryFactor D (((m : ℝ) + 1)⁻¹) ≤
      case1SourceConstant m r := by
  let d := finrank ℝ D.C0
  let n := m + r
  let q : ℝ := (m : ℝ) + 1
  let rho : ℝ := q⁻¹
  have hq : 0 < q := by positivity
  have hrho : 0 < rho := inv_pos.mpr hq
  have hrho_one : rho ≤ 1 := by
    rw [show rho = q⁻¹ from rfl]
    apply (inv_le_one₀ hq).2
    dsimp only [q]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hpow : rho ^ n ≤ rho ^ (n - d) :=
    pow_le_pow_of_le_one hrho.le hrho_one (Nat.sub_le n d)
  have hfactorial : (1 : ENNReal) ≤ (d.factorial : ENNReal) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos d)
  have hlower : ENNReal.ofReal (rho ^ n) ≤
      (d.factorial : ENNReal) * ENNReal.ofReal (rho ^ (n - d)) := by
    calc
      ENNReal.ofReal (rho ^ n) ≤ ENNReal.ofReal (rho ^ (n - d)) :=
        ENNReal.ofReal_le_ofReal hpow
      _ = 1 * ENNReal.ofReal (rho ^ (n - d)) := by simp
      _ ≤ (d.factorial : ENNReal) * ENNReal.ofReal (rho ^ (n - d)) := by
        gcongr
  have hinv : ((d.factorial : ENNReal) *
        ENNReal.ofReal (rho ^ (n - d)))⁻¹ ≤
      (ENNReal.ofReal (rho ^ n))⁻¹ :=
    ENNReal.inv_le_inv.mpr hlower
  have hinvpow : (ENNReal.ofReal (rho ^ n))⁻¹ =
      ENNReal.ofReal (q ^ n) := by
    rw [ENNReal.ofReal_pow hrho.le]
    have hrho_ofReal : ENNReal.ofReal rho = (ENNReal.ofReal q)⁻¹ := by
      exact ENNReal.ofReal_inv_of_pos hq
    rw [hrho_ofReal]
    calc
      (((ENNReal.ofReal q)⁻¹) ^ n)⁻¹ =
          (((ENNReal.ofReal q) ^ n)⁻¹)⁻¹ :=
        congrArg (fun x : ENNReal ↦ x⁻¹)
          (ENNReal.inv_pow (a := ENNReal.ofReal q) (n := n)).symm
      _ = (ENNReal.ofReal q) ^ n := inv_inv _
      _ = ENNReal.ofReal (q ^ n) := (ENNReal.ofReal_pow hq.le n).symm
  unfold case1GeometryFactor case1SourceConstant
  change ((d.factorial : ENNReal) * ENNReal.ofReal (rho ^ (n - d)))⁻¹ *
      (n.factorial : ENNReal) * 2 ^ n ≤
    2 ^ n * (n.factorial : ENNReal) * ENNReal.ofReal (q ^ n)
  rw [hinvpow] at hinv
  calc
    ((d.factorial : ENNReal) * ENNReal.ofReal (rho ^ (n - d)))⁻¹ *
          (n.factorial : ENNReal) * 2 ^ n ≤
        ENNReal.ofReal (q ^ n) * (n.factorial : ENNReal) * 2 ^ n := by
      gcongr
    _ = 2 ^ n * (n.factorial : ENNReal) * ENNReal.ofReal (q ^ n) := by
      ac_rfl

/-- Solved form of Proposition 8.5 for the source section. -/
theorem case1_section_volume_le {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {rho : ℝ} (X : Case1Witness D rho) :
    μHE[finrank ℝ D.C0] D.B0 ≤
      case1GeometryFactor D rho * volume B := by
  let factor : ENNReal :=
    ((finrank ℝ D.C0).factorial : ENNReal) *
      ENNReal.ofReal (rho ^ (m + r - finrank ℝ D.C0))
  let coefficient : ENNReal :=
    ((m + r).factorial : ENNReal) * (2 : ENNReal) ^ (m + r)
  have hfactor0 : factor ≠ 0 := by
    dsimp only [factor]
    apply mul_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero (finrank ℝ D.C0)
    · exact ENNReal.ofReal_ne_zero_iff.mpr
        (pow_pos X.rho_pos (m + r - finrank ℝ D.C0))
  have hfactortop : factor ≠ ∞ := by
    dsimp only [factor]
    finiteness
  have hraw : factor * μHE[finrank ℝ D.C0] D.B0 ≤
      coefficient * volume B := by
    simpa only [factor, coefficient, mul_assoc] using raw_case1_bound X
  have hsolve :=
    Section8Case2Canonical.section_le_of_factor_mul_le
      hfactor0 hfactortop hraw
  simpa only [case1GeometryFactor, factor, coefficient, mul_assoc] using hsolve

/-- **Proposition 7.5, Case 1.**  If the covolume is above the source
threshold, equivalently `1 ≤ scale * covolume`, Proposition 8.5 proves
equation (7.8) with its exact geometric factor. -/
theorem proposition75Conclusion_case1 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {rho : ℝ} (X : Case1Witness D rho)
    (scale : ENNReal)
    (hthreshold : 1 ≤ scale * ENNReal.ofReal
      (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])) :
    Proposition75Conclusion D (case1GeometryFactor D rho) scale := by
  let V0 : ENNReal := μHE[finrank ℝ D.C0] D.B0
  let covol : ENNReal := ENNReal.ofReal
    (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])
  let G : ENNReal := case1GeometryFactor D rho
  have hsection : V0 ≤ G * volume B := by
    simpa only [V0, G] using case1_section_volume_le X
  change V0 ≤ G * volume B * scale * covol
  calc
    V0 ≤ G * volume B := hsection
    _ = (G * volume B) * 1 := by simp
    _ ≤ (G * volume B) * (scale * covol) := by gcongr
    _ = G * volume B * scale * covol := by ac_rfl

/-- Enlarging the dimension-only factor preserves the Case 1 conclusion.
This is the form used when the exact factors are bounded uniformly over the
finite range of dimensions in Sections 8--9. -/
theorem proposition75Conclusion_case1_of_factor_le {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {rho : ℝ} (X : Case1Witness D rho)
    (constant scale : ENNReal)
    (hfactor : case1GeometryFactor D rho ≤ constant)
    (hthreshold : 1 ≤ scale * ENNReal.ofReal
      (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])) :
    Proposition75Conclusion D constant scale := by
  have hsmall := proposition75Conclusion_case1 X scale hthreshold
  unfold Proposition75Conclusion at hsmall ⊢
  exact hsmall.trans (by gcongr)

/-- Source-threshold form of Case 1: if `threshold ≤ covolume`, the scale
`threshold⁻¹` satisfies the multiplicative Case 1 hypothesis. -/
theorem proposition75Conclusion_case1_of_covolume_ge {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {rho : ℝ} (X : Case1Witness D rho)
    (threshold : ENNReal) (hthreshold0 : threshold ≠ 0)
    (hthresholdtop : threshold ≠ ∞)
    (hcovol : threshold ≤ ENNReal.ofReal
      (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])) :
    Proposition75Conclusion D (case1GeometryFactor D rho) threshold⁻¹ := by
  apply proposition75Conclusion_case1 X threshold⁻¹
  calc
    1 = threshold⁻¹ * threshold :=
      (ENNReal.inv_mul_cancel hthreshold0 hthresholdtop).symm
    _ ≤ threshold⁻¹ * ENNReal.ofReal
        (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0]) := by
      gcongr

end

end Erdos186.CFP.Bilu.Proposition75Case1

#print axioms Erdos186.CFP.Bilu.Proposition75Case1.raw_case1_bound
#print axioms Erdos186.CFP.Bilu.Proposition75Case1.proposition75Conclusion_case1
#print axioms
  Erdos186.CFP.Bilu.Proposition75Case1.proposition75Conclusion_case1_of_covolume_ge
