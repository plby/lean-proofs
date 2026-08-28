import Wikipedia.HopfProblem.CuspRetractionPolar
import Wikipedia.HopfProblem.ToricHexagon
import Wikipedia.HopfProblem.CuspComponentProper
import Wikipedia.HopfProblem.CuspProper

/-!
# The literal positive zero component and its bounded affine charts

The positive component is the intersection of the actual ray divisor with
the actual modulus-fixed locus. Its topology and compactness are inherited
from the toric space. The bounded-chart result below uses the established
zero-twist compact representatives and then translates back; it does not
assume a polygon or moment-map description.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open ToricCharts ToricFan ToricSpace ToricComponent

def positiveComponentSet (v : Fin 2 → ℤ) : Set (rayDivisor v) :=
  Subtype.val ⁻¹' positivePart

abbrev PositiveComponent (v : Fin 2 → ℤ) := positiveComponentSet v

/-- The positive part of the actual zero ray component `E₀`. -/
abbrev PositiveE0 := PositiveComponent 0

theorem positiveComponentSet_isClosed (v : Fin 2 → ℤ) :
    IsClosed (positiveComponentSet v) :=
  positivePart_isClosed.preimage continuous_subtype_val

instance positiveComponent_compactSpace (v : Fin 2 → ℤ) :
    CompactSpace (PositiveComponent v) :=
  isCompact_iff_compactSpace.mp (positiveComponentSet_isClosed v).isCompact

theorem modulus_mem_rayDivisor_iff (v : Fin 2 → ℤ) (x : Space) :
    modulus x ∈ rayDivisor v ↔ x ∈ rayDivisor v := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [modulus_inclusion, mem_rayDivisor_inclusion, mem_rayDivisor_inclusion]
  simp [coordinateModulus]

def componentModulus (v : Fin 2 → ℤ) (x : rayDivisor v) : rayDivisor v :=
  ⟨modulus x, (modulus_mem_rayDivisor_iff v x).mpr x.property⟩

def positiveComponentRetraction (v : Fin 2 → ℤ) (x : rayDivisor v) : PositiveComponent v :=
  ⟨componentModulus v x, modulus_mem_positivePart x⟩

theorem positiveComponentRetraction_continuous (v : Fin 2 → ℤ) :
    Continuous (positiveComponentRetraction v) :=
  ((modulus_continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _

@[simp] theorem positiveComponentRetraction_subtype_val (v : Fin 2 → ℤ)
    (x : PositiveComponent v) : positiveComponentRetraction v x.1 = x :=
  Subtype.ext (Subtype.ext x.property)

theorem coordinateModulus_insertZero (j : Fin 3) (z : CoordinateSpace 2) :
    coordinateModulus (insertZero j z) = insertZero j (coordinateModulus z) := by
  funext k
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simp [coordinateModulus]
  · simp [coordinateModulus, insertZero, Fin.insertNth_apply_succAbove]

theorem affineInclusion_mem_positive_iff {v : Fin 2 → ℤ} (c : ChartIndex v)
    (z : CoordinateSpace 2) :
    affineInclusion c z ∈ positiveComponentSet v ↔ z ∈ nonnegativeCoordinates := by
  change modulus (inclusion c.triangle (insertZero c.coordinate z)) =
    inclusion c.triangle (insertZero c.coordinate z) ↔ _
  rw [modulus_inclusion, coordinateModulus_insertZero,
    (inclusion_openEmbedding c.triangle).injective.eq_iff,
    ← coordinateModulus_eq_self_iff]
  constructor
  · intro h
    simpa only [removeCoordinate_insertZero] using congrArg (removeCoordinate c.coordinate) h
  · intro h
    exact congrArg (insertZero c.coordinate) h

abbrev PositiveQuadrant := {r : Fin 2 → ℝ // ∀ i, 0 ≤ r i}

def positiveAffineInclusion {v : Fin 2 → ℤ} (c : ChartIndex v) (r : PositiveQuadrant) :
    PositiveComponent v :=
  ⟨affineInclusion c (fun i => (r.1 i : ℂ)),
    (affineInclusion_mem_positive_iff c _).mpr ⟨r.1, r.2, rfl⟩⟩

@[simp] theorem positiveAffineInclusion_coe {v : Fin 2 → ℤ} (c : ChartIndex v)
    (r : PositiveQuadrant) :
    (positiveAffineInclusion c r : rayDivisor v) =
      affineInclusion c (fun i => (r.1 i : ℂ)) := rfl

theorem positiveAffineInclusion_continuous {v : Fin 2 → ℤ} (c : ChartIndex v) :
    Continuous (positiveAffineInclusion c) := by
  have h : Continuous (fun r : PositiveQuadrant => fun i => (r.1 i : ℂ)) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp continuous_subtype_val)
  exact ((affineInclusion_openEmbedding c).continuous.comp h).subtype_mk _

theorem positiveAffineInclusion_jointly_surjective {v : Fin 2 → ℤ}
    (x : PositiveComponent v) :
    ∃ (c : ChartIndex v) (r : PositiveQuadrant), positiveAffineInclusion c r = x := by
  obtain ⟨c, z, hz⟩ := affineInclusion_jointly_surjective x.1
  have hp : affineInclusion c z ∈ positiveComponentSet v := hz.symm ▸ x.2
  obtain ⟨r, hr, he⟩ := (affineInclusion_mem_positive_iff c z).mp hp
  refine ⟨c, ⟨r, hr⟩, Subtype.ext ?_⟩
  change affineInclusion c (fun i => (r i : ℂ)) = x.1
  rw [← he]
  exact hz

theorem positiveZeroChart_jointly_surjective (x : PositiveE0) :
    ∃ (i : Fin 6) (r : PositiveQuadrant), positiveAffineInclusion (zeroChart i) r = x := by
  obtain ⟨c, r, hr⟩ := positiveAffineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  exact ⟨i, r, hr⟩

theorem twistedTranslate_zero_correction (v : Fin 2 → ℤ) (x : Space) :
    twistedTranslate (fun _ => 0) v x = translate (cuspVector v) x := by
  have he : exponentialMultiplier (fun _ => 0) v = fun _ => 1 := by
    funext t
    ext i
    simp [exponentialMultiplier]
  simp [twistedTranslate, he]

/-- Every point of the actual zero component has a coordinate chart in
which both coordinates lie in the complex closed unit disc. -/
theorem zeroComponent_bounded_chart (x : rayDivisor 0) :
    ∃ (i : Fin 6) (z : CoordinateSpace 2),
      ‖z‖ ≤ 1 ∧ affineInclusion (zeroChart i) z = x := by
  let C : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 0
  have hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 (1 : ℝ)) :=
    fun _ _ => contDiffOn_const
  obtain ⟨ε, hε, _, hε1, hR, hCε⟩ :=
    CuspQuotient.exists_admissible_radius C (by norm_num) hC
  let a : Tube (CuspQuotient.disc ε) := CuspQuotient.componentLift ε hε x
  have ha0 : time (a : Space) = 0 := time_eq_zero_of_mem_rayDivisor x.2
  have hrep := CuspQuotient.mem_quotientRepresentatives C ε hε hε1 hCε hR
    (half_pos hε) (half_lt_self hε) (x := a) (by
      rw [ha0, norm_zero]
      exact (half_pos hε).le)
  obtain ⟨b, hb, hba⟩ := hrep
  let := tubeAction C (CuspQuotient.disc ε)
  have horb := Quotient.exact hba
  change b ∈ MulAction.orbit CuspQuotient.LatticeGroup a at horb
  obtain ⟨g, hg⟩ := horb
  have hgb : translate (cuspVector g.toAdd) (x : Space) = (b : Space) := by
    have h := congrArg Subtype.val hg
    change twistedTranslate C g.toAdd (x : Space) = (b : Space) at h
    rwa [show C = (fun _ => 0) from rfl, twistedTranslate_zero_correction] at h
  change (b : Space) ∈ CuspQuotient.compactRepresentatives (ε / 2) at hb
  obtain ⟨s, _hs, z, hz, hzb⟩ := Set.mem_iUnion₂.mp hb
  have hx : inclusion (s.shift (-cuspVector g.toAdd)) z = (x : Space) := by
    rw [← translate_inclusion, hzb, ← hgb, translate_add]
    simp
  obtain ⟨j, hj, hv⟩ := (mem_rayDivisor_inclusion 0 _ z).mp (hx.symm ▸ x.2)
  let c : ChartIndex 0 := ⟨s.shift (-cuspVector g.toAdd), j, hv⟩
  obtain ⟨i, hi⟩ := zeroChart_surjective c
  refine ⟨i, removeCoordinate j z, ?_, ?_⟩
  · have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro k
    exact (norm_le_pi_norm z (j.succAbove k)).trans hz1
  · rw [hi]
    apply Subtype.ext
    change inclusion (s.shift (-cuspVector g.toAdd)) (insertZero j (removeCoordinate j z)) =
      (x : Space)
    rw [insertZero_removeCoordinate j z hj]
    exact hx

/-- The six literal positive unit squares cover the positive component. -/
theorem positiveE0_bounded_chart (x : PositiveE0) :
    ∃ (i : Fin 6) (r : PositiveQuadrant),
      (∀ k, r.1 k ≤ 1) ∧ positiveAffineInclusion (zeroChart i) r = x := by
  obtain ⟨i, z, hz, he⟩ := zeroComponent_bounded_chart x.1
  have hp : affineInclusion (zeroChart i) z ∈ positiveComponentSet 0 := he.symm ▸ x.2
  obtain ⟨r, hr, hzr⟩ := (affineInclusion_mem_positive_iff (zeroChart i) z).mp hp
  refine ⟨i, ⟨r, hr⟩, ?_, Subtype.ext ?_⟩
  · intro k
    have hk := (norm_le_pi_norm z k).trans hz
    rwa [hzr, Complex.norm_of_nonneg (hr k)] at hk
  · change affineInclusion (zeroChart i) (fun k => (r k : ℂ)) = x.1
    rw [← hzr]
    exact he

end Wikipedia.HopfProblem.CuspHoneycombHexagon
