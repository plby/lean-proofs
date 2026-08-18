/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.OrthogonalTransport
import ErdosProblems.Erdos186.CFP.Bilu.Section92ShortKernel

/-!
# Bilu Section 9.2: the projected gauge body

This file supplies the analytic half of the primitive-kernel descent.  A
primitive generator is selected from the saturated integral direction, the
old seminorm ball is projected orthogonally away from that direction, and
the projected compact convex body is made into the unit ball of a definite
seminorm on a space of rank one less.
-/

namespace Erdos186.CFP.Bilu.Section92ProjectedGauge

open scoped ENNReal Pointwise RealInnerProductSpace
open Module Submodule Set MeasureTheory Filter
open Mahler MinkowskiUpper VolumeSections Section92ShortKernel

noncomputable section

variable {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
  {phi : IntegralPoint n →+ ℤ} {T : ℝ}

namespace PrimitiveIntegralQuotient

/-- A chosen primitive integral generator of the saturated kernel line. -/
def primitiveGenerator {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) : IntegralPoint n :=
  (Q.primitiveBasis 0 : primitiveDirection q)

theorem primitiveGenerator_mem {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) :
    primitiveGenerator Q ∈ primitiveDirection q :=
  (Q.primitiveBasis 0).property

theorem primitiveGenerator_ne_zero {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) :
    primitiveGenerator Q ≠ 0 := by
  intro hzero
  have hbzero : Q.primitiveBasis (0 : Fin 1) = 0 := by
    apply Subtype.ext
    exact hzero
  have hrepr := congrArg (fun x ↦ Q.primitiveBasis.repr x (0 : Fin 1)) hbzero
  simpa using hrepr

/-- The original short vector is an integral multiple of the selected
primitive generator. -/
theorem exists_smul_primitiveGenerator {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) :
    ∃ a : ℤ, q = a • primitiveGenerator Q := by
  let qp : primitiveDirection q := ⟨q, mem_primitiveDirection q⟩
  let a : ℤ := Q.primitiveBasis.repr qp 0
  refine ⟨a, ?_⟩
  have hsum := Q.primitiveBasis.sum_repr qp
  have hone : (∑ i : Fin 1, (Q.primitiveBasis.repr qp i) •
      Q.primitiveBasis i) = a • Q.primitiveBasis 0 := by
    simp [a]
  rw [hone] at hsum
  exact congrArg Subtype.val hsum.symm

/-- Dividing by the integral content can only shorten a seminorm. -/
theorem seminorm_primitiveGenerator_le {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) (hq : q ≠ 0) :
    p (integralEmbed (primitiveGenerator Q)) ≤ p (integralEmbed q) := by
  obtain ⟨a, ha⟩ := exists_smul_primitiveGenerator Q
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hq
    rw [ha, ha0, zero_smul]
  have haabs : (1 : ℝ) ≤ |(a : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha0
  have hembed : integralEmbed q = (a : ℝ) •
      integralEmbed (primitiveGenerator Q) := by
    ext i
    have hi := congrFun ha i
    change (q i : ℝ) = (a : ℝ) * (primitiveGenerator Q i : ℝ)
    exact_mod_cast hi
  rw [hembed, map_smul_eq_mul]
  exact le_mul_of_one_le_left (apply_nonneg p _) haabs

theorem map_primitiveGenerator_eq_zero {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) :
    phi (primitiveGenerator Q) = 0 := by
  change primitiveGenerator Q ∈ LinearMap.ker phi.toIntLinearMap
  exact Q.direction_le_ker (primitiveGenerator_mem Q)

end PrimitiveIntegralQuotient

namespace PrimitiveKernelStep

/-- The old seminorm transported to its canonical Euclidean-space copy. -/
def euclideanSeminorm (S : PrimitiveKernelStep p phi T) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  p.comp (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

/-- The transported closed unit ball. -/
def euclideanUnitBall (S : PrimitiveKernelStep p phi T) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (euclideanSeminorm S).closedBall 0 1

theorem isCompact_euclideanUnitBall (S : PrimitiveKernelStep p phi T)
    (hp : IsDefinite p) : IsCompact (euclideanUnitBall S) := by
  have hpreimage : euclideanUnitBall S =
      (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' unitBall p := by
    ext x
    simp [euclideanUnitBall, euclideanSeminorm, unitBall,
      Seminorm.mem_closedBall]
  rw [hpreimage]
  exact (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.mpr
    (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_unitBall p, isBounded_unitBall p hp⟩)

/-- The selected primitive vector in Euclidean coordinates. -/
def primitiveReal (S : PrimitiveKernelStep p phi T) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (integralEmbed (PrimitiveIntegralQuotient.primitiveGenerator S.quotient))

theorem primitiveReal_ne_zero (S : PrimitiveKernelStep p phi T) :
    primitiveReal S ≠ 0 := by
  intro hzero
  apply PrimitiveIntegralQuotient.primitiveGenerator_ne_zero S.quotient
  funext i
  have hembed : integralEmbed
      (PrimitiveIntegralQuotient.primitiveGenerator S.quotient) = 0 := by
    have := congrArg (EuclideanSpace.equiv (Fin n) ℝ) hzero
    simpa [primitiveReal] using this
  have hi := congrFun hembed i
  exact Int.cast_eq_zero.mp hi

@[simp] theorem euclideanSeminorm_primitiveReal
    (S : PrimitiveKernelStep p phi T) :
    euclideanSeminorm S (primitiveReal S) =
      p (integralEmbed
        (PrimitiveIntegralQuotient.primitiveGenerator S.quotient)) := by
  change p ((EuclideanSpace.equiv (Fin n) ℝ)
    ((EuclideanSpace.equiv (Fin n) ℝ).symm
      (integralEmbed
        (PrimitiveIntegralQuotient.primitiveGenerator S.quotient)))) = _
  rw [(EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply]

theorem euclideanSeminorm_primitiveReal_le_short
    (S : PrimitiveKernelStep p phi T) :
    euclideanSeminorm S (primitiveReal S) ≤
      p (integralEmbed S.short.vector) := by
  rw [euclideanSeminorm_primitiveReal]
  exact PrimitiveIntegralQuotient.seminorm_primitiveGenerator_le
    S.quotient S.short.ne_zero

theorem euclideanSeminorm_primitiveReal_le_two_mul
    (S : PrimitiveKernelStep p phi T) :
    euclideanSeminorm S (primitiveReal S) ≤ 2 * T :=
  (euclideanSeminorm_primitiveReal_le_short S).trans S.short.seminorm_le

/-- The real quotient space perpendicular to the primitive direction. -/
def projectedSpace (S : PrimitiveKernelStep p phi T) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (ℝ ∙ primitiveReal S)ᗮ

theorem finrank_projectedSpace (S : PrimitiveKernelStep p phi T) :
    finrank ℝ (projectedSpace S) = S.quotient.complementRank := by
  have hsum := (ℝ ∙ primitiveReal S).finrank_add_finrank_orthogonal
  have hline : finrank ℝ (ℝ ∙ primitiveReal S) = 1 :=
    finrank_span_singleton (primitiveReal_ne_zero S)
  have hambient : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  rw [hline, hambient] at hsum
  have hsum' : 1 + finrank ℝ (projectedSpace S) = n := by
    change 1 + finrank ℝ (projectedSpace S) = n at hsum
    exact hsum
  have hrank := S.quotient.rank_eq
  omega

theorem complementRank_eq_pred (hn : 0 < n)
    (S : PrimitiveKernelStep p phi T) :
    S.quotient.complementRank = n - 1 := by
  have hrank := S.quotient.rank_eq
  omega

/-- An isometric coordinate identification of the quotient space with
`Fin complementRank`. -/
def projectedEquiv (S : PrimitiveKernelStep p phi T) :
    projectedSpace S ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin S.quotient.complementRank) :=
  ((stdOrthonormalBasis ℝ (projectedSpace S)).reindex
    (finCongr (finrank_projectedSpace S))).repr

/-- The old unit ball after orthogonal projection and rank-normalizing
isometric coordinates. -/
def projectedBody (S : PrimitiveKernelStep p phi T) :
    Set (EuclideanSpace ℝ (Fin S.quotient.complementRank)) :=
  projectedEquiv S ''
    ((ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto ''
      euclideanUnitBall S)

theorem isCompact_projectedBody (S : PrimitiveKernelStep p phi T)
    (hp : IsDefinite p) : IsCompact (projectedBody S) := by
  have hpreimage : euclideanUnitBall S =
      (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹'
        unitBall p := by
    ext x
    simp [euclideanUnitBall, euclideanSeminorm, unitBall,
      Seminorm.mem_closedBall]
  have hcompact : IsCompact (euclideanUnitBall S) := by
    rw [hpreimage]
    exact (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.mpr
      (Metric.isCompact_iff_isClosed_bounded.mpr
        ⟨isClosed_unitBall p, isBounded_unitBall p hp⟩)
  exact (hcompact.image
    (ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto.continuous).image
      (projectedEquiv S).continuous

theorem intrinsicVolume_projectedBody
    (S : PrimitiveKernelStep p phi T) :
    intrinsicVolume S.quotient.complementRank (projectedBody S) =
      intrinsicVolume S.quotient.complementRank
        ((projectedSpace S).orthogonalProjectionOnto ''
          euclideanUnitBall S) := by
  exact (projectedEquiv S).isometry.euclideanHausdorffMeasure_image
    (d := S.quotient.complementRank)
    ((projectedSpace S).orthogonalProjectionOnto '' euclideanUnitBall S)

theorem intrinsicVolume_projectedBody_eq_volume
    (S : PrimitiveKernelStep p phi T) :
    intrinsicVolume S.quotient.complementRank (projectedBody S) =
      volume (projectedBody S) := by
  unfold intrinsicVolume
  have hmeasure :
      (μHE[S.quotient.complementRank] :
          Measure (EuclideanSpace ℝ (Fin S.quotient.complementRank))) =
        volume := by
    simpa using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
        (V := EuclideanSpace ℝ (Fin S.quotient.complementRank)))
  rw [hmeasure]

theorem intrinsicVolume_euclideanUnitBall_eq_volume
    (S : PrimitiveKernelStep p phi T) :
    intrinsicVolume n (euclideanUnitBall S) =
      volume (euclideanUnitBall S) := by
  unfold intrinsicVolume
  have hmeasure :
      (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) = volume := by
    simpa using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
        (V := EuclideanSpace ℝ (Fin n)))
  rw [hmeasure]

theorem volume_euclideanUnitBall_eq_unitBall
    (S : PrimitiveKernelStep p phi T) :
    volume (euclideanUnitBall S) = volume (unitBall p) := by
  have hpreimage : euclideanUnitBall S =
      (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' unitBall p := by
    ext x
    simp [euclideanUnitBall, euclideanSeminorm, unitBall,
      Seminorm.mem_closedBall]
  rw [hpreimage]
  exact (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (isClosed_unitBall p).measurableSet.nullMeasurableSet

theorem convex_projectedBody (S : PrimitiveKernelStep p phi T) :
    Convex ℝ (projectedBody S) := by
  exact (((euclideanSeminorm S).convex_closedBall 0 1).linear_image
    (ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto.toLinearMap).linear_image
      (projectedEquiv S).toLinearEquiv.toLinearMap

theorem zero_mem_projectedBody (S : PrimitiveKernelStep p phi T) :
    0 ∈ projectedBody S := by
  refine ⟨0, ⟨0, by simp [euclideanUnitBall], ?_⟩, ?_⟩
  · exact map_zero _
  · exact map_zero _

theorem projectedBody_mem_nhds_zero (S : PrimitiveKernelStep p phi T)
    (hp : IsDefinite p) : projectedBody S ∈ nhds 0 := by
  let f := (ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto.toLinearMap
  have hfSurj : Function.Surjective f := by
    intro y
    refine ⟨(y : EuclideanSpace ℝ (Fin n)), ?_⟩
    exact Subtype.ext (by simp [f])
  have hfOpen : IsOpenMap f := f.isOpenMap_of_finiteDimensional hfSurj
  let g := (projectedEquiv S).toLinearMap.comp f
  have hgSurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hfSurj ((projectedEquiv S).symm y)
    refine ⟨x, ?_⟩
    change projectedEquiv S (f x) = y
    rw [hx, (projectedEquiv S).apply_symm_apply]
  have hgOpen : IsOpenMap g := g.isOpenMap_of_finiteDimensional hgSurj
  have hpEContinuous : Continuous (euclideanSeminorm S) :=
    (seminorm_continuous_pi p).comp
      (EuclideanSpace.equiv (Fin n) ℝ).continuous
  have hopenBall : (euclideanSeminorm S).ball 0 1 ∈
      nhds (0 : EuclideanSpace ℝ (Fin n)) :=
    Seminorm.ball_mem_nhds hpEContinuous zero_lt_one
  have himageOpen : f '' (euclideanSeminorm S).ball 0 1 ∈
      nhds (0 : projectedSpace S) := by
    change f '' (euclideanSeminorm S).ball 0 1 ∈
      nhds (0 : (ℝ ∙ primitiveReal S)ᗮ)
    simpa only [map_zero] using hfOpen.image_mem_nhds hopenBall
  have hcoordOpen : projectedEquiv S ''
      (f '' (euclideanSeminorm S).ball 0 1) ∈ nhds 0 := by
    have hgImage : g '' (euclideanSeminorm S).ball 0 1 =
        projectedEquiv S '' (f '' (euclideanSeminorm S).ball 0 1) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [← hgImage]
    simpa only [map_zero] using hgOpen.image_mem_nhds hopenBall
  apply mem_of_superset hcoordOpen
  apply Set.image_mono
  apply Set.image_mono
  intro x hx
  rw [Seminorm.mem_ball] at hx
  unfold euclideanUnitBall
  rw [Seminorm.mem_closedBall]
  exact hx.le

/-- The reduced seminorm is the Minkowski functional of the projected
compact convex body. -/
def projectedSeminorm (S : PrimitiveKernelStep p phi T)
    (hp : IsDefinite p) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin S.quotient.complementRank)) :=
  gaugeSeminorm
    (by
      apply balanced_iff_smul_mem.mpr
      intro a ha x hx
      change x ∈ projectedEquiv S ''
        ((ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto ''
          euclideanUnitBall S) at hx
      change a • x ∈ projectedEquiv S ''
        ((ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto ''
          euclideanUnitBall S)
      obtain ⟨y, hy, hxy⟩ := hx
      subst x
      obtain ⟨z, hz, hyz⟩ := hy
      subst y
      refine ⟨a •
        (ℝ ∙ primitiveReal S)ᗮ.orthogonalProjectionOnto z, ?_, ?_⟩
      · refine ⟨a • z, ?_, ?_⟩
        · apply ((euclideanSeminorm S).balanced_closedBall_zero 1).smul_mem ha
          exact hz
        · exact map_smul _ _ _
      · exact map_smul _ _ _
    )
    (convex_projectedBody S)
    (absorbent_nhds_zero (projectedBody_mem_nhds_zero S hp))

theorem unitBall_projectedSeminorm
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    {x | projectedSeminorm S hp x ≤ 1} = projectedBody S := by
  ext x
  change gauge (projectedBody S) x ≤ 1 ↔ x ∈ projectedBody S
  rw [gauge_le_one_iff_mem_closure (convex_projectedBody S)
    (projectedBody_mem_nhds_zero S hp)]
  rw [(isCompact_projectedBody S hp).isClosed.closure_eq]

theorem isDefinite_projectedSeminorm
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    ∀ x, projectedSeminorm S hp x = 0 → x = 0 := by
  intro x hx
  apply (gauge_eq_zero
    (absorbent_nhds_zero (projectedBody_mem_nhds_zero S hp))
    (NormedSpace.isVonNBounded_of_isBounded ℝ
      (isCompact_projectedBody S hp).isBounded)).mp
  exact hx

/-- A positive Euclidean ball sits inside the transported seminorm ball.
This records the inball needed by the source Lemma 6.6 wrapper without
exporting an auxiliary radius in the kernel-reduction interface. -/
theorem exists_closedBall_subset_euclideanUnitBall
    (S : PrimitiveKernelStep p phi T) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆
        euclideanUnitBall S := by
  have hpEContinuous : Continuous (euclideanSeminorm S) :=
    (seminorm_continuous_pi p).comp
      (EuclideanSpace.equiv (Fin n) ℝ).continuous
  have hopenBall : (euclideanSeminorm S).ball 0 1 ∈
      nhds (0 : EuclideanSpace ℝ (Fin n)) :=
    Seminorm.ball_mem_nhds hpEContinuous zero_lt_one
  have hunitNhds : euclideanUnitBall S ∈
      nhds (0 : EuclideanSpace ℝ (Fin n)) := by
    apply mem_of_superset hopenBall
    intro x hx
    rw [Seminorm.mem_ball] at hx
    unfold euclideanUnitBall
    rw [Seminorm.mem_closedBall]
    exact hx.le
  exact Metric.nhds_basis_closedBall.mem_iff.mp hunitNhds

/-- Lemma 6.6 applied to the primitive kernel direction and the transported
old unit ball.  This is the sharp analytic projection estimate before the
projected lattice covolume is expressed in complement coordinates. -/
theorem lemma66Conclusion_euclideanUnitBall (hn : 0 < n)
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    Lemma66Conclusion (euclideanUnitBall S) (euclideanSeminorm S)
      (primitiveReal S) := by
  obtain ⟨ρ, hρ, hball⟩ := exists_closedBall_subset_euclideanUnitBall S
  apply lemma66_compact_seminorm_unitBall hn
    (euclideanUnitBall S) (euclideanSeminorm S) (primitiveReal S)
    (primitiveReal_ne_zero S)
    ((euclideanSeminorm S).convex_closedBall 0 1)
    (isCompact_euclideanUnitBall S hp)
    hρ hball
  ext x
  simp [euclideanUnitBall, Seminorm.mem_closedBall]

/-- The same sharp estimate with the primitive seminorm factor enlarged to
the seminorm of the original short kernel vector. -/
theorem lemma66Conclusion_le_short (hn : 0 < n)
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    (2 : ENNReal) * ENNReal.ofReal ‖primitiveReal S‖ *
        intrinsicVolume (n - 1)
          ((projectedSpace S).orthogonalProjectionOnto ''
            euclideanUnitBall S) ≤
      (n : ENNReal) * ENNReal.ofReal
          (p (integralEmbed S.short.vector)) *
        intrinsicVolume n (euclideanUnitBall S) := by
  apply (lemma66Conclusion_euclideanUnitBall hn S hp).trans
  gcongr
  exact euclideanSeminorm_primitiveReal_le_short S

/-- Coordinate form of the projected-volume estimate: the quotient body is
the exact unit ball of `projectedSeminorm`, and its dimension is one less
than the old rank. -/
theorem projectedBody_intrinsicVolume_bound (hn : 0 < n)
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    (2 : ENNReal) * ENNReal.ofReal ‖primitiveReal S‖ *
        intrinsicVolume S.quotient.complementRank (projectedBody S) ≤
      (n : ENNReal) * ENNReal.ofReal
          (p (integralEmbed S.short.vector)) *
        intrinsicVolume n (euclideanUnitBall S) := by
  rw [intrinsicVolume_projectedBody]
  simpa only [complementRank_eq_pred hn S] using
    lemma66Conclusion_le_short hn S hp

/-- Lebesgue-volume form of the quotient estimate, with the old ball
transported back to the original `Fin n → ℝ` coordinates. -/
theorem projectedBody_volume_bound (hn : 0 < n)
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    (2 : ENNReal) * ENNReal.ofReal ‖primitiveReal S‖ *
        volume (projectedBody S) ≤
      (n : ENNReal) * ENNReal.ofReal
          (p (integralEmbed S.short.vector)) * volume (unitBall p) := by
  have h := projectedBody_intrinsicVolume_bound hn S hp
  rw [intrinsicVolume_projectedBody_eq_volume,
    intrinsicVolume_euclideanUnitBall_eq_volume,
    volume_euclideanUnitBall_eq_unitBall] at h
  exact h

/-- Coarse form using the defining `2*T` length bound on the selected
short kernel vector. -/
theorem projectedBody_volume_bound_two_mul (hn : 0 < n)
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    (2 : ENNReal) * ENNReal.ofReal ‖primitiveReal S‖ *
        volume (projectedBody S) ≤
      (n : ENNReal) * ENNReal.ofReal (2 * T) * volume (unitBall p) := by
  apply (projectedBody_volume_bound hn S hp).trans
  gcongr
  exact S.short.seminorm_le

end PrimitiveKernelStep

end

end Erdos186.CFP.Bilu.Section92ProjectedGauge
