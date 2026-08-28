import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelShear
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseTopology

/-!
# Homotoping the actual source-phase shear on the theta boundary

On each oriented theta edge, interpolate the planar argument of the actual
source phase character from zero to its original value. The suspension
collapses both endpoint circles, so the interpolation respects the literal
theta identifications even when distinct edges have different planar
endpoint representatives. Continuity descends through that same quotient.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The explicit interpolated character on one oriented edge cylinder. -/
def thetaShearCylinder (s : unitInterval) (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) : ThreeCircleSuspension :=
  Suspension.mk t (thetaCircleInclusion j
    (hexagonCharacter (thetaEdgeIndex j)
      (u * SpecializationModel.sourcePhaseCharacter C₀
        ((s : ℝ) • orientedEdgeBasePoint t j))))

theorem thetaShearCylinder_respects (s : unitInterval) (u : CompactFibreTorus)
    (p q : unitInterval × Fin 3) (hpq : (suspensionSetoid (Fin 3)).r p q) :
    thetaShearCylinder C₀ s u p.1 p.2 = thetaShearCylinder C₀ s u q.1 q.2 := by
  apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
  rcases hpq with ⟨ht, hzero | hone | hj⟩
  · exact ⟨ht, Or.inl hzero⟩
  · exact ⟨ht, Or.inr (Or.inl hone)⟩
  · refine ⟨ht, Or.inr (Or.inr ?_)⟩
    rw [ht, hj]

private def thetaShearLiftFun (p : (unitInterval × CompactFibreTorus) × Theta) :
    ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid (Fin 3))
    (fun q => thetaShearCylinder C₀ p.1.1 p.1.2 q.1 q.2)
    (thetaShearCylinder_respects C₀ p.1.1 p.1.2) p.2

@[simp] private theorem thetaShearLiftFun_mk (s : unitInterval) (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaShearLiftFun C₀ ((s, u), Suspension.mk t j) = thetaShearCylinder C₀ s u t j := rfl

/-- Joint continuity on the actual edge cylinders before taking the
suspension quotient. The finite edge label has its existing discrete topology. -/
theorem thetaShearCylinder_continuous :
    Continuous (fun p : (unitInterval × CompactFibreTorus) × (unitInterval × Fin 3) =>
      thetaShearCylinder C₀ p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h : Continuous
      (fun p : ((unitInterval × CompactFibreTorus) × unitInterval) × Fin 3 =>
        Suspension.mk p.1.2
          (thetaCircleInclusion p.2
            (hexagonCharacter (thetaEdgeIndex p.2)
              (p.1.1.2 * SpecializationModel.sourcePhaseCharacter C₀
                ((p.1.1.1 : ℝ) • orientedEdgeBasePoint p.1.2 p.2))))) := by
    apply continuous_prod_of_discrete_right.mpr
    intro j
    exact Suspension.continuous_mk.comp
      (continuous_snd.prodMk
        ((thetaCircleInclusion_continuous j).comp
          ((edgeCharacter_continuous (hexagonRay (thetaEdgeIndex j))).comp
            ((continuous_snd.comp continuous_fst).mul
              ((SpecializationModel.sourcePhaseCharacter_continuous C₀).comp
                ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
                  ((orientedEdgeBasePoint_continuous j).comp continuous_snd)))))))
  exact h.comp
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))

private theorem thetaShearLiftFun_continuous : Continuous (thetaShearLiftFun C₀) := by
  apply (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_lift_prod_right
  change Continuous (fun p : (unitInterval × CompactFibreTorus) × (unitInterval × Fin 3) =>
    thetaShearCylinder C₀ p.1.1 p.1.2 p.2.1 p.2.2)
  exact thetaShearCylinder_continuous C₀

/-- The time-dependent shear, with the homotopy interval placed first. -/
def thetaShearMap : C(unitInterval × (CompactFibreTorus × Theta), ThreeCircleSuspension) where
  toFun p := thetaShearLiftFun C₀ ((p.1, p.2.1), p.2.2)
  continuous_toFun := (thetaShearLiftFun_continuous C₀).comp
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))

@[simp] theorem thetaShearMap_mk (s : unitInterval) (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaShearMap C₀ (s, (u, Suspension.mk t j)) = thetaShearCylinder C₀ s u t j := rfl

@[simp] theorem thetaShearMap_zero (p : CompactFibreTorus × Theta) :
    thetaShearMap C₀ (0, p) = thetaCharacterCollapse p := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaShearMap_mk]
  simp [thetaShearCylinder]

/-- The actual source-phase shear at its full planar argument. -/
def shearedThetaCollapse : C(CompactFibreTorus × Theta, ThreeCircleSuspension) :=
  (thetaShearMap C₀).comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩

@[simp] theorem shearedThetaCollapse_mk (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    shearedThetaCollapse C₀ (u, Suspension.mk t j) =
      Suspension.mk t (thetaCircleInclusion j
        (hexagonCharacter (thetaEdgeIndex j)
          (u * SpecializationModel.sourcePhaseCharacter C₀ (orientedEdgeBasePoint t j)))) := by
  change Suspension.mk t (thetaCircleInclusion j
    (hexagonCharacter (thetaEdgeIndex j)
      (u * SpecializationModel.sourcePhaseCharacter C₀
        ((1 : ℝ) • orientedEdgeBasePoint t j)))) = _
  rw [one_smul]

/-- Scaling the planar argument of the genuine source phase gives an
actual homotopy from the original character collapse to its sheared form. -/
def thetaShearHomotopy : thetaCharacterCollapse.Homotopy (shearedThetaCollapse C₀) where
  toContinuousMap := thetaShearMap C₀
  map_zero_left := thetaShearMap_zero C₀
  map_one_left _ := rfl

@[simp] theorem thetaShearHomotopy_mk (s : unitInterval) (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaShearHomotopy C₀ (s, (u, Suspension.mk t j)) =
      Suspension.mk t (thetaCircleInclusion j
        (hexagonCharacter (thetaEdgeIndex j)
          (u * SpecializationModel.sourcePhaseCharacter C₀
            ((s : ℝ) • orientedEdgeBasePoint t j)))) := rfl

@[simp] theorem thetaShearHomotopy_north (s : unitInterval) (u : CompactFibreTorus) :
    thetaShearHomotopy C₀ (s, (u, Suspension.north)) = Suspension.north := by
  simpa only [Suspension.mk_zero] using thetaShearHomotopy_mk C₀ s u 0 0

@[simp] theorem thetaShearHomotopy_south (s : unitInterval) (u : CompactFibreTorus) :
    thetaShearHomotopy C₀ (s, (u, Suspension.south)) = Suspension.south := by
  simpa only [Suspension.mk_one] using thetaShearHomotopy_mk C₀ s u 1 0

end Wikipedia.HopfProblem.CuspCentralHomology
