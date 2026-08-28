import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Forgetting the circles in the actual three-circle suspension

The circle-label map descends through the literal suspension quotients to the
three-edge theta graph. It keeps height and the two poles, and its composite
with the actual character collapse is the second product projection. The
theta graph's higher singular homology vanishes by the proved suspension
Mayer--Vietoris sequence and actual homology of the discrete three-point set.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

/-- The labels of the three actual circle summands. -/
def thetaCircleLabel : C(ThreeCircles, Fin 3) where
  toFun := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  continuous_toFun := continuous_const.sumElim
    (continuous_const.sumElim continuous_const)

@[simp] theorem thetaCircleLabel_inl (z : _root_.Circle) :
    thetaCircleLabel (Sum.inl z) = 0 := rfl

@[simp] theorem thetaCircleLabel_inr_inl (z : _root_.Circle) :
    thetaCircleLabel (Sum.inr (Sum.inl z)) = 1 := rfl

@[simp] theorem thetaCircleLabel_inr_inr (z : _root_.Circle) :
    thetaCircleLabel (Sum.inr (Sum.inr z)) = 2 := rfl

@[simp] theorem thetaCircleLabel_inclusion (j : Fin 3) (z : _root_.Circle) :
    thetaCircleLabel (thetaCircleInclusion j z) = j := by
  fin_cases j <;> rfl

private def thetaForgetCircleFun : ThreeCircleSuspension → Theta :=
  Quotient.lift (s := suspensionSetoid ThreeCircles)
    (fun p => Suspension.mk p.1 (thetaCircleLabel p.2))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hz⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (congrArg thetaCircleLabel hz))⟩)

private theorem thetaForgetCircleFun_continuous : Continuous thetaForgetCircleFun := by
  apply (Suspension.isQuotientMap_mk (X := ThreeCircles)).continuous_iff.mpr
  change Continuous (fun p : unitInterval × ThreeCircles =>
    Suspension.mk p.1 (thetaCircleLabel p.2))
  exact Suspension.continuous_mk.comp
    (continuous_fst.prodMk (thetaCircleLabel.continuous.comp continuous_snd))

/-- Forget the circle coordinate while retaining the actual edge and height. -/
def thetaForgetCircle : C(ThreeCircleSuspension, Theta) :=
  ⟨thetaForgetCircleFun, thetaForgetCircleFun_continuous⟩

@[simp] theorem thetaForgetCircle_mk (t : unitInterval) (z : ThreeCircles) :
    thetaForgetCircle (Suspension.mk t z) = Suspension.mk t (thetaCircleLabel z) := rfl

@[simp] theorem thetaForgetCircle_circle (t : unitInterval) (j : Fin 3)
    (z : _root_.Circle) :
    thetaForgetCircle (Suspension.mk t (thetaCircleInclusion j z)) = Suspension.mk t j := by
  rw [thetaForgetCircle_mk, thetaCircleLabel_inclusion]

theorem thetaForgetCircle_continuous : Continuous thetaForgetCircle :=
  thetaForgetCircle.continuous

@[simp] theorem thetaForgetCircle_north :
    thetaForgetCircle Suspension.north = Suspension.north := by
  simpa only [Suspension.mk_zero] using
    thetaForgetCircle_mk 0 (Sum.inl (1 : _root_.Circle))

@[simp] theorem thetaForgetCircle_south :
    thetaForgetCircle Suspension.south = Suspension.south := by
  simpa only [Suspension.mk_one] using
    thetaForgetCircle_mk 1 (Sum.inl (1 : _root_.Circle))

@[simp] theorem thetaForgetCircle_height (q : ThreeCircleSuspension) :
    Suspension.height (thetaForgetCircle q) = Suspension.height q := by
  obtain ⟨⟨t, z⟩, rfl⟩ := Suspension.mk_surjective q
  rfl

/-- Forgetting the character values recovers the original actual theta point. -/
@[simp] theorem thetaForgetCircle_collapse (u : CompactFibreTorus) (q : Theta) :
    thetaForgetCircle (thetaCharacterCollapse (u, q)) = q := by
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaCharacterCollapse_mk, thetaForgetCircle_circle]

theorem thetaForgetCircle_comp_collapse :
    thetaForgetCircle.comp thetaCharacterCollapse =
      (⟨Prod.snd, continuous_snd⟩ : C(CompactFibreTorus × Theta, Theta)) := by
  ext p
  exact thetaForgetCircle_collapse p.1 p.2

/-- Positive-degree actual integral singular homology of the discrete
three-point set is zero. -/
theorem threePoint_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology (Fin 3) n) :=
  totallyDisconnected_homology_subsingleton (Fin 3) n hn

/-- The actual theta quotient has no singular homology in degree at least two. -/
theorem theta_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology Theta (n + 2)) := by
  let := threePoint_homology_subsingleton (n + 1) (Nat.succ_ne_zero n)
  exact ((contractibleCoverHomologyHigherEquiv
    (Suspension.northOpen : Set Theta) Suspension.southOpen
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover n).trans
      (homotopyEquivHomologyEquiv
        (Suspension.middleBandHomotopyEquiv (X := Fin 3)) (n + 1))).injective.subsingleton

/-- In these degrees, the actual forgetful map induces the zero homomorphism. -/
theorem thetaForgetCircle_homology_eq_zero (n : ℕ) :
    singularHomologyMap thetaForgetCircle (n + 2) = 0 := by
  let := theta_homology_subsingleton n
  exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.CuspCentralHomology
