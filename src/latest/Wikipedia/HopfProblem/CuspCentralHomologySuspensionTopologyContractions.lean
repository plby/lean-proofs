import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopologyBasic
import Mathlib.Topology.CompactOpen

/-!
# Contractions of the two open suspension cones

The maps are defined on the actual suspension quotient.  On the northern
truncated cylinder the homotopy replaces `t` by `(1-s)t`; on the southern
truncated cylinder it replaces `t` by `1-(1-s)(1-t)`.  Restricting the quotient
map to the open cones removes the opposite pole and makes these formulas
well-defined.  Their joint continuity descends through this restricted quotient.
-/

noncomputable section

open Set Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspCentralHomology.Suspension

private def liftFromSurjection {A B S Z : Type*} (q : A → B)
    (hq : Function.Surjective q) (F : S × A → Z) (p : S × B) : Z :=
  F (p.1, Function.surjInv hq p.2)

private theorem liftFromSurjection_comp {A B S Z : Type*} (q : A → B)
    (hq : Function.Surjective q) (F : S × A → Z)
    (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (s : S) (a : A) :
    liftFromSurjection q hq F (s, q a) = F (s, a) :=
  hF s _ _ (Function.surjInv_eq hq (q a))

private theorem liftFromSurjection_continuous {A B S Z : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S] [TopologicalSpace Z]
    [LocallyCompactSpace S] (q : A → B) (hq : IsQuotientMap q) (F : S × A → Z)
    (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (hcont : Continuous F) :
    Continuous (liftFromSurjection q hq.surjective F) := by
  apply hq.continuous_lift_prod_right
  convert hcont using 1
  funext p
  exact liftFromSurjection_comp q hq.surjective F hF p.1 p.2

variable {X : Type*} [TopologicalSpace X]

private abbrev NorthCylinder (X : Type*) [TopologicalSpace X] :=
  (fun p : unitInterval × X => mk p.1 p.2) ⁻¹' northOpen

private def northProjection : NorthCylinder X → (northOpen : Set (Suspension X)) :=
  northOpen.restrictPreimage (fun p : unitInterval × X => mk p.1 p.2)

private theorem northProjection_isQuotientMap :
    IsQuotientMap (northProjection (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen northOpen_isOpen

private def northCylinderContraction
    (p : unitInterval × NorthCylinder X) : (northOpen : Set (Suspension X)) :=
  ⟨mk (unitInterval.symm p.1 * p.2.1.1) p.2.1.2, by
    change ((unitInterval.symm p.1 * p.2.1.1 : unitInterval) : ℝ) < 3 / 4
    exact lt_of_le_of_lt unitInterval.mul_le_right p.2.2⟩

private theorem northCylinderContraction_respects (s : unitInterval)
    (a b : NorthCylinder X) (h : northProjection a = northProjection b) :
    northCylinderContraction (s, a) = northCylinderContraction (s, b) := by
  apply Subtype.ext
  have hab : mk a.1.1 a.1.2 = mk b.1.1 b.1.2 := congrArg Subtype.val h
  rcases (mk_eq_mk_iff _ _ _ _).mp hab with ⟨ht, hzero | hone | hx⟩
  · apply (mk_eq_mk_iff _ _ _ _).mpr
    exact ⟨congrArg (fun t => unitInterval.symm s * t) ht,
      Or.inl (by rw [hzero, mul_zero])⟩
  · have ha : (a.1.1 : ℝ) < 3 / 4 := a.2
    rw [hone] at ha
    norm_num at ha
  · change mk (unitInterval.symm s * a.1.1) a.1.2 =
      mk (unitInterval.symm s * b.1.1) b.1.2
    rw [ht, hx]

private theorem northCylinderContraction_continuous :
    Continuous (northCylinderContraction (X := X)) := by
  apply Continuous.subtype_mk
  apply continuous_mk.comp
    (f := fun p : unitInterval × NorthCylinder X =>
      (unitInterval.symm p.1 * p.2.1.1, p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

private def northContract : unitInterval × (northOpen : Set (Suspension X)) →
    (northOpen : Set (Suspension X)) :=
  liftFromSurjection northProjection northProjection_isQuotientMap.surjective
    northCylinderContraction

private theorem northContract_projection (s : unitInterval) (a : NorthCylinder X) :
    northContract (s, northProjection a) = northCylinderContraction (s, a) :=
  liftFromSurjection_comp _ _ _ northCylinderContraction_respects s a

private theorem northContract_continuous : Continuous (northContract (X := X)) :=
  liftFromSurjection_continuous _ northProjection_isQuotientMap _
    northCylinderContraction_respects northCylinderContraction_continuous

section NorthPole

variable [Nonempty X]

/-- The northern open cone contracts to its actual height-zero pole. -/
def northContraction :
    Homotopy (ContinuousMap.id (northOpen : Set (Suspension X)))
      (ContinuousMap.const _ ⟨north, north_mem_northOpen⟩) where
  toFun := northContract
  continuous_toFun := northContract_continuous
  map_zero_left q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap.surjective q
    rw [northContract_projection]
    apply Subtype.ext
    change mk (unitInterval.symm 0 * a.1.1) a.1.2 = mk a.1.1 a.1.2
    simp
  map_one_left q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap.surjective q
    rw [northContract_projection]
    apply Subtype.ext
    change mk (unitInterval.symm 1 * a.1.1) a.1.2 = north
    simp

/-- The explicit contraction has the expected cylinder-coordinate formula. -/
theorem northContraction_mk (s t : unitInterval) (x : X)
    (ht : (t : ℝ) < 3 / 4) :
    (northContraction (s, ⟨mk t x, ht⟩) : Suspension X) =
      mk (unitInterval.symm s * t) x := by
  exact congrArg Subtype.val
    (northContract_projection s (⟨(t, x), ht⟩ : NorthCylinder X))

instance northOpen_contractibleSpace :
    ContractibleSpace (northOpen : Set (Suspension X)) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨north, north_mem_northOpen⟩, ⟨northContraction⟩⟩

end NorthPole

private abbrev SouthCylinder (X : Type*) [TopologicalSpace X] :=
  (fun p : unitInterval × X => mk p.1 p.2) ⁻¹' southOpen

private def southProjection : SouthCylinder X → (southOpen : Set (Suspension X)) :=
  southOpen.restrictPreimage (fun p : unitInterval × X => mk p.1 p.2)

private theorem southProjection_isQuotientMap :
    IsQuotientMap (southProjection (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen southOpen_isOpen

private def southCylinderContraction
    (p : unitInterval × SouthCylinder X) : (southOpen : Set (Suspension X)) :=
  ⟨mk (unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1))
      p.2.1.2, by
    change 1 / 4 <
      ((unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1) :
        unitInterval) : ℝ)
    have hle : unitInterval.symm p.1 * unitInterval.symm p.2.1.1 ≤
        unitInterval.symm p.2.1.1 := unitInterval.mul_le_right
    have hbound : p.2.1.1 ≤
        unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1) :=
      unitInterval.le_symm_comm.mpr hle
    exact lt_of_lt_of_le p.2.2 hbound⟩

private theorem southCylinderContraction_respects (s : unitInterval)
    (a b : SouthCylinder X) (h : southProjection a = southProjection b) :
    southCylinderContraction (s, a) = southCylinderContraction (s, b) := by
  apply Subtype.ext
  have hab : mk a.1.1 a.1.2 = mk b.1.1 b.1.2 := congrArg Subtype.val h
  rcases (mk_eq_mk_iff _ _ _ _).mp hab with ⟨ht, hzero | hone | hx⟩
  · have ha : 1 / 4 < (a.1.1 : ℝ) := a.2
    rw [hzero] at ha
    norm_num at ha
  · apply (mk_eq_mk_iff _ _ _ _).mpr
    refine ⟨congrArg (fun t => unitInterval.symm
      (unitInterval.symm s * unitInterval.symm t)) ht, Or.inr (Or.inl ?_)⟩
    simp [hone]
  · change mk (unitInterval.symm (unitInterval.symm s * unitInterval.symm a.1.1))
        a.1.2 =
      mk (unitInterval.symm (unitInterval.symm s * unitInterval.symm b.1.1)) b.1.2
    rw [ht, hx]

private theorem southCylinderContraction_continuous :
    Continuous (southCylinderContraction (X := X)) := by
  apply Continuous.subtype_mk
  apply continuous_mk.comp
    (f := fun p : unitInterval × SouthCylinder X =>
      (unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1), p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_const.sub
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_const.sub (continuous_subtype_val.comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

private def southContract : unitInterval × (southOpen : Set (Suspension X)) →
    (southOpen : Set (Suspension X)) :=
  liftFromSurjection southProjection southProjection_isQuotientMap.surjective
    southCylinderContraction

private theorem southContract_projection (s : unitInterval) (a : SouthCylinder X) :
    southContract (s, southProjection a) = southCylinderContraction (s, a) :=
  liftFromSurjection_comp _ _ _ southCylinderContraction_respects s a

private theorem southContract_continuous : Continuous (southContract (X := X)) :=
  liftFromSurjection_continuous _ southProjection_isQuotientMap _
    southCylinderContraction_respects southCylinderContraction_continuous

variable [Nonempty X]

/-- The southern open cone contracts to its actual height-one pole. -/
def southContraction :
    Homotopy (ContinuousMap.id (southOpen : Set (Suspension X)))
      (ContinuousMap.const _ ⟨south, south_mem_southOpen⟩) where
  toFun := southContract
  continuous_toFun := southContract_continuous
  map_zero_left q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap.surjective q
    rw [southContract_projection]
    apply Subtype.ext
    change mk (unitInterval.symm (unitInterval.symm 0 * unitInterval.symm a.1.1))
      a.1.2 = mk a.1.1 a.1.2
    simp
  map_one_left q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap.surjective q
    rw [southContract_projection]
    apply Subtype.ext
    change mk (unitInterval.symm (unitInterval.symm 1 * unitInterval.symm a.1.1))
      a.1.2 = south
    simp

/-- The southern contraction has the reflected cylinder-coordinate formula. -/
theorem southContraction_mk (s t : unitInterval) (x : X)
    (ht : 1 / 4 < (t : ℝ)) :
    (southContraction (s, ⟨mk t x, ht⟩) : Suspension X) =
      mk (unitInterval.symm (unitInterval.symm s * unitInterval.symm t)) x := by
  exact congrArg Subtype.val
    (southContract_projection s (⟨(t, x), ht⟩ : SouthCylinder X))

instance southOpen_contractibleSpace :
    ContractibleSpace (southOpen : Set (Suspension X)) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨south, south_mem_southOpen⟩, ⟨southContraction⟩⟩

end Wikipedia.HopfProblem.CuspCentralHomology.Suspension
