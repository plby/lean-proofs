import Wikipedia.HopfProblem.CuspRetractionPolar
import Wikipedia.HopfProblem.CuspRetractionBasic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CompactOpen

/-!
# Spreading a positive-part deformation by the compact torus

This is the construction in Lemma 7.9.  A continuous homotopy of the
actual closed positive sub-tube, fixing its central part, descends through
the polar quotient to a continuous equivariant homotopy of the actual
closed toric tube.  If the supplied homotopy starts at the identity and
ends in the central part, the result is a strong deformation retraction
onto the actual central fibre.

No existence of the supplied positive-part homotopy is asserted here.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace

/-- The existing compact torus action restricted to the actual closed tube. -/
def closedCompactAction (η : ℝ) (u : CompactTorus) (x : ClosedTube η) : ClosedTube η :=
  ⟨compactTorusAction u x, by
    rw [norm_time_compactTorusAction]
    exact x.2⟩

@[simp] theorem closedCompactAction_coe (η : ℝ) (u : CompactTorus) (x : ClosedTube η) :
    (closedCompactAction η u x : Space) = compactTorusAction u x := rfl

@[simp] theorem closedCompactAction_one (η : ℝ) (x : ClosedTube η) :
    closedCompactAction η 1 x = x := Subtype.ext (compactTorusAction_one x)

theorem closedCompactAction_mul (η : ℝ) (u v : CompactTorus) (x : ClosedTube η) :
    closedCompactAction η u (closedCompactAction η v x) =
      closedCompactAction η (u * v) x := Subtype.ext (compactTorusAction_mul u v x)

theorem closedCompactAction_closedPolarMap (η : ℝ) (u v : CompactTorus)
    (q : ClosedPositiveTube η) :
    closedCompactAction η u (closedPolarMap η (v, q)) =
      closedPolarMap η (u * v, q) :=
  Subtype.ext (compactTorusAction_mul u v q.1)

variable {η : ℝ}
variable (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
variable (hfix : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
  time (q.1 : Space) = 0 → P (s, q) = q)

include hfix in
/-- Polar representatives remain equivalent after applying the positive
homotopy. At the central fibre the homotopy is fixed; elsewhere the
compact-torus action has trivial stabilizer. -/
theorem positiveHomotopy_polar_compatible (s : unitInterval) (u v : CompactTorus)
    (q r : ClosedPositiveTube η) (h : closedPolarMap η (u, q) = closedPolarMap η (v, r)) :
    closedPolarMap η (u, P (s, q)) = closedPolarMap η (v, P (s, r)) := by
  have hqr : q = r := by
    apply Subtype.ext
    apply Subtype.ext
    have hm : modulus (compactTorusAction u q.1) = modulus (compactTorusAction v r.1) :=
      congrArg (fun x : ClosedTube η => modulus (x : Space)) h
    rwa [modulus_compactTorusAction, modulus_compactTorusAction, q.1.2, r.1.2] at hm
  subst r
  by_cases hq : time (q.1 : Space) = 0
  · rw [hfix s q hq]
    exact h
  · have huv : u = v := compactTorusAction_injective_of_time_ne_zero hq
      (congrArg Subtype.val h)
    rw [huv]

private def polarRepresentative (η : ℝ) (x : ClosedTube η) :
    CompactTorus × ClosedPositiveTube η := (closedPolarMap_surjective η x).choose

private theorem polarRepresentative_spec (η : ℝ) (x : ClosedTube η) :
    closedPolarMap η (polarRepresentative η x) = x :=
  (closedPolarMap_surjective η x).choose_spec

/-- The spread map uses a polar representative only to define a function.
Compatibility proves that it is independent of this choice. -/
def polarSpread (s : unitInterval) (x : ClosedTube η) : ClosedTube η :=
  let p := polarRepresentative η x
  closedPolarMap η (p.1, P (s, p.2))

include hfix in
/-- The defining formula on the actual polar quotient. -/
theorem polarSpread_closedPolarMap (s : unitInterval)
    (p : CompactTorus × ClosedPositiveTube η) :
    polarSpread P s (closedPolarMap η p) =
      closedPolarMap η (p.1, P (s, p.2)) := by
  change closedPolarMap η
      ((polarRepresentative η (closedPolarMap η p)).1,
        P (s, (polarRepresentative η (closedPolarMap η p)).2)) = _
  exact positiveHomotopy_polar_compatible P hfix s
    (polarRepresentative η (closedPolarMap η p)).1 p.1
    (polarRepresentative η (closedPolarMap η p)).2 p.2
    (polarRepresentative_spec η (closedPolarMap η p))

include hfix in
/-- Joint continuity follows from the original polar quotient topology,
using local compactness of the homotopy interval. -/
theorem polarSpread_continuous :
    Continuous (fun p : unitInterval × ClosedTube η => polarSpread P p.1 p.2) := by
  apply (closedPolarMap_isQuotientMap η).continuous_lift_prod_right
  have h : Continuous (fun p : unitInterval × (CompactTorus × ClosedPositiveTube η) =>
      closedPolarMap η (p.2.1, P (p.1, p.2.2))) :=
    (closedPolarMap_continuous η).comp
      ((continuous_fst.comp continuous_snd).prodMk
        (P.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  simpa only [polarSpread_closedPolarMap P hfix] using h

include hfix in
/-- Every stage commutes with the genuine compact torus, not just the
compact torus acting on one coordinate chart. -/
theorem polarSpread_compactTorus_equivariant (s : unitInterval) (u : CompactTorus)
    (x : ClosedTube η) :
    polarSpread P s (closedCompactAction η u x) =
      closedCompactAction η u (polarSpread P s x) := by
  obtain ⟨⟨v, q⟩, rfl⟩ := closedPolarMap_surjective η x
  rw [closedCompactAction_closedPolarMap, polarSpread_closedPolarMap P hfix,
    polarSpread_closedPolarMap P hfix, closedCompactAction_closedPolarMap]

include hfix in
theorem polarSpread_zero (hzero : ∀ q : ClosedPositiveTube η, P (0, q) = q)
    (x : ClosedTube η) : polarSpread P 0 x = x := by
  obtain ⟨p, rfl⟩ := closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix, hzero]

include hfix in
/-- The spread homotopy fixes every point of the actual central fibre. -/
theorem polarSpread_fixed (s : unitInterval) (x : ClosedTube η) (hx : time (x : Space) = 0) :
    polarSpread P s x = x := by
  obtain ⟨⟨u, q⟩, rfl⟩ := closedPolarMap_surjective η x
  have hq : time (q.1 : Space) = 0 := by
    have hn := congrArg norm hx
    change ‖time (compactTorusAction u q.1)‖ = ‖(0 : ℂ)‖ at hn
    rw [norm_time_compactTorusAction, norm_zero] at hn
    exact norm_eq_zero.mp hn
  rw [polarSpread_closedPolarMap P hfix, hfix s q hq]

include hfix in
theorem polarSpread_one_central
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (x : ClosedTube η) : time (polarSpread P 1 x : Space) = 0 := by
  obtain ⟨⟨u, q⟩, rfl⟩ := closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix]
  change time (compactTorusAction u ((P (1, q)).1 : Space)) = 0
  simp only [compactTorusAction, time_torusAction, hone q, mul_zero]

/-- The actual central toric fibre, with its inherited subspace topology. -/
abbrev CentralFibre := {x : Space // time x = 0}

def centralIntoClosedTube (η : ℝ) (hη : 0 ≤ η) : C(CentralFibre, ClosedTube η) where
  toFun x := ⟨x, by rw [x.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Time one, with codomain restricted to the actual central fibre. -/
def polarRetraction
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) :
    C(ClosedTube η, CentralFibre) where
  toFun x := ⟨polarSpread P 1 x, polarSpread_one_central P hfix hone x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      ((polarSpread_continuous P hfix).comp (continuous_const.prodMk continuous_id))).subtype_mk _

@[simp] theorem polarRetraction_comp_inclusion
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) (hη : 0 ≤ η) :
    (polarRetraction P hfix hone).comp (centralIntoClosedTube η hη) =
      ContinuousMap.id CentralFibre := by
  ext x
  change (polarSpread P 1 (centralIntoClosedTube η hη x) : Space) = (x : Space)
  have h := polarSpread_fixed P hfix 1 (centralIntoClosedTube η hη x) x.2
  exact congrArg Subtype.val h

/-- Lemma 7.9's actual strong deformation retraction, conditional only on
the supplied positive homotopy having its stated three properties. -/
def polarStrongDeformationRetraction
    (hzero : ∀ q : ClosedPositiveTube η, P (0, q) = q)
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (hη : 0 ≤ η) :
    (ContinuousMap.id (ClosedTube η)).HomotopyRel
      ((centralIntoClosedTube η hη).comp (polarRetraction P hfix hone))
      (range (centralIntoClosedTube η hη)) where
  toFun p := polarSpread P p.1 p.2
  continuous_toFun := polarSpread_continuous P hfix
  map_zero_left := polarSpread_zero P hfix hzero
  map_one_left _ := rfl
  prop' s x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact polarSpread_fixed P hfix s (centralIntoClosedTube η hη y) y.2

end Wikipedia.HopfProblem.CuspRetraction
