import Wikipedia.HopfProblem.CuspRetractionRadius
import Mathlib.Topology.Homotopy.Basic

/-!
# Descending an equivariant closed-tube homotopy

A supplied continuous, twisted-lattice-equivariant homotopy on the actual
closed toric tube descends through the existing open quotient map. Its
initial value, central fixed set, central endpoint, and norm-time bound
are retained in the literal closed subspace of the original cusp quotient.
This file constructs the descent and does not assume or assert existence
of an input homotopy.
-/

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}

private noncomputable def descentRepresentative (hηε : η < ε)
    (q : ClosedQuotient C ε η) : ClosedTube η :=
  (closedQuotientMap_surjective C hηε q).choose

private theorem descentRepresentative_spec (hηε : η < ε)
    (q : ClosedQuotient C ε η) :
    closedQuotientMap C hηε (descentRepresentative C hηε q) = q :=
  (closedQuotientMap_surjective C hηε q).choose_spec

/-- Descent is defined on representatives; equivariance below makes it
independent of the chosen representative. -/
noncomputable def closedHomotopyDescent (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (s : unitInterval) (q : ClosedQuotient C ε η) : ClosedQuotient C ε η :=
  closedQuotientMap C hηε (H (s, descentRepresentative C hηε q))

variable (hηε : η < ε)
variable (H : C(unitInterval × ClosedTube η, ClosedTube η))
variable (hH : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
  H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))

include hH in
theorem closedHomotopyDescent_compatible (s : unitInterval) (x y : ClosedTube η)
    (hxy : closedQuotientMap C hηε x = closedQuotientMap C hηε y) :
    closedQuotientMap C hηε (H (s, x)) = closedQuotientMap C hηε (H (s, y)) := by
  obtain ⟨v, hv⟩ := (closedQuotientMap_eq_iff C hηε x y).mp hxy
  have hv' : closedTranslate C η v y = x := Subtype.ext hv
  apply (closedQuotientMap_eq_iff C hηε _ _).mpr
  refine ⟨v, ?_⟩
  have he := hH s v y
  rw [hv'] at he
  exact (congrArg Subtype.val he).symm

include hH in
/-- The descended map has the requested formula on every toric representative. -/
theorem closedHomotopyDescent_closedQuotientMap (s : unitInterval) (x : ClosedTube η) :
    closedHomotopyDescent C hηε H s (closedQuotientMap C hηε x) =
      closedQuotientMap C hηε (H (s, x)) :=
  closedHomotopyDescent_compatible C hηε H hH s _ _
    (descentRepresentative_spec C hηε (closedQuotientMap C hηε x))

include hH in
/-- The product of the quotient map with the identity on the interval is
an open quotient map, so the descended homotopy is jointly continuous. -/
theorem closedHomotopyDescent_continuous
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Continuous (fun p : unitInterval × ClosedQuotient C ε η =>
      closedHomotopyDescent C hηε H p.1 p.2) := by
  have hq := closedQuotientMap_isOpenQuotientMap C hηε hC
  have hprod : IsOpenQuotientMap
      (Prod.map (id : unitInterval → unitInterval) (closedQuotientMap C hηε)) :=
    IsOpenQuotientMap.id.prodMap hq
  apply hprod.continuous_comp_iff.mp
  change Continuous (fun p : unitInterval × ClosedTube η =>
    closedHomotopyDescent C hηε H p.1 (closedQuotientMap C hηε p.2))
  simpa only [closedHomotopyDescent_closedQuotientMap C hηε H hH,
    Prod.mk.eta, Function.comp_def] using
    hq.continuous.comp H.continuous

/-- The descended continuous family in the original quotient. -/
noncomputable def closedHomotopyDescentMap
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    C(unitInterval × ClosedQuotient C ε η, ClosedQuotient C ε η) :=
  ⟨fun p => closedHomotopyDescent C hηε H p.1 p.2,
    closedHomotopyDescent_continuous C hηε H hH hC⟩

include hH in
theorem closedHomotopyDescent_zero
    (hzero : ∀ x : ClosedTube η, H (0, x) = x) (q : ClosedQuotient C ε η) :
    closedHomotopyDescent C hηε H 0 q = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, hzero]

include hH in
theorem closedHomotopyDescent_fixed
    (hfix : ∀ (s : unitInterval) (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x)
    (s : unitInterval) (q : ClosedQuotient C ε η) (hq : projection C ε q = 0) :
    closedHomotopyDescent C hηε H s q = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, hfix s x hq]

include hH in
theorem closedHomotopyDescent_one_central
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0)
    (q : ClosedQuotient C ε η) :
    projection C ε (closedHomotopyDescent C hηε H 1 q) = 0 := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH,
    closedQuotientMap_projection, hone]

include hH in
theorem closedHomotopyDescent_norm_nonincrease
    (hmono : ∀ (s : unitInterval) (x : ClosedTube η),
      ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖)
    (s : unitInterval) (q : ClosedQuotient C ε η) :
    ‖projection C ε (closedHomotopyDescent C hηε H s q)‖ ≤ ‖projection C ε q‖ := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH,
    closedQuotientMap_projection, closedQuotientMap_projection]
  exact hmono s x

/-- The literal central fibre of the original quotient, with its inherited
subspace topology; it is independent of the closed working radius. -/
abbrev QuotientCentralFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  {q : QuotientSpace C ε // projection C ε q = 0}

/-- Inclusion of the actual central fibre in a nonnegative-radius closed tube. -/
def quotientCentralIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ)
    (hη : 0 ≤ η) : C(QuotientCentralFibre C ε, ClosedQuotient C ε η) where
  toFun q := ⟨q, by rw [q.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The actual quotient retraction obtained from the endpoint of the
supplied equivariant homotopy. -/
noncomputable def closedHomotopyDescentRetraction
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0) :
    C(ClosedQuotient C ε η, QuotientCentralFibre C ε) where
  toFun q := ⟨closedHomotopyDescent C hηε H 1 q,
    closedHomotopyDescent_one_central C hηε H hH hone q⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      ((closedHomotopyDescent_continuous C hηε H hH hC).comp
        (continuous_const.prodMk continuous_id))).subtype_mk _

theorem closedHomotopyDescentRetraction_comp_inclusion
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hfix : ∀ (s : unitInterval) (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x)
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0) (hη : 0 ≤ η) :
    (closedHomotopyDescentRetraction C hηε H hH hC hone).comp
      (quotientCentralIntoClosed C ε η hη) = ContinuousMap.id (QuotientCentralFibre C ε) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change (closedHomotopyDescent C hηε H 1 (quotientCentralIntoClosed C ε η hη q) :
    QuotientSpace C ε) = (q : QuotientSpace C ε)
  exact congrArg Subtype.val
    (closedHomotopyDescent_fixed C hηε H hH hfix 1 (quotientCentralIntoClosed C ε η hη q) q.2)

/-- The descended homotopy fixes the literal central subset pointwise and
ends at the inclusion composed with its retraction. -/
noncomputable def closedHomotopyDescentHomotopyRel
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hzero : ∀ x : ClosedTube η, H (0, x) = x)
    (hfix : ∀ (s : unitInterval) (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x)
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0) (hη : 0 ≤ η) :
    (ContinuousMap.id (ClosedQuotient C ε η)).HomotopyRel
      ((quotientCentralIntoClosed C ε η hη).comp
        (closedHomotopyDescentRetraction C hηε H hH hC hone))
      {q : ClosedQuotient C ε η | projection C ε q = 0} where
  toFun p := closedHomotopyDescent C hηε H p.1 p.2
  continuous_toFun := closedHomotopyDescent_continuous C hηε H hH hC
  map_zero_left := closedHomotopyDescent_zero C hηε H hH hzero
  map_one_left _ := rfl
  prop' s q hq := closedHomotopyDescent_fixed C hηε H hH hfix s q hq

end Wikipedia.HopfProblem.CuspRetraction
