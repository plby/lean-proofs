import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic
import Wikipedia.HopfProblem.EllipticLogGaugeBasic

/-!
# Vertical translation and the actual logarithmic elliptic gauge

The vertical flow restricts to the original punctured period family.
Its compatibility with the logarithmic gauge is the commutativity of
two translations in the same real torus, not a change of complex atlas.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge

open Wikipedia.HopfProblem.Elliptic.LogGauge

variable (P : HolomorphicPeriodMap ℂ Disc)

/-- The restriction of the actual period-family translation to the
punctured disc. -/
def familyFlow (s : ℂ) (x : FamilyStar P) : FamilyStar P :=
  ⟨Period.flow P s x.val, x.property⟩

@[simp] theorem familyFlow_coe (s : ℂ) (x : FamilyStar P) :
    (familyFlow P s x : P.TotalSpace) = Period.flow P s x.val := rfl

@[simp] theorem familyFlow_base (s : ℂ) (x : FamilyStar P) :
    (familyFlow P s x).val.1 = x.val.1 := rfl

@[simp] theorem familyFlow_projection (s : ℂ) (x : FamilyStar P) :
    P.projection (familyFlow P s x).val = P.projection x.val := rfl

/-- The literal vertical translation on the punctured complex cover. -/
def coverFlow (s : ℂ) (x : CoverStar) : CoverStar :=
  ⟨Period.vectorFlow s x.val, x.property⟩

@[simp] theorem coverFlow_coe (s : ℂ) (x : CoverStar) :
    (coverFlow s x : Disc × ComplexPlane₂) = Period.vectorFlow s x.val := rfl

@[simp] theorem coverFlow_base (s : ℂ) (x : CoverStar) :
    (coverFlow s x).val.1 = x.val.1 := rfl

/-- The punctured flow is the descent of the original complex translation. -/
@[simp] theorem familyFlow_project (s : ℂ) (x : CoverStar) :
    familyFlow P s (project P x) = project P (coverFlow s x) :=
  Subtype.ext (Period.flow_quotientMap P s x.val)

@[simp] theorem familyFlow_zero (x : FamilyStar P) : familyFlow P 0 x = x :=
  Subtype.ext (Period.flow_zero P x.val)

theorem familyFlow_add (s t : ℂ) (x : FamilyStar P) :
    familyFlow P (s + t) x = familyFlow P s (familyFlow P t x) :=
  Subtype.ext (Period.flow_add P s t x.val)

@[simp] theorem familyFlow_neg_familyFlow (s : ℂ) (x : FamilyStar P) :
    familyFlow P (-s) (familyFlow P s x) = x := by
  rw [← familyFlow_add, neg_add_cancel, familyFlow_zero]

@[simp] theorem familyFlow_familyFlow_neg (s : ℂ) (x : FamilyStar P) :
    familyFlow P s (familyFlow P (-s) x) = x := by
  rw [← familyFlow_add, add_neg_cancel, familyFlow_zero]

@[simp] theorem familyFlow_int_cast (n : ℤ) (x : FamilyStar P) :
    familyFlow P (n : ℂ) x = x :=
  Subtype.ext (Period.flow_int_cast P n x.val)

/-- The inverse translation is given by negative time. -/
def familyFlowEquiv (s : ℂ) : Equiv.Perm (FamilyStar P) where
  toFun := familyFlow P s
  invFun := familyFlow P (-s)
  left_inv := familyFlow_neg_familyFlow P s
  right_inv := familyFlow_familyFlow_neg P s

@[simp] theorem familyFlowEquiv_apply (s : ℂ) (x : FamilyStar P) :
    familyFlowEquiv P s x = familyFlow P s x := rfl

@[simp] theorem familyFlowEquiv_symm_apply (s : ℂ) (x : FamilyStar P) :
    (familyFlowEquiv P s).symm x = familyFlow P (-s) x := rfl

theorem familyFlow_injective (s : ℂ) : Function.Injective (familyFlow P s) :=
  (familyFlowEquiv P s).injective

theorem familyFlow_surjective (s : ℂ) : Function.Surjective (familyFlow P s) :=
  (familyFlowEquiv P s).surjective

/-- Any chosen scalar branch gives a commuting translation already on
the original complex cover. -/
theorem gaugeLift_coverFlow (v : Lattice) (a : ℂ → ℂ) (s : ℂ) (x : CoverStar) :
    gaugeLift P v a (coverFlow s x) = coverFlow s (gaugeLift P v a x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (x.val.2 + Period.vector s) + a x.val.1 • periodVector P v x.val.1 =
      (x.val.2 + a x.val.1 • periodVector P v x.val.1) + Period.vector s
    exact add_right_comm _ _ _

/-- The global logarithmic gauge commutes with the actual vertical flow
for every integral twist, without an admissibility hypothesis. -/
theorem gaugeMap_familyFlow (v : Lattice) (s : ℂ) (x : FamilyStar P) :
    gaugeMap P v (familyFlow P s x) = familyFlow P s (gaugeMap P v x) := by
  obtain ⟨y, rfl⟩ := project_surjective P x
  rw [familyFlow_project, gaugeMap_project, gaugeMap_project,
    familyFlow_project, gaugeLift_coverFlow]

theorem familyFlow_gaugeMap (v : Lattice) (s : ℂ) (x : FamilyStar P) :
    familyFlow P s (gaugeMap P v x) = gaugeMap P v (familyFlow P s x) :=
  (gaugeMap_familyFlow P v s x).symm

theorem gaugeEquiv_familyFlow (v : Lattice) (s : ℂ) (x : FamilyStar P) :
    gaugeEquiv P v (familyFlow P s x) = familyFlow P s (gaugeEquiv P v x) :=
  gaugeMap_familyFlow P v s x

theorem gaugeEquiv_symm_familyFlow (v : Lattice) (s : ℂ) (x : FamilyStar P) :
    (gaugeEquiv P v).symm (familyFlow P s x) =
      familyFlow P s ((gaugeEquiv P v).symm x) :=
  gaugeMap_familyFlow P (-v) s x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge
