import Wikipedia.HopfProblem.PeriodTorusExponentialChernFactorCover
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCover
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Original local lifts and actual singular-edge labels

The difference between each original quotient-chart lift and the fixed
vertex representative is an actual lattice element.  On a singular edge
contained in that chart, the genuine covering displacement is the
difference of these endpoint elements.  On a chart overlap the change of
local lift is constant along every actual singular edge.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open FirstHurewicz PeriodTorusAppellHumbert
  PeriodTorusLineBundle.ChernCover PeriodTorusLineBundle.ChernCocycle

/-- The actual inclusion of an original open subspace. -/
def openInclusion (p : PeriodDomain) (U : Opens p.Torus) : C(U, p.Torus) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The original quotient-chart lift on its actual open domain. -/
def chartLift (p : PeriodDomain) (i : p.Torus) : C(chartCover p i, ComplexPlane₂) :=
  ⟨fun x => Core.lift p i x,
    continuousOn_iff_continuous_domRestrict.mp (Core.lift_holomorphic p i).continuousOn⟩

@[simp] theorem chartLift_projection (p : PeriodDomain) (i : p.Torus)
    (x : chartCover p i) : p.lattice.mkQ (chartLift p i x) = x :=
  Core.lift_project p i x.property

/-- The actual lattice displacement from the fixed vertex representative
to this original local chart lift. -/
def liftDisplacement (p : PeriodDomain) (i : p.Torus) (x : chartCover p i) : p.lattice :=
  ⟨chartLift p i x - vertexLift p x, by
    apply (Submodule.Quotient.mk_eq_zero p.lattice).mp
    change p.lattice.mkQ (chartLift p i x - vertexLift p x) = 0
    rw [map_sub, chartLift_projection, vertexLift_projection, sub_self]⟩

@[simp] theorem liftDisplacement_coe (p : PeriodDomain) (i : p.Torus)
    (x : chartCover p i) :
    (liftDisplacement p i x : ComplexPlane₂) = chartLift p i x - vertexLift p x := rfl

theorem chartLift_eq_vertex_add (p : PeriodDomain) (i : p.Torus) (x : chartCover p i) :
    chartLift p i x = vertexLift p x + (liftDisplacement p i x : ComplexPlane₂) := by
  rw [liftDisplacement_coe]
  abel

/-- The original edge cocycle, in the actual lattice rather than its
integer-coordinate marking. -/
def latticeEdgeCocycle (p : PeriodDomain) : EdgeCocycle p.Torus p.lattice :=
  (edgeCocycle p).map p.latticeEquiv.symm.toAddMonoidHom

@[simp] theorem latticeEdgeCocycle_apply (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 1) : latticeEdgeCocycle p σ = edgeDisplacement p σ := by
  change p.latticeEquiv.symm (p.latticeEquiv (edgeDisplacement p σ)) = _
  exact p.latticeEquiv.symm_apply_apply _

/-- Literal restriction of the actual covering edge labels to an original open set. -/
def localEdgeCocycle (p : PeriodDomain) (U : Opens p.Torus) : EdgeCocycle U p.lattice :=
  (latticeEdgeCocycle p).pullback (openInclusion p U)

/-- The original covering labels are endpoint differences in every original chart. -/
theorem localEdgeCocycle_eq_displacement (p : PeriodDomain) (i : p.Torus)
    (σ : SingularSimplex (chartCover p i) 1) :
    localEdgeCocycle p (chartCover p i) σ =
      liftDisplacement p i (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) -
        liftDisplacement p i (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) := by
  let γ := (openInclusion p (chartCover p i)).comp σ
  let Γ := (chartLift p i).comp σ
  have hΓ : p.lattice.mkQ ∘ Γ = γ := by
    funext t
    exact chartLift_projection p i (σ t)
  have h := periodVector_edgeCocycleValue_of_lift p γ Γ hΓ
  rw [edgeCocycleValue, p.periodVector_latticeEquiv] at h
  change latticeEdgeCocycle p γ = _
  rw [latticeEdgeCocycle_apply]
  apply Subtype.ext
  change (edgeDisplacement p γ : ComplexPlane₂) =
    (liftDisplacement p i (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) : ComplexPlane₂) -
      (liftDisplacement p i (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) : ComplexPlane₂)
  rw [h, liftDisplacement_coe, liftDisplacement_coe]
  change chartLift p i (σ _) - chartLift p i (σ _) + vertexLift p (σ _) -
    vertexLift p (σ _) = (chartLift p i (σ _) - vertexLift p (σ _)) -
      (chartLift p i (σ _) - vertexLift p (σ _))
  abel

/-- On an original overlap the local lattice representatives differ by
the original chart deck change. -/
theorem liftDisplacement_overlap (p : PeriodDomain) (i j : p.Torus)
    (x : ↥(chartCover p i ⊓ chartCover p j)) :
    liftDisplacement p j ⟨x, x.property.2⟩ =
      Core.deck p i j x + liftDisplacement p i ⟨x, x.property.1⟩ := by
  apply Subtype.ext
  change Core.lift p j x - vertexLift p x =
    (Core.deck p i j x : ComplexPlane₂) + (Core.lift p i x - vertexLift p x)
  rw [Core.deck_coe p i j x.property]
  abel

/-- The original deck change is constant along every actual overlap edge. -/
theorem deck_constant_on_overlap_edge (p : PeriodDomain) (i j : p.Torus)
    (σ : SingularSimplex ↥(chartCover p i ⊓ chartCover p j) 1)
    (s t : Simplex 1) : Core.deck p i j (σ s) = Core.deck p i j (σ t) := by
  let _ := simplex_simplyConnected 1
  have h : IsLocallyConstant (fun u : Simplex 1 => Core.deck p i j (σ u)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro u
    exact (Core.deck_locally_constant p i j (σ u).property).comp_tendsto
      (continuous_subtype_val.comp σ.continuous).continuousAt
  exact h.apply_eq_of_preconnectedSpace s t

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
