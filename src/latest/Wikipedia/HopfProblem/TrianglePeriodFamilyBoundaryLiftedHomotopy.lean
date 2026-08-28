import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCylinder
import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry
import Mathlib.Topology.Homotopy.Lifting

/-!
# Genuine lifted base homotopies of boundary maps

A periodic homotopy of curves in the actual regular base lifts through
the actual triangle covering.  Uniqueness of path lifting preserves the
initial integer deck transformation.  Coupling this lift with the original
equivariant fibre-coordinate map gives an actual homotopy of boundary maps
into the regular family, with every fibre translation retained.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle MappingTorus
open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The unique continuous lift of the entire real-parameter base homotopy,
starting with the given actual upstairs curve. -/
def baseHomotopyLift (H : C(unitInterval × ℝ, TriangleRegularQuotient))
    (L : C(ℝ, TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = triangleRegularProject (L t)) :
    C(unitInterval × ℝ, TriangleRegularPoint) :=
  triangleRegularProject_covering.isCoveringMap.liftHomotopy H L hzero

@[simp] theorem baseHomotopyLift_zero
    (H : C(unitInterval × ℝ, TriangleRegularQuotient))
    (L : C(ℝ, TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = triangleRegularProject (L t)) (t : ℝ) :
    baseHomotopyLift H L hzero (0, t) = L t :=
  triangleRegularProject_covering.isCoveringMap.liftHomotopy_zero H L hzero t

theorem baseHomotopyLift_projection
    (H : C(unitInterval × ℝ, TriangleRegularQuotient))
    (L : C(ℝ, TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = triangleRegularProject (L t))
    (s : unitInterval) (t : ℝ) :
    triangleRegularProject (baseHomotopyLift H L hzero (s, t)) = H (s, t) :=
  congr_fun (triangleRegularProject_covering.isCoveringMap.liftHomotopy_lifts
    H L hzero) (s, t)

/-- Periodicity downstairs and the initial deck relation imply the exact
same deck relation throughout the lifted homotopy. -/
theorem baseHomotopyLift_translate
    (H : C(unitInterval × ℝ, TriangleRegularQuotient))
    (L : C(ℝ, TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = triangleRegularProject (L t))
    (g : TriangleGroup)
    (hperiod : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = H (s, t))
    (hdeck : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    baseHomotopyLift H L hzero (s, t + k) =
      (g ^ (-k)) • baseHomotopyLift H L hzero (s, t) := by
  have hleft : Continuous (fun u : unitInterval =>
      baseHomotopyLift H L hzero (u, t + k)) :=
    (baseHomotopyLift H L hzero).continuous.comp (continuous_id.prodMk continuous_const)
  have hright : Continuous (fun u : unitInterval =>
      (g ^ (-k)) • baseHomotopyLift H L hzero (u, t)) :=
    (continuous_const_smul (g ^ (-k))).comp
      ((baseHomotopyLift H L hzero).continuous.comp
        (continuous_id.prodMk continuous_const))
  have he : triangleRegularProject ∘ (fun u : unitInterval =>
        baseHomotopyLift H L hzero (u, t + k)) =
      triangleRegularProject ∘ (fun u : unitInterval =>
        (g ^ (-k)) • baseHomotopyLift H L hzero (u, t)) := by
    funext u
    simp only [Function.comp_apply, baseHomotopyLift_projection,
      triangleRegularProject_covering.map_smul, hperiod]
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 (by simp only [baseHomotopyLift_zero, hdeck])) s

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (φ : X ≃ₜ X)

/-- The literal family cylinder with the complete original fibre map. -/
def familyCylinderMap (L : C(ℝ, TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄)) :
    C(ℝ × X, D.Space) :=
  ⟨fun p => D.quotient (L p.1, G p),
    D.quotient_continuous.comp ((L.continuous.comp continuous_fst).prodMk G.continuous)⟩

@[simp] theorem familyCylinderMap_apply (L : C(ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (p : ℝ × X) :
    familyCylinderMap D L G p = D.quotient (L p.1, G p) := rfl

/-- The two actual deck relations make the original family cylinder
invariant under the defining mapping-torus equivalence relation. -/
theorem familyCylinderMap_deck (L : C(ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p)
    (k : ℤ) (p : ℝ × X) :
    familyCylinderMap D L G (deck φ k p) = familyCylinderMap D L G p := by
  change D.quotient (L (p.1 + k), G (deck φ k p)) = D.quotient (L p.1, G p)
  rw [hL, hG]
  exact DiagonalQuotient.quotient_smul TriangleGroup TriangleRegularPoint RealTorus₄
    (g ^ (-k)) (L p.1, G p)

/-- The actual boundary map obtained from the specified lifted cylinder. -/
def familyBoundaryMap (L : C(ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p) :
    C(Torus φ, D.Space) :=
  Cylinder.descend φ (familyCylinderMap D L G)
    (familyCylinderMap_deck D φ L G g hL hG)

@[simp] theorem familyBoundaryMap_mk (L : C(ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p) (p : ℝ × X) :
    familyBoundaryMap D φ L G g hL hG (mk φ p) = D.quotient (L p.1, G p) := rfl

/-- A fixed-time slice of an actual upstairs base homotopy. -/
def baseHomotopySlice (H : C(unitInterval × ℝ, TriangleRegularPoint))
    (s : unitInterval) : C(ℝ, TriangleRegularPoint) :=
  ⟨fun t => H (s, t), H.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- The complete family cylinder homotopy keeps the original fibre map,
including any time-dependent translation, exactly unchanged. -/
def familyCylinderHomotopy (H : C(unitInterval × ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) :
    (familyCylinderMap D (baseHomotopySlice H 0) G).Homotopy
      (familyCylinderMap D (baseHomotopySlice H 1) G) where
  toFun p := D.quotient (H (p.1, p.2.1), G p.2)
  continuous_toFun := D.quotient_continuous.comp
    ((H.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (G.continuous.comp continuous_snd))
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem familyCylinderHomotopy_deck
    (H : C(unitInterval × ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p)
    (s : unitInterval) (k : ℤ) (p : ℝ × X) :
    familyCylinderHomotopy D H G (s, deck φ k p) =
      familyCylinderHomotopy D H G (s, p) := by
  change D.quotient (H (s, p.1 + k), G (deck φ k p)) =
    D.quotient (H (s, p.1), G p)
  rw [hH, hG]
  exact DiagonalQuotient.quotient_smul TriangleGroup TriangleRegularPoint RealTorus₄
    (g ^ (-k)) (H (s, p.1), G p)

/-- A deck-equivariant upstairs base homotopy induces a genuine homotopy
of the literal boundary maps into the actual regular family. -/
def familyBoundaryHomotopy (H : C(unitInterval × ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p) :
    (familyBoundaryMap D φ (baseHomotopySlice H 0) G g (hH 0) hG).Homotopy
      (familyBoundaryMap D φ (baseHomotopySlice H 1) G g (hH 1) hG) :=
  Cylinder.descendHomotopy φ _ _
    (familyCylinderMap_deck D φ _ G g (hH 0) hG)
    (familyCylinderMap_deck D φ _ G g (hH 1) hG)
    (familyCylinderHomotopy D H G) (familyCylinderHomotopy_deck D φ H G g hH hG)

@[simp] theorem familyBoundaryHomotopy_mk
    (H : C(unitInterval × ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p)
    (s : unitInterval) (p : ℝ × X) :
    familyBoundaryHomotopy D φ H G g hH hG (s, mk φ p) =
      D.quotient (H (s, p.1), G p) := rfl

/-- This comparison holds for the actual homology map in every degree. -/
theorem familyBoundaryHomotopy_homology
    (H : C(unitInterval × ℝ, TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = (g ^ (-k)) • G p) (n : ℕ) :
    singularHomologyMap
        (familyBoundaryMap D φ (baseHomotopySlice H 0) G g (hH 0) hG) n =
      singularHomologyMap
        (familyBoundaryMap D φ (baseHomotopySlice H 1) G g (hH 1) hG) n :=
  homotopy_homologyMap (familyBoundaryHomotopy D φ H G g hH hG) n

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
