import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusLoops
import Wikipedia.HopfProblem.FirstHurewiczNaturality
import Mathlib.Topology.Homotopy.Affine

/-!
# Projected affine paths and their integral periods

Straight segments in the real covering plane determine actual paths in
the coordinate two-torus.  The difference between two such paths with
a common starting lift is the actual period-loop class of their integral
endpoint difference.  The proof uses a homotopy of the affine triangle
and the homotopy from a torus translation to the identity.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz PeriodTorusHigherHomology SingularMayerVietoris

/-- The actual projection of the straight segment joining two real lifts. -/
def projectedSegment (a b : Fin 2 → ℝ) :
    Path (coordinateProjection 2 a) (coordinateProjection 2 b) :=
  (Path.segment a b).map (coordinateProjection_continuous 2)

@[simp] theorem projectedSegment_apply (a b : Fin 2 → ℝ) (t : unitInterval) :
    projectedSegment a b t =
      coordinateProjection 2 ((1 - (t : ℝ)) • a + (t : ℝ) • b) := by
  simp only [projectedSegment, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module]

/-- Common-start affine coordinates for the actual projected path. -/
theorem projectedSegment_apply_add (a d : Fin 2 → ℝ) (t : unitInterval) :
    projectedSegment a (a + d) t =
      coordinateProjection 2 (a + (t : ℝ) • d) := by
  rw [projectedSegment_apply]
  congr 1
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private def affinePathHomotopy {a b : Fin 2 → ℝ} (p q : Path a b) :
    p.Homotopy q where
  toHomotopy := ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap
  prop' t x hx := by
    rcases hx with hx | hx
    · subst x
      simp
    · have hx' : x = 1 := Set.mem_singleton_iff.mp hx
      subst x
      simp

/-- Projecting the endpoint-fixed affine triangle homotopy compares its
straight side with the concatenation of the other two sides. -/
theorem projectedSegment_homotopic_trans (a b c : Fin 2 → ℝ) :
    (projectedSegment a b).Homotopic
      ((projectedSegment a c).trans (projectedSegment c b)) := by
  have h : (Path.segment a b).Homotopic
      ((Path.segment a c).trans (Path.segment c b)) := ⟨affinePathHomotopy _ _⟩
  simpa only [projectedSegment, Path.map_trans] using
    h.map (⟨coordinateProjection 2, coordinateProjection_continuous 2⟩ :
      C((Fin 2 → ℝ), ProductTorus 2))

/-- The triangle identity holds in the actual quotient of singular one-chains. -/
theorem projectedSegment_pathClass_triangle (a b c : Fin 2 → ℝ) :
    pathClass (projectedSegment a b) =
      pathClass (projectedSegment a c) + pathClass (projectedSegment c b) :=
  (pathClass_homotopic (projectedSegment_homotopic_trans a b c)).trans
    (pathClass_trans _ _)

private theorem coordinateProjection_add_integer (c : Fin 2 → ℝ) (v : Fin 2 → ℤ) :
    coordinateProjection 2 (c + fun i => (v i : ℝ)) = coordinateProjection 2 c := by
  rw [map_add, (coordinateProjection_eq_zero_iff 2 _).mpr ⟨v, rfl⟩, add_zero]

/-- Translation of an actual loop by a projected real point preserves its
genuine first singular-homology class. -/
theorem loopHomologyClass_map_projectedTranslation (c : Fin 2 → ℝ)
    {x : ProductTorus 2} (p : Path x x) :
    loopHomologyClass (p.map (rightTranslation (coordinateProjection 2 c)).continuous) =
      loopHomologyClass p := by
  let pc : Path (0 : ProductTorus 2) (coordinateProjection 2 c) :=
    (projectedSegment 0 c).cast (map_zero (coordinateProjection 2)).symm rfl
  have hmap : inducedHomology (rightTranslation (coordinateProjection 2 c)) =
      LinearMap.id := rightTranslation_singularHomologyMap_of_path pc 1
  rw [← inducedHomology_loopHomologyClass
    (rightTranslation (coordinateProjection 2 c)) x p, hmap]
  rfl

/-- The projected segment from a real point to its integral translate has
the path-chain class of the actual coordinate period loop. -/
theorem projectedSegment_pathClass_add_integer (c : Fin 2 → ℝ) (v : Fin 2 → ℤ) :
    pathClass (projectedSegment c (c + fun i => (v i : ℝ))) =
      pathClass (coordinatePeriodLoop 2 v) := by
  let p := (coordinatePeriodLoop 2 v).map
    (rightTranslation (coordinateProjection 2 c)).continuous
  have hp : rightTranslation (coordinateProjection 2 c) (0 : ProductTorus 2) =
      coordinateProjection 2 c := by simp
  have hpath :
      (projectedSegment c (c + fun i => (v i : ℝ))).cast rfl
        (coordinateProjection_add_integer c v).symm =
      p.cast hp.symm hp.symm := by
    apply Path.ext
    funext t
    change projectedSegment c (c + fun i => (v i : ℝ)) t =
      coordinatePeriodLoop 2 v t + coordinateProjection 2 c
    rw [projectedSegment_apply_add, coordinatePeriodLoop_eq_projection, map_add, add_comm]
  have hclass : pathClass p = pathClass (coordinatePeriodLoop 2 v) := by
    have h := congrArg (homologyToChainClass (ProductTorus 2))
      (loopHomologyClass_map_projectedTranslation c (coordinatePeriodLoop 2 v))
    simpa only [homologyToChainClass_loopHomologyClass] using h
  have h := congrArg
    (fun q : Path (coordinateProjection 2 c) (coordinateProjection 2 c) => pathClass q) hpath
  exact h.trans hclass

/-- Two projected affine paths with a common starting lift differ by the
actual period-loop class of their integral endpoint difference. -/
theorem projectedSegment_pathClass_sub_of_eq_add_integer
    (a b c : Fin 2 → ℝ) (v : Fin 2 → ℤ)
    (hbc : b = c + fun i => (v i : ℝ)) :
    pathClass (projectedSegment a b) - pathClass (projectedSegment a c) =
      homologyToChainClass (ProductTorus 2)
        (loopHomologyClass (coordinatePeriodLoop 2 v)) := by
  calc
    pathClass (projectedSegment a b) - pathClass (projectedSegment a c) =
        (pathClass (projectedSegment a c) + pathClass (projectedSegment c b)) -
          pathClass (projectedSegment a c) := by
      rw [projectedSegment_pathClass_triangle a b c]
    _ = pathClass (projectedSegment c b) := add_sub_cancel_left _ _
    _ = pathClass (coordinatePeriodLoop 2 v) := by
      rw [hbc]
      exact projectedSegment_pathClass_add_integer c v
    _ = homologyToChainClass (ProductTorus 2)
        (loopHomologyClass (coordinatePeriodLoop 2 v)) :=
      (homologyToChainClass_loopHomologyClass _).symm

/-- The same identity in common-start displacement coordinates. -/
theorem projectedSegment_pathClass_sub_of_displacement_sub
    (a d e : Fin 2 → ℝ) (v : Fin 2 → ℤ)
    (hde : d - e = fun i => (v i : ℝ)) :
    pathClass (projectedSegment a (a + d)) - pathClass (projectedSegment a (a + e)) =
      homologyToChainClass (ProductTorus 2)
        (loopHomologyClass (coordinatePeriodLoop 2 v)) := by
  apply projectedSegment_pathClass_sub_of_eq_add_integer
  rw [← hde]
  abel

end Wikipedia.HopfProblem.CuspCentralHomology
