import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedHomotopy
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopy

/-!
# Deck transformations transported by actual loop squares

The genuine covering homotopy lift of a continuous loop square retains
the initial endpoint deck transformation.  Comparing its final edge with
another actual lifted loop produces the precise conjugating deck frame.
Both the frame and its conjugation identity follow from covering-space
uniqueness and the free action, not from an assumed loop identification.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.EllipticAttachingMeridians

variable {a b : TriangleRegularQuotient} {p : Path a a} {q : Path b b}
  (S : LoopSquare p q) (L : C(unitInterval, TriangleRegularPoint))
  (hL : ∀ t, triangleRegularProject (L t) = p t)

/-- Lift the literal square using the specified entire initial lifted loop. -/
def loopSquareLift : C(unitInterval × unitInterval, TriangleRegularPoint) :=
  triangleRegularProject_covering.isCoveringMap.liftHomotopy S.map L
    (fun t => (S.initial t).trans (hL t).symm)

@[simp] theorem loopSquareLift_zero (t : unitInterval) :
    loopSquareLift S L hL (0, t) = L t :=
  triangleRegularProject_covering.isCoveringMap.liftHomotopy_zero _ _ _ t

theorem loopSquareLift_projection (s t : unitInterval) :
    triangleRegularProject (loopSquareLift S L hL (s, t)) = S.map (s, t) :=
  congr_fun (triangleRegularProject_covering.isCoveringMap.liftHomotopy_lifts _ _
    (fun t => (S.initial t).trans (hL t).symm)) (s, t)

/-- The same actual deck transformation relates the two vertical edges
at every homotopy time. -/
theorem loopSquareLift_endpoint (g : TriangleGroup) (hend : L 1 = g • L 0)
    (s : unitInterval) :
    loopSquareLift S L hL (s, 1) = g • loopSquareLift S L hL (s, 0) := by
  have hleft : Continuous (fun u : unitInterval => loopSquareLift S L hL (u, 1)) :=
    (loopSquareLift S L hL).continuous.comp (continuous_id.prodMk continuous_const)
  have hright : Continuous (fun u : unitInterval => g • loopSquareLift S L hL (u, 0)) :=
    (continuous_const_smul g).comp
      ((loopSquareLift S L hL).continuous.comp (continuous_id.prodMk continuous_const))
  have he : triangleRegularProject ∘ (fun u : unitInterval =>
        loopSquareLift S L hL (u, 1)) =
      triangleRegularProject ∘ (fun u : unitInterval =>
        g • loopSquareLift S L hL (u, 0)) := by
    funext u
    simp only [Function.comp_apply, loopSquareLift_projection,
      triangleRegularProject_covering.map_smul]
    exact (S.closed u).symm
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 (by simpa only [loopSquareLift_zero] using hend)) s

/-- If the final edge starts in deck frame `d`, uniqueness places its
entire lifted path in that same frame. -/
theorem loopSquareLift_final_frame (K : C(unitInterval, TriangleRegularPoint))
    (hK : ∀ t, triangleRegularProject (K t) = q t) (d : TriangleGroup)
    (hd : loopSquareLift S L hL (1, 0) = d • K 0) (t : unitInterval) :
    loopSquareLift S L hL (1, t) = d • K t := by
  have hleft : Continuous (fun u : unitInterval => loopSquareLift S L hL (1, u)) :=
    (loopSquareLift S L hL).continuous.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun u : unitInterval => d • K u) :=
    (continuous_const_smul d).comp K.continuous
  have he : triangleRegularProject ∘ (fun u : unitInterval =>
        loopSquareLift S L hL (1, u)) =
      triangleRegularProject ∘ (fun u : unitInterval => d • K u) := by
    funext u
    simp only [Function.comp_apply, loopSquareLift_projection, S.final,
      triangleRegularProject_covering.map_smul, hK]
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 hd) t

/-- The actual loop square and the two actual lifted endpoints determine
the exact conjugation relation on the deck group. -/
theorem loopSquareLift_frame_relation (g : TriangleGroup) (hend : L 1 = g • L 0)
    (K : C(unitInterval, TriangleRegularPoint))
    (hK : ∀ t, triangleRegularProject (K t) = q t)
    (h : TriangleGroup) (hKend : K 1 = h • K 0) (d : TriangleGroup)
    (hd : loopSquareLift S L hL (1, 0) = d • K 0) : g * d = d * h := by
  let := triangleRegularProject_covering.isCancelSMul
  apply IsCancelSMul.right_cancel _ _ (K 0)
  calc
    (g * d) • K 0 = g • loopSquareLift S L hL (1, 0) := by rw [mul_smul, hd]
    _ = loopSquareLift S L hL (1, 1) := (loopSquareLift_endpoint S L hL g hend 1).symm
    _ = d • K 1 := loopSquareLift_final_frame S L hL K hK d hd 1
    _ = (d * h) • K 0 := by rw [hKend, mul_smul]

/-- The final basepoint has an actual deck frame relative to any chosen
lift of the final loop's basepoint. -/
theorem loopSquareLift_exists_frame (z : TriangleRegularPoint)
    (hz : triangleRegularProject z = b) :
    ∃ d : TriangleGroup, loopSquareLift S L hL (1, 0) = d • z := by
  have he : triangleRegularProject (loopSquareLift S L hL (1, 0)) =
      triangleRegularProject z := by
    rw [loopSquareLift_projection, S.final, q.source, hz]
  obtain ⟨d, hd⟩ := triangleRegularProject_covering.apply_eq_iff_mem_orbit.mp he
  exact ⟨d, hd.symm⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
