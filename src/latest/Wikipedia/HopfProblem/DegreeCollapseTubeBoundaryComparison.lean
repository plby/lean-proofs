import Wikipedia.HopfProblem.DegreeCollapseBallBoundaryHomotopy

/-!
# Compare an actual small trace boundary with its native normal meridian

The trace extends over the parameter ball in the original Morse chart.
Its positive coordinate therefore contracts through that extension.
Only the original nonzero normal boundary remains, with its original
radial normalization. The homotopy stays in the whole belt complement.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def beltBallCoordinates (d : MorseSurgeryData E f p) (ε : ℝ)
    (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius)) :
    C(closedBall (0 : A) ε,
      sphere (0 : d.chart.PositiveCoordinates) 1 × d.chart.NegativeCoordinates) :=
  ⟨fun z => ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm (F z)).val,
    continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm.continuous.comp F.continuous)⟩

theorem beltBallCoordinates_normal (d : MorseSurgeryData E f p) (ε : ℝ)
    (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (z : closedBall (0 : A) ε) :
    (beltBallCoordinates d ε F z).2 = d.radius⁻¹ • d.beltNormal (F z).val := rfl

def beltBallBoundaryNormal (d : MorseSurgeryData E f p) (ε : ℝ) (hε : 0 < ε)
    (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(sphere (0 : A) 1, PuncturedBall.Space d.chart.NegativeCoordinates 1) :=
  ⟨fun u => ⟨(beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2,
      hne u, hsmall _⟩,
    ((beltBallCoordinates d ε F).continuous.snd.comp
      (parameterBallBoundary ε hε).continuous).subtype_mk _⟩

def beltBallBoundaryInComplement (d : MorseSurgeryData E f p) (ε : ℝ) (hε : 0 < ε)
    (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(sphere (0 : A) 1, ((range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    (((ContinuousMap.fst.comp (beltBallCoordinates d ε F)).comp
      (parameterBallBoundary ε hε)).prodMk (beltBallBoundaryNormal d ε hε F hsmall hne))

theorem beltBallBoundaryInComplement_coe (d : MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : sphere (0 : A) 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne u).val =
      (F (parameterBallBoundary ε hε u)).val := by
  let y := F (parameterBallBoundary ε hε u)
  let e := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
  change (e (nativeBeltTubeSource d ((e.symm y).val.1,
    (beltBallBoundaryNormal d ε hε F hsmall hne u)))).val = y.val
  have hs : nativeBeltTubeSource d ((e.symm y).val.1,
      (beltBallBoundaryNormal d ε hε F hsmall hne u)) = e.symm y := by
    apply Subtype.ext
    rfl
  rw [hs, e.apply_symm_apply]

theorem beltBallBoundary_homotopic_meridian (d : MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne).Homotopic
      ((nativeBeltTubeMeridian d
        (beltBallCoordinates d ε F (parameterBallCenter ε hε)).1 r hr hr1).comp
          ((PuncturedBall.toSphere 1).comp (beltBallBoundaryNormal d ε hε F hsmall hne))) := by
  let a := ContinuousMap.fst.comp (beltBallCoordinates d ε F)
  have ha := parameterBall_boundary_nullhomotopic ε hε a
  exact nativeBeltTube_homotopic_meridian d (a.comp (parameterBallBoundary ε hε))
    (beltBallBoundaryNormal d ε hε F hsmall hne) (a (parameterBallCenter ε hε)) ha r hr hr1

theorem beltBallBoundary_normalized_coe (d : MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : sphere (0 : A) 1) :
    (PuncturedBall.toSphere 1 (beltBallBoundaryNormal d ε hε F hsmall hne u)).val =
      ‖d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        d.beltNormal (F (parameterBallBoundary ε hε u)).val := by
  change ‖d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
    (d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val) = _
  exact normalized_pos_smul d.radius⁻¹ (inv_pos.mpr d.radius_pos) _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
