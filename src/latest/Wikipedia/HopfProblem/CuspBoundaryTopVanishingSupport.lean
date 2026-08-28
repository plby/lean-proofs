import Wikipedia.HopfProblem.CuspBoundaryTopVanishingBaseCoordinate
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingAxis
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingHomology

/-!
# Actual top-homology vanishing over the zero first base coordinate

The genuine radial overlap is the compact phase two-torus times an
open hexagonal annulus.  A map with zero first base-circle coordinate
has its annular coordinate on the literal horizontal axis.  The
explicit ambient annular contraction, with phase unchanged, makes its
overlap restriction homotopic to a map through that two-torus.

Naturality and injectivity of the actual Mayer--Vietoris connecting
map then give vanishing in degree four of the actual central fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open ToricSpace CuspRetraction CuspCentralHomology SingularMayerVietoris

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)
    {X : Type} [TopologicalSpace X]

include hr1 hC hR

/-- The literal overlap restriction of a zero-first-base-coordinate
map is homotopic, keeping phase unchanged, to a genuine map through
the compact phase two-torus. -/
theorem baseFirstZero_overlap_homotopic_phase
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (f : C(X, QuotientCentralFibre C r))
    (hzero : ∀ x, baseTorusProjection C r hr (f x) 0 = 0) :
    ∃ g : C(((f ⁻¹' outerRegion C r hr a) ∩ (f ⁻¹' innerRegion C r hr) : Set X),
        CompactFibreTorus),
      ∃ k : C(CompactFibreTorus, overlapRegion C r hr a),
        (centralPullbackIntersectionMap C r hr a f).Homotopic (k.comp g) := by
  let e := overlapPhaseHomeomorph C r hr hr1 hC hR a
  let i := centralPullbackIntersectionMap C r hr a f
  let g : C(((f ⁻¹' outerRegion C r hr a) ∩ (f ⁻¹' innerRegion C r hr) : Set X),
      CompactFibreTorus) :=
    ⟨fun x => (e.symm (i x)).1, (e.symm.continuous.comp i.continuous).fst⟩
  let b : C(((f ⁻¹' outerRegion C r hr a) ∩ (f ⁻¹' innerRegion C r hr) : Set X),
      AxisAnnulus a) :=
    ⟨fun x => ⟨(e.symm (i x)).2,
        overlapPhaseHomeomorph_symm_second_zero C r hr hr1 hC hR a (i x)
          (hzero x.1)⟩,
      (e.symm.continuous.comp i.continuous).snd.subtype_mk _⟩
  let k : C(CompactFibreTorus, overlapRegion C r hr a) :=
    ⟨fun z => e (z, axisAnnulusContractionPoint a ha ha1),
      e.continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨g, k, ⟨?_⟩⟩
  refine
    { toFun := fun p => e (g p.2, axisAnnulusContraction a ha ha1 (p.1, b p.2))
      continuous_toFun := e.continuous.comp
        ((g.continuous.comp continuous_snd).prodMk
          ((axisAnnulusContraction a ha ha1).continuous.comp
            (continuous_fst.prodMk (b.continuous.comp continuous_snd))))
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    change e ((e.symm (i x)).1, axisAnnulusContract a ha ha1 0 (b x)) = i x
    rw [axisAnnulusContract_zero]
    exact e.apply_symm_apply (i x)
  · intro x
    change e (g x, axisAnnulusContract a ha ha1 1 (b x)) =
      e (g x, axisAnnulusContractionPoint a ha ha1)
    rw [axisAnnulusContract_one]

/-- Every actual continuous map supported over the zero first base
coordinate induces zero on the actual fourth integral singular
homology of the central cusp fibre. -/
theorem central_homologyFourMap_eq_zero_of_baseFirstZero
    (f : C(X, QuotientCentralFibre C r))
    (hzero : ∀ x, baseTorusProjection C r hr (f x) 0 = 0) :
    singularHomologyMap f 4 = 0 := by
  obtain ⟨g, k, hfactor⟩ := baseFirstZero_overlap_homotopic_phase
    C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num) f hzero
  exact central_homologyFourMap_eq_zero_of_phase_homotopic_factor
    C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num) f g k hfactor

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
