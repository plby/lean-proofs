import Wikipedia.HopfProblem.CuspSimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The universal cusp cover and its fundamental group

Corollary 4.8 of `tex/s6.tex` identifies the universal cover of the cusp
neighbourhood and its fundamental group with the rank-two lattice. Here the
cover is the actual toric tube and the base is the actual twisted orbit
quotient. Simple connectivity of the tube and the established quotient
covering map give the isomorphism through Mathlib's monodromy construction.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- Monodromy identifies the fundamental group at the image of a chosen point
upstairs with the actual acting lattice. Commutativity removes the opposite
group that appears in the general quotient-covering theorem. -/
def fundamentalGroupEquivAt (e : Tube (disc ε)) :
    FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e) ≃* LatticeGroup := by
  let := tubeAction C (disc ε)
  let := tube_simplyConnected hε
  let hq := quotientMap_covering C ε hε hε1 hC hR
  exact (hq.fundamentalGroupEquiv ⟨e, rfl⟩).trans MulOpposite.opMulEquiv.symm

/-- The fundamental group of the actual cusp neighbourhood is `ℤ²`, at every
basepoint. No fundamental-group presentation is assumed. -/
def fundamentalGroupEquiv (x : QuotientSpace C ε) :
    FundamentalGroup (QuotientSpace C ε) x ≃* LatticeGroup := by
  let := tubeAction C (disc ε)
  let := tube_simplyConnected hε
  let hq := quotientMap_covering C ε hε hε1 hC hR
  let e : quotientMap C ε ⁻¹' {x} :=
    ⟨(hq.surjective x).choose, (hq.surjective x).choose_spec⟩
  exact (hq.fundamentalGroupEquiv e).trans MulOpposite.opMulEquiv.symm

/-- The lattice element assigned to a loop is exactly the translation taking
the chosen lift of its basepoint to the endpoint of its lifted loop. -/
theorem fundamentalGroupEquivAt_monodromy (e : Tube (disc ε))
    (γ : FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e)) :
    letI := tubeAction C (disc ε)
    tubeTranslate C (disc ε) (fundamentalGroupEquivAt C ε hε hε1 hC hR e γ).toAdd e =
      ((quotientMap_covering C ε hε hε1 hC hR).isCoveringMap.monodromy γ
        ⟨e, rfl⟩ : Tube (disc ε)) := by
  let := tubeAction C (disc ε)
  let := tube_simplyConnected hε
  exact (quotientMap_covering C ε hε hε1 hC hR).unop_fundamentalGroupToMulOpposite_smul

/-- The pointed universal lifting property: the cusp projection lifts uniquely
through every covering of the cusp neighbourhood once a point above the
chosen basepoint has been specified. -/
theorem existsUnique_cover_lift (hε : 0 < ε) {Y : Type*} [TopologicalSpace Y]
    {p : Y → QuotientSpace C ε} (hp : IsCoveringMap p)
    (a : Tube (disc ε)) (b : Y) (hb : p b = quotientMap C ε a) :
    ∃! F : ContinuousMap (Tube (disc ε)) Y,
      F a = b ∧ p ∘ F = quotientMap C ε := by
  let : SimplyConnectedSpace (Tube (disc ε)) := tube_simplyConnected hε
  let : LocallyPathConnectedSpace (Tube (disc ε)) :=
    ChartedSpace.locallyPathConnectedSpace (CoordinateSpace 3) (Tube (disc ε))
  exact hp.existsUnique_continuousMap_lifts
    ⟨quotientMap C ε, quotientMap_continuous C ε⟩ a b hb

/-- Holomorphic input on any disc supplies an actual smaller cusp
neighbourhood whose fundamental group is the rank-two lattice. -/
theorem exists_fundamentalGroupEquiv {r : ℝ} (hr : 0 < r)
    (hCr : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η : ℝ, 0 < η ∧ η < r ∧ ∀ x : QuotientSpace C η,
      Nonempty (FundamentalGroup (QuotientSpace C η) x ≃* LatticeGroup) := by
  obtain ⟨η, hη, hηr, hη1, hRη, hCη⟩ := exists_admissible_radius C hr hCr
  exact ⟨η, hη, hηr, fun x => ⟨fundamentalGroupEquiv C η hη hη1 hCη hRη x⟩⟩

end Wikipedia.HopfProblem.CuspQuotient
