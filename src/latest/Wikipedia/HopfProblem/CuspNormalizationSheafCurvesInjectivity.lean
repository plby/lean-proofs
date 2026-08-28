import Wikipedia.HopfProblem.CuspBoundaryIdentifications
import Wikipedia.HopfProblem.ToricDoubleLocus

/-!
# Injectivity on the normalization boundary curves

For a fixed positive edge direction, a triangular chart contains at most one
edge with that direction. Consequently a lattice translation identifying two
points of the same boundary curve in the component at zero must be trivial.
The opposite-boundary equivalence gives the corresponding result for the
negative direction. These statements require no analytic hypotheses on the
twisting matrix.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

/-- A fixed positive edge direction has at most one start among the branch
vertices at any point of the toric space. -/
theorem branchVertices_edgeStart_unique (x : Space) (i : Fin 3)
    {v w : Fin 2 → ℤ} (hv : v ∈ branchVertices x)
    (hv' : v + edgeDirection i ∈ branchVertices x)
    (hw : w ∈ branchVertices x)
    (hw' : w + edgeDirection i ∈ branchVertices x) : v = w := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [branchVertices_inclusion] at hv hv' hw hw'
  obtain ⟨j, _, rfl⟩ := hv
  obtain ⟨k, _, hk⟩ := hv'
  obtain ⟨l, _, rfl⟩ := hw
  obtain ⟨m, _, hm⟩ := hw'
  have hj := ((vertices_edge_iff s i j k).mp hk).1
  have hl := ((vertices_edge_iff s i l m).mp hm).1
  rw [hj, hl]

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual normalization projection is injective on each positive
boundary curve, including its two corner points. -/
theorem componentProjection_boundary_injective (i : Fin 3) :
    Function.Injective (fun x : componentBoundary (edgeDirection i) =>
      componentProjection C ε hε x.1) := by
  let := tubeAction C (disc ε)
  intro x y hxy
  have horb := Quotient.exact hxy
  change componentLift ε hε x.1 ∈
    MulAction.orbit LatticeGroup (componentLift ε hε y.1) at horb
  obtain ⟨g, hg⟩ := horb
  have he : twistedTranslate C g.toAdd (y.1 : Space) = (x.1 : Space) :=
    congrArg Subtype.val hg
  have hv : -cuspVector g.toAdd ∈ branchVertices (y.1 : Space) := by
    change (y.1 : Space) ∈ rayDivisor (-cuspVector g.toAdd)
    have hx : twistedTranslate C g.toAdd (y.1 : Space) ∈ rayDivisor 0 := by
      rw [he]
      exact x.1.2
    simpa only [zero_sub] using
      (twistedTranslate_mem_rayDivisor C g.toAdd 0 (y.1 : Space)).mp hx
  have hv' : -cuspVector g.toAdd + edgeDirection i ∈
      branchVertices (y.1 : Space) := by
    change (y.1 : Space) ∈ rayDivisor (-cuspVector g.toAdd + edgeDirection i)
    rw [add_comm, ← sub_eq_add_neg]
    apply (twistedTranslate_mem_rayDivisor C g.toAdd (edgeDirection i) _).mp
    rw [he]
    exact x.2
  have hd : -cuspVector g.toAdd = 0 :=
    branchVertices_edgeStart_unique (y.1 : Space) i hv hv' y.1.2
      (by rw [zero_add]; exact y.2)
  have hg0 : g.toAdd = 0 :=
    cuspVector_injective ((neg_eq_zero.mp hd).trans cuspVector_zero.symm)
  rw [hg0, twistedTranslate_zero] at he
  exact Subtype.ext (Subtype.ext he.symm)

/-- The same projection is injective on the opposite boundary curve. -/
theorem componentProjection_negativeBoundary_injective (i : Fin 3) :
    Function.Injective (fun x : componentBoundary (-edgeDirection i) =>
      componentProjection C ε hε x.1) := by
  intro x y hxy
  let e := oppositeBoundaryEquiv C (edgeDirection i)
  apply e.symm.injective
  apply componentProjection_boundary_injective C ε hε i
  have hx := componentProjection_oppositeBoundaryMap C ε hε (edgeDirection i) (e.symm x)
  have hy := componentProjection_oppositeBoundaryMap C ε hε (edgeDirection i) (e.symm y)
  change componentProjection C ε hε (e (e.symm x)).1 = _ at hx
  change componentProjection C ε hε (e (e.symm y)).1 = _ at hy
  rw [e.apply_symm_apply] at hx hy
  exact hx.symm.trans (hxy.trans hy)

end Wikipedia.HopfProblem.CuspQuotient
