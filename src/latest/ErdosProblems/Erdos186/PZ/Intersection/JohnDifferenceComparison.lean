/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.LemmaSeven
import ErdosProblems.Erdos186.CFP.BiluFreiman

/-!
# Comparing a centered John progression with an uncentered CFP core

The discrete-John certificate is centered at a lattice point of the thin
region, whereas the CFP cardinality estimates are stated for the original
core together with zero.  Because the thin region also contains zero, the
doubled symmetric John progression contains that uncentered core.  This is
the exact translation cancellation used in the slab branch of PZ Lemma 14.
-/

namespace Erdos186.PZ.Intersection

open OneStepAssembly

noncomputable section

set_option autoImplicit false

/-- A discrete-John outer progression is symmetric with its displayed
radii. -/
theorem centeredDiscreteJohn_outer_symmetric
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega) :
    J.certificate.outer.Symmetric := by
  exact ⟨J.certificate.radii, ⟨rfl, rfl⟩⟩

/-- If zero and a finite core belong to the region used by a centered John
certificate, the doubled outer progression contains the core together with
zero in the original coordinates. -/
theorem insert_core_subset_dilate_two_outer
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega)
    (core : Finset (LatticePoint d))
    (hcore : core ⊆ boxLatticePointsIn B Omega)
    (hzero : (0 : LatticePoint d) ∈ boxLatticePointsIn B Omega) :
    insert 0 core ⊆ (J.certificate.outer.dilate 2).carrier := by
  have hcentered := J.centeredRestriction_subset_outer
    (A := B.carrier) (Finset.Subset.rfl)
  have hsymm := centeredDiscreteJohn_outer_symmetric J
  have hminusCenter : -J.center ∈ J.certificate.outer.carrier := by
    apply hcentered
    exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩
  have hplusCenter : J.center ∈ J.certificate.outer.carrier := by
    simpa using hsymm.neg_mem_carrier_of_mem hminusCenter
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact (hsymm.dilate 2).zero_mem_carrier
  · have hminus : x - J.center ∈ J.certificate.outer.carrier := by
      apply hcentered
      exact Finset.mem_image.mpr ⟨x, hcore hx, by
        simp [sub_eq_add_neg, add_comm]⟩
    have hadd := J.certificate.outer.add_mem_dilate_two hminus hplusCenter
    simpa [sub_eq_add_neg, add_assoc] using hadd

/-- The doubled comparison progression has the expected dimension-only
volume cost. -/
theorem dilate_two_outer_volume_le
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega) :
    (J.certificate.outer.dilate 2).volume ≤
      3 ^ J.rank * J.certificate.outer.volume := by
  simpa using J.certificate.outer.volume_dilate_le 2

/-- Dimension-sensitive CFP comparison with a centered John certificate.
The extra factor `3^rank` is precisely the cost of doubling the outer
progression to undo its choice of center. -/
theorem cfpWitness_dimensionIncrease_centeredDiscreteJohn
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    {B : IntegerBox d} {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega)
    (hcore : W.core ⊆ boxLatticePointsIn B Omega)
    (hzero : (0 : LatticePoint d) ∈ boxLatticePointsIn B Omega)
    (hrank : J.rank ≤ W.rank) :
    k ^ (W.rank - J.rank) * W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ J.rank *
        (3 ^ J.rank * J.certificate.outer.volume) := by
  have hcomparison := Reduction.Estimates.cfpWitness_dimensionIncrease
    W (J.certificate.outer.dilate 2)
      (insert_core_subset_dilate_two_outer J W.core hcore hzero) hrank
  exact hcomparison.trans (Nat.mul_le_mul_left _
    (dilate_two_outer_volume_le J))

/-- Real-cast form used by the parameter hierarchy. -/
theorem cfpWitness_dimensionIncrease_centeredDiscreteJohn_real
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    {B : IntegerBox d} {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega)
    (hcore : W.core ⊆ boxLatticePointsIn B Omega)
    (hzero : (0 : LatticePoint d) ∈ boxLatticePointsIn B Omega)
    (hrank : J.rank ≤ W.rank) :
    (k : ℝ) ^ (W.rank - J.rank) * W.progression.volume ≤
      (2 : ℝ) ^ W.rank * (2 * W.scaleDen) ^ J.rank *
        ((3 : ℝ) ^ J.rank * J.certificate.outer.volume) := by
  exact_mod_cast cfpWitness_dimensionIncrease_centeredDiscreteJohn
    W J hcore hzero hrank

end

end Erdos186.PZ.Intersection
