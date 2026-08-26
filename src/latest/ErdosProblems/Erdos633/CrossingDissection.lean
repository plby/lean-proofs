import ErdosProblems.Erdos633.GenericCrossing

/-!
# Recovering an actual dissection from a crossing identity

An almost-everywhere sum of interior indicators determines coverage and
pairwise disjoint interiors for finitely many nondegenerate triangles.
Consequently a common orientation and a boundary crossing identity suffice
to construct the geometric dissection. Extracting the transformed boundary
identity from the original dissection is a separate remaining obligation.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators

noncomputable def Triangle.interiorOccupancy (P : Triangle) : ℂ → ℝ :=
  (interior P.carrier).indicator (fun _ => 1)

theorem Triangle.interiorOccupancy_of_mem (P : Triangle) {z : ℂ}
    (hz : z ∈ interior P.carrier) : P.interiorOccupancy z = 1 :=
  Set.indicator_of_mem hz _

theorem Triangle.interiorOccupancy_of_not_mem (P : Triangle) {z : ℂ}
    (hz : z ∉ interior P.carrier) : P.interiorOccupancy z = 0 :=
  Set.indicator_of_notMem hz _

theorem Triangle.interiorOccupancy_nonneg (P : Triangle) (z : ℂ) :
    0 ≤ P.interiorOccupancy z := by
  classical
  by_cases hz : z ∈ interior P.carrier
  · rw [P.interiorOccupancy_of_mem hz]
    norm_num
  · rw [P.interiorOccupancy_of_not_mem hz]

theorem Triangle.interiorOccupancy_le_one (P : Triangle) (z : ℂ) :
    P.interiorOccupancy z ≤ 1 := by
  classical
  by_cases hz : z ∈ interior P.carrier
  · rw [P.interiorOccupancy_of_mem hz]
  · rw [P.interiorOccupancy_of_not_mem hz]
    norm_num

theorem Triangle.crossingAt_ae_eq_orientation_mul_occupancy (P : Triangle) :
    (fun z => (P.crossingAt z : ℝ)) =ᵐ[volume]
      fun z => P.orientationSign * P.interiorOccupancy z := by
  classical
  filter_upwards [P.crossingAt_ae_eq_indicator] with z hz
  rw [hz]
  by_cases hi : z ∈ interior P.carrier
  · rw [Set.indicator_of_mem hi, P.interiorOccupancy_of_mem hi, mul_one]
  · rw [Set.indicator_of_notMem hi, P.interiorOccupancy_of_not_mem hi, mul_zero]

theorem occupancy_identity_geometry (P : Triangle) {N : ℕ} (Q : Fin N → Triangle)
    (h : P.interiorOccupancy =ᵐ[volume] fun z => ∑ i : Fin N, (Q i).interiorOccupancy z) :
    (⋃ i : Fin N, (Q i).carrier) = P.carrier ∧
      Pairwise fun i j : Fin N => Disjoint (interior (Q i).carrier) (interior (Q j).carrier) := by
  classical
  have hdense := Measure.dense_of_ae h
  have hsub (i : Fin N) : (Q i).carrier ⊆ P.carrier := by
    have hi : interior (Q i).carrier ⊆ P.carrier := by
      intro x hx
      by_contra hxP
      obtain ⟨z, ⟨hzi, hzP⟩, hze⟩ := hdense.inter_open_nonempty
        (interior (Q i).carrier ∩ P.carrierᶜ)
        (isOpen_interior.inter P.isCompact_carrier.isClosed.isOpen_compl) ⟨x, hx, hxP⟩
      have hzPi : z ∉ interior P.carrier := fun hz => hzP (interior_subset hz)
      have hle := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => (Q j).interiorOccupancy_nonneg z)
        (Finset.mem_univ i)
      change P.interiorOccupancy z = ∑ j : Fin N, (Q j).interiorOccupancy z at hze
      rw [(Q i).interiorOccupancy_of_mem hzi, ← hze, P.interiorOccupancy_of_not_mem hzPi] at hle
      norm_num at hle
    calc
      (Q i).carrier = closure (interior (Q i).carrier) := (Q i).closure_interior_carrier.symm
      _ ⊆ closure P.carrier := closure_mono hi
      _ = P.carrier := P.isCompact_carrier.isClosed.closure_eq
  have hclosed : IsClosed (⋃ i : Fin N, (Q i).carrier) :=
    isClosed_iUnion_of_finite (fun i => (Q i).isCompact_carrier.isClosed)
  have hcover : P.carrier ⊆ ⋃ i : Fin N, (Q i).carrier := by
    have hi : interior P.carrier ⊆ ⋃ i : Fin N, (Q i).carrier := by
      intro x hx
      by_contra hxQ
      obtain ⟨z, ⟨hzP, hzQ⟩, hze⟩ := hdense.inter_open_nonempty
        (interior P.carrier ∩ (⋃ i : Fin N, (Q i).carrier)ᶜ)
        (isOpen_interior.inter hclosed.isOpen_compl) ⟨x, hx, hxQ⟩
      have hznone (i : Fin N) : z ∉ interior (Q i).carrier :=
        fun hz => hzQ (Set.mem_iUnion.mpr ⟨i, interior_subset hz⟩)
      have hsum : (∑ i : Fin N, (Q i).interiorOccupancy z) = 0 :=
        Finset.sum_eq_zero (fun i _ => (Q i).interiorOccupancy_of_not_mem (hznone i))
      change P.interiorOccupancy z = ∑ i : Fin N, (Q i).interiorOccupancy z at hze
      rw [P.interiorOccupancy_of_mem hzP, hsum] at hze
      norm_num at hze
    calc
      P.carrier = closure (interior P.carrier) := P.closure_interior_carrier.symm
      _ ⊆ closure (⋃ i : Fin N, (Q i).carrier) := closure_mono hi
      _ = ⋃ i : Fin N, (Q i).carrier := hclosed.closure_eq
  refine ⟨Set.Subset.antisymm (Set.iUnion_subset hsub) hcover, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨z, ⟨hzi, hzj⟩, hze⟩ := hdense.inter_open_nonempty
    (interior (Q i).carrier ∩ interior (Q j).carrier)
    (isOpen_interior.inter isOpen_interior) ⟨x, hxi, hxj⟩
  have hle := Finset.add_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) => (Q k).interiorOccupancy_nonneg z)
    (Finset.mem_univ i) (Finset.mem_univ j) hij
  change P.interiorOccupancy z = ∑ k : Fin N, (Q k).interiorOccupancy z at hze
  rw [(Q i).interiorOccupancy_of_mem hzi, (Q j).interiorOccupancy_of_mem hzj, ← hze] at hle
  have hp := P.interiorOccupancy_le_one z
  linarith

def TriangleDissection.ofOccupancy (P : Triangle) {N : ℕ} (Q : Fin N → Triangle)
    (h : P.interiorOccupancy =ᵐ[volume] fun z => ∑ i : Fin N, (Q i).interiorOccupancy z) :
    TriangleDissection P N where
  tile := Q
  covers := (occupancy_identity_geometry P Q h).1
  disjoint := (occupancy_identity_geometry P Q h).2

theorem occupancy_identity_of_crossing (P : Triangle) {N : ℕ} (Q : Fin N → Triangle)
    (hsign : ∀ i : Fin N, (Q i).orientationSign = P.orientationSign)
    (h : (fun z => (P.crossingAt z : ℝ)) =ᵐ[volume]
      fun z => ∑ i : Fin N, ((Q i).crossingAt z : ℝ)) :
    P.interiorOccupancy =ᵐ[volume] fun z => ∑ i : Fin N, (Q i).interiorOccupancy z := by
  have hQ : ∀ᵐ z ∂volume, ∀ i : Fin N, ((Q i).crossingAt z : ℝ) =
      (Q i).orientationSign * (Q i).interiorOccupancy z :=
    ae_all_iff.mpr (fun i => (Q i).crossingAt_ae_eq_orientation_mul_occupancy)
  filter_upwards [h, P.crossingAt_ae_eq_orientation_mul_occupancy, hQ] with z hz hP hQ
  rw [hP] at hz
  simp_rw [hQ, hsign] at hz
  rw [← Finset.mul_sum] at hz
  have hsign0 : P.orientationSign ≠ 0 := by
    intro hzero
    have hs := P.orientationSign_mul_self
    rw [hzero, zero_mul] at hs
    exact zero_ne_one hs
  exact mul_left_cancel₀ hsign0 hz

/-- A boundary identity supplies coverage and disjointness, not merely an
area equality. The tile field of the resulting dissection is exactly `Q`. -/
def TriangleDissection.ofCrossing (P : Triangle) {N : ℕ} (Q : Fin N → Triangle)
    (hsign : ∀ i : Fin N, (Q i).orientationSign = P.orientationSign)
    (h : (fun z => (P.crossingAt z : ℝ)) =ᵐ[volume]
      fun z => ∑ i : Fin N, ((Q i).crossingAt z : ℝ)) : TriangleDissection P N :=
  TriangleDissection.ofOccupancy P Q (occupancy_identity_of_crossing P Q hsign h)

theorem occupancy_identity_of_oriented_crossing (P : Triangle) {N : ℕ}
    (Q : Fin N → Triangle)
    (h : (fun z => P.orientationSign * (P.crossingAt z : ℝ)) =ᵐ[volume]
      fun z => ∑ i : Fin N, (Q i).orientationSign * ((Q i).crossingAt z : ℝ)) :
    P.interiorOccupancy =ᵐ[volume] fun z => ∑ i : Fin N, (Q i).interiorOccupancy z := by
  have hQ : ∀ᵐ z ∂volume, ∀ i : Fin N, ((Q i).crossingAt z : ℝ) =
      (Q i).orientationSign * (Q i).interiorOccupancy z :=
    ae_all_iff.mpr (fun i => (Q i).crossingAt_ae_eq_orientation_mul_occupancy)
  filter_upwards [h, P.crossingAt_ae_eq_orientation_mul_occupancy, hQ] with z hz hP hQ
  rw [hP] at hz
  simp_rw [hQ, ← mul_assoc, Triangle.orientationSign_mul_self, one_mul] at hz
  exact hz

/-- This version permits arbitrary vertex labellings and reflected tiles. -/
def TriangleDissection.ofOrientedCrossing (P : Triangle) {N : ℕ}
    (Q : Fin N → Triangle)
    (h : (fun z => P.orientationSign * (P.crossingAt z : ℝ)) =ᵐ[volume]
      fun z => ∑ i : Fin N, (Q i).orientationSign * ((Q i).crossingAt z : ℝ)) :
    TriangleDissection P N :=
  TriangleDissection.ofOccupancy P Q (occupancy_identity_of_oriented_crossing P Q h)

end Erdos633
