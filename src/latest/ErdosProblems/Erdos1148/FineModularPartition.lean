import ErdosProblems.Erdos1148.FiniteCoverPartition
import ErdosProblems.Erdos1148.CoherentNeighborhoods
import ErdosProblems.Erdos1148.NullBoundaryNeighborhoods
import ErdosProblems.Erdos1148.CompactCoreLiftRadius
import ErdosProblems.Erdos1148.ModularTopology

/-! # Fine modular partitions with one exceptional atom -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

structure FineModularPartition where
  size : ℕ
  partition : FiniteMeasurablePartition ModularOrbitSpace (Option (Fin size))
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ 1 / 192
  core : Set ModularOrbitSpace
  compact_core : IsCompact core
  regular_subset_core : ∀ i, partition.atom (some i) ⊆ core
  regular_lifts : ∀ i, ∃ E : Set SL(2, ℝ), modularMk '' E = partition.atom (some i) ∧
    LiftForwardClose radius 0 E
  lift_upgrade : ∀ g h : SL(2, ℝ), modularMk g ∈ core →
    EntryCloseOne (radius * Real.exp 1) (g⁻¹ * h) →
    (modularMk g, modularMk h) ∈ modularClosePairs radius → EntryCloseOne radius (g⁻¹ * h)

lemma coherent_lifts_restrict {η : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η 0 E) {A : Set ModularOrbitSpace} (hA : A ⊆ modularMk '' E) :
    ∃ F : Set SL(2, ℝ), modularMk '' F = A ∧ LiftForwardClose η 0 F := by
  refine ⟨E ∩ modularMk ⁻¹' A, ?_, hE.mono Set.inter_subset_left⟩
  rw [Set.image_inter_preimage, Set.inter_eq_right.mpr hA]

theorem exists_fine_modular_partition (ν : Measure ModularOrbitSpace) [SFinite ν]
    {K : Set ModularOrbitSpace} (hK : IsCompact K) :
    ∃ P : FineModularPartition, P.partition.atom none ⊆ Kᶜ ∧
      ∀ i, ν (frontier (P.partition.atom i)) = 0 := by
  classical
  obtain ⟨U, hUopen, hKU, hUc, hUnull⟩ := exists_open_compact_null_boundary_superset ν hK
  obtain ⟨η, hηpos, hηle, hradius⟩ := exists_compact_lift_radius hUc
  have hneighborhood (x : closure U) : ∃ (V : Set ModularOrbitSpace) (E : Set SL(2, ℝ)),
      IsOpen V ∧ x.val ∈ V ∧ ν (frontier V) = 0 ∧
      modularMk '' E = V ∧ LiftForwardClose η 0 E := by
    obtain ⟨W, E, hWopen, hxW, hEW, hE⟩ := exists_open_coherent_modular_neighborhood hηpos x.val
    obtain ⟨V, hVopen, hxV, hVW, hVnull⟩ := exists_open_null_boundary_neighborhood ν hWopen hxW
    obtain ⟨F, hF, hclose⟩ := coherent_lifts_restrict hE (hVW.trans_eq hEW.symm)
    exact ⟨V, F, hVopen, hxV, hVnull, hF, hclose⟩
  choose V E hVopen hxV hVnull hEV hE using hneighborhood
  obtain ⟨s, hcover⟩ := hUc.elim_finite_subcover V hVopen (by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let e := Fintype.equivFin s
  let N := Fintype.card s
  let W : Fin N → Set ModularOrbitSpace := fun i => V (e.symm i).val
  have hWopen (i : Fin N) : IsOpen (W i) := hVopen (e.symm i).val
  have hWnull (i : Fin N) : ν (frontier (W i)) = 0 := hVnull (e.symm i).val
  have hUcover : U ⊆ ⋃ i, W i := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hcover (subset_closure hx))
    refine Set.mem_iUnion.mpr ⟨e ⟨a, ha⟩, ?_⟩
    change x ∈ V (e.symm (e ⟨a, ha⟩)).val
    rw [e.symm_apply_apply]
    exact hxa
  let P := partitionOfFiniteCover U W hUopen.measurableSet
    (fun i => (hWopen i).measurableSet) hUcover
  have hlifts (i : Fin N) : ∃ F : Set SL(2, ℝ),
      modularMk '' F = P.atom (some i) ∧ LiftForwardClose η 0 F := by
    apply coherent_lifts_restrict (hE (e.symm i).val)
    have hsub := finiteCoverAtom_some_subset U W i
    exact hsub.trans_eq (hEV (e.symm i).val).symm
  let Q : FineModularPartition := {
    size := N
    partition := P
    radius := η
    radius_pos := hηpos
    radius_le := hηle
    core := closure U
    compact_core := hUc
    regular_subset_core := fun _ => Set.inter_subset_left.trans subset_closure
    regular_lifts := hlifts
    lift_upgrade := hradius }
  refine ⟨Q, ?_, ?_⟩
  · exact Set.compl_subset_compl.mpr hKU
  · exact measure_frontier_finiteCoverAtom_eq_zero ν U W hUnull hWnull

theorem FineModularPartition.regular_pairs (P : FineModularPartition) (i : Fin P.size) :
    P.partition.atom (some i) ×ˢ P.partition.atom (some i) ⊆ modularClosePairs P.radius := by
  obtain ⟨E, hE, hclose⟩ := P.regular_lifts i
  rw [← hE]
  rintro ⟨_, _⟩ ⟨⟨g, hg, rfl⟩, ⟨h, hh, rfl⟩⟩
  refine ⟨g, h, rfl, ?_⟩
  have hc := hclose g hg h hh 0 ⟨le_rfl, le_rfl⟩
  simpa only [diagonalFlow_zero, mul_one] using hc

end Erdos1148.DukeArithmetic
