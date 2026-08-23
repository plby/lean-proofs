/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.AbsorberWellSpread
import ErdosProblems.Erdos551.External.Erdos207.OutsideAvailability

/-!
# Local characterization of constrained-greedy legality

A new triangle is legal precisely when it is new, all three of its pairs are
uncovered, and it does not complete a forbidden configuration.  This turns
the cover-down analysis into explicit counts of edge and configuration
threats.
-/

namespace Erdos207

open Finset

/-- `T` completes a member of `F` over the already chosen family `P`. -/
def CompletesForbidden {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (T : TripleOn V) : Prop :=
  ∃ S ∈ F, T ∈ S ∧ S.erase T ⊆ P

/-- A triangle can be inserted into a packing exactly when none of its pairs
has already been covered. -/
theorem packing_insert_iff_avoids_coveredGraph
    {V : Type*} [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) (T : TripleOn V)
    (hTP : T ∉ P) :
    IsPackingOn (insert T P) ↔ TriangleAvoidsGraph (coveredGraph P) T := by
  constructor
  · intro hins u hu v hv huv hcovered
    obtain ⟨U, hUP, huU, hvU, _⟩ := coveredGraph_adj.mp hcovered
    have hTU := hins u v huv T (mem_insert_self T P) hu hv U
      (mem_insert_of_mem hUP) huU hvU
    exact hTP (hTU ▸ hUP)
  · intro hav u v huv A hA huA hvA C hC huC hvC
    rw [mem_insert] at hA hC
    rcases hA with rfl | hAP
    · rcases hC with rfl | hCP
      · rfl
      · exfalso
        exact hav u huA v hvA huv
          (coveredGraph_adj.mpr ⟨C, hCP, huC, hvC, huv⟩)
    · rcases hC with rfl | hCP
      · exfalso
        exact hav u huC v hvC huv
          (coveredGraph_adj.mpr ⟨A, hAP, huA, hvA, huv⟩)
      · exact hP u v huv A hAP huA hvA C hCP huC hvC

/-- Over an already forbidden-free packing, failure of forbidden-freeness
after inserting `T` is exactly completion of one forbidden member. -/
theorem avoidsForbidden_insert_iff_not_completes
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    (hP : AvoidsForbidden P F) (T : TripleOn V) :
    AvoidsForbidden (insert T P) F ↔ ¬ CompletesForbidden F P T := by
  constructor
  · intro hins hcomplete
    obtain ⟨S, hSF, hTS, hSerase⟩ := hcomplete
    apply hins S hSF
    intro U hUS
    by_cases hUT : U = T
    · subst U
      exact mem_insert_self T P
    · exact mem_insert_of_mem (hSerase (mem_erase.mpr ⟨hUT, hUS⟩))
  · intro hnot S hSF hSinsert
    by_cases hTS : T ∈ S
    · apply hnot
      refine ⟨S, hSF, hTS, ?_⟩
      intro U hUerase
      have hUS : U ∈ S := (mem_erase.mp hUerase).2
      rcases mem_insert.mp (hSinsert hUS) with hUT | hUP
      · exact ((mem_erase.mp hUerase).1 hUT).elim
      · exact hUP
    · apply hP S hSF
      intro U hUS
      rcases mem_insert.mp (hSinsert hUS) with hUT | hUP
      · subst U
        exact (hTS hUS).elim
      · exact hUP

/-- Exact local form of `IsLegalExtension`. -/
theorem isLegalExtension_iff
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (T : TripleOn V) :
    IsLegalExtension F P T ↔
      T ∉ P ∧ TriangleAvoidsGraph (coveredGraph P) T ∧
        ¬ CompletesForbidden F P T := by
  rw [IsLegalExtension, and_congr_right_iff]
  intro hTP
  rw [packing_insert_iff_avoids_coveredGraph hpacking T hTP,
    avoidsForbidden_insert_iff_not_completes havoid T]

end Erdos207
