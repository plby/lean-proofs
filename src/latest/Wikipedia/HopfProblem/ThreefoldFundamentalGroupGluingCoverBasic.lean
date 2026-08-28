import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingTopology

/-!
# Finite stages of the actual threefold star cover

Start with the full regular family and attach any finite collection of
the three genuine fillings.  Distinct fillings are disjoint, so every
new attachment meets the preceding stage exactly in its regular overlap.
-/

noncomputable section

open Set TopologicalSpace

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- The actual regular piece together with the selected actual fillings. -/
def partialPatch (s : Finset Puncture) : Opens Space :=
  liftedPatch none ⊔ ⨆ i ∈ s, liftedPatch (some i)

@[simp] theorem mem_partialPatch (s : Finset Puncture) (x : Space) :
    x ∈ partialPatch s ↔ x ∈ liftedPatch none ∨ ∃ i ∈ s, x ∈ liftedPatch (some i) := by
  simp only [partialPatch, Opens.mem_sup, Opens.mem_iSup, exists_prop]

@[simp] theorem partialPatch_empty : partialPatch ∅ = liftedPatch none := by
  apply Opens.ext
  apply Set.ext
  intro x
  change x ∈ partialPatch ∅ ↔ x ∈ liftedPatch none
  simp only [mem_partialPatch, Finset.notMem_empty, false_and, exists_false, or_false]

theorem regular_le_partialPatch (s : Finset Puncture) : liftedPatch none ≤ partialPatch s :=
  fun x hx => (mem_partialPatch s x).mpr (Or.inl hx)

theorem filling_le_partialPatch {s : Finset Puncture} {i : Puncture} (hi : i ∈ s) :
    liftedPatch (some i) ≤ partialPatch s :=
  fun x hx => (mem_partialPatch s x).mpr (Or.inr ⟨i, hi, hx⟩)

theorem partialPatch_mono {s t : Finset Puncture} (hst : s ⊆ t) :
    partialPatch s ≤ partialPatch t := by
  intro x hx
  rcases (mem_partialPatch s x).mp hx with hx | ⟨i, hi, hx⟩
  · exact regular_le_partialPatch t hx
  · exact filling_le_partialPatch (hst hi) hx

@[simp] theorem partialPatch_insert (s : Finset Puncture) (i : Puncture) :
    partialPatch (insert i s) = partialPatch s ⊔ liftedPatch (some i) := by
  apply Opens.ext
  apply Set.ext
  intro x
  change x ∈ partialPatch (insert i s) ↔ x ∈ partialPatch s ⊔ liftedPatch (some i)
  simp only [mem_partialPatch, Finset.mem_insert, Opens.mem_sup]
  constructor
  · rintro (hr | ⟨j, hj | hj, hx⟩)
    · exact Or.inl (Or.inl hr)
    · subst j
      exact Or.inr hx
    · exact Or.inl (Or.inr ⟨j, hj, hx⟩)
  · rintro ((hr | ⟨j, hj, hx⟩) | hx)
    · exact Or.inl hr
    · exact Or.inr ⟨j, Or.inr hj, hx⟩
    · exact Or.inr ⟨i, Or.inl rfl, hx⟩

theorem partialPatch_le_insert (s : Finset Puncture) (i : Puncture) :
    partialPatch s ≤ partialPatch (insert i s) :=
  partialPatch_mono (Finset.subset_insert i s)

theorem filling_le_partialPatch_insert (s : Finset Puncture) (i : Puncture) :
    liftedPatch (some i) ≤ partialPatch (insert i s) :=
  filling_le_partialPatch (Finset.mem_insert_self i s)

/-- Once all three genuine fillings are attached, the stage is the entire space. -/
@[simp] theorem partialPatch_univ : partialPatch Finset.univ = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ ⋃ j : Index, (liftedPatch j : Set Space) := by
    rw [liftedPatch_iUnion]
    trivial
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  cases j with
  | none => exact regular_le_partialPatch _ hj
  | some i => exact filling_le_partialPatch (Finset.mem_univ i) hj

/-- A new filling only meets the old stage along its full regular overlap. -/
theorem partialPatch_inter_filling_eq (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (partialPatch s : Set Space) ∩ liftedPatch (some i) =
      (liftedPatch none : Set Space) ∩ liftedPatch (some i) := by
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    rcases (mem_partialPatch s x).mp hx with hr | ⟨j, hj, hxj⟩
    · exact ⟨hr, hxi⟩
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact (Set.disjoint_left.mp (liftedFilling_disjoint hji) hxj hxi).elim
  · rintro ⟨hr, hxi⟩
    exact ⟨regular_le_partialPatch s hr, hxi⟩

/-- Every actual finite attachment stage is path connected. -/
theorem partialPatch_isPathConnected (s : Finset Puncture) :
    IsPathConnected (partialPatch s : Set Space) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [partialPatch_empty]
      exact liftedPatch_isPathConnected none
  | @insert i s _ ih =>
      rw [partialPatch_insert, Opens.coe_sup]
      apply ih.union (liftedPatch_isPathConnected (some i))
      obtain ⟨x, hr, hi⟩ := liftedPatch_regular_inter_nonempty i
      exact ⟨x, regular_le_partialPatch s hr, hi⟩

theorem partialPatch_nonempty (s : Finset Puncture) : (partialPatch s : Set Space).Nonempty :=
  (partialPatch_isPathConnected s).nonempty

theorem partialPatch_pathConnectedSpace (s : Finset Puncture) :
    PathConnectedSpace (partialPatch s) :=
  isPathConnected_iff_pathConnectedSpace.mp (partialPatch_isPathConnected s)

/-- An actual point of the regular/filling overlap, independent of the previous stage. -/
def attachmentPoint (i : Puncture) : Space :=
  (liftedPatch_regular_inter_nonempty i).choose

theorem attachmentPoint_mem_regular (i : Puncture) : attachmentPoint i ∈ liftedPatch none :=
  (liftedPatch_regular_inter_nonempty i).choose_spec.1

theorem attachmentPoint_mem_filling (i : Puncture) : attachmentPoint i ∈ liftedPatch (some i) :=
  (liftedPatch_regular_inter_nonempty i).choose_spec.2

theorem attachmentPoint_mem_partialPatch (s : Finset Puncture) (i : Puncture) :
    attachmentPoint i ∈ partialPatch s :=
  regular_le_partialPatch s (attachmentPoint_mem_regular i)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
