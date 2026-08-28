import Wikipedia.HopfProblem.OrbitPairSubdivisionFaceRecovery

/-!
# Positive coordinate levels are exactly the chain thresholds

Each vertex enters a nested chain at a first face. Conversely, every face
of a strictly increasing chain contains a vertex which enters there. This
identifies the range of the strictly decreasing thresholds using only the
resulting geometric coordinates.
-/

noncomputable section

universe u

open PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz

variable {n k : ℕ}
variable (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
variable (t : Simplex k)

theorem coordinate_eq_tailWeight (j : Fin (k + 1)) (i : Fin (n + 1))
    (hi : ∀ l, ULift.up i ∈ (A l).finset ↔ j ≤ l) :
    chainCoordinate A t i = tailWeight A t j := by
  classical
  unfold chainCoordinate tailWeight
  apply Finset.sum_congr rfl
  intro l hl
  simp only [hi l]

theorem exists_entry_face (hA : Monotone A) (i : Fin (n + 1))
    (hi : 0 < chainCoordinate A t i) :
    ∃ j : Fin (k + 1), ∀ l, ULift.up i ∈ (A l).finset ↔ j ≤ l := by
  classical
  let J : Finset (Fin (k + 1)) := Finset.univ.filter (fun l ↦ ULift.up i ∈ (A l).finset)
  have hJ : J.Nonempty := by
    by_contra h
    have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hn : ∀ l, ULift.up i ∉ (A l).finset := by
      intro l hl
      have hm : l ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
      rw [he] at hm
      exact Finset.notMem_empty l hm
    have hz : chainCoordinate A t i = 0 := by simp [chainCoordinate, hn]
    exact (ne_of_gt hi) hz
  refine ⟨J.min' hJ, ?_⟩
  intro l
  constructor
  · intro hl
    exact Finset.min'_le J l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩)
  · intro hjl
    have hj : ULift.up i ∈ (A (J.min' hJ)).finset :=
      (Finset.mem_filter.mp (Finset.min'_mem J hJ)).2
    exact (hA hjl : (A (J.min' hJ)).finset ⊆ (A l).finset) hj

theorem exists_vertex_entering_face (hA : StrictMono A) (j : Fin (k + 1)) :
    ∃ i : Fin (n + 1), ∀ l, ULift.up i ∈ (A l).finset ↔ j ≤ l := by
  classical
  by_cases hj : j = 0
  · subst j
    obtain ⟨a, ha⟩ := (A 0).nonempty
    refine ⟨a.down, ?_⟩
    intro l
    change a ∈ (A l).finset ↔ (0 : Fin (k + 1)) ≤ l
    exact ⟨fun _ ↦ Fin.zero_le l,
      fun h ↦ (hA.monotone h : (A 0).finset ⊆ (A l).finset) ha⟩
  · have hjpos : 0 < j.val := by
      have hn : j.val ≠ 0 := fun h ↦ hj (Fin.ext h)
      omega
    let p : Fin (k + 1) := ⟨j.val - 1, by omega⟩
    have hpj : p < j := by change j.val - 1 < j.val; omega
    obtain ⟨a, ha, hpa⟩ := Finset.exists_of_ssubset
      (hA hpj : (A p).finset ⊂ (A j).finset)
    refine ⟨a.down, ?_⟩
    intro l
    change a ∈ (A l).finset ↔ j ≤ l
    constructor
    · intro hl
      by_contra hjl
      have hlp : l ≤ p := by
        change l.val ≤ j.val - 1
        have hlt : l.val < j.val := lt_of_not_ge hjl
        omega
      exact hpa ((hA.monotone hlp : (A l).finset ⊆ (A p).finset) hl)
    · intro hjl
      exact (hA.monotone hjl : (A j).finset ⊆ (A l).finset) ha

theorem tailWeight_range (hA : StrictMono A) (ht : ∀ j, 0 < t j) :
    Set.range (tailWeight A t) =
      {r : ℝ | ∃ i : Fin (n + 1), 0 < chainCoordinate A t i ∧ chainCoordinate A t i = r} := by
  ext r
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := exists_vertex_entering_face A hA j
    have he := coordinate_eq_tailWeight A t j i hi
    exact ⟨i, he.symm ▸ tailWeight_pos A t ht j, he⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := exists_entry_face A t hA.monotone i hi
    exact ⟨j, (coordinate_eq_tailWeight A t j i hj).symm⟩

end Wikipedia.HopfProblem.OrbitPair.Subdivision
