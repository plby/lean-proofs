import Wikipedia.HopfProblem.DegreeCollapseFiniteSheetPreparation

/-!
# The exact finite union of original surface images is one smooth image

Use a finite disjoint sum of the original source surface. The existing
sum atlas has the same model and every component map retains its original
formula. This supplies the protected smooth image required by the relative
passage construction, including the empty family case.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

def sheetSum (X : Type) : ℕ → Type
  | 0 => PEmpty
  | n + 1 => X ⊕ sheetSum X n

variable {X : Type} [TopologicalSpace X]

instance sheetSumTopology : (n : ℕ) → TopologicalSpace (sheetSum X n)
  | 0 => inferInstanceAs (TopologicalSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumTopology n
    inferInstanceAs (TopologicalSpace (X ⊕ sheetSum X n))

instance sheetSumCompact [CompactSpace X] : (n : ℕ) → CompactSpace (sheetSum X n)
  | 0 => inferInstanceAs (CompactSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumCompact n
    inferInstanceAs (CompactSpace (X ⊕ sheetSum X n))

instance sheetSumT2 [T2Space X] : (n : ℕ) → T2Space (sheetSum X n)
  | 0 => inferInstanceAs (T2Space PEmpty)
  | n + 1 =>
    let _ := sheetSumT2 n
    inferInstanceAs (T2Space (X ⊕ sheetSum X n))

instance sheetSumSecondCountable [SecondCountableTopology X] :
    (n : ℕ) → SecondCountableTopology (sheetSum X n)
  | 0 => inferInstanceAs (SecondCountableTopology PEmpty)
  | n + 1 =>
    let _ := sheetSumSecondCountable n
    inferInstanceAs (SecondCountableTopology (X ⊕ sheetSum X n))

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H X]

instance sheetSumChartedSpace : (n : ℕ) → ChartedSpace H (sheetSum X n)
  | 0 => ChartedSpace.empty H PEmpty
  | n + 1 =>
    let _ := sheetSumChartedSpace n
    inferInstanceAs (ChartedSpace H (X ⊕ sheetSum X n))

instance sheetSumIsManifold [IsManifold I ∞ X] : (n : ℕ) → IsManifold I ∞ (sheetSum X n)
  | 0 =>
    let _ : ChartedSpace H PEmpty := sheetSumChartedSpace (X := X) 0
    inferInstanceAs (IsManifold I ∞ PEmpty)
  | n + 1 =>
    let _ := sheetSumIsManifold n
    inferInstanceAs (IsManifold I ∞ (X ⊕ sheetSum X n))

def sheetSumMap {N : Type} : (n : ℕ) → (Fin n → X → N) → sheetSum X n → N
  | 0, _, x => x.elim
  | n + 1, a, x => Sum.elim (a 0) (sheetSumMap n (fun i => a i.succ)) x

theorem range_sheetSumMap {N : Type} (n : ℕ) (a : Fin n → X → N) :
    range (sheetSumMap n a) = ⋃ i, range (a i) := by
  induction n with
  | zero =>
    ext y
    simp only [mem_range, mem_iUnion]
    constructor
    · rintro ⟨x, _⟩
      exact x.elim
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    ext y
    constructor
    · rintro ⟨x, hx⟩
      rcases x with x | x
      · exact mem_iUnion.mpr ⟨0, ⟨x, hx⟩⟩
      · have hy : y ∈ range (sheetSumMap n (fun i => a i.succ)) := ⟨x, hx⟩
        rw [ih] at hy
        obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨i.succ, hi⟩
    · intro hy
      obtain ⟨i, x, hx⟩ := mem_iUnion.mp hy
      cases i using Fin.cases with
      | zero => exact ⟨Sum.inl x, hx⟩
      | succ i =>
        have hy' : y ∈ ⋃ i : Fin n, range (a i.succ) := mem_iUnion.mpr ⟨i, ⟨x, hx⟩⟩
        rw [← ih] at hy'
        obtain ⟨z, hz⟩ := hy'
        exact ⟨Sum.inr z, hz⟩

variable {G K N : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  [TopologicalSpace N] [ChartedSpace K N]

theorem contMDiff_sheetSumMap (n : ℕ) (a : Fin n → X → N)
    (ha : ∀ i, ContMDiff I J ∞ (a i)) : ContMDiff I J ∞ (sheetSumMap n a) := by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih =>
    exact (ha 0).sumElim (ih (fun i => a i.succ) (fun i => ha i.succ))

theorem exists_sheetSumMap_for_finite_family {ι : Type} [Finite ι]
    (a : ι → X → N) (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ∃ (n : ℕ) (b : sheetSum X n → N), ContMDiff I J ∞ b ∧ range b = ⋃ i, range (a i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let a' : Fin (Fintype.card ι) → X → N := fun j => a (e.symm j)
  refine ⟨Fintype.card ι, sheetSumMap (Fintype.card ι) a',
    contMDiff_sheetSumMap _ a' (fun j => ha (e.symm j)), ?_⟩
  rw [range_sheetSumMap]
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨e.symm j, hj⟩
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    refine mem_iUnion.mpr ⟨e i, ?_⟩
    simpa only [a', e.symm_apply_apply] using hi

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
