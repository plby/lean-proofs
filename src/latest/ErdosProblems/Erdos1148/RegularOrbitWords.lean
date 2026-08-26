import ErdosProblems.Erdos1148.FiniteOrbitPartition
import ErdosProblems.Erdos1148.InvariantVisitCount

/-! # Orbit words represented by trajectories with few visits to an exceptional set -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

noncomputable def regularOrbitWords {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : FiniteMeasurablePartition X ι) (f : X → X) (Q : Set X) (τ : ℝ) (n : ℕ) (A : Set X) :
    Finset (Fin n → ι) := by
  classical
  exact Finset.univ.filter (fun w => ∃ x ∈ A, orbitVisitCount f Q n x ≤ τ * n ∧
    x ∈ P.orbitAtom f n w)

lemma mem_regularOrbitWords {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : FiniteMeasurablePartition X ι) (f : X → X) (Q : Set X) (τ : ℝ) (n : ℕ) (A : Set X)
    (w : Fin n → ι) : w ∈ regularOrbitWords P f Q τ n A ↔
      ∃ x ∈ A, orbitVisitCount f Q n x ≤ τ * n ∧ x ∈ P.orbitAtom f n w := by
  classical
  simp only [regularOrbitWords, Finset.mem_filter, Finset.mem_univ, true_and]

lemma regularOrbitWords_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : FiniteMeasurablePartition X ι) (f : X → X) (Q : Set X) (τ : ℝ) (n : ℕ) (A : Set X)
    {x : X} (hx : x ∈ A) (hcount : orbitVisitCount f Q n x ≤ τ * n) :
    x ∈ ⋃ w : regularOrbitWords P f Q τ n A, P.orbitAtom f n w.val := by
  have hcover : x ∈ ⋃ w : Fin n → ι, P.orbitAtom f n w := by
    rw [P.iUnion_orbitAtom]
    exact Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hcover
  have hmem := (mem_regularOrbitWords P f Q τ n A w).mpr ⟨x, hx, hcount, hw⟩
  exact Set.mem_iUnion.mpr ⟨⟨w, hmem⟩, hw⟩

theorem orbitWord_family_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : FiniteMeasurablePartition X ι) {f : X → X} (hf : Measurable f) (n : ℕ)
    (μ : Measure X) [IsFiniteMeasure μ] (F : Finset (Fin n → ι)) :
    (∑ w ∈ F, μ.real (P.orbitAtom f n w)) = μ.real (⋃ w : F, P.orbitAtom f n w.val) := by
  classical
  rw [← Finset.sum_coe_sort]
  apply (measureReal_iUnion_fintype _ _).symm
  · intro v w hne
    exact P.pairwise_disjoint_orbitAtom f n (fun h => hne (Subtype.ext h))
  · intro w
    exact P.measurableSet_orbitAtom hf n w.val

theorem regularOrbitWords_mass_lower {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : FiniteMeasurablePartition X ι) (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → X} (hf : MeasurePreserving f μ μ) {Q : Set X} (hQ : MeasurableSet Q)
    {τ : ℝ} (hτ : 0 < τ) {n : ℕ} (hn : 0 < n) (A : Set X) :
    μ.real A - μ.real Q / τ ≤
      ∑ w ∈ regularOrbitWords P f Q τ n A, μ.real (P.orbitAtom f n w) := by
  have hsub : A ⊆ (⋃ w : regularOrbitWords P f Q τ n A, P.orbitAtom f n w.val) ∪
      {x | τ * n ≤ orbitVisitCount f Q n x} := by
    intro x hx
    by_cases hc : orbitVisitCount f Q n x ≤ τ * n
    · exact Or.inl (regularOrbitWords_cover P f Q τ n A hx hc)
    · exact Or.inr (lt_of_not_ge hc).le
  have hbound := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  rw [← orbitWord_family_mass P hf.measurable n μ] at hbound
  have htail := orbitVisitCount_exceedance_mass_le hf hQ hτ hn
  linarith only [hbound, htail]

end Erdos1148.DukeArithmetic
