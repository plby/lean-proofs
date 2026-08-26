import ErdosProblems.Erdos1148.FiniteOrbitPartition
import ErdosProblems.Erdos1148.NullBoundaryOperations

/-! # Turning a finite cover of a core into a partition with one exceptional atom -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

def finiteCoverAtom {X : Type*} {N : ℕ} (U : Set X) (V : Fin N → Set X) :
    Option (Fin N) → Set X
  | none => Uᶜ
  | some i => U ∩ disjointed V i

lemma finiteCoverAtom_measurable {X : Type*} [MeasurableSpace X] {N : ℕ}
    {U : Set X} (hU : MeasurableSet U) {V : Fin N → Set X}
    (hV : ∀ i, MeasurableSet (V i)) (i : Option (Fin N)) :
    MeasurableSet (finiteCoverAtom U V i) := by
  cases i with
  | none => exact hU.compl
  | some i => exact hU.inter (disjointedRec (fun {_ j} h => h.diff (hV j)) (hV i))

lemma finiteCoverAtom_disjoint {X : Type*} {N : ℕ} (U : Set X) (V : Fin N → Set X) :
    Pairwise (Disjoint on finiteCoverAtom U V) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => exact Set.disjoint_left.mpr (fun _ hx hy => hx hy.1)
  | some i =>
    cases j with
    | none => exact Set.disjoint_left.mpr (fun _ hx hy => hy hx.1)
    | some j =>
      exact (disjoint_disjointed V (fun h => hij (congrArg some h))).mono
        Set.inter_subset_right Set.inter_subset_right

lemma iUnion_finiteCoverAtom {X : Type*} {N : ℕ} (U : Set X) (V : Fin N → Set X)
    (hcover : U ⊆ ⋃ i, V i) : (⋃ i, finiteCoverAtom U V i) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ U
  · have hxd : x ∈ ⋃ i, disjointed V i := by rw [iUnion_disjointed]; exact hcover hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxd
    exact Set.mem_iUnion.mpr ⟨some i, hx, hi⟩
  · exact Set.mem_iUnion.mpr ⟨none, hx⟩

def partitionOfFiniteCover {X : Type*} [MeasurableSpace X] {N : ℕ}
    (U : Set X) (V : Fin N → Set X) (hU : MeasurableSet U)
    (hV : ∀ i, MeasurableSet (V i)) (hcover : U ⊆ ⋃ i, V i) :
    FiniteMeasurablePartition X (Option (Fin N)) where
  atom := finiteCoverAtom U V
  measurable_atom := finiteCoverAtom_measurable hU hV
  disjoint_atom := finiteCoverAtom_disjoint U V
  iUnion_atom := iUnion_finiteCoverAtom U V hcover

lemma finiteCoverAtom_some_subset {X : Type*} {N : ℕ} (U : Set X)
    (V : Fin N → Set X) (i : Fin N) : finiteCoverAtom U V (some i) ⊆ V i :=
  Set.inter_subset_right.trans (disjointed_le V i)

theorem measure_frontier_finiteCoverAtom_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) {N : ℕ} (U : Set X) (V : Fin N → Set X)
    (hU : μ (frontier U) = 0) (hV : ∀ i, μ (frontier (V i)) = 0)
    (i : Option (Fin N)) : μ (frontier (finiteCoverAtom U V i)) = 0 := by
  cases i with
  | none => simpa only [finiteCoverAtom, frontier_compl] using hU
  | some i =>
    apply measure_frontier_inter_eq_zero μ hU
    exact disjointedRec (p := fun s : Set X => μ (frontier s) = 0)
      (fun {_ j} h => measure_frontier_diff_eq_zero μ h (hV j)) (hV i)

end Erdos1148.DukeArithmetic
