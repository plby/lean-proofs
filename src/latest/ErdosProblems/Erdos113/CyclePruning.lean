import ErdosProblems.Erdos113.FourCycles

open scoped Real SimpleGraph BigOperators

namespace Erdos113CyclePruning

open Erdos113Cycles
open Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def orderedFourCycles (D : Finset (Sym2 V)) :
    Finset (Fin 4 → V) :=
  genuineCycles (graphOfEdges D) 4

noncomputable def orderedFourCyclesThroughEdge
    (D : Finset (Sym2 V)) (e : Sym2 V) : Finset (Fin 4 → V) :=
  cyclesThroughEdge (graphOfEdges D) 4 e

@[simp] lemma mem_orderedFourCycles {D : Finset (Sym2 V)} {x : Fin 4 → V} :
    x ∈ orderedFourCycles D ↔ IsGenuineCycle (graphOfEdges D) x := by
  simp [orderedFourCycles]

@[simp] lemma mem_orderedFourCyclesThroughEdge
    {D : Finset (Sym2 V)} {e : Sym2 V} {x : Fin 4 → V} :
    x ∈ orderedFourCyclesThroughEdge D e ↔
      IsGenuineCycle (graphOfEdges D) x ∧ ∃ i, cycleEdge x i = e := by
  simp [orderedFourCyclesThroughEdge]

lemma orderedFourCyclesThroughEdge_subset
    (D : Finset (Sym2 V)) (e : Sym2 V) :
    orderedFourCyclesThroughEdge D e ⊆ orderedFourCycles D := by
  intro x hx
  exact mem_orderedFourCycles.mpr
    (mem_orderedFourCyclesThroughEdge.mp hx).1

lemma orderedFourCycles_erase_edge
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) {e : Sym2 V} (he : e ∈ D) :
    orderedFourCycles (D.erase e) =
      orderedFourCycles D \ orderedFourCyclesThroughEdge D e := by
  classical
  ext x
  rw [Finset.mem_sdiff, mem_orderedFourCycles,
    mem_orderedFourCycles, mem_orderedFourCyclesThroughEdge]
  have hDerase : D.erase e ⊆ G.edgeFinset := (Finset.erase_subset _ _).trans hD
  rw [IsGenuineCycle, IsGenuineCycle,
    isHomCycle_graphOfEdges_iff hDerase,
    isHomCycle_graphOfEdges_iff hD]
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨⟨hinj, fun i ↦ Finset.mem_of_mem_erase (hedge i)⟩, ?_⟩
    rintro ⟨_hgen, i, hi⟩
    exact (Finset.mem_erase.mp (hedge i)).1 hi
  · rintro ⟨⟨hinj, hedge⟩, hnot⟩
    refine ⟨hinj, fun i ↦ Finset.mem_erase.mpr ⟨?_, hedge i⟩⟩
    intro hi
    exact hnot ⟨⟨hinj, hedge⟩, i, hi⟩

lemma card_orderedFourCycles_erase_add_through
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) {e : Sym2 V} (he : e ∈ D) :
    (orderedFourCycles (D.erase e)).card +
        (orderedFourCyclesThroughEdge D e).card =
      (orderedFourCycles D).card := by
  rw [orderedFourCycles_erase_edge hD he]
  exact Finset.card_sdiff_add_card_eq_card
    (orderedFourCyclesThroughEdge_subset D e)

lemma card_orderedFourCycles_le (D : Finset (Sym2 V)) :
    (orderedFourCycles D).card ≤ (Fintype.card V) ^ 4 := by
  calc
    (orderedFourCycles D).card ≤ Fintype.card (Fin 4 → V) := by
      simpa using Finset.card_le_card (Finset.subset_univ (s := orderedFourCycles D))
    _ = (Fintype.card V) ^ 4 := by simp

lemma cycleEdge_injective_four {x : Fin 4 → V}
    (hx : Function.Injective x) :
    Function.Injective (cycleEdge x) := by
  have h01 : x 0 ≠ x 1 := hx.ne (by decide)
  have h02 : x 0 ≠ x 2 := hx.ne (by decide)
  have h03 : x 0 ≠ x 3 := hx.ne (by decide)
  have h12 : x 1 ≠ x 2 := hx.ne (by decide)
  have h13 : x 1 ≠ x 3 := hx.ne (by decide)
  have h23 : x 2 ≠ x 3 := hx.ne (by decide)
  have h10 : x 1 ≠ x 0 := h01.symm
  have h20 : x 2 ≠ x 0 := h02.symm
  have h30 : x 3 ≠ x 0 := h03.symm
  have h21 : x 2 ≠ x 1 := h12.symm
  have h31 : x 3 ≠ x 1 := h13.symm
  have h32 : x 3 ≠ x 2 := h23.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cycleEdge, Sym2.eq_iff]

lemma four_le_card_of_mem_orderedFourCycles
    {D : Finset (Sym2 V)} {x : Fin 4 → V}
    (hx : x ∈ orderedFourCycles D) : 4 ≤ D.card := by
  have hgen := mem_orderedFourCycles.mp hx
  let f : Fin 4 → ↑D := fun i ↦
    ⟨cycleEdge x i, by
      exact (graphOfEdges_adj_iff.mp (hgen.2 i)).1⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply cycleEdge_injective_four hgen.1
    exact congrArg Subtype.val hij
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

lemma orderedFourCycles_eq_empty_of_card_lt_four
    {D : Finset (Sym2 V)} (hD : D.card < 4) :
    orderedFourCycles D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_le_of_gt hD) (four_le_card_of_mem_orderedFourCycles hx)

/-- Repeatedly remove an edge carried by at least `K` ordered four-cycles.
The number of removed edges, times `K`, is paid for by the ordered
four-cycles that disappear. -/
theorem exists_pruned_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℕ) :
    ∀ E : Finset (Sym2 V), E ⊆ G.edgeFinset →
      ∃ D : Finset (Sym2 V),
        D ⊆ E ∧
        (E \ D).card * K + (orderedFourCycles D).card ≤
          (orderedFourCycles E).card ∧
        ∀ e ∈ D, (orderedFourCyclesThroughEdge D e).card < K := by
  classical
  intro E
  induction E using Finset.strongInductionOn with
  | _ E ih =>
      intro hE
      by_cases hgood :
          ∀ e ∈ E, (orderedFourCyclesThroughEdge E e).card < K
      · exact ⟨E, Finset.Subset.rfl, by simp, hgood⟩
      · push_neg at hgood
        obtain ⟨e, he, hload⟩ := hgood
        have hproper : E.erase e ⊂ E := Finset.erase_ssubset he
        have hEraseG : E.erase e ⊆ G.edgeFinset :=
          (Finset.erase_subset e E).trans hE
        obtain ⟨D, hDErase, hpaid, hDgood⟩ :=
          ih (E.erase e) hproper hEraseG
        have hDE : D ⊆ E := hDErase.trans (Finset.erase_subset e E)
        have heD : e ∉ D := by
          intro heMem
          exact (Finset.mem_erase.mp (hDErase heMem)).1 rfl
        have heDiff : e ∉ (E.erase e \ D) := by simp
        have hdiff : E \ D = insert e (E.erase e \ D) := by
          ext z
          by_cases hze : z = e <;> simp_all
        have hcycle := card_orderedFourCycles_erase_add_through hE he
        refine ⟨D, hDE, ?_, hDgood⟩
        rw [hdiff, Finset.card_insert_of_notMem heDiff]
        simp only [add_mul, one_mul]
        omega

/-- If the initial ordered-four-cycle count is small relative to `K |E|`,
the deletion process keeps strictly more than half of the edges. -/
theorem exists_pruned_subset_more_than_half
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset) (K : ℕ) (hK : 0 < K)
    (hsmall : 2 * (orderedFourCycles E).card < E.card * K) :
    ∃ D : Finset (Sym2 V),
      D ⊆ E ∧ E.card < 2 * D.card ∧
      ∀ e ∈ D, (orderedFourCyclesThroughEdge D e).card < K := by
  obtain ⟨D, hDE, hpaid, hload⟩ := exists_pruned_subset G K E hE
  have hremoved : (E \ D).card * K ≤ (orderedFourCycles E).card := by
    omega
  have hmul : (2 * (E \ D).card) * K < E.card * K := by
    calc
      (2 * (E \ D).card) * K = 2 * ((E \ D).card * K) := by
        simp only [mul_assoc]
      _ ≤ 2 * (orderedFourCycles E).card :=
        Nat.mul_le_mul_left 2 hremoved
      _ < E.card * K := hsmall
  have hremoved_lt : 2 * (E \ D).card < E.card :=
    Nat.lt_of_mul_lt_mul_right hmul
  have hcard := Finset.card_sdiff_add_card_eq_card hDE
  refine ⟨D, hDE, ?_, hload⟩
  omega

/-- A per-edge ordered-four-cycle cap gives the local extension cap used by
the few-four-cycle conflict encoder. -/
lemma extensionsThroughEdge_card_lt_of_pruned
    {D : Finset (Sym2 V)} {K : ℕ}
    (hload : ∀ e ∈ D, (orderedFourCyclesThroughEdge D e).card < K)
    {u y : V} (huy : (graphOfEdges D).Adj y u) :
    (extensionsThroughEdge (graphOfEdges D) u y).card < K := by
  have hedge : s(u, y) ∈ D := by
    rw [Sym2.eq_swap]
    exact (graphOfEdges_adj_iff.mp huy).1
  exact lt_of_le_of_lt
    (card_extensionsThroughEdge_le_cyclesThroughEdge
      (graphOfEdges D) u y huy)
    (hload s(u, y) hedge)

end Erdos113CyclePruning
