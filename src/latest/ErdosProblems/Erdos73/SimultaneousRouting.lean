/- A finite recurrence producing mutually disjoint proper connecting paths. -/
import ErdosProblems.Erdos73.SimultaneousLinkage
import ErdosProblems.Erdos73.AvoidanceGraph

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
open scoped BigOperators

def simultaneousRoutingBound (g h : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * (2 * qualitativeGrillRows g h * simultaneousRoutingBound g h n + 1) *
      (2 * qualitativeGrillColumns g h + 1)

theorem simultaneousRoutingBound_pos (g h n : ℕ) : 0 < simultaneousRoutingBound g h n := by
  cases n with
  | zero => exact Nat.zero_lt_one
  | succ n => exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)

theorem simultaneousRoutingBound_rows_le (g h n : ℕ) :
    2 * qualitativeGrillRows g h * simultaneousRoutingBound g h n ≤
      simultaneousRoutingBound g h (n + 1) := by
  dsimp only [simultaneousRoutingBound]
  have hp := Nat.mul_le_mul
    (Nat.mul_le_mul (show 1 ≤ n + 1 by omega) (Nat.le_succ
      (2 * qualitativeGrillRows g h * simultaneousRoutingBound g h n)))
    (show 1 ≤ 2 * qualitativeGrillColumns g h + 1 by omega)
  simpa only [Nat.one_mul, Nat.mul_one] using hp

theorem simultaneousRoutingBound_union_lt (g h n : ℕ) :
    n * (2 * qualitativeGrillRows g h * simultaneousRoutingBound g h n + 1) *
      (2 * qualitativeGrillColumns g h) < simultaneousRoutingBound g h (n + 1) := by
  dsimp only [simultaneousRoutingBound]
  exact (Nat.mul_le_mul_left _ (Nat.le_succ _)).trans_lt
    (Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self n) (Nat.succ_pos _)) (Nat.succ_pos _))

/-- Sufficiently large proper linkages for finitely many pairs yield
mutually vertex-disjoint proper paths for every pair. -/
theorem exists_boundaryProper_disjoint_paths
    {V : Type*} [Fintype V] [DecidableEq V] (g h : ℕ) (hh : 0 < h) :
    ∀ n, ∀ {G : SimpleGraph V} (A B : Fin n → Finset V) (Z : Finset V)
      (P : ∀ i, PathPacking G (A i) (B i)),
      (∀ i, (P i).IsBoundaryProper Z) → (∀ i, A i ⊆ Z) → (∀ i, B i ⊆ Z) →
      (∀ i, simultaneousRoutingBound g h n ≤ (P i).card) →
      ¬ IsMinor (squareGrid g) G →
      ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G →
      ∃ R : Fin n → GraphPath G,
        (∀ i, (R i).Connects (A i) (B i) ∧ (R i).IsBoundaryProper Z) ∧
        Pairwise fun i j => Disjoint (R i).vertexSet (R j).vertexSet := by
  intro n
  induction n with
  | zero =>
    intro G A B Z P hP hA hB hcard hgrid hbip
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro G A B Z P hP hA hB hcard hgrid hbip
    let m := 2 * qualitativeGrillRows g h * simultaneousRoutingBound g h n
    have hm (i : Fin n) : m ≤ (P i.castSucc).card :=
      (simultaneousRoutingBound_rows_le g h n).trans (hcard i.castSucc)
    have hex (i : Fin n) := (P i.castSucc).exists_indexSet_card_eq (hm i)
    choose S hS hRcard using hex
    let R (i : Fin n) := (P i.castSucc).restrictIndexSet (S i)
    have hRproper (i : Fin n) : (R i).IsBoundaryProper Z :=
      (hP i.castSucc).restrictIndexSet (S i)
    have hRm (i : Fin n) : (R i).card = m := hRcard i
    have hM : qualitativeGrillRows g h ≤ m := by
      have hp := Nat.mul_le_mul (show qualitativeGrillRows g h ≤
          2 * qualitativeGrillRows g h by omega)
        (simultaneousRoutingBound_pos g h n)
      simpa only [Nat.mul_one] using hp
    have hsize : (∑ i : Fin n, ((R i).card + 1) * (2 * qualitativeGrillColumns g h)) <
        (P (Fin.last n)).card := by
      simp only [hRm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Nat.mul_assoc]
      exact (simultaneousRoutingBound_union_lt g h n).trans_le (hcard (Fin.last n))
    obtain ⟨q, hq⟩ := exists_path_simultaneously_preserving
      (fun i : Fin n => A i.castSucc) (fun i => B i.castSucc) R (P (Fin.last n))
      hRproper (hP (Fin.last n)) (fun i => hA i.castSucc) (fun i => hB i.castSucc)
      g h hh (fun i => (hRm i).symm ▸ hM) hsize hgrid hbip
    let Q := (P (Fin.last n)).path q
    let D := Q.vertexSet
    choose C hCcard hCd hCproper using hq
    let J := avoidanceGraph G D
    let C' (i : Fin n) := (C i).toAvoidanceGraph (hCd i)
    have hC'card (i : Fin n) : simultaneousRoutingBound g h n ≤ (C' i).card := by
      have hp := hCcard i
      rw [hRm i] at hp
      have hdpos : 0 < 2 * qualitativeGrillRows g h :=
        Nat.mul_pos (by omega) (qualitativeGrillRows_pos g h)
      have hdiv : m / (2 * qualitativeGrillRows g h) = simultaneousRoutingBound g h n := by
        exact Nat.mul_div_right _ hdpos
      rw [hdiv] at hp
      exact (Nat.le_succ _).trans hp
    have hJle : J ≤ G := avoidanceGraph_le D
    obtain ⟨T, hT, hTd⟩ := ih
      (fun i => A i.castSucc \ D) (fun i => B i.castSucc \ D) Z C'
      (fun i => (hCproper i).toAvoidanceGraph (hCd i))
      (fun i => Finset.sdiff_subset.trans (hA i.castSucc))
      (fun i => Finset.sdiff_subset.trans (hB i.castSucc)) hC'card
      (fun hz => hgrid (hz.mono hJle)) (fun hz => hbip (hz.mono hJle))
    let T' (i : Fin n) := (T i).mapLe hJle
    have hT' (i : Fin n) : (T' i).Connects (A i.castSucc) (B i.castSucc) ∧
        (T' i).IsBoundaryProper Z := by
      refine ⟨?_, (hT i).2.mapLe hJle⟩
      rcases (hT i).1 with hc | hc
      · exact Or.inl ⟨(Finset.mem_sdiff.mp hc.1).1, (Finset.mem_sdiff.mp hc.2).1⟩
      · exact Or.inr ⟨(Finset.mem_sdiff.mp hc.1).1, (Finset.mem_sdiff.mp hc.2).1⟩
    have hT'D (i : Fin n) : Disjoint (T' i).vertexSet Q.vertexSet := by
      change Disjoint ((T i).mapLe hJle).vertexSet D
      rw [GraphPath.mapLe_vertexSet]
      apply (T i).avoidanceGraph_disjoint
      rcases (hT i).1 with hc | hc
      · exact (Finset.mem_sdiff.mp hc.1).2
      · exact (Finset.mem_sdiff.mp hc.1).2
    refine ⟨Fin.snoc T' Q, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using And.intro ((P (Fin.last n)).connects q) (hP (Fin.last n) q)
      · simpa only [Fin.snoc_castSucc] using hT' j
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hT'D j').symm
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro _
          simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hT'D i'
        · intro hij
          have hne : i' ≠ j' := fun he => hij (congrArg Fin.castSucc he)
          simpa only [Fin.snoc_castSucc, T', GraphPath.mapLe_vertexSet] using hTd hne

/-- The routing theorem is invariant under enumerating any finite index type. -/
theorem exists_boundaryProper_disjoint_paths_fintype
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (A B : I → Finset V) (Z : Finset V)
    (P : ∀ i, PathPacking G (A i) (B i))
    (hP : ∀ i, (P i).IsBoundaryProper Z) (hA : ∀ i, A i ⊆ Z) (hB : ∀ i, B i ⊆ Z)
    (g h : ℕ) (hh : 0 < h)
    (hcard : ∀ i, simultaneousRoutingBound g h (Fintype.card I) ≤ (P i).card)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ R : I → GraphPath G,
      (∀ i, (R i).Connects (A i) (B i) ∧ (R i).IsBoundaryProper Z) ∧
      Pairwise fun i j => Disjoint (R i).vertexSet (R j).vertexSet := by
  let e := Fintype.equivFin I
  obtain ⟨R, hR, hd⟩ := exists_boundaryProper_disjoint_paths g h hh (Fintype.card I)
    (fun i => A (e.symm i)) (fun i => B (e.symm i)) Z (fun i => P (e.symm i))
    (fun i => hP (e.symm i)) (fun i => hA (e.symm i)) (fun i => hB (e.symm i))
    (fun i => hcard (e.symm i)) hgrid hbip
  refine ⟨fun i => R (e i), fun i => ?_, fun i j hij => hd (e.injective.ne hij)⟩
  simpa only [Equiv.symm_apply_apply] using hR (e i)

/-- Localized routing: if the linkages and their boundary lie in a region,
the simultaneous paths can be required to stay in that region as well. -/
theorem exists_boundaryProper_disjoint_paths_staysIn
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (A B : I → Finset V) (Z W : Finset V)
    (P : ∀ i, PathPacking G (A i) (B i))
    (hP : ∀ i, (P i).IsBoundaryProper Z) (hA : ∀ i, A i ⊆ Z) (hB : ∀ i, B i ⊆ Z)
    (hZW : Z ⊆ W) (hPW : ∀ i, (P i).StaysIn W)
    (g h : ℕ) (hh : 0 < h)
    (hcard : ∀ i, simultaneousRoutingBound g h (Fintype.card I) ≤ (P i).card)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ R : I → GraphPath G,
      (∀ i, (R i).Connects (A i) (B i) ∧ (R i).IsBoundaryProper Z ∧ (R i).vertexSet ⊆ W) ∧
      Pairwise fun i j => Disjoint (R i).vertexSet (R j).vertexSet := by
  let D := Finset.univ \ W
  have hd (i : I) (r : (P i).Index) : Disjoint ((P i).path r).vertexSet D := by
    apply Finset.disjoint_left.mpr
    intro x hx hxD
    exact (Finset.mem_sdiff.mp hxD).2 (hPW i r hx)
  let Q (i : I) := (P i).toAvoidanceGraph (hd i)
  have hle : avoidanceGraph G D ≤ G := avoidanceGraph_le D
  obtain ⟨R, hR, hRd⟩ := exists_boundaryProper_disjoint_paths_fintype A B Z Q
    (fun i => (hP i).toAvoidanceGraph (hd i)) hA hB g h hh hcard
    (fun hz => hgrid (hz.mono hle)) (fun hz => hbip (hz.mono hle))
  refine ⟨fun i => (R i).mapLe hle, fun i => ?_, ?_⟩
  · refine ⟨(hR i).1, (hR i).2.mapLe hle, ?_⟩
    rw [GraphPath.mapLe_vertexSet]
    have hsource : (R i).source ∉ D :=
      fun h => (Finset.mem_sdiff.mp h).2 (hZW (hR i).2.source_mem)
    have havoid := (R i).avoidanceGraph_disjoint hsource
    intro x hx
    by_contra hxW
    exact Finset.disjoint_left.mp havoid hx
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxW⟩)
  · intro i j hij
    simpa only [GraphPath.mapLe_vertexSet] using hRd hij

end
end Erdos73
