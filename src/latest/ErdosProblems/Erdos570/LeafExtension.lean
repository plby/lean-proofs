/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.LeafDeletion

/-!
# Extending a copy after deleting leaves

Given a copy of the graph induced outside a selected leaf set, a partial
assignment sends some of the deleted leaves to fresh host vertices adjacent
to their copied parents.  A maximum-cardinality assignment either covers all
selected leaves or exposes an unassigned leaf whose copied parent is
nonadjacent to every unused host vertex.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

section Assignment

variable {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1)
    (C : SimpleGraph W)

abbrev LeafType := ↥L
abbrev LeafCoreType :=
  {v : Fin H.vertexCount // v ∈ (Finset.univ \ L)}

/-- The unique neighbor of a selected leaf. -/
def selectedLeafNeighbor (v : LeafType H L) : Fin H.vertexCount :=
  Classical.choose
    ((H.graph.degree_eq_one_iff_existsUnique_adj).mp (hL v.1 v.2))

theorem selectedLeafNeighbor_adj (v : LeafType H L) :
    H.graph.Adj v.1 (selectedLeafNeighbor H L hL v) :=
  Classical.choose_spec
    ((H.graph.degree_eq_one_iff_existsUnique_adj).mp (hL v.1 v.2)) |>.1

include hconn hn
theorem selectedLeafNeighbor_not_mem (v : LeafType H L) :
    selectedLeafNeighbor H L hL v ∉ L := by
  intro hmem
  exact not_adj_of_leaves_of_connected H hconn hn
    (hL v.1 v.2) (hL _ hmem) (selectedLeafNeighbor_adj H L hL v)

/-- The parent of a selected leaf as a vertex of the retained core. -/
def selectedLeafParent (v : LeafType H L) : LeafCoreType H L :=
  ⟨selectedLeafNeighbor H L hL v,
    by simp [selectedLeafNeighbor_not_mem H hconn hn L hL v]⟩

/-- A partial assignment of selected leaves to fresh host vertices. -/
structure LeafAssignment
    (copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C)
    (J : Finset (LeafType H L)) where
  toFun : ↥J → W
  injective : Function.Injective toFun
  fresh_core : ∀ j d, toFun j ≠ copy d
  adjacent_parent : ∀ j,
    C.Adj (copy (selectedLeafParent H hconn hn L hL j.1)) (toFun j)

/-- The empty partial assignment is always available. -/
def LeafAssignment.empty
    (copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C) :
    LeafAssignment H hconn hn L hL C copy ∅ where
  toFun := fun j ↦ by
    have hpos : 0 < Fintype.card ↥(∅ : Finset (LeafType H L)) :=
      Fintype.card_pos_iff.mpr ⟨j⟩
    exact False.elim (by simpa using hpos)
  injective := fun x ↦ by
    have hpos : 0 < Fintype.card ↥(∅ : Finset (LeafType H L)) :=
      Fintype.card_pos_iff.mpr ⟨x⟩
    exact False.elim (by simpa using hpos)
  fresh_core := fun j ↦ by
    have hpos : 0 < Fintype.card ↥(∅ : Finset (LeafType H L)) :=
      Fintype.card_pos_iff.mpr ⟨j⟩
    exact False.elim (by simpa using hpos)
  adjacent_parent := fun j ↦ by
    have hpos : 0 < Fintype.card ↥(∅ : Finset (LeafType H L)) :=
      Fintype.card_pos_iff.mpr ⟨j⟩
    exact False.elim (by simpa using hpos)

/-- A full leaf assignment extends the retained-core copy to a copy of the
whole target. -/
theorem isContained_of_full_leafAssignment
    (copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C)
    (a : LeafAssignment H hconn hn L hL C copy Finset.univ) :
    H.graph ⊑ C := by
  classical
  let f : Fin H.vertexCount → W := fun v ↦
    if hv : v ∈ L then
      a.toFun ⟨⟨v, hv⟩, Finset.mem_univ _⟩
    else
      copy ⟨v, by simp [hv]⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ L <;> by_cases hy : y ∈ L
    · dsimp only [f] at hxy
      rw [dif_pos hx, dif_pos hy] at hxy
      have hsub := a.injective hxy
      exact congrArg (fun z : ↥(Finset.univ : Finset (LeafType H L)) ↦ z.1.1) hsub
    · dsimp only [f] at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      exact (a.fresh_core
        ⟨⟨x, hx⟩, Finset.mem_univ _⟩ ⟨y, by simpa [hy]⟩ hxy).elim
    · dsimp only [f] at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      exact (a.fresh_core
        ⟨⟨y, hy⟩, Finset.mem_univ _⟩ ⟨x, by simpa [hx]⟩ hxy.symm).elim
    · dsimp only [f] at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val (copy.injective hxy)
  let hom : H.graph →g C :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        by_cases hx : x ∈ L <;> by_cases hy : y ∈ L
        · exact (not_adj_of_leaves_of_connected H hconn hn
            (hL x hx) (hL y hy) hxy).elim
        · dsimp only [f]
          rw [dif_pos hx, dif_neg hy]
          have hparent : selectedLeafNeighbor H L hL ⟨x, hx⟩ = y := by
            exact (Classical.choose_spec
              ((H.graph.degree_eq_one_iff_existsUnique_adj).mp (hL x hx)) |>.2
                y hxy).symm
          have ha := a.adjacent_parent
            ⟨⟨x, hx⟩, Finset.mem_univ _⟩
          simpa only [selectedLeafParent, hparent] using ha.symm
        · dsimp only [f]
          rw [dif_neg hx, dif_pos hy]
          have hparent : selectedLeafNeighbor H L hL ⟨y, hy⟩ = x := by
            exact (Classical.choose_spec
              ((H.graph.degree_eq_one_iff_existsUnique_adj).mp (hL y hy)) |>.2
                x hxy.symm).symm
          have ha := a.adjacent_parent
            ⟨⟨y, hy⟩, Finset.mem_univ _⟩
          simpa only [selectedLeafParent, hparent] using ha
        · dsimp only [f]
          rw [dif_neg hx, dif_neg hy]
          exact copy.toHom.map_adj hxy }
  exact ⟨hom.toCopy hf⟩

/-- Host vertices occupied by the retained core and by a partial leaf
assignment. -/
def LeafAssignment.used
    {copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C}
    {J : Finset (LeafType H L)}
    (a : LeafAssignment H hconn hn L hL C copy J) : Finset W :=
  (Finset.univ.image copy) ∪ (Finset.univ.image a.toFun)

theorem LeafAssignment.copy_mem_used
    {copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C}
    {J : Finset (LeafType H L)}
    (a : LeafAssignment H hconn hn L hL C copy J)
    (d : LeafCoreType H L) :
    copy d ∈ a.used H hconn hn L hL C := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩

theorem LeafAssignment.assigned_mem_used
    {copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C}
    {J : Finset (LeafType H L)}
    (a : LeafAssignment H hconn hn L hL C copy J) (j : ↥J) :
    a.toFun j ∈ a.used H hconn hn L hL C := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem LeafAssignment.used_card_le
    {copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C}
    {J : Finset (LeafType H L)}
    (a : LeafAssignment H hconn hn L hL C copy J) :
    (a.used H hconn hn L hL C).card ≤
      (H.vertexCount - L.card) + J.card := by
  classical
  calc
    (a.used H hconn hn L hL C).card ≤
        (Finset.univ.image copy).card +
          (Finset.univ.image a.toFun).card := Finset.card_union_le _ _
    _ = Fintype.card (LeafCoreType H L) + Fintype.card ↥J := by
      have hcopy : (Finset.univ.image
          (fun d : LeafCoreType H L ↦ copy d)).card =
          Fintype.card (LeafCoreType H L) := by
        have hi : Set.InjOn (fun d : LeafCoreType H L ↦ copy d)
            (Finset.univ : Finset (LeafCoreType H L)) :=
          fun ⦃x⦄ _ ⦃y⦄ _ hxy ↦ copy.injective hxy
        simpa using Finset.card_image_of_injOn hi
      have hassigned : (Finset.univ.image
          (fun j : ↥J ↦ a.toFun j)).card = Fintype.card ↥J := by
        have hi : Set.InjOn (fun j : ↥J ↦ a.toFun j)
            (Finset.univ : Finset ↥J) :=
          fun ⦃x⦄ _ ⦃y⦄ _ hxy ↦ a.injective hxy
        simpa using Finset.card_image_of_injOn hi
      exact congrArg₂ (· + ·) hcopy hassigned
    _ = (H.vertexCount - L.card) + J.card := by
      simp [LeafCoreType, Finset.card_sdiff_of_subset (Finset.subset_univ L)]

/-- Add one fresh leaf to a partial assignment. -/
def LeafAssignment.insert
    {copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C}
    {J : Finset (LeafType H L)}
    (a : LeafAssignment H hconn hn L hL C copy J)
    (l : LeafType H L) (hl : l ∉ J) (x : W)
    (hx : x ∉ a.used H hconn hn L hL C)
    (hadj : C.Adj (copy (selectedLeafParent H hconn hn L hL l)) x) :
    LeafAssignment H hconn hn L hL C copy (J.cons l hl) := by
  let f : ↥(J.cons l hl) → W := fun j ↦
    if hj : j.1 = l then x
    else a.toFun ⟨j.1, (Finset.mem_cons.mp j.2).resolve_left hj⟩
  refine
    { toFun := f
      injective := ?_
      fresh_core := ?_
      adjacent_parent := ?_ }
  · intro i j hij
    by_cases hi : i.1 = l <;> by_cases hj : j.1 = l
    · exact Subtype.ext (hi.trans hj.symm)
    · change f i = f j at hij
      dsimp only [f] at hij
      rw [dif_pos hi, dif_neg hj] at hij
      have hmem := a.assigned_mem_used H hconn hn L hL C
        ⟨j.1, (Finset.mem_cons.mp j.2).resolve_left hj⟩
      rw [← hij] at hmem
      exact (hx hmem).elim
    · change f i = f j at hij
      dsimp only [f] at hij
      rw [dif_neg hi, dif_pos hj] at hij
      have hmem := a.assigned_mem_used H hconn hn L hL C
        ⟨i.1, (Finset.mem_cons.mp i.2).resolve_left hi⟩
      rw [hij] at hmem
      exact (hx hmem).elim
    · change f i = f j at hij
      dsimp only [f] at hij
      rw [dif_neg hi, dif_neg hj] at hij
      have hsub := a.injective hij
      apply Subtype.ext
      exact congrArg (fun z : ↥J ↦ z.1) hsub
  · intro j d
    by_cases hj : j.1 = l
    · change f j ≠ copy d
      dsimp only [f]
      rw [dif_pos hj]
      intro hxd
      apply hx
      rw [hxd]
      exact a.copy_mem_used H hconn hn L hL C d
    · change f j ≠ copy d
      dsimp only [f]
      rw [dif_neg hj]
      exact a.fresh_core
        ⟨j.1, (Finset.mem_cons.mp j.2).resolve_left hj⟩ d
  · intro j
    by_cases hj : j.1 = l
    · change C.Adj (copy (selectedLeafParent H hconn hn L hL j.1)) (f j)
      dsimp only [f]
      rw [dif_pos hj]
      have hjval : j.1 = l := hj
      simpa only [hjval] using hadj
    · change C.Adj (copy (selectedLeafParent H hconn hn L hL j.1)) (f j)
      dsimp only [f]
      rw [dif_neg hj]
      exact a.adjacent_parent
        ⟨j.1, (Finset.mem_cons.mp j.2).resolve_left hj⟩

/-- A maximal partial assignment either reconstructs the target or produces
a copied parent whose every unused host vertex is complementary-adjacent to
it.  The unused set has the sharp cardinal lower bound coming from the fact
that a non-full assignment occupies at most `|H|-1` vertices. -/
theorem isContained_or_leaf_obstruction
    (hLeaves : ∀ v ∈ L, H.graph.degree v = 1)
    (copy : SimpleGraph.Copy
      (H.graph.induce ((Finset.univ \ L : Finset _) : Set _)) C) :
    H.graph ⊑ C ∨
      ∃ d : LeafCoreType H L, ∃ U : Finset W,
        Fintype.card W - (H.vertexCount - 1) ≤ U.card ∧
        (∀ x ∈ U, Cᶜ.Adj (copy d) x) ∧
        ∀ R : Finset W, (∀ e, copy e ∈ R) →
          Rᶜ.card - (L.card - 1) ≤ (U ∩ Rᶜ).card := by
  classical
  let feasible : Finset (LeafType H L) → Prop := fun J ↦
    Nonempty (LeafAssignment H hconn hn L hLeaves C copy J)
  let candidates : Finset (Finset (LeafType H L)) :=
    Finset.univ.filter feasible
  have hempty : (∅ : Finset (LeafType H L)) ∈ candidates := by
    rw [show candidates = Finset.univ.filter feasible from rfl,
      Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨LeafAssignment.empty H hconn hn L hLeaves C copy⟩⟩
  have hcandne : candidates.Nonempty := ⟨∅, hempty⟩
  obtain ⟨J, hJcand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandne
  have hJfeasible : feasible J := (Finset.mem_filter.mp hJcand).2
  let a : LeafAssignment H hconn hn L hLeaves C copy J :=
    Classical.choice hJfeasible
  by_cases hfull : J = Finset.univ
  · left
    subst J
    exact isContained_of_full_leafAssignment H hconn hn L hLeaves C copy a
  · right
    have hJssub : J ⊂ (Finset.univ : Finset (LeafType H L)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ J, hfull⟩
    obtain ⟨l, _hluniv, hlJ⟩ := Finset.exists_of_ssubset hJssub
    let d : LeafCoreType H L := selectedLeafParent H hconn hn L hLeaves l
    let used := a.used H hconn hn L hLeaves C
    let U : Finset W := Finset.univ \ used
    have hJcard : J.card < L.card := by
      have hcard := Finset.card_lt_card hJssub
      simpa using hcard
    refine ⟨d, U, ?_, ?_, ?_⟩
    ·
      have hused : used.card ≤ H.vertexCount - 1 := by
        have haCard := a.used_card_le H hconn hn L hLeaves C
        have hLcard : L.card ≤ H.vertexCount := by
          simpa using Finset.card_le_card (Finset.subset_univ L)
        dsimp only [used]
        omega
      have hsplit : U.card + used.card = Fintype.card W := by
        have h := Finset.card_sdiff_add_card_eq_card
          (show used ⊆ (Finset.univ : Finset W) from Finset.subset_univ _)
        simpa [U, add_comm] using h
      omega
    · intro x hxU
      have hxnot : x ∉ used := (Finset.mem_sdiff.mp hxU).2
      rw [SimpleGraph.compl_adj]
      refine ⟨?_, ?_⟩
      · intro heq
        apply hxnot
        rw [← heq]
        exact a.copy_mem_used H hconn hn L hLeaves C d
      · intro hadj
        let a' := a.insert H hconn hn L hLeaves C l hlJ x hxnot hadj
        have ha'cand : J.cons l hlJ ∈ candidates := by
          rw [show candidates = Finset.univ.filter feasible from rfl,
            Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ⟨a'⟩⟩
        have hle := hmax (J.cons l hlJ) ha'cand
        rw [Finset.card_cons] at hle
        omega
    · intro R hcopyR
      let T : Finset W := Rᶜ
      let assigned : Finset W := Finset.univ.image a.toFun
      have hinterSubset : used ∩ T ⊆ assigned := by
        intro x hx
        have hxused := (Finset.mem_inter.mp hx).1
        have hxT := (Finset.mem_inter.mp hx).2
        rcases Finset.mem_union.mp hxused with hxcore | hxassigned
        · rw [Finset.mem_image] at hxcore
          obtain ⟨e, _, rfl⟩ := hxcore
          exact (Finset.mem_compl.mp hxT (hcopyR e)).elim
        · exact hxassigned
      have hinterCard : (used ∩ T).card ≤ J.card := by
        calc
          (used ∩ T).card ≤ assigned.card :=
            Finset.card_le_card hinterSubset
          _ ≤ J.card := by
            dsimp only [assigned]
            exact (Finset.card_image_le.trans (by simp))
      have hUT : U ∩ T = T \ used := by
        ext x
        simp [U, T, and_comm]
      have hinterCard' : (T ∩ used).card ≤ J.card := by
        simpa [Finset.inter_comm] using hinterCard
      have hsplit : (U ∩ T).card + (T ∩ used).card = T.card := by
        rw [hUT]
        exact Finset.card_sdiff_add_card_inter T used
      have hpred : J.card ≤ L.card - 1 := by omega
      have hinterPred : (T ∩ used).card ≤ L.card - 1 :=
        hinterCard'.trans hpred
      change T.card - (L.card - 1) ≤ (U ∩ T).card
      calc
        T.card - (L.card - 1) ≤ T.card - (T ∩ used).card :=
          Nat.sub_le_sub_left hinterPred T.card
        _ = (U ∩ T).card := by omega

end Assignment

end Erdos570
