import ErdosProblems.Erdos547.Attachment
import ErdosProblems.Erdos547.TreeCore

/-!
# Growing a connected subtree in pairs

If a connected subtree omits a nonleaf and is too small to contain every
nonleaf, it can be enlarged along a two-edge path by two new vertices. This
is the tree-side step used by the matched-prefix embedding argument.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U : Type*} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]

open scoped Classical in
/-- Unless a connected vertex set already contains every nonleaf, a tree has
a two-edge path which starts in that set and then uses two new vertices. -/
theorem exists_two_vertex_attachment (hT : T.IsTree) (S : Finset U)
    (hS : (T.induce (S : Set U)).Connected)
    (hsmall : S.card < Fintype.card (treeCore T)) :
    ∃ p ∈ S, ∃ u ∉ S, ∃ v ∉ S, T.Adj p u ∧ T.Adj u v := by
  classical
  by_contra hno
  let A : Set U := (S : Set U) ∪ {u | ∃ p ∈ S, T.Adj p u}
  have hA : A.Nonempty := by
    obtain ⟨p⟩ := hS.nonempty
    exact ⟨p.val, Or.inl p.property⟩
  have hfull : A = Set.univ := by
    by_contra hproper
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_boundary_edge hT.connected.preconnected A hA hproper
    have hyS : y ∉ S := fun h ↦ hy (Or.inl h)
    rcases hx with hxS | ⟨p, hp, hpx⟩
    · exact hy (Or.inr ⟨x, hxS, hxy⟩)
    · by_cases hxS : x ∈ S
      · exact hy (Or.inr ⟨x, hxS, hxy⟩)
      · exact hno ⟨p, hp, x, hxS, y, hyS, hpx, hxy⟩
  have hcore : treeCore T ⊆ (S : Set U) := by
    intro u hu
    by_contra huS
    have huA : u ∈ A := hfull ▸ Set.mem_univ u
    obtain ⟨p, hp, hpu⟩ := huA.resolve_left huS
    have hparent : ∀ y, T.Adj u y → y = p := by
      intro y huy
      have hyS : y ∈ S := by
        by_contra hyS
        exact hno ⟨p, hp, u, huS, y, hyS, hpu, huy⟩
      exact unique_attachment_to_connected hT.isAcyclic (S : Set U) hS.preconnected
        huS hyS hp huy hpu.symm
    have hdeg : T.degree u = 1 := T.degree_eq_one_iff_existsUnique_adj.mpr
      ⟨p, hpu.symm, hparent⟩
    change 2 ≤ T.degree u at hu
    omega
  let f : treeCore T → (S : Set U) := fun x ↦ ⟨x.val, hcore x.property⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : (S : Set U) ↦ z.val) h)
  have hcard := Fintype.card_le_of_injective f hinj
  have hcardS : Fintype.card (S : Set U) = S.card := by
    apply Fintype.card_of_subtype
    intro x
    rfl
  rw [hcardS] at hcard
  omega

open scoped Classical in
/-- A connected prefix built from one edge by repeatedly attaching a pair of
new vertices along a two-edge path. The index counts the pairs. -/
inductive PairedPrefix : ℕ → Finset U → Prop
  | edge (u v : U) (huv : T.Adj u v) : PairedPrefix 1 {u, v}
  | step {r : ℕ} {S : Finset U} (hS : PairedPrefix r S)
      (p : U) (hp : p ∈ S) (u : U) (hu : u ∉ S) (v : U) (hv : v ∉ S)
      (hpu : T.Adj p u) (huv : T.Adj u v) : PairedPrefix (r + 1) (insert v (insert u S))

open scoped Classical in
omit [Fintype U] [DecidableRel T.Adj] in
theorem PairedPrefix.pos {r : ℕ} {S : Finset U} (h : PairedPrefix T r S) : 0 < r := by
  cases h <;> omega

open scoped Classical in
omit [Fintype U] [DecidableRel T.Adj] in
theorem PairedPrefix.card {r : ℕ} {S : Finset U} (h : PairedPrefix T r S) : S.card = 2 * r := by
  induction h with
  | edge u v huv => simp [huv.ne]
  | @step r S hS p hp u hu v hv hpu huv ih =>
    have hv' : v ∉ insert u S := by simp [hv, huv.ne']
    rw [Finset.card_insert_of_notMem hv', Finset.card_insert_of_notMem hu, ih]
    omega

open scoped Classical in
omit [Fintype U] [DecidableRel T.Adj] in
theorem PairedPrefix.connected {r : ℕ} {S : Finset U} (h : PairedPrefix T r S) :
    (T.induce (S : Set U)).Connected := by
  induction h with
  | edge u v huv =>
    let : Nonempty ({u} : Set U) := ⟨⟨u, rfl⟩⟩
    have hsingle : (T.induce ({u} : Set U)).Connected :=
      SimpleGraph.IsTree.of_subsingleton.connected
    have hconn := connected_induce_insert ({u} : Set U) hsingle v ⟨u, rfl⟩ huv.symm
    have hco : (↑({u, v} : Finset U) : Set U) = insert v ({u} : Set U) := by
      ext x
      simp [or_comm]
    rw [hco]
    exact hconn
  | @step r S hS p hp u hu v hv hpu huv ih =>
    have hfirst := connected_induce_insert (S : Set U) ih u ⟨p, hp⟩ hpu.symm
    have hsecond := connected_induce_insert (insert u (S : Set U)) hfirst v
      ⟨u, Set.mem_insert u (S : Set U)⟩ huv.symm
    have hco : (↑(insert v (insert u S)) : Set U) = insert v (insert u (S : Set U)) := by
      ext x
      simp
    rw [hco]
    exact hsecond

open scoped Classical in
/-- If there are at least `2*r` nonleaves, a paired prefix with exactly `r`
pairs exists. All attachment data are retained by `PairedPrefix`. -/
theorem exists_paired_prefix (hT : T.IsTree) (r : ℕ) (hr : 0 < r)
    (hsize : 2 * r ≤ Fintype.card (treeCore T)) :
    ∃ S : Finset U, PairedPrefix T r S := by
  classical
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hrzero : r = 0
    · subst r
      have hcorepos : 0 < Fintype.card (treeCore T) := by omega
      obtain ⟨u⟩ := Fintype.card_pos_iff.mp hcorepos
      have hu : 0 < T.degree u.val := by
        have h := u.property
        change 2 ≤ T.degree u.val at h
        omega
      obtain ⟨v, huv⟩ := (T.degree_pos_iff_exists_adj u.val).mp hu
      exact ⟨{u.val, v}, PairedPrefix.edge u.val v huv⟩
    · obtain ⟨S, hS⟩ := ih (by omega) (by omega)
      have hcard := hS.card
      obtain ⟨p, hp, u, hu, v, hv, hpu, huv⟩ := exists_two_vertex_attachment T hT S
        hS.connected (by omega)
      exact ⟨insert v (insert u S), PairedPrefix.step hS p hp u hu v hv hpu huv⟩

end Erdos547

#print axioms Erdos547.exists_two_vertex_attachment
#print axioms Erdos547.exists_paired_prefix
