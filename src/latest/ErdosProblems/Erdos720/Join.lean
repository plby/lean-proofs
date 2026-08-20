import ErdosProblems.Erdos720.Connector
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Erdos720

open Finset SimpleGraph
open ExtendableState

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple path represented by a vertex list, with specified endpoints and
exactly the specified number of edges. -/
def ExactSimplePath (G : SimpleGraph V) (first : V) (length : ℕ) (last : V) : Prop :=
  ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = length + 1 ∧
    l.head? = some first ∧ l.getLast? = some last

lemma isChain_append_tail {α : Type*} {R : α → α → Prop}
    {l r : List α} {x : α} (hl : l.IsChain R) (hr : r.IsChain R)
    (hlast : l.getLast? = some x) (hrhead : r.head? = some x) :
    (l ++ r.tail).IsChain R := by
  obtain ⟨rs, rfl⟩ := List.head?_eq_some_iff.mp hrhead
  rw [List.isChain_append]
  refine ⟨hl, hr.tail, ?_⟩
  intro a ha b hb
  have ha' : a = x := (by simpa [hlast] using ha : x = a).symm
  subst a
  exact (List.isChain_cons.mp hr).1 b hb

lemma isChain_reverse_append_tail {α : Type*} {R : α → α → Prop}
    (hsymm : Symmetric R) {l r : List α} {x : α}
    (hl : l.IsChain R) (hr : r.IsChain R)
    (hlhead : l.head? = some x) (hrhead : r.head? = some x) :
    (l.reverse ++ r.tail).IsChain R := by
  have hrev : l.reverse.IsChain R := by
    rw [List.isChain_reverse]
    exact hl.imp fun _ _ hab => hsymm hab
  apply isChain_append_tail hrev hr
  · simpa only [List.getLast?_reverse] using hlhead
  · exact hrhead

lemma RobustConnector.exactSimplePath {height q : ℕ} (C : RobustConnector G height q)
    (hh : 0 < height) (hq : 0 < q) {a b : V}
    (ha : a ∈ C.leftLeaves) (hb : b ∈ C.rightLeaves) :
    ExactSimplePath G a (2 * height + q) b := by
  classical
  rcases C.leftPaths ha with
    ⟨l, hlnd, hlch, hllen, hlhead, hllast, hlsub, hlfresh⟩
  rcases C.centerPath with
    ⟨c, hcnd, hcch, hclen, hchead, hclast, hcsub, hcfresh⟩
  rcases C.rightPaths hb with
    ⟨r, hrnd, hrch, hrlen, hrhead, hrlast, hrsub, hrfresh⟩
  have hchain₁ : (l.reverse ++ c.tail).IsChain G.Adj :=
    isChain_reverse_append_tail (fun _ _ h => (G.adj_comm _ _).mp h)
      hlch hcch hlhead hchead
  have hcne : c.length ≠ 1 := by omega
  have hctailLast : c.tail.getLast? = some C.rootRight := by
    rw [List.getLast?_tail, if_neg hcne, hclast]
  have hchain₁Last : (l.reverse ++ c.tail).getLast? = some C.rootRight := by
    rw [List.getLast?_append, hctailLast]
    rfl
  have hchain : ((l.reverse ++ c.tail) ++ r.tail).IsChain G.Adj :=
    isChain_append_tail hchain₁ hrch hchain₁Last hrhead
  have hcroot : C.rootLeft ∉ c.tail := by
    obtain ⟨cs, rfl⟩ := List.head?_eq_some_iff.mp hchead
    exact (List.nodup_cons.mp hcnd).1
  have hrroot : C.rootRight ∉ r.tail := by
    obtain ⟨rs, rfl⟩ := List.head?_eq_some_iff.mp hrhead
    exact (List.nodup_cons.mp hrnd).1
  have hsep₁ : ∀ x ∈ l.reverse, ∀ y ∈ c.tail, x ≠ y := by
    intro x hxl y hyc hxy
    subst y
    have hxl' : x ∈ l := List.mem_reverse.mp hxl
    have hxc : x ∈ c := by
      obtain ⟨cs, rfl⟩ := List.head?_eq_some_iff.mp hchead
      exact List.mem_cons_of_mem _ hyc
    have hxcore : x ∈ C.core := hcsub x hxc
    rcases hlfresh x hxl' with hxroot | hxout
    · exact hcroot (hxroot ▸ hyc)
    · exact hxout hxcore
  have hnd₁ : (l.reverse ++ c.tail).Nodup := by
    rw [List.nodup_append]
    exact ⟨List.nodup_reverse.mpr hlnd, hcnd.tail, hsep₁⟩
  have hsep₂ : ∀ x ∈ l.reverse ++ c.tail, ∀ y ∈ r.tail, x ≠ y := by
    intro x hx y hyr hxy
    subst y
    have hxr : x ∈ r := by
      obtain ⟨rs, rfl⟩ := List.head?_eq_some_iff.mp hrhead
      exact List.mem_cons_of_mem _ hyr
    rcases hrfresh x hxr with hxroot | hxout
    · exact hrroot (hxroot ▸ hyr)
    · apply hxout
      rcases List.mem_append.mp hx with hxl | hxc
      · exact hlsub x (List.mem_reverse.mp hxl)
      · exact C.core_subset_leftBase (hcsub x (by
          obtain ⟨cs, rfl⟩ := List.head?_eq_some_iff.mp hchead
          exact List.mem_cons_of_mem _ hxc))
  have hnd : ((l.reverse ++ c.tail) ++ r.tail).Nodup := by
    rw [List.nodup_append]
    exact ⟨hnd₁, hrnd.tail, hsep₂⟩
  have hrne : r.length ≠ 1 := by omega
  have hrtailLast : r.tail.getLast? = some b := by
    rw [List.getLast?_tail, if_neg hrne, hrlast]
  refine ⟨(l.reverse ++ c.tail) ++ r.tail, hnd, hchain, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse, List.length_tail]
    omega
  · rw [List.head?_append, List.head?_append, List.head?_reverse, hllast]
    rfl
  · rw [List.getLast?_append, hrtailLast]
    rfl

lemma ExactSimplePath.cycleGraph_isContained {n : ℕ} (hn : 2 < n)
    {a b : V} (P : ExactSimplePath G a (n - 1) b) (hab : G.Adj a b) :
    cycleGraph n ⊑ G := by
  rcases P with ⟨l, hlnd, hlch, hllen, hlhead, hllast⟩
  obtain ⟨ls, rfl⟩ := List.head?_eq_some_iff.mp hlhead
  let hne : a :: ls ≠ [] := List.cons_ne_nil _ _
  have hlast : (a :: ls).getLast hne = b := by
    have h := hllast
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at h
    exact Option.some.inj h
  let w₀ := Walk.ofSupport (G := G) (a :: ls) hne hlch
  let w : G.Walk a b := w₀.copy rfl hlast
  have hwsupport : w.support = a :: ls := by
    change (w₀.copy rfl hlast).support = a :: ls
    rw [Walk.support_copy]
    exact Walk.support_ofSupport hne hlch
  have hwpath : w.IsPath := by
    rw [Walk.isPath_def, hwsupport]
    exact hlnd
  have hwlen : w.length = n - 1 := by
    change (w₀.copy rfl hlast).length = n - 1
    rw [Walk.length_copy]
    change (Walk.ofSupport (G := G) (a :: ls) hne hlch).length = n - 1
    rw [Walk.length_ofSupport, hllen]
    omega
  have hclose : s(a, b) ∉ w.edges := by
    intro he
    have hone := hwpath.length_eq_one_of_mem_edges he
    rw [hwlen] at hone
    omega
  let c : G.Walk b b := Walk.cons hab.symm w
  have hcycle : c.IsCycle := by
    change (Walk.cons hab.symm w).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨hwpath, by simpa [Sym2.eq_swap] using hclose⟩
  apply (cycleGraph_isContained_iff hn).2
  refine ⟨b, c, hcycle, ?_⟩
  change (Walk.cons hab.symm w).length = n
  simp [hwlen]
  omega

end Erdos720
