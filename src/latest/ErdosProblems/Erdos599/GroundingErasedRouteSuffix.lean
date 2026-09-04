/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedRouteCore
import ErdosProblems.Erdos599.HalfwayFiniteInputDirectionEdgeCoverage
import Mathlib.Data.List.Nodup

/-!
# Suffixes of loop-erased signed routes

The source's last-contact repair replaces a decoded route by the suffix
beginning at its last contact with the starting ladder component.  This
module supplies the endpoint-preserving suffix operation at the signed-route
level.  It deliberately takes an arbitrary visited vertex; the later
last-contact module is responsible for choosing the final contact and for
transporting any boundary point on the discarded ladder tail.
-/

noncomputable section

open Set

namespace Erdos599
namespace PopularAuxiliary.Input

open PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace ErasedSignedRoute

variable {x y : V} {raw : List (SignedEdge V)}

/-- The suffix of a loop-erased signed route beginning at a visited vertex.
The suffix remains a sublist of the original raw route and its projected
vertex chain remains repetition-free. -/
noncomputable def suffixFrom
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain) : ErasedSignedRoute z y raw := by
  let data := Classical.choose (E.runs.exists_suffix_from_mem hz)
  have hdata := Classical.choose_spec (E.runs.exists_suffix_from_mem hz)
  exact {
    steps := data
    runs := hdata.2.1
    steps_sublist := hdata.1.sublist.trans E.steps_sublist
    vertexChain_nodup := hdata.2.2.nodup E.vertexChain_nodup }

theorem suffixFrom_steps_suffix
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain) :
    (E.suffixFrom z hz).steps <:+ E.steps := by
  exact (Classical.choose_spec (E.runs.exists_suffix_from_mem hz)).1

theorem suffixFrom_vertexChain_suffix
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain) :
    (E.suffixFrom z hz).vertexChain <:+ E.vertexChain := by
  exact (Classical.choose_spec (E.runs.exists_suffix_from_mem hz)).2.2

theorem suffixFrom_steps_subset
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain) :
    ∀ {s : SignedEdge V}, s ∈ (E.suffixFrom z hz).steps → s ∈ E.steps := by
  intro s hs
  exact (E.suffixFrom_steps_suffix z hz).subset hs

theorem suffixFrom_vertexChain_subset
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain) :
    ∀ {v : V}, v ∈ (E.suffixFrom z hz).vertexChain → v ∈ E.vertexChain := by
  intro v hv
  exact (E.suffixFrom_vertexChain_suffix z hz).subset hv

/-- Validity of the original signed route transfers to every last-contact
suffix, hence the suffix has an honest alternating compression. -/
noncomputable def suffixCompressionOfValid
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    ErasedCompression (Gamma := Gamma) (E.suffixFrom z hz) :=
  (E.suffixFrom z hz).compressionOfValid fun {_s} hs ↦
    hvalid (E.suffixFrom_steps_subset z hz hs)

theorem suffixCompressionOfValid_initial_eq
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    (E.suffixCompressionOfValid z hz hvalid).path.initial = z :=
  (E.suffixCompressionOfValid z hz hvalid).initial_eq

theorem suffixCompressionOfValid_terminal_eq
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    (E.suffixCompressionOfValid z hz hvalid).path.terminal? = some y :=
  (E.suffixCompressionOfValid z hz hvalid).terminal_eq

/-- Every unoriented edge of the compressed suffix already occurs in the
compressed original route. -/
theorem suffixCompressionOfValid_edgeSet_subset
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    (E.suffixCompressionOfValid z hz hvalid).path.edgeSet ⊆
      (E.compressionOfValid hvalid).path.edgeSet := by
  rw [(E.suffixCompressionOfValid z hz hvalid).edgeSet_eq,
    (E.compressionOfValid hvalid).edgeSet_eq]
  rintro e ⟨s, hs, rfl⟩
  exact ⟨s, E.suffixFrom_steps_subset z hz hs, rfl⟩

/-- Maximal-run compression preserves every directed signed edge, not just
the underlying unoriented edge.  Together with the converse theorem in
`GroundingErasedRouteCore`, this identifies the compressed direction sets
exactly. -/
theorem directedSignedEdgeSet_subset_compressionOfValid_directionEdges
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    (d : Alternating.Direction) :
    directedSignedEdgeSet d E.steps ⊆
      (E.compressionOfValid hvalid).path.directionEdges d := by
  classical
  by_cases hnil : E.steps = []
  · simp [hnil, directedSignedEdgeSet, compressionOfValid,
      Alternating.AltPath.directionEdges, Alternating.AltPath.links]
  · let S := E.toFiniteInputOfValid hnil hvalid
    intro e he
    obtain ⟨s, hs, hsdir, rfl⟩ := he
    obtain ⟨n, hns⟩ := List.get_of_mem hs
    have hnDir : (E.steps.get n).direction = d := by
      rw [hns]
      exact hsdir
    have hraw := S.rawEdge_mem_directionEdges n
    have hcolour : S.colour n = d := by
      change (E.steps.get n).direction = d
      exact hnDir
    rw [hcolour] at hraw
    have hrawEq : S.rawEdge n = s.edge := by
      rw [← hns]
      cases d with
      | forward =>
          have hedge := E.step_edge_eq_routeVertices_forward n hnDir
          change (match (E.steps.get n).direction with
            | .forward => (E.routeVertex n.1, E.routeVertex (n.1 + 1))
            | .backward => (E.routeVertex (n.1 + 1), E.routeVertex n.1)) =
              (E.steps.get n).edge
          rw [hnDir]
          exact hedge.symm
      | backward =>
          have hedge := E.step_edge_eq_routeVertices_backward n hnDir
          change (match (E.steps.get n).direction with
            | .forward => (E.routeVertex n.1, E.routeVertex (n.1 + 1))
            | .backward => (E.routeVertex (n.1 + 1), E.routeVertex n.1)) =
              (E.steps.get n).edge
          rw [hnDir]
          exact hedge.symm
    simpa only [compressionOfValid, hnil, S] using hrawEq ▸ hraw

/-- Direction-exact form of maximal-run compression. -/
theorem compressionOfValid_directionEdges_eq_directedSignedEdgeSet
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    (d : Alternating.Direction) :
    (E.compressionOfValid hvalid).path.directionEdges d =
      directedSignedEdgeSet d E.steps := by
  apply Set.Subset.antisymm
  · exact E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      hvalid d
  · exact E.directedSignedEdgeSet_subset_compressionOfValid_directionEdges
      hvalid d

/-- The last-contact suffix preserves directions inside the original
compressed route. -/
theorem suffixCompressionOfValid_directionEdges_subset
    (E : ErasedSignedRoute x y raw) (z : V)
    (hz : z ∈ E.vertexChain)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    (d : Alternating.Direction) :
    (E.suffixCompressionOfValid z hz hvalid).path.directionEdges d ⊆
      (E.compressionOfValid hvalid).path.directionEdges d := by
  intro e he
  have heSigned : e ∈ directedSignedEdgeSet d
      (E.suffixFrom z hz).steps :=
    (E.suffixFrom z hz)
      |>.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
        (fun {_s} hs ↦ hvalid (E.suffixFrom_steps_subset z hz hs)) d he
  obtain ⟨s, hs, hsdir, rfl⟩ := heSigned
  apply E.directedSignedEdgeSet_subset_compressionOfValid_directionEdges
    hvalid d
  exact ⟨s, E.suffixFrom_steps_subset z hz hs, hsdir, rfl⟩

/-- Every endpoint of a compressed edge occurs in the projected signed
vertex chain.  This is the bridge from alternating-link contact data to the
finite list on which the last contact is selected. -/
theorem compressionOfValid_edge_endpoints_mem_vertexChain
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    {e : V × V} (he : e ∈ (E.compressionOfValid hvalid).path.edgeSet) :
    e.1 ∈ E.vertexChain ∧ e.2 ∈ E.vertexChain := by
  rw [(E.compressionOfValid hvalid).edgeSet_eq] at he
  obtain ⟨s, hs, rfl⟩ := he
  obtain ⟨n, hns⟩ := List.get_of_mem hs
  have hchain := E.runs.signedVertexChain_get_entry_exit n.1 n.2
  have hentry : s.entry ∈ E.vertexChain := by
    rw [← hns]
    change E.steps[n.1].entry ∈ signedVertexChain x E.steps
    rw [← hchain.1]
    exact List.getElem_mem (by simp [signedVertexChain])
  have hexit : s.exit ∈ E.vertexChain := by
    rw [← hns]
    change E.steps[n.1].exit ∈ signedVertexChain x E.steps
    rw [← hchain.2]
    exact List.getElem_mem (by simp [signedVertexChain])
  cases hdir : s.direction with
  | forward =>
      simpa [SignedEdge.entry_eq_fst_of_direction_forward _ hdir,
        SignedEdge.exit_eq_snd_of_direction_forward _ hdir] using
          And.intro hentry hexit
  | backward =>
      simpa [SignedEdge.exit_eq_fst_of_direction_backward _ hdir,
        SignedEdge.entry_eq_snd_of_direction_backward _ hdir] using
          And.intro hexit hentry

/-- Every vertex of the maximally compressed alternating route is one of
the vertices of the underlying loop-erased signed chain. -/
theorem compressionOfValid_vertexSet_subset_vertexChain
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    (E.compressionOfValid hvalid).path.vertexSet ⊆
      {v | v ∈ E.vertexChain} := by
  classical
  by_cases hnil : E.steps = []
  · simpa [compressionOfValid, hnil, ErasedSignedRoute.vertexChain,
      signedVertexChain]
  · let S := E.toFiniteInputOfValid hnil hvalid
    intro v hv
    simp only [mem_ofPred_eq] at hv
    have hv' : v ∈ S.toFiniteRunWalk.toFiniteTrace.vertexSet := by
      change v ∈ S.toFiniteRunWalk.toFiniteTrace.vertexSet at hv
      exact hv
    rw [S.toFiniteTrace_vertexSet] at hv'
    obtain ⟨n, hn, rfl⟩ := hv'
    change E.routeVertex n ∈ E.vertexChain
    have hnlt : n < E.vertexChain.length := by
      rw [E.vertexChain_length]
      have hnle : n ≤ E.steps.length := by
        simpa only [S, toFiniteInputOfValid] using hn.2
      omega
    unfold routeVertex
    rw [List.getD_eq_get E.vertexChain y ⟨n, hnlt⟩]
    exact List.get_mem E.vertexChain ⟨n, hnlt⟩

/-- Conversely, maximal-run compression retains every vertex of the
loop-erased signed chain.  Runs only group consecutive edges; they do not
discard their internal original vertices. -/
theorem vertexChain_subset_compressionOfValid_vertexSet
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    {v | v ∈ E.vertexChain} ⊆
      (E.compressionOfValid hvalid).path.vertexSet := by
  classical
  by_cases hnil : E.steps = []
  · simpa [compressionOfValid, hnil, ErasedSignedRoute.vertexChain,
      signedVertexChain]
  · let S := E.toFiniteInputOfValid hnil hvalid
    intro v hv
    obtain ⟨n, rfl⟩ := List.get_of_mem hv
    have hnle : n.1 ≤ E.steps.length := by
      have hnlt : n.1 < E.steps.length + 1 := by
        simpa only [E.vertexChain_length] using n.2
      omega
    have hroute : E.routeVertex n.1 = E.vertexChain.get n := by
      unfold routeVertex
      rw [List.getD_eq_get E.vertexChain y n]
    rw [← hroute]
    simp only [compressionOfValid, hnil]
    change S.vertex n.1 ∈ S.toFiniteRunWalk.toFiniteTrace.vertexSet
    rw [S.toFiniteTrace_vertexSet]
    exact ⟨n.1, ⟨Nat.zero_le _, by
      simpa only [S, toFiniteInputOfValid] using hnle⟩, rfl⟩

/-- Exact carrier equality for a compressed loop-erased signed route. -/
theorem compressionOfValid_vertexSet_eq_vertexChain
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    (E.compressionOfValid hvalid).path.vertexSet =
      {v | v ∈ E.vertexChain} := by
  exact Set.Subset.antisymm
    (E.compressionOfValid_vertexSet_subset_vertexChain hvalid)
    (E.vertexChain_subset_compressionOfValid_vertexSet hvalid)

/-- A maximal occurrence of a set on the finite projected vertex chain.
The chosen position is a contact and every strictly later position is not. -/
structure LastContact
    (E : ErasedSignedRoute x y raw) (A : Set V) where
  position : Fin E.vertexChain.length
  mem : E.vertexChain[position] ∈ A
  no_mem_after : ∀ j : Fin E.vertexChain.length,
    position.1 < j.1 → E.vertexChain[j] ∉ A

/-- Every nonempty contact set has a final occurrence on the loop-erased
route. -/
theorem exists_lastContact
    (E : ErasedSignedRoute x y raw) (A : Set V)
    (hcontact : ∃ i : Fin E.vertexChain.length,
      E.vertexChain[i] ∈ A) :
    Nonempty (E.LastContact A) := by
  classical
  let contacts : Finset (Fin E.vertexChain.length) :=
    Finset.univ.filter fun i ↦ E.vertexChain[i] ∈ A
  obtain ⟨i, hi⟩ := hcontact
  have hiContact : i ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  let last : Fin E.vertexChain.length :=
    contacts.max' ⟨i, hiContact⟩
  have hlastContact : last ∈ contacts :=
    Finset.max'_mem contacts ⟨i, hiContact⟩
  refine ⟨{
    position := last
    mem := by
      simpa only [contacts, Finset.mem_filter, Finset.mem_univ,
        true_and] using hlastContact
    no_mem_after := ?_ }⟩
  intro j hlastj hj
  have hjContact : j ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj
  exact (not_le_of_gt hlastj) (Finset.le_max' contacts j hjContact)

def LastContact.vertex
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A) : V :=
  E.vertexChain[C.position]

theorem LastContact.vertex_mem_chain
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A) : C.vertex ∈ E.vertexChain :=
  List.getElem_mem (l := E.vertexChain) C.position.2

theorem LastContact.vertex_mem
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A) : C.vertex ∈ A :=
  C.mem

/-- Last contacts are stable when a larger contact set has its final contact
inside a smaller one.  This is the exact comparison used when a selected
route's final contact with a whole ladder component is known, by Assertion
8.21, to lie in the finite prefix currently being normalized. -/
theorem LastContact.position_eq_of_subset_of_vertex_mem
    {E : ErasedSignedRoute x y raw} {A B : Set V}
    (CA : E.LastContact A) (CB : E.LastContact B)
    (hAB : A ⊆ B) (hCB : CB.vertex ∈ A) :
    CA.position = CB.position := by
  have hCALe : CA.position.1 ≤ CB.position.1 := by
    by_contra hnot
    have hlt : CB.position.1 < CA.position.1 := Nat.lt_of_not_ge hnot
    exact CB.no_mem_after CA.position hlt (hAB CA.mem)
  have hCBLe : CB.position.1 ≤ CA.position.1 := by
    by_contra hnot
    have hlt : CA.position.1 < CB.position.1 := Nat.lt_of_not_ge hnot
    exact CA.no_mem_after CB.position hlt hCB
  exact Fin.ext (Nat.le_antisymm hCALe hCBLe)

/-- Vertex form of `position_eq_of_subset_of_vertex_mem`. -/
theorem LastContact.vertex_eq_of_subset_of_vertex_mem
    {E : ErasedSignedRoute x y raw} {A B : Set V}
    (CA : E.LastContact A) (CB : E.LastContact B)
    (hAB : A ⊆ B) (hCB : CB.vertex ∈ A) :
    CA.vertex = CB.vertex := by
  exact congrArg (fun i : Fin E.vertexChain.length ↦ E.vertexChain.get i)
    (CA.position_eq_of_subset_of_vertex_mem CB hAB hCB)

/-- If the route's prescribed terminal belongs to the contact set, then it
is necessarily the final contact.  This is the endpoint fact used to remove
the apparent edge-tail alternative for a selected route returning to the
component containing its own request apex. -/
theorem LastContact.eq_terminal_of_terminal_mem
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A) (hy : y ∈ A) : C.vertex = y := by
  have hlastChain : E.steps.length < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  let j : Fin E.vertexChain.length := ⟨E.steps.length, hlastChain⟩
  have hj : E.vertexChain[j] = y := by
    change E.vertexChain.get j = y
    have hroute := E.routeVertex_last
    unfold routeVertex at hroute
    simpa only [j, List.getD_eq_get E.vertexChain y j] using hroute
  have hposLe : C.position.1 ≤ j.1 := by
    have hpos := C.position.2
    have hlen := E.vertexChain_length
    change C.position.1 ≤ E.steps.length
    omega
  by_cases heq : C.position.1 = j.1
  · have hfin : C.position = j := Fin.ext heq
    exact (congrArg (fun i : Fin E.vertexChain.length ↦ E.vertexChain[i])
      hfin).trans hj
  · have hlt : C.position.1 < j.1 := lt_of_le_of_ne hposLe heq
    apply False.elim
    apply C.no_mem_after j hlt
    rw [hj]
    exact hy

/-- A repetition-free erased signed route with equal prescribed endpoints
has no step. -/
theorem steps_eq_nil_of_start_eq_terminal
    (E : ErasedSignedRoute x y raw) (hxy : x = y) : E.steps = [] := by
  have hzeroChain : 0 < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  have hlastChain : E.steps.length < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  let i : Fin E.vertexChain.length := ⟨0, hzeroChain⟩
  let j : Fin E.vertexChain.length := ⟨E.steps.length, hlastChain⟩
  have hget : E.vertexChain.get i = E.vertexChain.get j := by
    have hroute : E.routeVertex 0 = E.routeVertex E.steps.length :=
      E.routeVertex_zero.trans (hxy.trans E.routeVertex_last.symm)
    unfold routeVertex at hroute
    simpa only [i, j, List.getD_eq_get E.vertexChain y i,
      List.getD_eq_get E.vertexChain y j] using hroute
  have hij : i = j := E.vertexChain_nodup.get_inj_iff.mp hget
  have hlen : E.steps.length = 0 := by
    simpa only [i, j] using (congrArg Fin.val hij).symm
  exact List.eq_nil_iff_length_eq_zero.mpr hlen

/-- Once the selected final contact is the prescribed terminal, its honest
last-contact suffix is the zero-edge route. -/
theorem LastContact.suffixFrom_steps_eq_nil_of_eq_terminal
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A) (hterminal : C.vertex = y) :
    (E.suffixFrom C.vertex C.vertex_mem_chain).steps = [] := by
  exact (E.suffixFrom C.vertex C.vertex_mem_chain)
    |>.steps_eq_nil_of_start_eq_terminal hterminal

/-- The honest alternating suffix which begins at the selected final
contact and retains the original route terminal. -/
noncomputable def LastContact.suffixCompressionOfValid
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    ErasedCompression (Gamma := Gamma)
      (E.suffixFrom C.vertex C.vertex_mem_chain) :=
  E.suffixCompressionOfValid C.vertex C.vertex_mem_chain hvalid

/-- The suffix beginning at the final contact contains no second point of
the contact set.  Thus the source splice cannot return to its old parent
after the normalization point. -/
theorem LastContact.eq_vertex_of_mem_suffix_vertexChain_of_mem
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A) {v : V}
    (hvSuffix : v ∈
      (E.suffixFrom C.vertex C.vertex_mem_chain).vertexChain)
    (hvA : v ∈ A) :
    v = C.vertex := by
  classical
  by_contra hvne
  let R := (E.suffixFrom C.vertex C.vertex_mem_chain).vertexChain
  have hR_suffix : R <:+ E.vertexChain := by
    exact E.suffixFrom_vertexChain_suffix C.vertex C.vertex_mem_chain
  obtain ⟨pre, hpre⟩ := hR_suffix
  have hnodup : (pre ++ R).Nodup := by
    rw [hpre]
    exact E.vertexChain_nodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  have hCmemR : C.vertex ∈ R := by
    change C.vertex ∈ signedVertexChain C.vertex
      (E.suffixFrom C.vertex C.vertex_mem_chain).steps
    simp [signedVertexChain]
  have hCnotPre : C.vertex ∉ pre := by
    intro hCpre
    exact hdisj C.vertex hCpre C.vertex hCmemR rfl
  have hvnotPre : v ∉ pre := by
    intro hvpre
    exact hdisj v hvpre v hvSuffix rfl
  have hidxC : E.vertexChain.idxOf C.vertex = C.position.1 := by
    exact List.get_idxOf E.vertexChain_nodup C.position
  have hidxC_R : R.idxOf C.vertex = 0 := by
    change (signedVertexChain C.vertex
      (E.suffixFrom C.vertex C.vertex_mem_chain).steps).idxOf C.vertex = 0
    simp [signedVertexChain]
  have hidxv_R_pos : 0 < R.idxOf v := by
    apply Nat.pos_of_ne_zero
    change (signedVertexChain C.vertex
      (E.suffixFrom C.vertex C.vertex_mem_chain).steps).idxOf v ≠ 0
    unfold signedVertexChain
    rw [List.idxOf_cons_ne _ (Ne.symm hvne)]
    exact Nat.succ_ne_zero _
  have hidxC_append : (pre ++ R).idxOf C.vertex = pre.length := by
    rw [List.idxOf_append_of_notMem hCnotPre, hidxC_R]
    omega
  have hidxv_append : (pre ++ R).idxOf v = pre.length + R.idxOf v :=
    List.idxOf_append_of_notMem hvnotPre
  have hlt : C.position.1 < E.vertexChain.idxOf v := by
    rw [← hidxC, ← hpre, hidxC_append, hidxv_append]
    omega
  let j : Fin E.vertexChain.length :=
    ⟨E.vertexChain.idxOf v, List.idxOf_lt_length_iff.2
      (hpre ▸ (List.mem_append_right pre hvSuffix))⟩
  have hjv : E.vertexChain[j] = v := by
    exact List.idxOf_get j.2
  exact C.no_mem_after j hlt (hjv ▸ hvA)

/-- Alternating compression of the last-contact suffix likewise has no
second contact with the old parent/contact set. -/
theorem LastContact.eq_vertex_of_mem_suffixCompression_vertexSet_of_mem
    {E : ErasedSignedRoute x y raw} {A : Set V}
    (C : E.LastContact A)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    {v : V}
    (hvSuffix : v ∈ (C.suffixCompressionOfValid hvalid).path.vertexSet)
    (hvA : v ∈ A) :
    v = C.vertex := by
  apply C.eq_vertex_of_mem_suffix_vertexChain_of_mem
  · exact (E.suffixFrom C.vertex C.vertex_mem_chain)
      |>.compressionOfValid_vertexSet_subset_vertexChain
        (fun {_s} hs ↦ hvalid (E.suffixFrom_steps_subset
          C.vertex C.vertex_mem_chain hs)) hvSuffix
  · exact hvA

end ErasedSignedRoute
end PopularAuxiliary.Input
end Erdos599

#print axioms
  Erdos599.PopularAuxiliary.Input.ErasedSignedRoute.suffixCompressionOfValid_edgeSet_subset
#print axioms
  Erdos599.PopularAuxiliary.Input.ErasedSignedRoute.suffixCompressionOfValid_directionEdges_subset
#print axioms
  Erdos599.PopularAuxiliary.Input.ErasedSignedRoute.exists_lastContact
#print axioms
  Erdos599.PopularAuxiliary.Input.ErasedSignedRoute.LastContact.eq_vertex_of_mem_suffix_vertexChain_of_mem
#print axioms
  Erdos599.PopularAuxiliary.Input.ErasedSignedRoute.LastContact.position_eq_of_subset_of_vertex_mem
