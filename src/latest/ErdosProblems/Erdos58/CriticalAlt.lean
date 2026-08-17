/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A finite critical-subgraph reduction

This file proves the standard reduction from a finite non-`n`-colorable graph
to a vertex-critical induced subgraph.  For `n > 0`, the critical graph is
connected after deletion of any one vertex and has minimum degree at least
`n`.
-/

namespace Erdos58.CriticalAlt

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Transport in a family of subtypes does not change the underlying value. -/
private lemma coe_cast_subtype {I α : Type*} (P : I → α → Prop)
    {i j : I} (h : i = j) (x : {a : α // P j a}) :
    (h.symm ▸ x : {a : α // P i a}).1 = x.1 := by
  cases h
  rfl

/-- Dependent function application commutes with transport in a family of
subtypes. -/
private lemma apply_cast_subtype {I α β : Type*} (P : I → α → Prop)
    (f : (i : I) → {a : α // P i a} → β)
    {i j : I} (h : i = j) (x : {a : α // P j a}) :
    f i (h.symm ▸ x) = f j x := by
  cases h
  rfl

/-- The graph obtained by deleting one vertex, on its natural subtype
carrier. -/
abbrev deleteVertex {X : Type*} (J : SimpleGraph X) (v : X) :
    SimpleGraph {w : X // w ≠ v} :=
  J.induce {w | w ≠ v}

/-- The vertex-deletion formulation of two-connectivity used here.  This
convention includes `K₂`, but excludes a singleton because its vertex deletion
has empty carrier. -/
def TwoConnected {X : Type*} (J : SimpleGraph X) : Prop :=
  J.Connected ∧ ∀ v : X, (deleteVertex J v).Connected

/-- An induced graph which is vertex-critical for non-`n`-colorability. -/
structure Witness (n : ℕ) where
  S : Finset V
  not_colorable :
    ¬(G.induce {v : V | v ∈ S}).Colorable n
  colorable_proper :
    ∀ (T : Set {v : V // v ∈ S}), T ≠ Set.univ →
      ((G.induce {v : V | v ∈ S}).induce T).Colorable n

/-- The critical induced graph carried by a witness. -/
abbrev Carrier {n : ℕ} (W : Witness G n) := {v : V // v ∈ W.S}

/-- The critical induced graph carried by a witness. -/
abbrev H {n : ℕ} (W : Witness G n) : SimpleGraph (Carrier G W) :=
  G.induce {v : V | v ∈ W.S}

/-- Every finite non-`n`-colorable graph has a vertex-critical induced
subgraph. -/
theorem exists_witness {n : ℕ} (hG : ¬G.Colorable n) :
    Nonempty (Witness G n) := by
  classical
  let bad : Finset V → Prop :=
    fun S ↦ ¬(G.induce {v : V | v ∈ S}).Colorable n
  have hbad_univ : bad (Finset.univ : Finset V) := by
    intro hcol
    have hcol' : (G.induce (Set.univ : Set V)).Colorable n := by
      have hpred :
          (Set.univ : Set V) = {v : V | v ∈ (Finset.univ : Finset V)} := by
        ext v
        simp
      rw [hpred]
      exact hcol
    exact hG (Colorable.of_hom (SimpleGraph.induceUnivIso G).symm.toHom hcol')
  let candidates : Finset (Finset V) :=
    (Finset.univ : Finset V).powerset.filter bad
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨?_, hbad_univ⟩⟩
    simp
  let S : Finset V :=
    Classical.choose (Finset.exists_min_image candidates Finset.card hcandidates)
  have hS :=
    Classical.choose_spec (Finset.exists_min_image candidates Finset.card hcandidates)
  have hSbad : bad S := (Finset.mem_filter.mp hS.1).2
  have hminimal : ∀ {U : Finset V}, U ⊂ S →
      (G.induce {v : V | v ∈ U}).Colorable n := by
    intro U hUS
    by_contra hU
    have hUmem : U ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hUS.le.trans (by simp)), hU⟩
    exact (Nat.not_lt_of_ge (hS.2 U hUmem)) (Finset.card_lt_card hUS)
  refine ⟨⟨S, hSbad, ?_⟩⟩
  intro T hT
  let U : Finset V := T.toFinset.image Subtype.val
  have hUSub : U ⊆ S := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hUne : U ≠ S := by
    intro hUS
    apply hT
    apply Set.eq_univ_of_forall
    intro x
    have hxU : x.1 ∈ U := by simpa [hUS] using x.property
    obtain ⟨y, hyT, hyv⟩ := Finset.mem_image.mp hxU
    have hyx : y = x := Subtype.ext (by simpa using hyv)
    simpa [hyx] using hyT
  have hcol := hminimal (Finset.ssubset_iff_subset_ne.mpr ⟨hUSub, hUne⟩)
  rcases hcol with ⟨C⟩
  refine ⟨Coloring.mk (fun x ↦ C ⟨x.1.1, ?_⟩) ?_⟩
  · refine Finset.mem_image.mpr ⟨x.1, ?_, rfl⟩
    simpa using x.2
  · intro a b hab
    apply C.valid
    simpa [H, SimpleGraph.induce_adj] using hab

/-- A critical witness has a vertex. -/
theorem witness_nonempty {n : ℕ} (W : Witness G n) : Nonempty (Carrier G W) := by
  by_contra h
  apply W.not_colorable
  refine ⟨Coloring.mk (fun x ↦ (h ⟨x⟩).elim) ?_⟩
  intro a
  exact (h ⟨a⟩).elim

/-- Every vertex in a critical witness has degree at least `n`. -/
theorem degree_ge {n : ℕ} (W : Witness G n) (v : Carrier G W) :
    n ≤ (H G W).degree v := by
  classical
  by_contra hdeg
  have hproper : ({w : Carrier G W | w ≠ v} : Set (Carrier G W)) ≠ Set.univ := by
    intro h
    have := Set.eq_univ_iff_forall.mp h v
    exact this rfl
  obtain ⟨C⟩ := W.colorable_proper _ hproper
  let neigh : Finset (Carrier G W) := (H G W).neighborFinset v
  let used : Finset (Fin n) :=
    neigh.attach.image (fun w ↦ C ⟨w.1, by
      exact (H G W).ne_of_adj
        ((SimpleGraph.mem_neighborFinset (G := H G W) v w.1).mp w.2) |>.symm⟩)
  have hused : used.card < (Finset.univ : Finset (Fin n)).card := by
    have hcard : used.card ≤ neigh.card := by
      exact (Finset.card_image_le.trans_eq Finset.card_attach)
    have hneigh : neigh.card < n := by
      simpa [neigh, SimpleGraph.card_neighborFinset_eq_degree] using
        (Nat.lt_of_not_ge hdeg)
    simpa using hcard.trans_lt hneigh
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  let color : Carrier G W → Fin n := fun w ↦
    if h : w = v then c else C ⟨w, h⟩
  have hvalid : ∀ {a b : Carrier G W}, (H G W).Adj a b → color a ≠ color b := by
    intro a b hab
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := ((H G W).ne_of_adj hab).symm
      have hbmem : b ∈ neigh :=
        (SimpleGraph.mem_neighborFinset (G := H G W) v b).mpr hab
      have hbused : C ⟨b, hb⟩ ∈ used := by
        refine Finset.mem_image.mpr ⟨⟨b, hbmem⟩, by simp, ?_⟩
        rfl
      intro heq
      have heq' : c = C ⟨b, hb⟩ := by
        simpa [color, hb] using heq
      exact hc (heq'.symm ▸ hbused)
    · by_cases hb : b = v
      · subst b
        have hamem : a ∈ neigh :=
          (SimpleGraph.mem_neighborFinset (G := H G W) v a).mpr hab.symm
        have haused : C ⟨a, ha⟩ ∈ used := by
          refine Finset.mem_image.mpr ⟨⟨a, hamem⟩, by simp, ?_⟩
          rfl
        intro heq
        have heq' : C ⟨a, ha⟩ = c := by
          simpa [color, ha] using heq
        exact hc (heq' ▸ haused)
      · have hab' : (deleteVertex (H G W) v).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
          simpa [deleteVertex, SimpleGraph.induce_adj] using hab
        simpa [color, ha, hb] using C.valid hab'
  exact W.not_colorable ⟨Coloring.mk color hvalid⟩

/-- The minimum degree of a critical witness is at least `n`. -/
theorem minDegree_ge {n : ℕ} (W : Witness G n) :
    n ≤ (H G W).minDegree := by
  classical
  letI : Nonempty (Carrier G W) := witness_nonempty (G := G) W
  exact (H G W).le_minDegree_of_forall_le_degree n (degree_ge (G := G) W)

/-- A critical witness is connected. -/
theorem connected {n : ℕ} (W : Witness G n) : (H G W).Connected := by
  classical
  by_contra hnot
  letI : Nonempty (Carrier G W) := witness_nonempty (G := G) W
  have hcomponents : ∀ c : (H G W).ConnectedComponent,
      c.toSimpleGraph.Colorable n := by
    intro c
    have hc : c.supp ≠ Set.univ := by
      intro hc
      apply hnot
      refine ⟨?_⟩
      intro a b
      exact c.reachable_of_mem_supp (by simp [hc]) (by simp [hc])
    exact W.colorable_proper c.supp hc
  exact W.not_colorable
    ((SimpleGraph.colorable_iff_forall_connectedComponent (G := H G W)).mpr hcomponents)

/-- Deleting any vertex from a positive-color critical witness leaves a
connected graph.  The proof normalizes the color assigned to the deleted
vertex separately on every component and then glues those colorings. -/
theorem deleteVertex_connected {n : ℕ} (hn : 0 < n) (W : Witness G n)
    (v : Carrier G W) : (deleteVertex (H G W) v).Connected := by
  classical
  let J : SimpleGraph (Carrier G W) := H G W
  let D : SimpleGraph {w : Carrier G W // w ≠ v} := deleteVertex J v
  have hvdeg : 0 < J.degree v := hn.trans_le (degree_ge (G := G) W v)
  have hneigh : J.neighborSet v |>.Nonempty :=
    SimpleGraph.degree_pos_iff_nonempty.mp hvdeg
  obtain ⟨w, hvw⟩ := hneigh
  letI : Nonempty {w : Carrier G W // w ≠ v} :=
    ⟨⟨w, (J.ne_of_adj hvw).symm⟩⟩
  refine ⟨?_⟩
  by_contra hD
  let piece : D.ConnectedComponent → Set (Carrier G W) := fun c ↦
    {v} ∪ Subtype.val '' c.supp
  have hpiece (c : D.ConnectedComponent) : piece c ≠ Set.univ := by
    have hc : c.supp ≠ Set.univ := by
      intro hc
      apply hD
      intro a b
      exact c.reachable_of_mem_supp (by simp [hc]) (by simp [hc])
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem c.supp).mp hc
    intro hp
    have hxp : x.1 ∈ piece c := Set.eq_univ_iff_forall.mp hp x.1
    rcases hxp with hxv | ⟨y, hy, hyx⟩
    · exact x.2 hxv
    · apply hx
      have hxy : y = x := Subtype.ext hyx
      simpa [hxy] using hy
  let raw (c : D.ConnectedComponent) :
      (J.induce (piece c)).Coloring (Fin n) :=
    (W.colorable_proper (piece c) (hpiece c)).some
  let zero : Fin n := ⟨0, hn⟩
  have hvpiece (c : D.ConnectedComponent) : v ∈ piece c := Or.inl rfl
  let root (c : D.ConnectedComponent) : {x : Carrier G W // x ∈ piece c} :=
    ⟨v, hvpiece c⟩
  let component (x : Carrier G W) (hx : x ≠ v) : D.ConnectedComponent :=
    D.connectedComponentMk ⟨x, hx⟩
  have hnode (x : Carrier G W) (hx : x ≠ v) : x ∈ piece (component x hx) := by
    right
    exact ⟨⟨x, hx⟩, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
  let node (x : Carrier G W) (hx : x ≠ v) :
      {y : Carrier G W // y ∈ piece (component x hx)} :=
    ⟨x, hnode x hx⟩
  let perm (c : D.ConnectedComponent) : Equiv.Perm (Fin n) :=
    Equiv.swap (raw c (root c)) zero
  let color : Carrier G W → Fin n := fun x ↦
    if hx : x = v then zero
    else perm (component x hx) (raw (component x hx) (node x hx))
  have hvalid : ∀ {a b : Carrier G W}, J.Adj a b → color a ≠ color b := by
    intro a b hab
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := (J.ne_of_adj hab).symm
      simp only [color, dif_pos rfl, dif_neg hb]
      intro heq
      have hadj : (J.induce (piece (component b hb))).Adj
          (root (component b hb)) (node b hb) := by
        exact hab
      apply (raw (component b hb)).valid hadj
      apply (perm (component b hb)).injective
      rw [show perm (component b hb) (raw (component b hb) (root (component b hb))) =
          zero by exact Equiv.swap_apply_left _ _]
      exact heq
    · by_cases hb : b = v
      · subst b
        have hav : (H G W).Adj v a := hab.symm
        have ha' : a ≠ v := ha
        simp only [color, dif_neg ha', dif_pos rfl]
        intro heq
        have hadj : (J.induce (piece (component a ha'))).Adj
            (root (component a ha')) (node a ha') := by
          exact hav
        apply (raw (component a ha')).valid hadj
        apply (perm (component a ha')).injective
        rw [show perm (component a ha') (raw (component a ha') (root (component a ha'))) =
            zero by exact Equiv.swap_apply_left _ _]
        exact heq.symm
      · simp only [color, dif_neg ha, dif_neg hb]
        have habD : D.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
          exact hab
        have hc : component a ha = component b hb :=
          SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj habD
        let b' : {y : Carrier G W // y ∈ piece (component a ha)} :=
          hc.symm ▸ node b hb
        have hb' : b'.1 = b := by
          exact coe_cast_subtype piece hc (node b hb)
        have hab' : (J.induce (piece (component a ha))).Adj (node a ha) b' := by
          change J.Adj a b'.1
          simpa [hb'] using hab
        have hne :
            perm (component a ha) (raw (component a ha) (node a ha)) ≠
              perm (component a ha) (raw (component a ha) b') := by
          apply (perm (component a ha)).injective.ne
          exact (raw (component a ha)).valid hab'
        have htransport :
            perm (component a ha) (raw (component a ha) b') =
              perm (component b hb) (raw (component b hb) (node b hb)) := by
          exact apply_cast_subtype piece
            (fun c x ↦ perm c (raw c x)) hc (node b hb)
        intro heq
        exact hne (heq.trans htransport.symm)
  exact W.not_colorable ⟨Coloring.mk color hvalid⟩

/-- A positive-color critical witness is two-connected in the
vertex-deletion sense. -/
theorem twoConnected {n : ℕ} (hn : 0 < n) (W : Witness G n) :
    TwoConnected (H G W) :=
  ⟨connected (G := G) W, deleteVertex_connected (G := G) hn W⟩

/-- Clean critical-subgraph reduction: a finite graph which is not
`n`-colorable, for `n > 0`, contains an induced two-connected subgraph of
minimum degree at least `n`. -/
theorem exists_induced_twoConnected_minDegree_ge {n : ℕ} (hn : 0 < n)
    (hG : ¬G.Colorable n) :
    ∃ (S : Finset V),
      let J := G.induce {v : V | v ∈ S}
      TwoConnected J ∧ n ≤ J.minDegree := by
  classical
  obtain ⟨W⟩ := exists_witness (G := G) hG
  exact ⟨W.S, twoConnected (G := G) hn W, minDegree_ge (G := G) W⟩

end Erdos58.CriticalAlt
