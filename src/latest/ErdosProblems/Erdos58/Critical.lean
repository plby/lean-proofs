/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite vertex-critical induced subgraphs

This file supplies the generic critical-subgraph reduction used in the proof of
Erdős Problem 58.  A `Witness G n` is an inclusion-minimal finite set of
vertices whose induced graph is not `n`-colorable.  We prove the standard
consequences: deleting any vertex makes it `n`-colorable, every vertex has
degree at least `n`, the critical graph is connected, and (when `n > 0`) it
remains connected after deletion of any vertex.
-/

namespace Erdos58.Critical

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The canonical finite-type instance on the carrier of a finite vertex set. -/
abbrev instSub (S : Finset V) : Fintype {v : V // v ∈ S} :=
  Finset.Subtype.fintype S

/-- An inclusion-minimal induced subgraph which is not `n`-colorable. -/
structure Witness (n : ℕ) where
  S : Finset V
  not_colorable :
    ¬(G.induce (fun v : V => v ∈ S)).Colorable n
  colorable_of_ssubset :
    ∀ {T : Finset V}, T ⊂ S →
      (G.induce (fun v : V => v ∈ T)).Colorable n

/-- Vertex type carried by a witness. -/
abbrev Carrier {n : ℕ} (W : Witness G n) := {v : V // v ∈ W.S}

/-- The induced graph carried by a critical witness. -/
abbrev H {n : ℕ} (W : Witness G n) : SimpleGraph (Carrier G W) :=
  G.induce (fun v : V => v ∈ W.S)

/-- Deleting a vertex, expressed on the usual subtype carrier. -/
abbrev deleteVertex {X : Type*} (J : SimpleGraph X) (v : X) :
    SimpleGraph {w : X // w ≠ v} :=
  J.induce (fun w => w ≠ v)

/-- The local vertex-two-connected interface needed by the cycle argument. -/
def VertexTwoConnected {X : Type*} (J : SimpleGraph X) : Prop :=
  J.Connected ∧ ∀ v : X, (deleteVertex J v).Connected

/-- A finite non-`n`-colorable graph has an inclusion-minimal non-`n`-colorable
induced subgraph. -/
theorem exists_witness {n : ℕ} (hG : ¬G.Colorable n) :
    Nonempty (Witness G n) := by
  classical
  let bad : Finset V → Prop :=
    fun S => ¬(G.induce (fun v : V => v ∈ S)).Colorable n
  have hbad_univ : bad (Finset.univ : Finset V) := by
    intro hcol
    rcases hcol with ⟨C⟩
    apply hG
    refine ⟨SimpleGraph.Coloring.mk (fun v => C ⟨v, Finset.mem_univ v⟩) ?_⟩
    intro a b hab
    apply C.valid
    simpa [SimpleGraph.induce_adj] using hab
  let cand : Finset (Finset V) :=
    (Finset.univ : Finset V).powerset.filter bad
  have hnonempty : cand.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨?_, hbad_univ⟩⟩
    simp
  let S : Finset V :=
    Classical.choose (Finset.exists_min_image cand (fun T => T.card) hnonempty)
  have hS_spec :=
    Classical.choose_spec (Finset.exists_min_image cand (fun T => T.card) hnonempty)
  have hS_bad : bad S := (Finset.mem_filter.mp hS_spec.1).2
  have hminimal :
      ∀ {T : Finset V}, T ⊂ S →
        (G.induce (fun v : V => v ∈ T)).Colorable n := by
    intro T hTS
    by_contra hTbad
    have hTmem : T ∈ cand := by
      refine Finset.mem_filter.mpr ⟨?_, hTbad⟩
      exact Finset.mem_powerset.mpr (Finset.subset_univ T)
    have hle : S.card ≤ T.card := hS_spec.2 T hTmem
    exact (not_lt_of_ge hle) (Finset.card_lt_card hTS)
  exact ⟨{
    S := S
    not_colorable := hS_bad
    colorable_of_ssubset := hminimal
  }⟩

/-- Every one-vertex deletion of a critical witness is `n`-colorable. -/
theorem colorable_delete {n : ℕ} (W : Witness G n) (v : Carrier G W) :
    (deleteVertex (H G W) v).Colorable n := by
  classical
  have hcol := W.colorable_of_ssubset (Finset.erase_ssubset v.property)
  rcases hcol with ⟨C⟩
  refine ⟨SimpleGraph.Coloring.mk (fun w =>
    C ⟨w.1.1, Finset.mem_erase.mpr ⟨?_, w.1.property⟩⟩) ?_⟩
  · intro h
    apply w.property
    apply Subtype.ext
    exact h
  · intro a b hab
    apply C.valid
    simpa [deleteVertex, H, SimpleGraph.induce_adj] using hab

/-- In a critical witness every vertex has degree at least the forbidden number
of colors. -/
theorem degree_ge {n : ℕ} (W : Witness G n) (v : Carrier G W) :
    n ≤ (H G W).degree v := by
  classical
  by_contra hdeg
  have hcol := colorable_delete (G := G) W v
  rcases hcol with ⟨C⟩
  let neigh : Finset (Carrier G W) := (H G W).neighborFinset v
  let colors : Finset (Fin n) :=
    neigh.attach.image (fun w => C ⟨w.1, by
      have hadj : (H G W).Adj v w.1 :=
        (SimpleGraph.mem_neighborFinset (G := H G W) (v := v) (w := w.1)).mp w.2
      exact (H G W).ne_of_adj hadj |>.symm⟩)
  have hcolors_lt : colors.card < (Finset.univ : Finset (Fin n)).card := by
    have hcard_le : colors.card ≤ neigh.card := by
      calc
        colors.card ≤ neigh.attach.card := Finset.card_image_le
        _ = neigh.card := Finset.card_attach
    have hneigh_lt : neigh.card < n := by
      simpa [neigh, SimpleGraph.card_neighborFinset_eq_degree] using
        (Nat.lt_of_not_ge hdeg)
    simpa using hcard_le.trans_lt hneigh_lt
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcolors_lt
  let color : Carrier G W → Fin n := fun w =>
    if h : w = v then c else C ⟨w, h⟩
  have hvalid : ∀ {a b : Carrier G W}, (H G W).Adj a b → color a ≠ color b := by
    intro a b hab
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := (H G W).ne_of_adj hab |>.symm
      have hbmem : b ∈ neigh := by
        exact (SimpleGraph.mem_neighborFinset (G := H G W) (v := v) (w := b)).mpr hab
      have hbcolor : color b ∈ colors := by
        refine Finset.mem_image.mpr ⟨⟨b, hbmem⟩, by simp, ?_⟩
        simp [color, hb]
      intro heq
      apply hc
      have hbc : color b = c := by
        simpa [color, hb] using heq.symm
      simpa [hbc] using hbcolor
    · by_cases hb : b = v
      · subst b
        have hamem : a ∈ neigh := by
          exact (SimpleGraph.mem_neighborFinset (G := H G W) (v := v) (w := a)).mpr hab.symm
        have hacolor : color a ∈ colors := by
          refine Finset.mem_image.mpr ⟨⟨a, hamem⟩, by simp, ?_⟩
          simp [color, ha]
        intro heq
        apply hc
        have hac : color a = c := by
          simpa [color, ha] using heq
        simpa [hac] using hacolor
      · have hdel : (deleteVertex (H G W) v).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
          simpa [deleteVertex, SimpleGraph.induce_adj] using hab
        simpa [color, ha, hb] using C.valid hdel
  exact W.not_colorable ⟨SimpleGraph.Coloring.mk color hvalid⟩

/-- The critical induced graph is connected. -/
theorem connected {n : ℕ} (W : Witness G n) : (H G W).Connected := by
  classical
  letI : Fintype (Carrier G W) := instSub W.S
  by_contra hnot
  have hnonempty : Nonempty (Carrier G W) := by
    by_contra hempty
    letI : IsEmpty (Carrier G W) := ⟨fun x => hempty ⟨x⟩⟩
    exact W.not_colorable
      (SimpleGraph.Colorable.of_isEmpty (G := H G W) n)
  have hcol_component :
      ∀ c : (H G W).ConnectedComponent, c.toSimpleGraph.Colorable n := by
    intro c
    have hne : (c.supp : Set (Carrier G W)) ≠ Set.univ := by
      intro hsupp
      apply hnot
      refine ⟨?_⟩
      intro a b
      exact c.reachable_of_mem_supp (by simp [hsupp]) (by simp [hsupp])
    obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem c.supp).mp hne
    let T : Finset V := c.supp.toFinset.image Subtype.val
    have hTsub : T ⊆ W.S := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact y.property
    have hTne : T ≠ W.S := by
      intro hT
      have hwT : w.1 ∈ T := by simp [hT]
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hwT
      have hy' : y ∈ c.supp := by simpa using hy
      have : y = w := Subtype.ext (by simpa using hyv)
      exact hw (this ▸ hy')
    have hcolT := W.colorable_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, hTne⟩)
    rcases hcolT with ⟨C⟩
    refine ⟨SimpleGraph.Coloring.mk (fun u => C ⟨u.1.1, ?_⟩) ?_⟩
    · refine Finset.mem_image.mpr ⟨u.1, ?_, rfl⟩
      simp
    · intro a b hab
      apply C.valid
      have habH : (H G W).Adj a.1 b.1 :=
        (SimpleGraph.ConnectedComponent.toSimpleGraph_adj c a.property b.property).mp hab
      simpa [H, SimpleGraph.induce_adj] using habH
  exact W.not_colorable
    ((SimpleGraph.colorable_iff_forall_connectedComponent (G := H G W) (n := n)).mpr
      hcol_component)

/-- A coloring-pasting lemma for a vertex separator.  The vertices other than
`v` are divided by `P`; the cross-edge hypothesis says that distinct sides do
not see each other.  The colorings of the two sides can be permuted to agree at
`v`, and hence paste to a coloring of the whole graph. -/
theorem colorable_of_cut_partition {X : Type*} {J : SimpleGraph X} {n : ℕ}
    (v : X) (P : X → Prop)
    (hcross : ∀ {a b : X}, a ≠ v → b ≠ v → P a → ¬P b → ¬J.Adj a b)
    (hleft : (J.induce (fun x => x = v ∨ P x)).Colorable n)
    (hright : (J.induce (fun x => x = v ∨ ¬P x)).Colorable n) :
    J.Colorable n := by
  classical
  rcases hleft with ⟨CL⟩
  rcases hright with ⟨CR⟩
  let vvL : {x : X // x = v ∨ P x} := ⟨v, Or.inl rfl⟩
  let vvR : {x : X // x = v ∨ ¬P x} := ⟨v, Or.inl rfl⟩
  let cL : Fin n := CL vvL
  let cR : Fin n := CR vvR
  let perm : Fin n ≃ Fin n :=
    if h : cR = cL then Equiv.refl _ else Equiv.swap cR cL
  have hperm : perm cR = cL := by
    by_cases h : cR = cL
    · simp [perm, h]
    · simp [perm, h, Equiv.swap_apply_left]
  let CR' : (J.induce (fun x => x = v ∨ ¬P x)).Coloring (Fin n) :=
    (SimpleGraph.recolorOfEquiv
      (G := J.induce (fun x => x = v ∨ ¬P x)) perm) CR
  have hCRv : CR' vvR = cL := by
    simpa [CR', SimpleGraph.coe_recolorOfEquiv, cR] using hperm
  let color : X → Fin n := fun x =>
    if hx : x = v then cL
    else if hP : P x then CL ⟨x, Or.inr hP⟩
    else CR' ⟨x, Or.inr hP⟩
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro a b hab
  have habne : a ≠ b := J.ne_of_adj hab
  by_cases ha : a = v
  · have hb : b ≠ v := by
      intro hb
      exact habne (ha.trans hb.symm)
    by_cases hPb : P b
    · have hadj :
          (J.induce (fun x => x = v ∨ P x)).Adj vvL ⟨b, Or.inr hPb⟩ := by
        simpa [vvL, SimpleGraph.induce_adj, ha] using hab
      have hne := CL.valid hadj
      simpa [color, ha, hb, hPb, cL, vvL] using hne
    · have hadj :
          (J.induce (fun x => x = v ∨ ¬P x)).Adj vvR ⟨b, Or.inr hPb⟩ := by
        simpa [vvR, SimpleGraph.induce_adj, ha] using hab
      have hne := CR'.valid hadj
      intro heq
      apply hne
      calc
        CR' vvR = cL := hCRv
        _ = color a := by simp [color, ha]
        _ = color b := heq
        _ = CR' ⟨b, Or.inr hPb⟩ := by simp [color, hb, hPb]
  · by_cases hb : b = v
    · by_cases hPa : P a
      · have hadj :
            (J.induce (fun x => x = v ∨ P x)).Adj ⟨a, Or.inr hPa⟩ vvL := by
          simpa [vvL, SimpleGraph.induce_adj, hb] using hab
        have hne := CL.valid hadj
        simpa [color, ha, hb, hPa, cL, vvL] using hne
      · have hadj :
            (J.induce (fun x => x = v ∨ ¬P x)).Adj ⟨a, Or.inr hPa⟩ vvR := by
          simpa [vvR, SimpleGraph.induce_adj, hb] using hab
        have hne := CR'.valid hadj
        intro heq
        apply hne
        calc
          CR' ⟨a, Or.inr hPa⟩ = color a := by simp [color, ha, hPa]
          _ = color b := heq
          _ = cL := by simp [color, hb]
          _ = CR' vvR := hCRv.symm
    · by_cases hPa : P a
      · by_cases hPb : P b
        · have hadj :
              (J.induce (fun x => x = v ∨ P x)).Adj
                ⟨a, Or.inr hPa⟩ ⟨b, Or.inr hPb⟩ := by
            simpa [SimpleGraph.induce_adj] using hab
          simpa [color, ha, hb, hPa, hPb] using CL.valid hadj
        · exact (hcross ha hb hPa hPb hab).elim
      · by_cases hPb : P b
        · exact (hcross hb ha hPb hPa hab.symm).elim
        · have hadj :
              (J.induce (fun x => x = v ∨ ¬P x)).Adj
                ⟨a, Or.inr hPa⟩ ⟨b, Or.inr hPb⟩ := by
            simpa [SimpleGraph.induce_adj] using hab
          simpa [color, ha, hb, hPa, hPb] using CR'.valid hadj

/-- Every proper induced subgraph of a minimal witness is `n`-colorable.  This
predicate form is more convenient than the stored finset form. -/
theorem colorable_induce_of_exists_not {n : ℕ} (W : Witness G n)
    (P : Carrier G W → Prop) (hproper : ∃ w, ¬P w) :
    ((H G W).induce P).Colorable n := by
  classical
  let T : Finset V := W.S.filter (fun x => ∃ hx : x ∈ W.S, P ⟨x, hx⟩)
  have hTsub : T ⊆ W.S := Finset.filter_subset _ _
  obtain ⟨w, hw⟩ := hproper
  have hwT : w.1 ∉ T := by
    intro h
    obtain ⟨hx, hPx⟩ := (Finset.mem_filter.mp h).2
    exact hw (by simpa using hPx)
  have hTne : T ≠ W.S := by
    intro h
    apply hwT
    rw [h]
    exact w.property
  have hcol := W.colorable_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, hTne⟩)
  rcases hcol with ⟨C⟩
  refine ⟨SimpleGraph.Coloring.mk (fun x => C ⟨x.1.1, ?_⟩) ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨x.1.property, ⟨x.1.property, x.property⟩⟩
  · intro a b hab
    apply C.valid
    simpa [H, SimpleGraph.induce_adj] using hab

/-- A finite minimal non-`n`-colorable induced subgraph is vertex-two-connected
as soon as `n` is positive. -/
theorem vertexTwoConnected {n : ℕ} (hn : 0 < n) (W : Witness G n) :
    VertexTwoConnected (H G W) := by
  classical
  refine ⟨connected (G := G) W, ?_⟩
  intro v
  let J : SimpleGraph {w : Carrier G W // w ≠ v} := deleteVertex (H G W) v
  have hJnonempty : Nonempty {w : Carrier G W // w ≠ v} := by
    have hdegpos : 0 < (H G W).degree v := hn.trans_le (degree_ge (G := G) W v)
    have hneighbors : ((H G W).neighborFinset v).Nonempty := by
      apply Finset.card_pos.mp
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegpos
    obtain ⟨w, hw⟩ := hneighbors
    have hadj : (H G W).Adj v w :=
      (SimpleGraph.mem_neighborFinset (G := H G W) (v := v) (w := w)).mp hw
    exact ⟨⟨w, (H G W).ne_of_adj hadj |>.symm⟩⟩
  by_contra hnot
  have hno_center : ¬∃ a, ∀ b, J.Reachable a b := by
    intro h
    exact hnot ((SimpleGraph.connected_iff_exists_forall_reachable (G := J)).mpr h)
  have hfar : ∀ a, ∃ b, ¬J.Reachable a b := by
    simpa [not_exists] using hno_center
  let a0 : {w : Carrier G W // w ≠ v} := Classical.choice hJnonempty
  obtain ⟨b0, hab0⟩ := hfar a0
  let c : J.ConnectedComponent := J.connectedComponentMk a0
  let P : Carrier G W → Prop := fun x =>
    ∃ hx : x ≠ v, J.connectedComponentMk ⟨x, hx⟩ = c
  have hPa0 : P a0.1 := by
    refine ⟨a0.property, ?_⟩
    rfl
  have hPb0 : ¬P b0.1 := by
    rintro ⟨hb0, heq⟩
    have heq' : J.connectedComponentMk a0 = J.connectedComponentMk b0 := by
      simpa [c] using heq.symm
    exact hab0 ((SimpleGraph.ConnectedComponent.eq (G := J)).mp heq')
  have hcross :
      ∀ {a b : Carrier G W}, a ≠ v → b ≠ v → P a → ¬P b →
        ¬(H G W).Adj a b := by
    intro a b ha hb hPa hPb hadj
    apply hPb
    obtain ⟨ha', hca⟩ := hPa
    refine ⟨hb, ?_⟩
    have hadjJ : J.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
      simpa [J, deleteVertex, SimpleGraph.induce_adj] using hadj
    have hcomp :
        J.connectedComponentMk ⟨a, ha⟩ = J.connectedComponentMk ⟨b, hb⟩ :=
      (SimpleGraph.ConnectedComponent.eq (G := J)).mpr
        (SimpleGraph.Adj.reachable (G := J) hadjJ)
    calc
      J.connectedComponentMk ⟨b, hb⟩ = J.connectedComponentMk ⟨a, ha⟩ := hcomp.symm
      _ = J.connectedComponentMk ⟨a, ha'⟩ := by congr
      _ = c := hca
  have hleft :
      ((H G W).induce (fun x => x = v ∨ P x)).Colorable n := by
    apply colorable_induce_of_exists_not (G := G) W
    refine ⟨b0.1, ?_⟩
    simp only [not_or]
    exact ⟨b0.property, hPb0⟩
  have hright :
      ((H G W).induce (fun x => x = v ∨ ¬P x)).Colorable n := by
    apply colorable_induce_of_exists_not (G := G) W
    refine ⟨a0.1, ?_⟩
    simp only [not_or, not_not]
    exact ⟨a0.property, hPa0⟩
  exact W.not_colorable
    (colorable_of_cut_partition v P hcross hleft hright)

/-- Bundled critical-subgraph reduction. -/
theorem exists_vertexTwoConnected_witness {n : ℕ} (hn : 0 < n)
    (hG : ¬G.Colorable n) :
    ∃ W : Witness G n,
      (∀ v : Carrier G W, n ≤ (H G W).degree v) ∧
      VertexTwoConnected (H G W) := by
  obtain ⟨W⟩ := exists_witness (G := G) hG
  exact ⟨W, degree_ge (G := G) W, vertexTwoConnected (G := G) hn W⟩

/-- Chromatic-number form of the critical-subgraph reduction. -/
theorem exists_vertexTwoConnected_witness_of_succ_le_chromaticNumber {n : ℕ}
    (hn : 0 < n) (hχ : (n + 1 : ℕ∞) ≤ G.chromaticNumber) :
    ∃ W : Witness G n,
      (∀ v : Carrier G W, n ≤ (H G W).degree v) ∧
      VertexTwoConnected (H G W) := by
  apply exists_vertexTwoConnected_witness (G := G) hn
  intro hcol
  have hle : (n + 1 : ℕ∞) ≤ (n : ℕ∞) := hχ.trans hcol.chromaticNumber_le
  have hle' : n + 1 ≤ n := by exact_mod_cast hle
  omega

end Erdos58.Critical
