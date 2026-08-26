-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.DecompForward

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sub-systems on a subset of edges

For the reconstruction step of the finite bridge decomposition we need to split
a finite triple system along its edges.  Given a finite triple system `F` and a
set `S` of its edges, `FTS.restrict F S` is the sub-triple-system with edge set
`S` and vertex set the vertices incident to some edge of `S`.

This file develops `FTS.restrict` and the reconstruction isomorphisms:

* a partition of the edges into two parts with no shared vertex gives a disjoint
  union;
* a partition whose only shared vertex is a single glue point gives a one-point
  amalgamation.
-/

open Cardinal

namespace Erdos1177

open Classical

universe u

/-- The intrinsic conditions together with the absence of isolated vertices;
this is the predicate maintained by the reconstruction induction. -/
def ReconOK (F : FTS) : Prop :=
  F.Linear ∧ (∀ x : F.V, ¬ F.Isolated x) ∧
  (∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed) ∧
  (∀ c : BergeCycle F, Even c.m)

/-- The sub-triple-system on a set `S` of edges of `F`: vertices are those
incident to some edge of `S`. -/
noncomputable def FTS.restrict (F : FTS) (S : Finset {e : Finset F.V // e ∈ F.edges}) : FTS where
  V := {v : F.V // ∃ e ∈ S, v ∈ e.1}
  finV := Fintype.ofFinite _
  decV := Subtype.instDecidableEq
  edges := S.attach.image (fun e =>
    Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1.1)
  card3 := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hs
    obtain ⟨e, rfl⟩ := hs
    rw [Finset.card_subtype]
    have hfil : e.1.1.filter (fun v => ∃ e' ∈ S, v ∈ e'.1) = e.1.1 := by
      apply Finset.filter_true_of_mem
      intro v hv
      exact ⟨e.1, e.2, hv⟩
    rw [hfil]
    exact F.card3 e.1.1 e.1.2

/-
Membership of an edge of `F.restrict S`.
-/
theorem FTS.mem_restrict_edges {F : FTS} {S : Finset {e : Finset F.V // e ∈ F.edges}}
    {s : Finset (F.restrict S).V} :
    s ∈ (F.restrict S).edges ↔
      ∃ e ∈ S, s = Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1 := by
  simp [FTS.restrict, Finset.mem_image, Finset.mem_attach];
  grind

/-
The number of edges of `F.restrict S` is `S.card`.
-/
theorem FTS.restrict_edges_card {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges}) :
    (F.restrict S).edges.card = S.card := by
  rw [ FTS.restrict, Finset.card_image_of_injOn ];
  · exact Finset.card_attach;
  · intro e₁ he₁ e₂ he₂ h_eq; simp_all +decide [ Finset.ext_iff ] ;
    grind +suggestions

/-
Restriction is linear when `F` is.
-/
theorem FTS.restrict_linear {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hlin : F.Linear) : (F.restrict S).Linear := by
  intro s₁ hs₁ s₂ hs₂ hne;
  convert! hlin _ _ _ _ _;
  rotate_left;
  exact s₁.map ( Function.Embedding.subtype fun v => ∃ e' ∈ S, v ∈ e'.1 );
  rotate_left;
  exact s₂.map ( Function.Embedding.subtype fun v => ∃ e' ∈ S, v ∈ e'.1 );
  · obtain ⟨ e, he, rfl ⟩ := FTS.mem_restrict_edges.mp hs₂;
    grind +suggestions;
  · exact fun h => hne <| Finset.map_injective ( Function.Embedding.subtype _ ) h;
  · rw [ ← Finset.map_inter ];
    rw [ Finset.card_map ];
  · obtain ⟨ e₁, he₁, rfl ⟩ := FTS.mem_restrict_edges.mp hs₁;
    convert! e₁.2 using 1;
    ext; simp [Finset.mem_map, Finset.mem_subtype];
    exact fun h => ⟨ e₁.1, ⟨ e₁.2, he₁ ⟩, h ⟩

/-
Restriction has no isolated vertices (its vertices are incident by
construction).
-/
theorem FTS.restrict_no_isolated {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (v : (F.restrict S).V) : ¬ (F.restrict S).Isolated v := by
  have h_isolated : ¬(F.restrict S).Isolated v := by
    -- v.2 : ∃ e ∈ S, v.1 ∈ e.1; take s := Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1.
    obtain ⟨e, heS, hev⟩ := v.2
    let s := Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1
    -- s ∈ (F.restrict S).edges by FTS.mem_restrict_edges (witness e ∈ S)
    have hs : s ∈ (F.restrict S).edges := by
      exact FTS.mem_restrict_edges.mpr ⟨ e, heS, rfl ⟩
    -- s ≤ v.1, so v ∈ s (Finset.mem_subtype)
    have hv_s : v ∈ s := by
      exact Finset.mem_subtype.mpr ( by aesop )
    -- unfold FTS.Isolated and use hs,hv_s
    -- FTS.Isolated G v := ∀ e ∈ G.edges, v ∉ e
    unfold FTS.Isolated
    push_neg
    exact ⟨s, hs, hv_s⟩;
  grind

/-
The subtype-inclusion image of a `restrict`-edge is an `F`-edge (in fact one
of `S`).
-/
theorem FTS.restrict_edge_map_mem {F : FTS} {S : Finset {e : Finset F.V // e ∈ F.edges}}
    {d : Finset (F.restrict S).V} (hd : d ∈ (F.restrict S).edges) :
    d.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) ∈ F.edges := by
  obtain ⟨ e, heS, rfl ⟩ := FTS.mem_restrict_edges.mp hd;
  grind +suggestions

/-- Transport a Berge cycle of a restriction up to `F` (same length). -/
noncomputable def BergeCycle.ofRestrict {F : FTS}
    {S : Finset {e : Finset F.V // e ∈ F.edges}} (c : BergeCycle (F.restrict S)) :
    BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) (c.v i)
  e := fun i => ⟨(c.e i).1.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)),
    FTS.restrict_edge_map_mem (c.e i).2⟩
  vinj := fun i j h => c.vinj ((Function.Embedding.subtype _).injective h)
  einj := by
    intro i j h
    apply c.einj
    have h2 : (c.e i).1.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) =
        (c.e j).1.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) := by
      simpa using! congrArg Subtype.val h
    exact Subtype.ext (Finset.map_injective _ h2)
  mem_left := fun i => Finset.mem_map_of_mem _ (c.mem_left i)
  mem_right := fun i => Finset.mem_map_of_mem _ (c.mem_right i)

/-- Restriction has only even Berge cycles when `F` does. -/
theorem FTS.restrict_even {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hev : ∀ c : BergeCycle F, Even c.m) (c : BergeCycle (F.restrict S)) : Even c.m :=
  hev (BergeCycle.ofRestrict c)

/-
Each hyperedge-node of a restriction is incident with a bridge, when `F` is
bridge-incident.
-/
theorem FTS.restrict_bridge {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (ed : {e : Finset (F.restrict S).V // e ∈ (F.restrict S).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.restrict S) w ed := by
  obtain ⟨ e, heS, he ⟩ := FTS.mem_restrict_edges.mp ed.2;
  obtain ⟨ w, hw₁, hw₂ ⟩ := hbr e;
  refine' ⟨ ⟨ w, ⟨ e, heS, hw₁ ⟩ ⟩, _, _ ⟩ <;> simp_all +decide [ IsBridgeInc ];
  · exact Finset.mem_subtype.mpr ( by aesop );
  · refine' ⟨ Finset.mem_subtype.mpr ( by aesop ), _ ⟩;
    rintro ⟨ c, i, hi, h ⟩;
    refine' hw₂ ⟨ BergeCycle.ofRestrict c, i, _, _ ⟩ <;> simp_all +decide [ BergeCycle.ofRestrict ];
    · ext; aesop;
    · exact Or.imp ( fun h => by simpa using! congr_arg Subtype.val h ) ( fun h => by simpa using! congr_arg Subtype.val h ) h

/-- The restriction of a `ReconOK`-input system is `ReconOK`. -/
theorem FTS.restrict_reconOK {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hlin : F.Linear)
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (hev : ∀ c : BergeCycle F, Even c.m) : ReconOK (F.restrict S) :=
  ⟨FTS.restrict_linear S hlin, FTS.restrict_no_isolated S,
    FTS.restrict_bridge S hbr, FTS.restrict_even S hev⟩

end Erdos1177
