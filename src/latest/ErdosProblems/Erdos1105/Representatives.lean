import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- Extend an edge coloring to all unordered pairs, with `none` on nonedges.
This is only a proof device; `antiRamseyNum` never counts these extra values. -/
noncomputable def extendColor {V C : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → C) (e : Sym2 V) : Option C := by
  classical
  exact if h : e ∈ G.edgeSet then some (c ⟨e, h⟩) else none

@[simp] lemma extendColor_edge {V C : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → C) (e : G.edgeSet) : extendColor c e = some (c e) := by
  simp [extendColor, e.property]

/-- Choose exactly one edge of every used color. -/
theorem exists_representative {V C : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → C) (hc : Function.Surjective c) :
    ∃ R : SimpleGraph V, R ≤ G ∧
      Set.InjOn (extendColor c) R.edgeSet ∧
      ∃ e : C ≃ R.edgeSet, ∀ i, extendColor c (e i) = some i := by
  classical
  choose pick hpick using hc
  let R := SimpleGraph.fromEdgeSet (Set.range fun i ↦ (pick i).val)
  have hR : R.edgeSet = Set.range (fun i ↦ (pick i).val) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    constructor
    · exact fun hx ↦ hx.1
    · rintro ⟨i, rfl⟩
      exact ⟨Set.mem_range_self i, G.not_isDiag_of_mem_edgeSet (pick i).property⟩
  have hRG : R ≤ G := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hR]
    rintro _ ⟨i, rfl⟩
    exact (pick i).property
  have hval : ∀ i, extendColor c (pick i).val = some i := by
    intro i
    rw [extendColor_edge, hpick]
  have hinj : Function.Injective (fun i ↦ (pick i).val) := by
    intro i j hij
    have := congrArg (extendColor c) hij
    simpa only [hval, Option.some.injEq] using this
  refine ⟨R, hRG, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hR] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hij : i = j := by simpa only [hval, Option.some.injEq] using hxy
    exact congrArg (fun i ↦ (pick i).val) hij
  · let f : C → R.edgeSet := fun i ↦ ⟨(pick i).val, hR ▸ Set.mem_range_self i⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro i j hij
        exact hinj (congrArg (fun x : R.edgeSet ↦ x.val) hij)
      · intro x
        have hx : x.val ∈ Set.range (fun i ↦ (pick i).val) := by
          rw [← hR]
          exact x.property
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩
    exact ⟨Equiv.ofBijective f hbij, hval⟩

/-- A copy in a subgraph whose edges have distinct colors is a rainbow copy
in the ambient graph. -/
lemma isRainbow_comp_of_color_injOn {α V C : Type*}
    {H : SimpleGraph α} {R G : SimpleGraph V} (hRG : R ≤ G)
    (c : G.edgeSet → C) (hr : Set.InjOn (extendColor c) R.edgeSet)
    (f : H.Copy R) : IsRainbow ((Copy.ofLE R G hRG).comp f) c := by
  let cr : R.edgeSet → C := fun e ↦ c ⟨e.val, edgeSet_mono hRG e.property⟩
  have hcr : Function.Injective cr := by
    intro x y hxy
    apply Subtype.ext
    apply hr x.property y.property
    rw [show extendColor c x.val = some (cr x) from
      extendColor_edge c ⟨x.val, edgeSet_mono hRG x.property⟩,
      show extendColor c y.val = some (cr y) from
      extendColor_edge c ⟨y.val, edgeSet_mono hRG y.property⟩]
    exact congrArg some hxy
  exact hcr.comp f.mapEdgeSet.injective

lemma representative_free {α V C : Type*} {H : SimpleGraph α}
    {R G : SimpleGraph V} (hRG : R ≤ G)
    (c : G.edgeSet → C) (hr : Set.InjOn (extendColor c) R.edgeSet)
    (hc : ∀ f : H.Copy G, ¬IsRainbow f c) : H.Free R := by
  rintro ⟨f⟩
  exact hc _ (isRainbow_comp_of_color_injOn hRG c hr f)

/-- Any ordinary extremal edge bound also bounds the number of colors. -/
theorem antiRamseyNum_le_of_free_bound {α : Type*} [Fintype α]
    {H : SimpleGraph α} {n b : ℕ}
    (hb : ∀ R : SimpleGraph (Fin n), H.Free R → Nat.card R.edgeSet ≤ b) :
    antiRamseyNum H n ≤ b := by
  classical
  apply antiRamseyNum_le
  intro q c hc hH
  obtain ⟨R, hRG, hr, e, _⟩ := exists_representative c hc
  have hcard : Nat.card R.edgeSet = q := by
    rw [Nat.card_eq_fintype_card]
    simpa using Fintype.card_congr e.symm
  rw [← hcard]
  exact hb R (representative_free hRG c hr hH)

/-- Transporting a trail through a rainbow copy gives a list of distinct colors. -/
lemma IsRainbow.nodup_colors {α V C : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    {f : H.Copy G} {c : G.edgeSet → C} (hc : IsRainbow f c)
    {u v : α} (p : H.Walk u v) (hp : p.IsTrail) :
    ((p.map f.toHom).edges.map (extendColor c)).Nodup := by
  rw [Walk.edges_map, List.map_map]
  apply hp.edges_nodup.map_on
  intro e he d hd hed
  have heH := p.edges_subset_edgeSet he
  have hdH := p.edges_subset_edgeSet hd
  have heq : c (f.mapEdgeSet ⟨e, heH⟩) = c (f.mapEdgeSet ⟨d, hdH⟩) := by
    apply Option.some.inj
    rw [← extendColor_edge c (f.mapEdgeSet ⟨e, heH⟩),
      ← extendColor_edge c (f.mapEdgeSet ⟨d, hdH⟩)]
    exact hed
  exact congrArg Subtype.val (hc heq)

end Erdos1105
