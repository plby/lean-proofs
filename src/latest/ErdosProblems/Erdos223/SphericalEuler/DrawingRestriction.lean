import ErdosProblems.Erdos223.SphericalEuler.PlaneDrawing

open Set Schoenflies
open scoped Graph

namespace Graph

variable {V W : Type*} {G : SimpleGraph V}
  (f : W ↪ V) (pos : V → Plane)
  (drawing : Sym2 V → ℝ → Plane)

noncomputable def comapDrawing (e : Sym2 W) : ℝ → Plane :=
  drawing (Sym2.map f e)

lemma map_sym2_injective : Function.Injective (Sym2.map f) := by
  intro e q heq
  induction e using Sym2.inductionOn with
  | _ a b =>
      induction q using Sym2.inductionOn with
      | _ c d =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at heq ⊢
          rcases heq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
          · exact Or.inl ⟨f.injective hac, f.injective hbd⟩
          · exact Or.inr ⟨f.injective had, f.injective hbc⟩

lemma sym2_map_mem_edgeSet_iff (e : Sym2 W) :
    Sym2.map f e ∈ G.edgeSet ↔ e ∈ (G.comap f).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ u v => simp [SimpleGraph.mem_edgeSet]

lemma ofSimpleGraph_comap_map_isLink_iff
    (e : Sym2 W) (x y : Plane) :
    ((ofSimpleGraph (G.comap f)).map (pos ∘ f)).IsLink e x y ↔
      ((ofSimpleGraph G).map pos).IsLink (Sym2.map f e) x y := by
  simp only [map_isLink]
  constructor
  · rintro ⟨u, v, ⟨rfl, he⟩, hu, hv⟩
    refine ⟨f u, f v, ⟨?_, ?_⟩, hu, hv⟩
    · simp
    · simpa [SimpleGraph.mem_edgeSet] using he
  · rintro ⟨u', v', ⟨heq, he⟩, hu, hv⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
        simp only [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
        · have hau' : pos (f a) = x := by simpa [hau] using hu
          have hbv' : pos (f b) = y := by simpa [hbv] using hv
          refine ⟨a, b, ⟨rfl, ?_⟩, hau', hbv'⟩
          simpa [SimpleGraph.mem_edgeSet, hau, hbv] using he
        · have hav' : pos (f a) = y := by simpa [hav] using hv
          have hbu' : pos (f b) = x := by simpa [hbu] using hu
          refine ⟨b, a, ⟨Sym2.eq_swap, ?_⟩, hbu', hav'⟩
          simpa [SimpleGraph.mem_edgeSet, hav, hbu] using he

theorem IsDrawing.comap
    (h : IsDrawing ((ofSimpleGraph G).map pos) drawing) :
    IsDrawing ((ofSimpleGraph (G.comap f)).map (pos ∘ f))
      (comapDrawing f drawing) := by
  constructor
  · intro e he
    have he' : Sym2.map f e ∈ G.edgeSet :=
      (sym2_map_mem_edgeSet_iff f e).2 he
    obtain ⟨hc, hi, hl⟩ := h.edge_param he'
    exact ⟨hc, hi, (ofSimpleGraph_comap_map_isLink_iff f pos e _ _).2 hl⟩
  · intro e x y v hl hv hve
    change v ∈ (pos ∘ f) '' Set.univ at hv
    obtain ⟨w, -, rfl⟩ := hv
    have hl' := (ofSimpleGraph_comap_map_isLink_iff f pos e x y).1 hl
    have hv' : pos (f w) ∈ V((ofSimpleGraph G).map pos) := by
      simp
    have hve' : pos (f w) ∈ edgeArc drawing (Sym2.map f e) := hve
    rcases h.vertex_mem_edgeArc hl' hv' hve' with hwx | hwy
    · left
      exact hwx
    · right
      exact hwy
  · intro e q he hq heq p hpe hpq
    have he' : Sym2.map f e ∈ G.edgeSet :=
      (sym2_map_mem_edgeSet_iff f e).2 he
    have hq' : Sym2.map f q ∈ G.edgeSet :=
      (sym2_map_mem_edgeSet_iff f q).2 hq
    have hneq : Sym2.map f e ≠ Sym2.map f q := fun hmap ↦
      heq (map_sym2_injective f hmap)
    obtain ⟨hpV, hpeInc, hpqInc⟩ := h.edge_inter he' hq' hneq hpe hpq
    have hpeInc' : ((ofSimpleGraph (G.comap f)).map (pos ∘ f)).Inc e p := by
      obtain ⟨y, hlink⟩ := hpeInc
      exact ⟨y, (ofSimpleGraph_comap_map_isLink_iff f pos e p y).2 hlink⟩
    have hpqInc' : ((ofSimpleGraph (G.comap f)).map (pos ∘ f)).Inc q p := by
      obtain ⟨y, hlink⟩ := hpqInc
      exact ⟨y, (ofSimpleGraph_comap_map_isLink_iff f pos q p y).2 hlink⟩
    exact ⟨hpeInc'.vertex_mem, hpeInc', hpqInc'⟩

end Graph

