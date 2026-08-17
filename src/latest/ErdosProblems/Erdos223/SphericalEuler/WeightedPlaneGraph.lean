import ErdosProblems.Erdos223.SphericalEuler.FiniteFaceSplit
import ErdosProblems.Erdos223.SphericalEuler.EarCounts
import ErdosProblems.Erdos223.SphericalEuler.BipartitePlaneGraph
import ErdosProblems.Erdos223.SphericalEuler.TwoRegionCrosscut

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A finite list of the actual faces of a plane graph, carrying boundary-cycle lengths and
the exact Euler/perimeter identities. -/
structure WeightedFaces (G : Graph Plane β) (drawing : β → ℝ → Plane) where
  support : Set Plane
  vertices : ℕ
  edges : ℕ
  faces : PlaneFace.Decomposition.WeightedDecomposition support vertices edges
  support_eq : support = exterior G drawing
  vertices_eq : vertices = V(G).ncard
  edges_eq : edges = E(G).ncard
  cells_nonempty : faces.cells.Nonempty
  boundaryCycle : ∀ U ∈ faces.cells,
    ∃ z ∈ U, ∃ (e : β) (u v : Plane) (D : List β),
      IsFaceCycle G drawing z e u v D ∧ faces.perimeter U = (e :: D).length

namespace WeightedFaces

/-- Each token in `WeightedFaces` is literally the connected-component face of any point it
contains. -/
theorem cell_eq_face (W : WeightedFaces G drawing) {U : Set Plane}
    (hU : U ∈ W.faces.cells) {z : Plane} (hz : z ∈ U) :
    U = face G drawing z := by
  rw [face, ← W.support_eq]
  exact W.faces.toDecomposition.cell_eq_connectedComponentIn hU hz

/-- The initial cycle in the relative-ear decomposition has its two Jordan regions as its two
weighted faces. -/
noncomputable def ofCycle (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    {e : β} {u v : Plane} {D : List β} (hc : G.IsCycleThrough e u v D) :
    WeightedFaces (G.cycleGraph u e D) drawing := by
  let C := edgesCover drawing (e :: D)
  let k := (e :: D).length
  have hsep : IsSeparating C := h.cycle_isSeparating hpoly hc
  have hext : exterior (G.cycleGraph u e D) drawing = Cᶜ := by
    simp only [exterior, C]
    rw [h.pointSet_cycleGraph hc]
  have hV : V(G.cycleGraph u e D).ncard = k := hc.ncard_vertexSet_cycleGraph
  have hE : E(G.cycleGraph u e D).ncard = k := hc.ncard_edgeSet_cycleGraph
  let F := PlaneFace.Decomposition.WeightedDecomposition.ofSeparatingCycle C k hsep
  refine ⟨Cᶜ, k, k, F, hext.symm, hV.symm, hE.symm, ?_, ?_⟩
  · exact ⟨inside C, by
      simp [F, PlaneFace.Decomposition.WeightedDecomposition.ofSeparatingCycle]⟩
  intro U hU
  obtain ⟨z, hz⟩ := F.nonempty U hU
  refine ⟨z, hz, e, u, v, D, ?_, ?_⟩
  · refine ⟨?_, hsep, ?_⟩
    · exact ⟨hc.cycleGraph_isLink,
        hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
          rw [hc.cycleGraph_edgeSet]
          exact List.mem_append_left _ hg,
        hc.notMem⟩
    · change IsRegionOf C (face (G.cycleGraph u e D) drawing z)
      rw [face, hext, ← F.toDecomposition.cell_eq_connectedComponentIn hU hz]
      have hmem : U = inside C ∨ U = outside C := by
        simpa only [F, PlaneFace.Decomposition.WeightedDecomposition.ofSeparatingCycle,
          Finset.mem_insert, Finset.mem_singleton] using hU
      exact Or.elim hmem
        (fun hI => Or.inl hI)
        (fun hO => Or.inr hO)
  · change F.perimeter U = k
    have hmem : U = inside C ∨ U = outside C := by
      simpa only [F, PlaneFace.Decomposition.WeightedDecomposition.ofSeparatingCycle,
        Finset.mem_insert, Finset.mem_singleton] using hU
    rcases hmem with rfl | rfl <;>
      simp [F, PlaneFace.Decomposition.WeightedDecomposition.ofSeparatingCycle]

#print axioms Graph.WeightedFaces.ofCycle

/-- The finite induction step once the geometric ear has been identified as splitting one
current face.  Unlike the pointwise `HasFaceCycles` interface, this theorem preserves the
finite face list, Euler's identity, and the total boundary-length identity simultaneously. -/
noncomputable def addEarOfSplit
    (W : WeightedFaces B drawing) {B' : Graph Plane β}
    {P Ω U V : Set Plane} {a₀ b₀ t : ℕ}
    (hΩ : Ω ∈ W.faces.cells) (hPS : P ∩ W.support ⊆ Ω)
    (hUV : Ω \ P = U ∪ V) (hU : U.Nonempty) (hV : V.Nonempty)
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUconn : IsPreconnected U) (hVconn : IsPreconnected V)
    (hdis : Disjoint U V) (hperim : W.faces.perimeter Ω = a₀ + b₀)
    (hsupport : exterior B' drawing = W.support \ P)
    (hvertices : V(B').ncard = W.vertices + t)
    (hedges : E(B').ncard = (W.edges + 1) + t)
    (childU : ∃ z ∈ U, ∃ (e : β) (u v : Plane) (D : List β),
      IsFaceCycle B' drawing z e u v D ∧ (e :: D).length = a₀ + (t + 1))
    (childV : ∃ z ∈ V, ∃ (e : β) (u v : Plane) (D : List β),
      IsFaceCycle B' drawing z e u v D ∧ (e :: D).length = b₀ + (t + 1))
    (survive : ∀ T, T ∈ W.faces.cells → T ≠ Ω →
      ∃ z ∈ T, ∃ (e : β) (u v : Plane) (D : List β),
        IsFaceCycle B' drawing z e u v D ∧ W.faces.perimeter T = (e :: D).length) :
    WeightedFaces B' drawing := by
  classical
  let F := W.faces.splitEar hΩ hPS hUV hU hV hUopen hVopen hUconn hVconn hdis hperim t
  refine ⟨W.support \ P, W.vertices + t, (W.edges + 1) + t, F,
    hsupport.symm, hvertices.symm, hedges.symm, ?_, ?_⟩
  · exact ⟨U, by
      simp [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
        PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
        PlaneFace.Decomposition.WeightedDecomposition.split,
        PlaneFace.Decomposition.split]⟩
  intro T hT
  have hUneV : U ≠ V := by
    intro heq
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1 hdis hx (heq ▸ hx)
  have hUsub : U ⊆ Ω := by
    intro x hx
    exact (show x ∈ Ω \ P by rw [hUV]; exact Or.inl hx).1
  have hVsub : V ⊆ Ω := by
    intro x hx
    exact (show x ∈ Ω \ P by rw [hUV]; exact Or.inr hx).1
  have hU_notmem : U ∉ W.faces.cells.erase Ω := by
    intro hmem
    have hUD := Finset.mem_of_mem_erase hmem
    have hUneΩ := Finset.ne_of_mem_erase hmem
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1
      (W.faces.pairwise_disjoint (by simpa using hUD) (by simpa using hΩ) hUneΩ)
      hx (hUsub hx)
  have hV_notmem : V ∉ W.faces.cells.erase Ω := by
    intro hmem
    have hVD := Finset.mem_of_mem_erase hmem
    have hVneΩ := Finset.ne_of_mem_erase hmem
    obtain ⟨x, hx⟩ := hV
    exact Set.disjoint_left.1
      (W.faces.pairwise_disjoint (by simpa using hVD) (by simpa using hΩ) hVneΩ)
      hx (hVsub hx)
  have hTcases : T = U ∨ T = V ∨ T ∈ W.faces.cells.erase Ω := by
    simpa only [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
      PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
      PlaneFace.Decomposition.WeightedDecomposition.split,
      PlaneFace.Decomposition.split, Finset.mem_insert] using hT
  rcases hTcases with rfl | rfl | hTold
  · obtain ⟨z, hz, e, u, v, D, hcyc, hlen⟩ := childU
    refine ⟨z, hz, e, u, v, D, hcyc, ?_⟩
    simp only [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
      PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
      PlaneFace.Decomposition.WeightedDecomposition.split]
    simp [hUneV]
    simp only [List.length_cons] at hlen ⊢
    omega
  · obtain ⟨z, hz, e, u, v, D, hcyc, hlen⟩ := childV
    refine ⟨z, hz, e, u, v, D, hcyc, ?_⟩
    simp only [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
      PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
      PlaneFace.Decomposition.WeightedDecomposition.split]
    simp [Ne.symm hUneV]
    simp only [List.length_cons] at hlen ⊢
    omega
  · have hTD : T ∈ W.faces.cells := Finset.mem_of_mem_erase hTold
    have hTne : T ≠ Ω := Finset.ne_of_mem_erase hTold
    obtain ⟨z, hz, e, u, v, D, hcyc, hlen⟩ := survive T hTD hTne
    refine ⟨z, hz, e, u, v, D, hcyc, ?_⟩
    have hTneU : T ≠ U := fun heq => hU_notmem (heq ▸ hTold)
    have hTneV : T ≠ V := fun heq => hV_notmem (heq ▸ hTold)
    simp only [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
      PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
      PlaneFace.Decomposition.WeightedDecomposition.split]
    simp [hTneU, hTneV, hlen]

#print axioms Graph.WeightedFaces.addEarOfSplit

/-- One relative ear of a polygonal plane drawing constructs the full weighted finite face
decomposition of the enlarged graph.  The two new tokens are supplied by
`crosscut_two_regions`, which works uniformly for a bounded or the unbounded old face. -/
theorem addEar [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (W : WeightedFaces B drawing)
    {a b : Plane} {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    Nonempty (WeightedFaces (B.union (G.pathGraphOf a D')) drawing) := by
  classical
  haveI : B.Finite := Finite.of_le hBG
  let B' := B.union (G.pathGraphOf a D')
  let P := edgesCover drawing D'
  have hne : D' ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a D' ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B' ≤ G := union_le hBG hPG
  have hBB' : B ≤ B' := left_le_union _ _
  have hB : IsDrawing B drawing := h.mono hBG
  have hB'draw : IsDrawing B' drawing := h.mono hB'G
  have hpoly' : ∀ g ∈ E(B'), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hB'G.edgeSet_mono hg)
  have hParc : IsArcBetween P a b := h.path_isArcBetween hpath hne
  have hPpoly : IsPolygonal P := h.isPolygonal_edgesCover hpoly hpath.isWalk hne
  have hext : exterior B' drawing = exterior B drawing \ P := by
    dsimp [B', P]
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  have hz₀S : z₀ ∈ W.support := W.support_eq.symm ▸ hz₀
  obtain ⟨Ω, hΩ, hz₀Ω⟩ := W.faces.toDecomposition.mem_cover.mp hz₀S
  have hΩface : Ω = face B drawing z₀ := W.cell_eq_face hΩ hz₀Ω
  have hPinter : P ∩ W.support ⊆ Ω := by
    intro x hx
    rw [hΩface]
    have hxext : x ∈ exterior B drawing := W.support_eq ▸ hx.2
    by_cases hxab : x ∈ ({a, b} : Set Plane)
    · exfalso
      rcases hxab with rfl | rfl
      · exact hxext (vertexSet_subset_pointSet ha)
      · exact hxext (vertexSet_subset_pointSet hb)
    · exact hsub₀ ⟨hx.1, hxab⟩
  obtain ⟨zΩ, hzΩ, e, u, v, D, hface, hweight⟩ := W.boundaryCycle Ω hΩ
  have hzΩext : zΩ ∈ exterior B drawing := W.support_eq ▸ W.faces.mem_cover.mpr ⟨Ω, hΩ, hzΩ⟩
  have hΩfacez : Ω = face B drawing zΩ := W.cell_eq_face hΩ hzΩ
  have hopenΩ : IsOpen Ω := W.faces.isOpen Ω hΩ
  have hsubΩ : P \ {a, b} ⊆ Ω := by rw [hΩface]; exact hsub₀
  obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face
    (hΩfacez ▸ hopenΩ) hpath hab ha hb (by rw [← hΩfacez]; exact hsubΩ)
  have hfr : frontier (face B drawing zΩ) = edgesCover drawing (e :: D) := hface.frontier_eq
  have haW : a ∈ B.walkVertices u D :=
    hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
  have hbW : b ∈ B.walkVertices u D :=
    hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
  obtain ⟨D₁, D₂, hD1, hD2, hperm, hmeet⟩ := hface.isCycle.split_at haW hbW hab
  have hnodup : (e :: D).Nodup := List.nodup_cons.2
    ⟨hface.isCycle.notMem, hface.isCycle.isPath.nodup⟩
  have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
    (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
  obtain ⟨harc₁, harc₂, hinter⟩ := hB.arcs_of_split hD1 hD2 hab hdisj hmeet
  have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ =
      edgesCover drawing (e :: D) := by
    rw [← edgesCover_append, edgesCover_perm hperm]
  have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
    edgesCover_subset_pointSet fun g hg => by
      rcases List.mem_cons.1 hg with rfl | hg'
      exacts [hface.isCycle.isLink.edge_mem, hface.isCycle.isPath.edge_mem hg']
  have hmeetJ : P ∩ edgesCover drawing (e :: D) = {a, b} := by
    refine Set.Subset.antisymm (fun w hw =>
      h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
    rintro w (rfl | rfl)
    exacts [⟨hParc.left_mem, hfr ▸ haF⟩, ⟨hParc.right_mem, hfr ▸ hbF⟩]
  have hpolyB : ∀ g ∈ E(B), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hBG.edgeSet_mono hg)
  have hD1poly : IsPolygonal (edgesCover drawing D₁) :=
    hB.isPolygonal_edgesCover hpolyB hD1.isWalk (hD1.ne_nil hab)
  have hD2poly : IsPolygonal (edgesCover drawing D₂) :=
    hB.isPolygonal_edgesCover hpolyB hD2.isWalk (hD2.ne_nil hab.symm)
  have hmeetP : ∀ (A : Set Plane), A ⊆ edgesCover drawing (e :: D) →
      ∀ w ∈ A, w ∈ P → w = a ∨ w = b := by
    intro A hAJ w hwA hwP
    have hw : w ∈ ({a, b} : Set Plane) := by
      rw [← hmeetJ]
      exact ⟨hwP, hAJ hwA⟩
    simpa using hw
  have hD1sub : edgesCover drawing D₁ ⊆ edgesCover drawing (e :: D) := by
    rw [← hunion]
    exact Set.subset_union_left
  have hD2sub : edgesCover drawing D₂ ⊆ edgesCover drawing (e :: D) := by
    rw [← hunion]
    exact Set.subset_union_right
  have hJ1sep : IsSeparating (edgesCover drawing D₁ ∪ P) :=
    isSeparating_of_isJordanCurve
      (isJordanCurve_union harc₁ hParc (hmeetP _ hD1sub))
      (hD1poly.union hPpoly ⟨a, harc₁.left_mem, hParc.left_mem⟩)
  have hJ2sep : IsSeparating (edgesCover drawing D₂ ∪ P) :=
    isSeparating_of_isJordanCurve
      (isJordanCurve_union harc₂.reverse hParc (hmeetP _ hD2sub))
      (hD2poly.union hPpoly ⟨a, harc₂.right_mem, hParc.left_mem⟩)
  have hΩreg : IsRegionOf (edgesCover drawing (e :: D)) Ω := by
    rw [hΩfacez]
    exact hface.isRegionOf
  have hPsub : P \ {a, b} ⊆ Ω := hsubΩ
  obtain ⟨U, V₀, hUV, hUVdis, hUne, hVne, hUopen, hVopen,
      hUconn, hVconn, hregions⟩ :=
    crosscut_two_regions hface.isSeparating hJ1sep hJ2sep
      (h.isPolygonal_edgesCover hpoly (hface.isCycle.isWalk_cons.mono hBG)
        (List.cons_ne_nil _ _)) hPpoly harc₁ harc₂.reverse hunion hinter hParc hmeetJ hΩreg hPsub
  let t := D'.length - 1
  have hlen : 1 ≤ D'.length := Nat.one_le_iff_ne_zero.mpr fun hzero =>
    hne (List.length_eq_zero_iff.mp hzero)
  have hVcount₀ := hpath.ncard_vertexSet_union_pathGraphOf hab ha hb hint
  have hEcount₀ := hpath.ncard_edgeSet_union_pathGraphOf hnew
  have hVcount : V(B').ncard = W.vertices + t := by
    dsimp only [B', t]
    rw [W.vertices_eq]
    exact hVcount₀
  have hEcount : E(B').ncard = (W.edges + 1) + t := by
    dsimp only [B', t]
    rw [W.edges_eq]
    rw [hEcount₀]
    omega
  have hsupport : exterior B' drawing = W.support \ P := by
    rw [hext, W.support_eq]
  have hperim : W.faces.perimeter Ω = D₁.length + D₂.length := by
    rw [hweight]
    have hp := hperm.length_eq
    simp only [List.length_cons, List.length_append] at hp ⊢
    omega
  let F := W.faces.splitEar hΩ hPinter hUV hUne hVne hUopen hVopen hUconn hVconn
    hUVdis hperim t
  have hUmem : U ∈ F.cells := by
    simp [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
      PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
      PlaneFace.Decomposition.WeightedDecomposition.split, PlaneFace.Decomposition.split]
  have hVmem : V₀ ∈ F.cells := by
    simp [F, PlaneFace.Decomposition.WeightedDecomposition.splitEar,
      PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces,
      PlaneFace.Decomposition.WeightedDecomposition.split, PlaneFace.Decomposition.split]
  have child₁ {X : Set Plane} (hXmem : X ∈ F.cells)
      (hreg : IsRegionOf (edgesCover drawing D₁ ∪ P) X) :
      ∃ z ∈ X, ∃ (f : β) (x y : Plane) (T : List β),
        IsFaceCycle B' drawing z f x y T ∧
          (f :: T).length = D₁.length + (t + 1) := by
    obtain ⟨f, x, y, T, hcyc, hpermT⟩ :=
      exists_spliced_cycle hBG hD1 hpath hab hnew hint
    have hsep := hB'draw.cycle_isSeparating hpoly' hcyc
    have hcov : edgesCover drawing (f :: T) = edgesCover drawing D₁ ∪ P := by
      dsimp only [P]
      rw [edgesCover_perm hpermT, edgesCover_append]
    have hreg' : IsRegionOf (edgesCover drawing (f :: T)) X := by
      rw [hcov]
      exact hreg
    obtain ⟨z, hz⟩ := (hreg'.isConnected hsep).nonempty
    have hfaceX : face B' drawing z = X := by
      rw [face, hsupport]
      exact (F.toDecomposition.cell_eq_connectedComponentIn hXmem hz).symm
    refine ⟨z, hz, f, x, y, T, ⟨hcyc, hsep, ?_⟩, ?_⟩
    · rw [hfaceX]
      exact hreg'
    · have hp := hpermT.length_eq
      simp only [List.length_cons, List.length_append, t] at hp ⊢
      omega
  have child₂ {X : Set Plane} (hXmem : X ∈ F.cells)
      (hreg : IsRegionOf (edgesCover drawing D₂ ∪ P) X) :
      ∃ z ∈ X, ∃ (f : β) (x y : Plane) (T : List β),
        IsFaceCycle B' drawing z f x y T ∧
          (f :: T).length = D₂.length + (t + 1) := by
    obtain ⟨f, x, y, T, hcyc, hpermT⟩ :=
      exists_spliced_cycle hBG hD2.reverse hpath hab hnew hint
    have hsep := hB'draw.cycle_isSeparating hpoly' hcyc
    have hcov : edgesCover drawing (f :: T) = edgesCover drawing D₂ ∪ P := by
      dsimp only [P]
      rw [edgesCover_perm hpermT, edgesCover_append, edgesCover_reverse]
    have hreg' : IsRegionOf (edgesCover drawing (f :: T)) X := by
      rw [hcov]
      exact hreg
    obtain ⟨z, hz⟩ := (hreg'.isConnected hsep).nonempty
    have hfaceX : face B' drawing z = X := by
      rw [face, hsupport]
      exact (F.toDecomposition.cell_eq_connectedComponentIn hXmem hz).symm
    refine ⟨z, hz, f, x, y, T, ⟨hcyc, hsep, ?_⟩, ?_⟩
    · rw [hfaceX]
      exact hreg'
    · have hp := hpermT.length_eq
      simp only [List.length_cons, List.length_append, List.length_reverse, t] at hp ⊢
      omega
  have survive : ∀ T, T ∈ W.faces.cells → T ≠ Ω →
      ∃ z ∈ T, ∃ (f : β) (x y : Plane) (L : List β),
        IsFaceCycle B' drawing z f x y L ∧ W.faces.perimeter T = (f :: L).length := by
    intro T hT hTΩ
    obtain ⟨z, hz, f, x, y, L, hfc, hwt⟩ := W.boundaryCycle T hT
    have hzext : z ∈ exterior B drawing := W.support_eq ▸ W.faces.mem_cover.mpr ⟨T, hT, hz⟩
    have hdisTP : Disjoint T (pointSet (G.pathGraphOf a D') drawing) := by
      rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
      intro w hwT hwP
      have hwS : w ∈ W.support := W.faces.mem_cover.mpr ⟨T, hT, hwT⟩
      have hwΩ : w ∈ Ω := hPinter ⟨hwP, hwS⟩
      exact Set.disjoint_left.1 (W.faces.pairwise_disjoint
        (by simpa using hT) (by simpa using hΩ) hTΩ) hwT hwΩ
    have hdisFace : Disjoint (face B drawing z)
        (pointSet (G.pathGraphOf a D') drawing) := by
      rw [← W.cell_eq_face hT hz]
      exact hdisTP
    refine ⟨z, hz, f, x, y, L,
      hfc.mono hBB' (face_union_eq_of_disjoint hzext hdisFace), hwt⟩
  rcases hregions with hreg | hreg
  · exact ⟨W.addEarOfSplit hΩ hPinter hUV hUne hVne hUopen hVopen hUconn hVconn
      hUVdis hperim hsupport hVcount hEcount (child₁ hUmem hreg.1)
        (child₂ hVmem hreg.2) survive⟩
  · have hVU : Ω \ P = V₀ ∪ U := by rw [hUV, union_comm]
    exact ⟨W.addEarOfSplit hΩ hPinter hVU hVne hUne hVopen hUopen hVconn hUconn
      hUVdis.symm hperim hsupport hVcount hEcount (child₁ hVmem hreg.1)
        (child₂ hUmem hreg.2) survive⟩

#print axioms Graph.WeightedFaces.addEar

/-- The weighted construction immediately gives the sharp bipartite plane edge inequality,
because every boundary token is an actual simple even cycle. -/
theorem edge_add_four_le_two_vertices [G.Simple]
    (W : WeightedFaces G drawing) {c : Plane → Bool} (hc : G.IsBicoloring c) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  have hfour : ∀ U ∈ W.faces.cells, 4 ≤ W.faces.perimeter U := by
    intro U hU
    obtain ⟨z, hz, e, u, v, D, hface, hlen⟩ := W.boundaryCycle U hU
    rw [hlen]
    exact hface.isCycle.four_le_length hc
  have hbound := W.faces.edge_add_four_le_two_vertices W.cells_nonempty hfour
  rwa [W.edges_eq, W.vertices_eq] at hbound

theorem edge_add_four_le_two_vertices_of_isBipartite [G.Simple]
    (W : WeightedFaces G drawing) (hbi : G.toSimpleGraph.IsBipartite) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨c, hc⟩ := exists_isBicoloring_of_toSimpleGraph_isBipartite hbi
  exact W.edge_add_four_le_two_vertices hc

#print axioms Graph.WeightedFaces.edge_add_four_le_two_vertices_of_isBipartite

end WeightedFaces
end Graph
