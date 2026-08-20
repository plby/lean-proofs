/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CircuitTwins
import ErdosProblems.Erdos916.ThreeTerminalPath
import ErdosProblems.Erdos916.ThreeTerminalCut
import ErdosProblems.Erdos916.Torso

/-!
# The three-terminal path density bound

A connected `(2,3)`-sparse graph with no simple path through three
prescribed distinct vertices has at most `2n-5` edges.  The proof below uses
the block/cut recursion; in particular it does not assert that one cut
vertex already separates all three terminals.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem hasThreeTerminalPath_swap_left {a b c : V} :
    HasThreeTerminalPath G a b c ↔ HasThreeTerminalPath G b a c := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
    refine ⟨x, y, ?_, ?_, hxy, p, hp, hb, ha, hc⟩
    · simpa [Finset.insert_comm] using hx
    · simpa [Finset.insert_comm] using hy
  · rintro ⟨x, y, hx, hy, hxy, p, hp, hb, ha, hc⟩
    refine ⟨x, y, ?_, ?_, hxy, p, hp, ha, hb, hc⟩
    · simpa [Finset.insert_comm] using hx
    · simpa [Finset.insert_comm] using hy

private theorem hasThreeTerminalPath_rotate {a b c : V} :
    HasThreeTerminalPath G a b c ↔ HasThreeTerminalPath G b c a := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
    refine ⟨x, y, ?_, ?_, hxy, p, hp, hb, hc, ha⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rintro ⟨x, y, hx, hy, hxy, p, hp, hb, hc, ha⟩
    refine ⟨x, y, ?_, ?_, hxy, p, hp, ha, hb, hc⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h

private theorem hasThreeTerminalPath_swap_right {a b c : V} :
    HasThreeTerminalPath G a b c ↔ HasThreeTerminalPath G a c b := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
    refine ⟨x, y, ?_, ?_, hxy, p, hp, ha, hc, hb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  · rintro ⟨x, y, hx, hy, hxy, p, hp, ha, hc, hb⟩
    refine ⟨x, y, ?_, ?_, hxy, p, hp, ha, hb, hc⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)

/-- A terminal path in an induced graph is an ambient terminal path. -/
private theorem HasThreeTerminalPath.map_induce {S : Set V} {a b c : S}
    (h : HasThreeTerminalPath (G.induce S) a b c) :
    HasThreeTerminalPath G a.1 b.1 c.1 := by
  rcases h with ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
  let inc : G.induce S →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := S)).toHom
  let q : G.Walk x.1 y.1 := p.map inc
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hx' : x.1 ∈ ({a.1, b.1, c.1} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hy' : y.1 ∈ ({a.1, b.1, c.1} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have ha' : a.1 ∈ q.support := by
    change a.1 ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hb' : b.1 ∈ q.support := by
    change b.1 ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hc' : c.1 ∈ q.support := by
    change c.1 ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  exact ⟨x.1, y.1, hx', hy', hxy', q, hq, ha', hb', hc'⟩

/-! ## Sparse cut arithmetic -/

/-- `(2,3)`-sparsity passes to an induced graph. -/
theorem Is23Sparse.induce {S : Set V} (hs : Is23Sparse G) :
    Is23Sparse (G.induce S) := by
  classical
  intro T hT
  let inc : S ↪ V := Function.Embedding.subtype _
  let U : Finset V := T.map inc
  have hcard : U.card = T.card := by simp [U]
  have hsU := hs U (by simpa [hcard] using hT)
  have hsets :
      ((fun w : S ↦ (w : V)) '' (T : Set S)) = (U : Set V) := by
    ext x
    simp [U, inc]
  let e₀ :
      {w : S // w ∈ (T : Set S)} ≃
        {x : V // x ∈ ((fun w : S ↦ (w : V)) '' (T : Set S))} :=
    Equiv.Set.image (fun w : S ↦ (w : V)) (T : Set S)
      Subtype.val_injective
  let e : {w : S // w ∈ (T : Set S)} ≃ {x : V // x ∈ (U : Set V)} :=
    e₀.trans (Equiv.setCongr hsets)
  let gi : (G.induce S).induce (T : Set S) ≃g G.induce (U : Set V) := by
    refine { toEquiv := e, map_rel_iff' := ?_ }
    intro x y
    simp only [SimpleGraph.induce_adj]
    rfl
  rw [gi.card_edgeFinset_eq]
  simpa only [hcard] using hsU

private theorem two_le_card_of_mem_ne {s : Finset V} {x y : V}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : 2 ≤ s.card := by
  have hsub : ({x, y} : Finset V) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hxy] at hcard
  exact hcard

/-- One genuine cut already improves the sparse bound from `2n-3` to
`2n-4`.  This is the numerical lemma used for a missing *rooted* path. -/
theorem edge_card_add_four_le_of_cut (hs : Is23Sparse G)
    {d : V} (hd : IsCutVertex G d) :
    G.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  classical
  obtain ⟨x, y, hxy⟩ := (isCutVertex_iff_exists_not_reachable G d).mp hd
  let K := (deleteVertex G d).connectedComponentMk x
  let P := CutDensity.piece G d K
  let R := CutDensity.remainder G d K
  have hxK : x.1 ∈ ComponentEndBlock.side (G := G) d K := by
    refine ⟨x.2, ?_⟩
    simp [K, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyNotK : y.1 ∉ ComponentEndBlock.side (G := G) d K := by
    rintro ⟨hyd, hyK⟩
    have hcomp : (deleteVertex G d).connectedComponentMk y = K := by
      simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hyK
    have hcomp' : (deleteVertex G d).connectedComponentMk x =
        (deleteVertex G d).connectedComponentMk y := by
      simpa [K] using hcomp.symm
    exact hxy (SimpleGraph.ConnectedComponent.exact hcomp')
  have hP2 : 2 ≤ P.card := by
    exact two_le_card_of_mem_ne
      (CutDensity.cut_mem_piece (G := G) d K)
      ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hxK))
      (fun h => x.2 h.symm)
  have hR2 : 2 ≤ R.card := by
    exact two_le_card_of_mem_ne
      (CutDensity.cut_mem_remainder (G := G) d K)
      ((CutDensity.mem_remainder_iff (G := G)).mpr hyNotK)
      (fun h => y.2 h.symm)
  have hsP := hs P hP2
  have hsR := hs R hR2
  have he := CutDensity.card_edges_piece_add_card_edges_remainder
    (G := G) d K
  have hv := CutDensity.card_piece_add_card_remainder (G := G) d K
  simp only [P, R, Fintype.card_coe] at hsP hsR he hv
  omega

/-! ## The rooted `2n-4` lemma -/

/-- A path from `r` to `b` which visits `a`. -/
def HasRootedThreePath (G : SimpleGraph V) (r a b : V) : Prop :=
  ∃ p : G.Walk r b, p.IsPath ∧ a ∈ p.support

/-- Failure of a rooted three-terminal path costs one unit beyond ordinary
`(2,3)`-sparsity. -/
theorem edge_card_add_four_le_of_not_rootedPath
    (hconn : G.Connected) (hs : Is23Sparse G)
    {r a b : V} (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    (hno : ¬ HasRootedThreePath G r a b) :
    G.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  classical
  by_cases hcut : ∃ d : V, IsCutVertex G d
  · obtain ⟨d, hd⟩ := hcut
    exact edge_card_add_four_le_of_cut hs hd
  · have hdelete : ∀ d : V,
        (G.induce fun w : V => w ≠ d).Connected := by
      intro d
      have hpre : (deleteVertex G d).Preconnected := by
        exact not_not.mp (not_exists.mp hcut d)
      have hne : Nonempty {w : V // w ≠ d} := by
        by_cases hdr : d = r
        · exact ⟨⟨a, by simpa [hdr] using hra.symm⟩⟩
        · exact ⟨⟨r, Ne.symm hdr⟩⟩
      letI : Nonempty {w : V // w ≠ d} := hne
      change (deleteVertex G d).Connected
      exact SimpleGraph.Connected.mk hpre
    obtain ⟨p, hp, hap⟩ :=
      exists_rooted_three_path (G := G) (r := r) (a := a) (b := b)
        hra hrb hab hconn hdelete
    exact False.elim (hno ⟨p, hp, hap⟩)

/-! ## Paths and components at a cut -/

/-- A path from a vertex of a component of `G-d` to `d`, staying in that
component apart from its endpoint. -/
private theorem exists_path_to_cut_in_component
    (hconn : G.Connected) (d : V)
    (K : (deleteVertex G d).ConnectedComponent) {x : V}
    (hx : x ∈ ComponentEndBlock.side (G := G) d K) :
    ∃ p : G.Walk x d, p.IsPath ∧
      ∀ z, z ∈ p.support →
        z = d ∨ z ∈ ComponentEndBlock.side (G := G) d K := by
  classical
  let S := ComponentEndBlock.verts (G := G) d K
  have hxS : x ∈ S := Set.mem_insert_iff.mpr (Or.inr hx)
  have hdS : d ∈ S := Set.mem_insert d _
  obtain ⟨q, hq⟩ :=
    ((ComponentEndBlock.verts_connected hconn K)
      ⟨x, hxS⟩ ⟨d, hdS⟩).exists_isPath
  let inc : G.induce S →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := S)).toHom
  let p : G.Walk x d := q.map inc
  refine ⟨p, hq.map Subtype.val_injective, ?_⟩
  intro z hz
  have hz' : z ∈ q.support.map inc := by
    change z ∈ (q.map inc).support at hz
    rw [Walk.support_map] at hz
    exact hz
  obtain ⟨w, -, hw⟩ := List.mem_map.mp hz'
  have hzS : z ∈ S := by
    have : (w : V) = z := by simpa [inc] using hw
    simpa [this] using w.2
  simpa only [S, ComponentEndBlock.verts, Set.mem_insert_iff] using hzS

private theorem component_side_disjoint {d : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L) :
    Disjoint (ComponentEndBlock.side (G := G) d K)
      (ComponentEndBlock.side (G := G) d L) := by
  rw [Set.disjoint_left]
  intro x hxK hxL
  obtain ⟨hxd, hxK'⟩ := hxK
  obtain ⟨hxd', hxL'⟩ := hxL
  have hK : (deleteVertex G d).connectedComponentMk ⟨x, hxd⟩ = K :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff K ⟨x, hxd⟩).mp hxK'
  have hL : (deleteVertex G d).connectedComponentMk ⟨x, hxd⟩ = L := by
    have hL' :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff L ⟨x, hxd'⟩).mp hxL'
    simpa using hL'
  exact hKL (hK.symm.trans hL)

/-- A rooted path in one component piece can be joined at the cut vertex to
a path from a different component.  The two supports meet only at the cut,
so the resulting walk is still a simple path. -/
private theorem hasThreeTerminalPath_of_rootedPath_in_component
    (hconn : G.Connected) {d x y z : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L)
    (hx : x ∈ ComponentEndBlock.side (G := G) d K)
    (hz : z ∈ ComponentEndBlock.side (G := G) d L)
    (q : G.Walk d z) (hq : q.IsPath) (hyq : y ∈ q.support)
    (hqside : ∀ w, w ∈ q.support →
      w = d ∨ w ∈ ComponentEndBlock.side (G := G) d L) :
    HasThreeTerminalPath G x y z := by
  obtain ⟨p, hp, hpside⟩ :=
    exists_path_to_cut_in_component hconn d K hx
  have hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = d := by
    intro w hwp hwq
    have hpCases := hpside w hwp
    have hqCases := hqside w hwq
    rcases hpCases with rfl | hwK
    · rfl
    · rcases hqCases with hwd | hwL
      · exact hwd
      · exact False.elim
          (Set.disjoint_left.mp (component_side_disjoint hKL) hwK hwL)
  have hr : (p.append q).IsPath :=
    Erdos916.Walk.IsPath.append_of_support_inter_eq_endpoint hp hq hinter
  refine ⟨x, z, by simp, by simp, ?_, p.append q, hr, ?_, ?_, ?_⟩
  · intro hxz
    subst z
    exact Set.disjoint_left.mp (component_side_disjoint hKL) hx hz
  · exact (p.append q).start_mem_support
  · exact Erdos916.Walk.mem_support_append_of_mem_right p q hyq
  · exact (p.append q).end_mem_support

/-- If one terminal lies in one component of `G-d` and the other two lie in
another, a rooted path through the latter component would give an ambient
three-terminal path. -/
private theorem not_rootedPath_component_piece_of_noThreePath
    (hconn : G.Connected) {d x y z : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L)
    (hx : x ∈ ComponentEndBlock.side (G := G) d K)
    (hy : y ∈ ComponentEndBlock.side (G := G) d L)
    (hz : z ∈ ComponentEndBlock.side (G := G) d L)
    (hyz : y ≠ z) (hno : ¬ HasThreeTerminalPath G x y z) :
    ¬ HasRootedThreePath
      (G.induce (CutDensity.piece G d L : Set V))
      ⟨d, CutDensity.cut_mem_piece (G := G) d L⟩
      ⟨y, (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hy)⟩
      ⟨z, (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hz)⟩ := by
  rintro ⟨q, hq, hyq⟩
  let inc : G.induce (CutDensity.piece G d L : Set V) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := (CutDensity.piece G d L : Set V))).toHom
  let qG : G.Walk d z := q.map inc
  have hqG : qG.IsPath := hq.map Subtype.val_injective
  have hyqG : y ∈ qG.support := by
    change y ∈ (q.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨_, hyq, rfl⟩
  have hqside : ∀ w, w ∈ qG.support →
      w = d ∨ w ∈ ComponentEndBlock.side (G := G) d L := by
    intro w hw
    have hw' : w ∈ q.support.map inc := by
      change w ∈ (q.map inc).support at hw
      rw [Walk.support_map] at hw
      exact hw
    obtain ⟨t, -, htw⟩ := List.mem_map.mp hw'
    have hwPiece : w ∈ CutDensity.piece G d L := by
      have : (t : V) = w := by simpa [inc] using htw
      rw [← this]
      exact t.2
    exact (CutDensity.mem_piece_iff (G := G)).mp hwPiece
  exact hno (hasThreeTerminalPath_of_rootedPath_in_component
    hconn hKL hx hz qG hqG hyqG hqside)

/-- If one terminal is in one component of `G-d` and the other two are in a
different component, the rooted `2n-4` estimate on the latter piece and the
ordinary sparse estimate on its complement give `2n-5`. -/
private theorem edge_card_add_five_le_of_component_pair
    (hconn : G.Connected) (hs : Is23Sparse G) {d x y z : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L)
    (hx : x ∈ ComponentEndBlock.side (G := G) d K)
    (hy : y ∈ ComponentEndBlock.side (G := G) d L)
    (hz : z ∈ ComponentEndBlock.side (G := G) d L)
    (hyz : y ≠ z) (hno : ¬ HasThreeTerminalPath G x y z) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  classical
  let P := CutDensity.piece G d L
  let R := CutDensity.remainder G d L
  let dP : {w : V // w ∈ (P : Set V)} :=
    ⟨d, CutDensity.cut_mem_piece (G := G) d L⟩
  let yP : {w : V // w ∈ (P : Set V)} :=
    ⟨y, (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hy)⟩
  let zP : {w : V // w ∈ (P : Set V)} :=
    ⟨z, (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hz)⟩
  have hdpy : dP ≠ yP := by
    intro h
    have : d = y := congrArg Subtype.val h
    subst y
    exact (ComponentEndBlock.cut_not_mem_side (G := G) d L) hy
  have hdpz : dP ≠ zP := by
    intro h
    have : d = z := congrArg Subtype.val h
    subst z
    exact (ComponentEndBlock.cut_not_mem_side (G := G) d L) hz
  have hypz : yP ≠ zP := fun h => hyz (congrArg Subtype.val h)
  have hconnP : (G.induce (P : Set V)).Connected :=
    CutDensity.piece_connected (G := G) hconn d L
  have hsP : Is23Sparse (G.induce (P : Set V)) := hs.induce
  have hnoP : ¬ HasRootedThreePath (G.induce (P : Set V)) dP yP zP := by
    simpa only [P, dP, yP, zP] using
      (not_rootedPath_component_piece_of_noThreePath
        hconn hKL hx hy hz hyz hno)
  have hboundP := edge_card_add_four_le_of_not_rootedPath
    hconnP hsP hdpy hdpz hypz hnoP
  have hcardP : Fintype.card {w : V // w ∈ (P : Set V)} = P.card := by
    simp
  rw [hcardP] at hboundP
  have hR2 : 2 ≤ R.card := by
    have hxNotL : x ∉ ComponentEndBlock.side (G := G) d L := by
      intro hxL
      exact
        Set.disjoint_left.mp (component_side_disjoint hKL) hx hxL
    have hdx : d ≠ x := by
      intro hdx
      have hxd := hdx.symm
      subst x
      exact (ComponentEndBlock.cut_not_mem_side (G := G) d K) hx
    exact two_le_card_of_mem_ne
      (CutDensity.cut_mem_remainder (G := G) d L)
      ((CutDensity.mem_remainder_iff (G := G)).mpr hxNotL) hdx
  have hsR := hs R hR2
  have he := CutDensity.card_edges_piece_add_card_edges_remainder
    (G := G) d L
  have hv := CutDensity.card_piece_add_card_remainder (G := G) d L
  simp only [P, R] at hboundP hsR he hv
  omega

/-- Reinsert the components outside a recursively treated cut piece. -/
private theorem edge_card_add_five_le_of_piece_bound
    (hs : Is23Sparse G) {d : V} (hd : IsCutVertex G d)
    (K : (deleteVertex G d).ConnectedComponent)
    (hpiece :
      (G.induce (CutDensity.piece G d K : Set V)).edgeFinset.card + 5 ≤
        2 * (CutDensity.piece G d K).card) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  classical
  let P := CutDensity.piece G d K
  let R := CutDensity.remainder G d K
  have hproper : P ≠ Finset.univ := CutDensity.piece_ne_univ (G := G) hd K
  obtain ⟨x, hxP⟩ : ∃ x : V, x ∉ P := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_of_forall h)
  have hxR : x ∈ R := by
    have hxSide : x ∉ ComponentEndBlock.side (G := G) d K := by
      intro hx
      exact hxP ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hx))
    exact (CutDensity.mem_remainder_iff (G := G)).mpr hxSide
  have hxd : x ≠ d := by
    intro h
    subst x
    exact hxP (CutDensity.cut_mem_piece (G := G) d K)
  have hR2 : 2 ≤ R.card := by
    exact two_le_card_of_mem_ne
      (CutDensity.cut_mem_remainder (G := G) d K) hxR (Ne.symm hxd)
  have hsR := hs R hR2
  have he := CutDensity.card_edges_piece_add_card_edges_remainder
    (G := G) d K
  have hv := CutDensity.card_piece_add_card_remainder (G := G) d K
  simp only [P, R, Fintype.card_coe] at hpiece hsR he hv
  omega

/-! ## The recursive three-terminal theorem -/

/-- A connected `(2,3)`-sparse graph with no simple path containing three
specified distinct terminals has at most `2n-5` edges. -/
theorem edge_card_add_five_le_of_no_threeTerminalPath
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hs : Is23Sparse G)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ HasThreeTerminalPath G a b c) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      subst n
      by_cases hcut : ∃ d : V, IsCutVertex G d
      · obtain ⟨d, hd⟩ := hcut
        have recurse (K : (deleteVertex G d).ConnectedComponent)
            (ha : a ∈ CutDensity.piece G d K)
            (hb : b ∈ CutDensity.piece G d K)
            (hc : c ∈ CutDensity.piece G d K) :
            G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
          let P := CutDensity.piece G d K
          let aP : {w : V // w ∈ (P : Set V)} :=
            ⟨a, ha⟩
          let bP : {w : V // w ∈ (P : Set V)} :=
            ⟨b, hb⟩
          let cP : {w : V // w ∈ (P : Set V)} :=
            ⟨c, hc⟩
          have hproper : P ≠ Finset.univ :=
            CutDensity.piece_ne_univ (G := G) hd K
          have hcardP : Fintype.card {w : V // w ∈ (P : Set V)} =
              P.card := by simp
          have hlt : Fintype.card {w : V // w ∈ (P : Set V)} <
              Fintype.card V := by
            rw [hcardP]
            exact Finset.card_lt_card
              (Finset.ssubset_univ_iff.mpr hproper)
          have hconnP : (G.induce (P : Set V)).Connected :=
            CutDensity.piece_connected (G := G) hconn d K
          have hsP : Is23Sparse (G.induce (P : Set V)) := hs.induce
          have habP : aP ≠ bP := fun h => hab (congrArg Subtype.val h)
          have hacP : aP ≠ cP := fun h => hac (congrArg Subtype.val h)
          have hbcP : bP ≠ cP := fun h => hbc (congrArg Subtype.val h)
          have hnoP : ¬ HasThreeTerminalPath
              (G.induce (P : Set V)) aP bP cP := by
            intro hp
            exact hno hp.map_induce
          have hboundP :
              (G.induce (P : Set V)).edgeFinset.card + 5 ≤
                2 * Fintype.card {w : V // w ∈ (P : Set V)} :=
            ih _ hlt (G.induce (P : Set V)) hconnP hsP
              habP hacP hbcP hnoP rfl
          rw [hcardP] at hboundP
          exact edge_card_add_five_le_of_piece_bound hs hd K (by
            simpa only [P] using hboundP)
        by_cases hda : d = a
        · subst d
          let b' : {w : V // w ≠ a} := ⟨b, hab.symm⟩
          let c' : {w : V // w ≠ a} := ⟨c, hac.symm⟩
          let B := (deleteVertex G a).connectedComponentMk b'
          let C := (deleteVertex G a).connectedComponentMk c'
          have hbB : b ∈ ComponentEndBlock.side (G := G) a B := by
            refine ⟨hab.symm, ?_⟩
            simp [B, b', SimpleGraph.ConnectedComponent.mem_supp_iff]
          have hcC : c ∈ ComponentEndBlock.side (G := G) a C := by
            refine ⟨hac.symm, ?_⟩
            simp [C, c', SimpleGraph.ConnectedComponent.mem_supp_iff]
          by_cases hBC : B = C
          · have hcB : c ∈ ComponentEndBlock.side (G := G) a B := by
              simpa [hBC] using hcC
            exact recurse B (CutDensity.cut_mem_piece (G := G) a B)
              ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hbB))
              ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hcB))
          · obtain ⟨q, hq, hqside⟩ :=
              exists_path_to_cut_in_component hconn a C hcC
            have hW : HasThreeTerminalPath G b a c :=
              hasThreeTerminalPath_of_rootedPath_in_component
                hconn hBC hbB hcC q.reverse hq.reverse
                  q.reverse.start_mem_support (by
                    intro w hw
                    have hw' : w ∈ q.support := by simpa [Walk.support_reverse] using hw
                    exact hqside w hw')
            exact False.elim (hno (hasThreeTerminalPath_swap_left.mpr hW))
        · by_cases hdb : d = b
          · subst d
            let a' : {w : V // w ≠ b} := ⟨a, hab⟩
            let c' : {w : V // w ≠ b} := ⟨c, hbc.symm⟩
            let A := (deleteVertex G b).connectedComponentMk a'
            let C := (deleteVertex G b).connectedComponentMk c'
            have haA : a ∈ ComponentEndBlock.side (G := G) b A := by
              refine ⟨hab, ?_⟩
              simp [A, a', SimpleGraph.ConnectedComponent.mem_supp_iff]
            have hcC : c ∈ ComponentEndBlock.side (G := G) b C := by
              refine ⟨hbc.symm, ?_⟩
              simp [C, c', SimpleGraph.ConnectedComponent.mem_supp_iff]
            by_cases hAC : A = C
            · have hcA : c ∈ ComponentEndBlock.side (G := G) b A := by
                simpa [hAC] using hcC
              exact recurse A
                ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr haA))
                (CutDensity.cut_mem_piece (G := G) b A)
                ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hcA))
            · obtain ⟨q, hq, hqside⟩ :=
                exists_path_to_cut_in_component hconn b C hcC
              have hW : HasThreeTerminalPath G a b c :=
                hasThreeTerminalPath_of_rootedPath_in_component
                  hconn hAC haA hcC q.reverse hq.reverse
                    q.reverse.start_mem_support (by
                      intro w hw
                      have hw' : w ∈ q.support := by
                        simpa [Walk.support_reverse] using hw
                      exact hqside w hw')
              exact False.elim (hno hW)
          · by_cases hdc : d = c
            · subst d
              let a' : {w : V // w ≠ c} := ⟨a, hac⟩
              let b' : {w : V // w ≠ c} := ⟨b, hbc⟩
              let A := (deleteVertex G c).connectedComponentMk a'
              let B := (deleteVertex G c).connectedComponentMk b'
              have haA : a ∈ ComponentEndBlock.side (G := G) c A := by
                refine ⟨hac, ?_⟩
                simp [A, a', SimpleGraph.ConnectedComponent.mem_supp_iff]
              have hbB : b ∈ ComponentEndBlock.side (G := G) c B := by
                refine ⟨hbc, ?_⟩
                simp [B, b', SimpleGraph.ConnectedComponent.mem_supp_iff]
              by_cases hAB : A = B
              · have hbA : b ∈ ComponentEndBlock.side (G := G) c A := by
                  simpa [hAB] using hbB
                exact recurse A
                  ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr haA))
                  ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hbA))
                  (CutDensity.cut_mem_piece (G := G) c A)
              · obtain ⟨q, hq, hqside⟩ :=
                  exists_path_to_cut_in_component hconn c B hbB
                have hW : HasThreeTerminalPath G a c b :=
                  hasThreeTerminalPath_of_rootedPath_in_component
                    hconn hAB haA hbB q.reverse hq.reverse
                      q.reverse.start_mem_support (by
                        intro w hw
                        have hw' : w ∈ q.support := by
                          simpa [Walk.support_reverse] using hw
                        exact hqside w hw')
                exact False.elim (hno (hasThreeTerminalPath_swap_right.mpr hW))
            · let a' : {w : V // w ≠ d} := ⟨a, Ne.symm hda⟩
              let b' : {w : V // w ≠ d} := ⟨b, Ne.symm hdb⟩
              let c' : {w : V // w ≠ d} := ⟨c, Ne.symm hdc⟩
              let A := (deleteVertex G d).connectedComponentMk a'
              let B := (deleteVertex G d).connectedComponentMk b'
              let C := (deleteVertex G d).connectedComponentMk c'
              have haA : a ∈ ComponentEndBlock.side (G := G) d A := by
                refine ⟨Ne.symm hda, ?_⟩
                simp [A, a', SimpleGraph.ConnectedComponent.mem_supp_iff]
              have hbB : b ∈ ComponentEndBlock.side (G := G) d B := by
                refine ⟨Ne.symm hdb, ?_⟩
                simp [B, b', SimpleGraph.ConnectedComponent.mem_supp_iff]
              have hcC : c ∈ ComponentEndBlock.side (G := G) d C := by
                refine ⟨Ne.symm hdc, ?_⟩
                simp [C, c', SimpleGraph.ConnectedComponent.mem_supp_iff]
              by_cases hAB : A = B
              · have hbA : b ∈ ComponentEndBlock.side (G := G) d A := by
                  simpa [hAB] using hbB
                by_cases hAC : A = C
                · have hcA : c ∈ ComponentEndBlock.side (G := G) d A := by
                    simpa [hAC] using hcC
                  exact recurse A
                    ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr haA))
                    ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hbA))
                    ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hcA))
                · have hno' : ¬ HasThreeTerminalPath G c a b := by
                    intro hW
                    exact hno (hasThreeTerminalPath_rotate.mpr
                      (hasThreeTerminalPath_rotate.mpr hW))
                  exact edge_card_add_five_le_of_component_pair
                    hconn hs (Ne.symm hAC) hcC haA hbA hab hno'
              · by_cases hAC : A = C
                · have hcA : c ∈ ComponentEndBlock.side (G := G) d A := by
                    simpa [hAC] using hcC
                  have hno' : ¬ HasThreeTerminalPath G b a c := by
                    intro hW
                    exact hno (hasThreeTerminalPath_swap_left.mpr hW)
                  exact edge_card_add_five_le_of_component_pair
                    hconn hs (Ne.symm hAB) hbB haA hcA hac hno'
                · by_cases hBC : B = C
                  · have hcB : c ∈ ComponentEndBlock.side (G := G) d B := by
                      simpa [hBC] using hcC
                    exact edge_card_add_five_le_of_component_pair
                      hconn hs hAB haA hbB hcB hbc hno
                  · obtain ⟨T⟩ := threeWayCut_of_three_components
                      d A B C hAB hAC hBC
                    exact T.edge_card_add_five_le hs
      · have hdelete : ∀ d : V,
            (G.induce fun w : V => w ≠ d).Connected := by
          intro d
          have hpre : (deleteVertex G d).Preconnected :=
            not_not.mp (not_exists.mp hcut d)
          have hne : Nonempty {w : V // w ≠ d} := by
            by_cases hda : d = a
            · exact ⟨⟨b, by simpa [hda] using hab.symm⟩⟩
            · exact ⟨⟨a, Ne.symm hda⟩⟩
          letI : Nonempty {w : V // w ≠ d} := hne
          change (deleteVertex G d).Connected
          exact SimpleGraph.Connected.mk hpre
        obtain ⟨p, hp, hcp⟩ :=
          exists_rooted_three_path (G := G) (r := a) (a := c) (b := b)
            hac hab hbc.symm hconn hdelete
        apply False.elim
        apply hno
        exact ⟨a, b, by simp, by simp, hab, p, hp,
          p.start_mem_support, p.end_mem_support, hcp⟩

end Erdos916
