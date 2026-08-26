/-
Adapted from Shashi456/erdos-formalizations, Erdos/P750/Proof.lean:
https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean
Original formalization posted by paws on 4 May 2026:
https://www.erdosproblems.com/forum/thread/750#post-6255
-/
import ErdosProblems.Erdos750.Basic

namespace Erdos750.Conditional

open SimpleGraph Filter
open scoped NNReal

universe u v

/-- Stiebitz's chromatic lower bound, isolated as an explicit hypothesis. -/
def StiebitzLowerBound : Prop :=
  ∀ {V : Type} (G : SimpleGraph V) (r : ℕ),
    IsRecursivelyBuiltMr r G → (r : ℕ∞) ≤ G.chromaticNumber


/-! ## §3. Key combinatorial lemmas -/

/-- Easy direction of Stiebitz: a `k`-colouring of `G` lifts to a `(k+1)`-colouring of
`Mₛ(G)` by reusing the colours on every level and giving the apex a fresh colour. -/
theorem genMyc_colorable_succ {V : Type u} (s : ℕ) (G : SimpleGraph V) (k : ℕ)
    (hG : G.Colorable k) : (genMyc s G).Colorable (k + 1) := by
  classical
  obtain ⟨c⟩ := hG
  refine ⟨Coloring.mk
    (fun a => Sum.elim (fun p : Fin s × V => (c p.2).castSucc) (fun _ : Unit => Fin.last k) a)
    ?_⟩
  intro a b hab
  match a, b, hab with
  | Sum.inl (i, u), Sum.inl (j, v), h =>
      simp only [Sum.elim_inl]
      have huv : G.Adj u v := by
        rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
      have hcuv : c u ≠ c v := c.valid huv
      intro heq
      exact hcuv (Fin.castSucc_injective _ heq)
  | Sum.inl (i, u), Sum.inr (), _ =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      intro heq
      have hh : ((c u).castSucc).val = k := by rw [heq]; rfl
      rw [Fin.val_castSucc] at hh
      have := (c u).isLt
      omega
  | Sum.inr (), Sum.inl (i, v), _ =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      intro heq
      have hh : (Fin.last k).val = ((c v).castSucc).val := by rw [heq]
      rw [Fin.val_castSucc] at hh
      have := (c v).isLt
      simp at hh
      omega
  | Sum.inr (), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h

/-- Easy direction of Stiebitz: `χ(Mₛ(G)) ≤ χ(G) + 1`. -/
theorem genMyc_chromaticNumber_le_succ {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    (genMyc s G).chromaticNumber ≤ G.chromaticNumber + 1 := by
  by_cases hG : G.chromaticNumber = ⊤
  · rw [hG]; simp
  · -- finite case: take k = G.chromaticNumber.toNat
    set n := G.chromaticNumber.toNat with hn_def
    have hcoe : (n : ℕ∞) = G.chromaticNumber := by
      rw [hn_def]; exact ENat.natCast_toNat hG
    have hGc : G.Colorable n := by
      rw [← chromaticNumber_le_iff_colorable, hcoe]
    have h1 : (genMyc s G).Colorable (n + 1) := genMyc_colorable_succ s G n hGc
    have h2 : (genMyc s G).chromaticNumber ≤ ((n + 1 : ℕ) : ℕ∞) := h1.chromaticNumber_le
    have h3 : ((n + 1 : ℕ) : ℕ∞) = G.chromaticNumber + 1 := by
      push_cast; rw [hcoe]
    rw [h3] at h2; exact h2

/--
The projection of a finite vertex set in `Mₛ(G)` to a `Finset` of `V`. Apex vertices
contribute nothing.
-/
def projFinset {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) : Finset V :=
  X.biUnion fun a => match a with | Sum.inl (_, v) => {v} | Sum.inr () => ∅

/-- The "lifted deletion set" used in Lemma 3.1's proof: from a transversal `T` of
`G[projFinset X]`, lift to a deletion set of `(genMyc s G)[X]` that includes every
copy `(i, v)` with `v ∈ T` *and* the apex if it appears in `X`.

Equivalently `(image of (Fin s) × T into MycVerts) ∪ {apex if in X}`, intersected
with `X`. -/
private noncomputable def liftedDeletion {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) (T : Finset V) : Finset (MycVerts s V) :=
  X ∩ (((Finset.univ : Finset (Fin s)) ×ˢ T).image (fun p => Sum.inl p) ∪
       ({apex s V} : Finset (MycVerts s V)))

private lemma liftedDeletion_subset {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) (T : Finset V) :
    liftedDeletion X T ⊆ X :=
  Finset.inter_subset_left

private lemma mem_liftedDeletion {V : Type u} [DecidableEq V] {s : ℕ}
    {X : Finset (MycVerts s V)} {T : Finset V} {a : MycVerts s V} :
    a ∈ liftedDeletion X T ↔
      a ∈ X ∧ ((∃ i : Fin s, ∃ v ∈ T, a = Sum.inl (i, v)) ∨ a = apex s V) := by
  classical
  unfold liftedDeletion
  rw [Finset.mem_inter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with ⟨⟨i, v⟩, hv, heq⟩ | hap
    · left
      rw [Finset.mem_product] at hv
      exact ⟨i, v, hv.2, heq.symm⟩
    · right; exact hap
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with ⟨i, v, hv, heq⟩ | hap
    · left
      refine ⟨(i, v), ?_, heq.symm⟩
      rw [Finset.mem_product]
      exact ⟨Finset.mem_univ _, hv⟩
    · right; exact hap

/-- Cardinality bound for the lifted deletion set. -/
private lemma liftedDeletion_card_le {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) (T : Finset V) :
    (liftedDeletion X T).card ≤ s * T.card +
      (if apex s V ∈ X then 1 else 0) := by
  classical
  -- liftedDeletion ⊆ levelLifts ∪ apexSet (with the apex set conditional on X)
  set levelLifts : Finset (MycVerts s V) :=
    ((Finset.univ : Finset (Fin s)) ×ˢ T).image (fun p => Sum.inl p) with h_lL
  set apexSet : Finset (MycVerts s V) :=
    if apex s V ∈ X then ({apex s V} : Finset _) else ∅ with h_aS
  have h_sub : liftedDeletion X T ⊆ levelLifts ∪ apexSet := by
    intro a ha
    rw [mem_liftedDeletion] at ha
    obtain ⟨ha_X, ha_or⟩ := ha
    rw [Finset.mem_union]
    rcases ha_or with ⟨i, v, hv, heq⟩ | hap
    · left; rw [h_lL, Finset.mem_image]
      refine ⟨(i, v), ?_, heq.symm⟩
      simp [Finset.mem_product, hv]
    · right; rw [h_aS]
      rw [hap] at ha_X
      simp [ha_X, hap]
  refine le_trans (Finset.card_le_card h_sub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  · rw [h_aS]; split_ifs <;> simp

/-- Bipartiteness of the survivor `(genMyc s G)[X \ liftedDeletion X T]`, given that
`G[projFinset X \ T]` is bipartite. The bipartition is "vertical": each level vertex
inherits the side of its projection in `G`. -/
private lemma liftedDeletion_survivor_isBipartite {V : Type u} [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (X : Finset (MycVerts s V)) (T : Finset V)
    (_hT : T ⊆ projFinset X)
    (hbip : (G.induce ((↑(projFinset X) : Set V) \ (↑T : Set V))).IsBipartite) :
    ((genMyc s G).induce
        ((↑X : Set (MycVerts s V)) \
          (↑(liftedDeletion X T) : Set (MycVerts s V)))).IsBipartite := by
  classical
  obtain ⟨c⟩ := hbip
  -- For a survivor a, extract its underlying V-vertex and properties: a = Sum.inl (i, v),
  -- v ∈ projFinset X, v ∉ T. The apex is excluded by `liftedDeletion`.
  -- We use a `match` term to define the coloring directly, taking the survivor's proof
  -- as input to discharge the apex case via `False.elim`.
  have hAux : ∀ a : MycVerts s V,
      a ∈ X → a ∉ liftedDeletion X T →
      Σ' (v : V), v ∈ projFinset X ∧ v ∉ T ∧ ∃ i : Fin s, a = Sum.inl (i, v) := by
    intro a haX haND
    match a, haX, haND with
    | Sum.inl (i, v), hX', hND' =>
        refine ⟨v, ?_, ?_, i, rfl⟩
        · unfold projFinset
          rw [Finset.mem_biUnion]
          exact ⟨Sum.inl (i, v), hX', by simp⟩
        · intro hvT
          apply hND'
          rw [mem_liftedDeletion]
          exact ⟨hX', Or.inl ⟨i, v, hvT, rfl⟩⟩
    | Sum.inr (), hX', hND' =>
        exfalso
        apply hND'
        rw [mem_liftedDeletion]
        exact ⟨hX', Or.inr rfl⟩
  -- Define the coloring on survivors by projecting and applying c.
  let colorFn : ((↑X : Set (MycVerts s V)) \
      (↑(liftedDeletion X T) : Set (MycVerts s V)) : Set _) → Fin 2 :=
    fun a =>
      let info := hAux a.val a.prop.1 a.prop.2
      c ⟨info.1, info.2.1, info.2.2.1⟩
  refine ⟨Coloring.mk colorFn ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : (genMyc s G).Adj a b := hab
  simp only [colorFn]
  -- Compute `hAux` outputs for a and b
  set ainfo := hAux a ha.1 ha.2 with h_ainfo
  set binfo := hAux b hb.1 hb.2 with h_binfo
  -- Show `Sum.inl (i, ainfo.1) = a` and `Sum.inl (j, binfo.1) = b` for some i, j.
  obtain ⟨i, hai⟩ := ainfo.2.2.2
  obtain ⟨j, hbj⟩ := binfo.2.2.2
  -- From hab' : (genMyc s G).Adj a b and the substitutions a = inl(i, ainfo.1), b = inl(j,
  -- binfo.1),
  -- conclude G.Adj ainfo.1 binfo.1.
  have huv : G.Adj ainfo.1 binfo.1 := by
    have : (genMyc s G).Adj (Sum.inl (i, ainfo.1)) (Sum.inl (j, binfo.1)) := by
      rw [← hai, ← hbj]; exact hab'
    -- Unfold MycAdj on inl-inl
    have hM : MycAdj s G (Sum.inl (i, ainfo.1)) (Sum.inl (j, binfo.1)) := this
    simp only [MycAdj] at hM
    rcases hM with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
  -- Apply c.valid
  exact c.valid huv

/--
**Lemma 3.1 (Projection inequality).** For every `X ⊆ V(Mₛ(G))` with projection
`P = projFinset X`, the induced subgraph satisfies
`oct(Mₛ(G)[X]) ≤ s · oct(G[P]) + 1{apex ∈ X}`.

Proof: take an OCT witness `T` of `G[projFinset X]`. Lift to `T' := liftedDeletion X T`.
Then `T' ⊆ X`, `|T'| ≤ s * |T| + 1{apex ∈ X}` (`liftedDeletion_card_le`), and the
survivor `(genMyc s G)[X \ T']` is bipartite (`liftedDeletion_survivor_isBipartite`).
Apply `oct_le_of_delete`.
-/
theorem oct_genMyc_le {V : Type u} [DecidableEq V]
    (s : ℕ) (G : SimpleGraph V) (X : Finset (MycVerts s V)) :
    oct (genMyc s G) X ≤ s * oct G (projFinset X) +
      (if apex s V ∈ X then 1 else 0) := by
  classical
  obtain ⟨T, hTsub, hTcard, hTbip⟩ := oct_witness G (projFinset X)
  have hcard := liftedDeletion_card_le X T
  rw [hTcard] at hcard
  refine oct_le_of_delete (liftedDeletion_subset X T) hcard ?_
  exact liftedDeletion_survivor_isBipartite G X T hTsub hTbip

/--
**Sub-lemma for Lemma 3.2.** `Mₛ(B)` minus the apex is bipartite when `B` is.
The bipartition is inherited "vertically" — every level uses `B`'s bipartition,
because every edge of `Mₛ(B)` not incident to the apex projects to a `B`-edge,
hence joins different sides.
-/
lemma genMyc_minus_apex_isBipartite {V : Type u} (s : ℕ) (B : SimpleGraph V)
    (hB : B.IsBipartite) :
    ((genMyc s B).induce {a : MycVerts s V | a ≠ apex s V}).IsBipartite := by
  classical
  obtain ⟨c⟩ := hB
  refine ⟨Coloring.mk (fun a => Sum.casesOn (motive := fun x => x ≠ apex s V → Fin 2)
    a.val
    (fun p => fun _ => c p.2)
    (fun _ => fun ha => absurd rfl ha) a.prop) ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  -- (genMyc s B).Adj a b
  have hab' : (genMyc s B).Adj a b := hab
  match a, b, ha, hb, hab' with
  | Sum.inl ⟨i, u⟩, Sum.inl ⟨j, v⟩, _, _, h =>
      have huv : B.Adj u v := by
        rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
      simp only
      exact c.valid huv
  | Sum.inl _, Sum.inr (), _, hb, _ => exact absurd rfl hb
  | Sum.inr (), _, ha, _, _ => exact absurd rfl ha

/-- **Height** of a vertex in `Mₛ(G)`: the apex sits at height `s`, every level-`i`
vertex sits at height `i.val < s`. Each edge changes height by at most `1`, with edges
that *preserve* height existing only at height `0` (level-0 internal edges). -/
def height {V : Type u} (s : ℕ) : MycVerts s V → ℕ
  | Sum.inl (i, _) => i.val
  | Sum.inr () => s

/-- Edges of `genMyc s G` change height by at most 1. -/
lemma height_diff_le_one {V : Type u} {s : ℕ} {G : SimpleGraph V}
    {a b : MycVerts s V} (h : (genMyc s G).Adj a b) :
    height s a ≤ height s b + 1 ∧ height s b ≤ height s a + 1 := by
  match a, b, h with
  | Sum.inl (i, _), Sum.inl (j, _), h =>
      simp only [height]
      rcases h with ⟨hi, hj, _⟩ | ⟨hji, _⟩ | ⟨hij, _⟩ <;> omega
  | Sum.inl (i, _), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h
      simp only [height]; omega
  | Sum.inr (), Sum.inl (i, _), h =>
      simp only [genMyc, MycAdj] at h
      simp only [height]; omega
  | Sum.inr (), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h

/-- An edge that preserves height has both endpoints at height 0 (level-0 internal edge). -/
lemma height_eq_of_adj {V : Type u} {s : ℕ} {G : SimpleGraph V}
    {a b : MycVerts s V} (hab : (genMyc s G).Adj a b)
    (heq : height s a = height s b) :
    height s a = 0 := by
  match a, b, hab with
  | Sum.inl (i, _), Sum.inl (j, _), h =>
      simp only [height] at heq ⊢
      rcases h with ⟨hi, _, _⟩ | ⟨hji, _⟩ | ⟨hij, _⟩
      · exact hi
      · omega
      · omega
  | Sum.inl (i, _), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h
      simp only [height] at heq
      omega
  | Sum.inr (), Sum.inl (i, _), h =>
      simp only [genMyc, MycAdj] at h
      simp only [height] at heq
      omega
  | Sum.inr (), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h

/-- Walks are 1-Lipschitz with respect to `height`: a walk of length `ℓ` from `a` to `b`
satisfies `|height a − height b| ≤ ℓ`. -/
lemma height_diff_le_walk_length {V : Type u} {s : ℕ} {G : SimpleGraph V}
    {a b : MycVerts s V} (w : (genMyc s G).Walk a b) :
    height s a ≤ height s b + w.length ∧ height s b ≤ height s a + w.length := by
  induction w with
  | nil => simp
  | @cons a c b hac w ih =>
      have hed := height_diff_le_one hac
      simp only [Walk.length_cons]
      omega

/-! ### Towards Lemma 3.2: parity coloring of `Mₛ(G)` minus level-0 internal edges -/

/-- The "level-0 internal" edges of `Mₛ(G)`: both endpoints at height 0. For `s ≥ 1`
this is exactly the level-0 internal edges of the PDF. -/
def IsLevelZeroEdge {V : Type u} {s : ℕ} (a b : MycVerts s V) : Prop :=
  height s a = 0 ∧ height s b = 0

lemma IsLevelZeroEdge.symm {V : Type u} {s : ℕ} {a b : MycVerts s V}
    (h : IsLevelZeroEdge a b) : IsLevelZeroEdge b a := ⟨h.2, h.1⟩

/-- The graph `Mₛ(G)` with level-0 internal edges removed. Closed walks here are
even-length: a height-parity coloring witnesses bipartiteness. -/
def genMycMinusZero {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    SimpleGraph (MycVerts s V) where
  Adj a b := (genMyc s G).Adj a b ∧ ¬ IsLevelZeroEdge a b
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, fun hz => h2 hz.symm⟩⟩
  loopless := ⟨fun _ ⟨h1, _⟩ => (genMyc s G).irrefl h1⟩

/-- The height parity is a 2-coloring of `Mₛ(G)` minus level-0 internal edges. -/
private lemma genMycMinusZero_isBipartite {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    (genMycMinusZero s G).IsBipartite := by
  refine ⟨Coloring.mk
    (fun a => (⟨(height s a) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
  intro a b ⟨hab, hnot0⟩
  -- Heights differ by exactly 1; height parities differ.
  have hheight : height s a + 1 = height s b ∨ height s b + 1 = height s a := by
    match a, b, hab with
    | Sum.inl (i, _), Sum.inl (j, _), h =>
        simp only [height]
        rcases h with ⟨hi, hj, _⟩ | ⟨hji, _⟩ | ⟨hij, _⟩
        · exact absurd ⟨by simpa [height] using hi, by simpa [height] using hj⟩ hnot0
        · left; omega
        · right; omega
    | Sum.inl (i, _), Sum.inr (), h =>
        have h' : i.val + 1 = s := h
        simp only [height]; left; omega
    | Sum.inr (), Sum.inl (i, _), h =>
        have h' : i.val + 1 = s := h
        simp only [height]; right; omega
    | Sum.inr (), Sum.inr (), h =>
        exact (h : False).elim
  -- From either case, parities differ
  intro heq
  have heq' : (height s a) % 2 = (height s b) % 2 := by
    have := congrArg Fin.val heq
    simpa using this
  rcases hheight with hh | hh
  · omega
  · omega

/--
**Generalized helper.** Any walk in `Mₛ(G)` containing a level-0 edge has length at
least `height a + height b + 1`, where `a, b` are the walk's endpoints.

Proof by induction on the walk. Base case (nil walk) is vacuous. For `cons hab rest`:
either the first edge is the level-0 edge (so `height a = height c = 0`, and
Lipschitz on `rest` gives `rest.length ≥ height b`); or the level-0 edge is in
`rest.edges`, in which case the induction hypothesis plus the height bound
`|height a − height c| ≤ 1` gives the result.
-/
private lemma walk_zero_edge_implies_long {V : Type u} {s : ℕ} {G : SimpleGraph V} :
    ∀ {a b : MycVerts s V} (w : (genMyc s G).Walk a b),
      (∃ e ∈ w.edges, ∀ v ∈ e, height s v = 0) →
      height s a + height s b + 1 ≤ w.length := by
  intro a b w hex
  induction w with
  | nil =>
      obtain ⟨e, he, _⟩ := hex
      simp at he
  | @cons a c b hab rest ih =>
      obtain ⟨e, he_in, he_zero⟩ := hex
      rw [Walk.edges_cons] at he_in
      rcases List.mem_cons.mp he_in with heq | hin
      · -- The first edge is the level-0 edge
        subst heq
        have h_a_zero : height s a = 0 := he_zero a (Sym2.mem_mk_left a c)
        have h_c_zero : height s c = 0 := he_zero c (Sym2.mem_mk_right a c)
        have hLip := (height_diff_le_walk_length rest).2
        -- hLip : height s b ≤ height s c + rest.length = rest.length
        simp only [Walk.length_cons]
        omega
      · -- Level-0 edge is inside `rest`
        have ih_appl : height s c + height s b + 1 ≤ rest.length :=
          ih ⟨e, hin, he_zero⟩
        have hedge := height_diff_le_one hab
        simp only [Walk.length_cons]
        omega

/-- An edge in `(genMyc s G).edgeSet` but not in `(genMycMinusZero s G).edgeSet` is a
level-0 edge: both endpoints have height 0. -/
private lemma sym2_zero_of_in_genMyc_not_minus {V : Type u} {s : ℕ}
    {G : SimpleGraph V} :
    ∀ (e : Sym2 (MycVerts s V)),
      e ∈ (genMyc s G).edgeSet → e ∉ (genMycMinusZero s G).edgeSet →
      ∀ v ∈ e, height s v = 0 := by
  refine Sym2.ind ?_
  intro a b hG hne v hv
  rw [SimpleGraph.mem_edgeSet] at hG
  have h_iszero : IsLevelZeroEdge a b := by
    by_contra h
    apply hne
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨hG, h⟩
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact h_iszero.1
  · exact h_iszero.2

/--
**Apex-to-apex closed walks with a non-`genMycMinusZero` edge are long.** If `w` is
a closed walk from `apex` to `apex` containing some edge not in `genMycMinusZero`,
then `w.length ≥ 2 s + 1`.
-/
private lemma walk_apex_long_of_zero_edge {V : Type u} {s : ℕ} {G : SimpleGraph V}
    (w : (genMyc s G).Walk (apex s V) (apex s V))
    (hex : ∃ e ∈ w.edges, e ∉ (genMycMinusZero s G).edgeSet) :
    2 * s + 1 ≤ w.length := by
  obtain ⟨e, he, hne⟩ := hex
  have hG : e ∈ (genMyc s G).edgeSet := w.edges_subset_edgeSet he
  have hzero : ∀ v ∈ e, height s v = 0 :=
    sym2_zero_of_in_genMyc_not_minus e hG hne
  have hlen := walk_zero_edge_implies_long w ⟨e, he, hzero⟩
  simp only [height] at hlen
  omega

/--
**Helper sub-lemma for Lemma 3.2.** Contrapositive of the above: if a closed apex
walk has length `< 2s + 1`, all its edges are in `genMycMinusZero s G`.
-/
private lemma walk_short_no_zero_edge {V : Type u} {s : ℕ} (G : SimpleGraph V)
    (w : (genMyc s G).Walk (apex s V) (apex s V))
    (hlen : w.length < 2 * s + 1) :
    ∀ e ∈ w.edges, e ∈ (genMycMinusZero s G).edgeSet := by
  intro e he
  by_contra hcon
  exact absurd hlen (not_lt.mpr (walk_apex_long_of_zero_edge w ⟨e, he, hcon⟩))

/--
**Lemma 3.2 (Apex closed walks of odd length are long).**

For every `s ≥ 1` and every closed walk in `Mₛ(G)` from the apex back to itself, if the
walk has odd length, the length is at least `2 * s + 1`.

This statement does **not** require `G` to be bipartite (audit #4). The argument is
purely a height/parity invariant: every edge changes `height` by 0 (only at height 0)
or ±1, so on a closed walk the count of `±1`-edges is even, meaning odd parity forces
at least one `0`-edge. A `0`-edge exists only at height 0, so the walk descends from
height `s` to `0` and re-ascends. Each leg costs at least `s` edges by Lipschitz, plus
the `0`-edge itself, giving total length at least `2 * s + 1`.

This proof is structured into two pieces: the parity coloring of
`genMycMinusZero` (proved above), and the helper `walk_short_no_zero_edge`
(the walk-decomposition + Lipschitz step). Given the helper, this theorem is
fully proved by `Walk.transfer` + `Coloring.even_length_iff_congr`.
-/
theorem genMyc_oddClosedWalk_through_apex_long {V : Type u} {s : ℕ} (_hs : 1 ≤ s)
    (G : SimpleGraph V) :
    ∀ (w : (genMyc s G).Walk (apex s V) (apex s V)),
      Odd w.length → 2 * s + 1 ≤ w.length := by
  intro w hodd
  by_contra hcon
  push Not at hcon
  -- hcon : w.length < 2 * s + 1.  Lift w to genMycMinusZero (no 0-edges).
  have hedges : ∀ e ∈ w.edges, e ∈ (genMycMinusZero s G).edgeSet :=
    walk_short_no_zero_edge G w hcon
  let w' : (genMycMinusZero s G).Walk (apex s V) (apex s V) := w.transfer _ hedges
  have hlen : w'.length = w.length := Walk.length_transfer w hedges
  -- Use bipartite parity to force even length.
  obtain ⟨c⟩ := genMycMinusZero_isBipartite s G
  let c' : (genMycMinusZero s G).Coloring Bool := SimpleGraph.recolorOfEquiv _ finTwoEquiv c
  have heven : Even w'.length := (c'.even_length_iff_congr w').mpr ⟨id, id⟩
  rw [hlen] at heven
  exact Nat.not_odd_iff_even.mpr heven hodd

/--
**Lemma 3.2 (Cycle form, as in the PDF).** Special case of
`genMyc_oddClosedWalk_through_apex_long`: every odd cycle of `Mₛ(B)` containing the
apex has length at least `2*s + 1`. The bipartite hypothesis on `B` is not used by
the length bound — it is what guarantees that *every* odd cycle of `Mₛ(B)` contains
the apex (via `genMyc_minus_apex_isBipartite`), but the length bound itself works
for any `G`.
-/
theorem genMyc_oddCycle_through_apex_long {V : Type u} (s : ℕ) (hs : 1 ≤ s)
    (B : SimpleGraph V) (_hB : B.IsBipartite) :
    ∀ (c : (genMyc s B).Walk (apex s V) (apex s V)),
      c.IsCycle → Odd c.length → 2 * s + 1 ≤ c.length := fun c _ hodd =>
  genMyc_oddClosedWalk_through_apex_long hs B c hodd

/-! ## §4. Finite local-oct profile -/

/--
**Helper.** In a simple graph, if `p : G.Walk v u` is a path of length at least 2,
then there is no edge between its endpoints `s(u, v)` lying within `p.edges`.
Reason: any such edge corresponds to a dart at some position `k < p.length` with
endpoints `{u, v}`. By `IsPath.getVert_eq_start_iff` and `getVert_eq_end_iff`,
the only positions giving `u` and `v` are `p.length` and `0` respectively. So
the dart spans `(0, 1) = (v, u)`, giving `1 = p.length`, contradicting `length ≥ 2`.
-/
private lemma noEndpointEdge_of_isPath_length_ge_two {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk v u) (hpath : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  intro hmem
  -- Get a dart witnessing the edge.
  rw [Walk.edges, List.mem_map] at hmem
  obtain ⟨d, hd_mem, hd_edge⟩ := hmem
  -- d is at some position k in p.darts.
  obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hd_mem
  rw [Walk.length_darts] at hk_lt
  -- d = ⟨(getVert k, getVert (k+1)), _⟩.
  have hk_lt' : k < p.darts.length := by rw [Walk.length_darts]; exact hk_lt
  have hd_eq := Walk.darts_getElem_eq_getVert (p := p) k hk_lt'
  rw [hk_eq] at hd_eq
  -- d.edge = s(u, v), so {d.fst, d.snd} = {u, v}.
  rcases d with ⟨⟨a, b⟩, hadj⟩
  simp only [Dart.mk.injEq] at hd_eq
  injection hd_eq with hfst hsnd
  -- now hfst : a = p.getVert k, hsnd : b = p.getVert (k + 1).
  -- d.edge = s(a, b) = s(u, v). So (a, b) = (u, v) or (a, b) = (v, u).
  simp only [Dart.edge, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk] at hd_edge
  rcases hd_edge with ⟨ha_u, hb_v⟩ | ⟨ha_v, hb_u⟩
  · -- a = u, b = v: p.getVert k = u, so k = p.length (by getVert_eq_end_iff). But k < p.length.
    have hgvk : p.getVert k = u := hfst.symm.trans ha_u
    rw [hpath.getVert_eq_end_iff (Nat.le_of_lt hk_lt)] at hgvk
    omega
  · -- a = v, b = u: p.getVert k = v, so k = 0. Then p.getVert 1 = u, so 1 = p.length.
    have h_a : p.getVert k = v := hfst.symm.trans ha_v
    have h_b : p.getVert (k + 1) = u := hsnd.symm.trans hb_u
    rw [hpath.getVert_eq_start_iff (Nat.le_of_lt hk_lt)] at h_a
    rw [h_a] at h_b
    -- now h_b : p.getVert 1 = u
    rw [hpath.getVert_eq_end_iff (by omega : (0 + 1 : ℕ) ≤ p.length)] at h_b
    omega

/--
**Helper.** A closed walk in a simple graph with `support.tail.Nodup` and length at
least three is automatically a cycle. The only obstruction to a nodup-tail closed
walk being a cycle is having length 2 — a walk `u → v → u` whose two edges coincide.
Odd closed walks have length ≠ 2, so for them tail-nodup suffices.
-/
private lemma isCycle_of_tail_nodup_three_le {V : Type*} {G : SimpleGraph V} :
    ∀ {u : V} (w : G.Walk u u), w.support.tail.Nodup → 3 ≤ w.length → w.IsCycle := by
  intro u w htail hlen
  match w, htail, hlen with
  | .nil, _, hlen => simp at hlen
  | .cons (v := v) h₀ p, htail, hlen =>
    have hpath : p.IsPath := by
      rw [Walk.isPath_def]
      simpa using htail
    have hlen_p : 2 ≤ p.length := by
      simp [Walk.length_cons] at hlen
      omega
    rw [Walk.cons_isCycle_iff]
    exact ⟨hpath, noEndpointEdge_of_isPath_length_ge_two p hpath hlen_p⟩

/--
**Helper.** From any odd closed walk in a simple graph, extract an odd cycle whose
length is at most the original walk's length and whose support is contained in the
walk's support. The proof is by strong induction on length: a non-cycle odd closed
walk admits a vertex repetition; rotating to that vertex and splitting via takeUntil
yields two strictly-shorter closed sub-walks summing to the original odd length, one
of which is therefore odd; recurse on it.
-/
private lemma exists_isCycle_of_odd_closedWalk
    {V : Type*} {G : SimpleGraph V} :
    ∀ (n : ℕ) {u : V} (w : G.Walk u u), w.length = n → Odd w.length →
      ∃ (v : V) (c : G.Walk v v),
        c.IsCycle ∧ Odd c.length ∧ c.length ≤ n ∧ ∀ x ∈ c.support, x ∈ w.support := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w hwn hodd
    -- Case 1: w is already a cycle. Done.
    by_cases hcyc : w.IsCycle
    · exact ⟨u, w, hcyc, hodd, hwn ▸ Nat.le_refl _, fun _ hx => hx⟩
    -- w not a cycle: derive length ≥ 3, then ¬ tail.Nodup, then splice.
    have hodd_ne_zero : w.length ≠ 0 := by
      rcases hodd with ⟨k, hk⟩; omega
    have hlen_ne_one : w.length ≠ 1 := by
      intro h1
      match w, h1 with
      | .cons (v := v) h₀ p, h1 =>
        simp [Walk.length_cons] at h1
        -- h1 : p.length = 0, p : Walk v u, so v = u, contradicting Adj u v.
        rcases p with _ | _
        · exact G.irrefl h₀
        · simp at h1
    have hlen_ne_two : w.length ≠ 2 := by
      intro h2; rw [h2] at hodd; exact (by decide : ¬ Odd 2) hodd
    have hlen_ge_three : 3 ≤ w.length := by
      rcases hodd with ⟨k, hk⟩; omega
    -- ¬ tail.Nodup (else cycle).
    have hnotnodup : ¬ w.support.tail.Nodup :=
      fun htail => hcyc (isCycle_of_tail_nodup_three_le w htail hlen_ge_three)
    -- Find a duplicate y in support.tail.
    rw [← List.exists_duplicate_iff_not_nodup] at hnotnodup
    obtain ⟨y, hy_dup⟩ := hnotnodup
    have hy_mem : y ∈ w.support :=
      (Walk.mem_support_iff w).mpr (Or.inr hy_dup.mem)
    -- Rotate to start at y.
    let w' := w.rotate y hy_mem
    have hw'_len : w'.length = w.length := by
      change ((w.dropUntil y hy_mem).append (w.takeUntil y hy_mem)).length = w.length
      rw [Walk.length_append, add_comm]
      have := congr_arg Walk.length (w.take_spec hy_mem)
      rw [Walk.length_append] at this
      exact this
    have hw'_odd : Odd w'.length := hw'_len ▸ hodd
    -- y has count ≥ 2 in w.support.tail (from the Duplicate).
    have hy_count_w : 2 ≤ List.count y w.support.tail :=
      List.duplicate_iff_two_le_count.mp hy_dup
    -- And in w'.support.tail (rotation preserves count).
    have hperm : List.Perm w'.support.tail w.support.tail :=
      (Walk.support_rotate w y hy_mem).perm
    have hy_count_w' : 2 ≤ List.count y w'.support.tail := by
      rw [hperm.count_eq]; exact hy_count_w
    -- w' is non-nil (odd length).
    have hw'_pos : 0 < w'.length := by rw [hw'_len]; omega
    -- Decompose w' = cons h_b q (q : Walk y' y for some y').
    match hw'_eq : w', hw'_pos, hy_count_w' with
    | .nil, h0, _ => simp at h0
    | .cons (v := y') h_b q, _, hy_count_w'_cons =>
      -- support.tail of cons = q.support.
      have hy_count_q : 2 ≤ List.count y q.support := by
        have : (Walk.cons h_b q).support.tail = q.support := by simp
        rwa [this] at hy_count_w'_cons
      have hy_in_q : y ∈ q.support := List.count_pos_iff.mp (by omega)
      -- q = q.takeUntil y hy_in_q ++ q.dropUntil y hy_in_q.
      let q_first := q.takeUntil y hy_in_q
      let q_rest := q.dropUntil y hy_in_q
      have hq_split : q_first.append q_rest = q := q.take_spec hy_in_q
      have hq_len : q_first.length + q_rest.length = q.length := by
        have := congr_arg Walk.length hq_split
        rwa [Walk.length_append] at this
      -- α = cons h_b q_first : Walk y y, length 1 + q_first.length.
      -- β = q_rest : Walk y y, length q_rest.length.
      -- α.length + β.length = 1 + q.length = (Walk.cons h_b q).length = w'.length = n.
      let α : G.Walk y y := Walk.cons h_b q_first
      let β : G.Walk y y := q_rest
      have hα_len : α.length = 1 + q_first.length := by
        change (Walk.cons h_b q_first).length = 1 + q_first.length
        rw [Walk.length_cons]; omega
      have hβ_len : β.length = q_rest.length := rfl
      have hsum : α.length + β.length = n := by
        rw [hα_len, hβ_len]
        -- (1 + q_first.length) + q_rest.length = n
        -- = 1 + q.length (from hq_len) = (cons h_b q).length = w.length = n
        have : (Walk.cons h_b q).length = n := hw'_len.trans hwn
        rw [Walk.length_cons] at this
        omega
      -- q_rest.length ≥ 1 (because y has count ≥ 2 in q.support, the takeUntil count is 1,
      -- so the rest contributes ≥ 1).
      have hq_rest_pos : 0 < q_rest.length := by
        -- count y in q.support = count y in q_first.support + count y in q_rest.support.tail.
        -- count y in q_first.support = 1.
        -- So count y in q_rest.support.tail = (count in q.support) - 1 ≥ 1.
        -- q_rest.support.tail.length = q_rest.length, and tail has y, so non-empty.
        have hsplit_supp : q.support = q_first.support ++ q_rest.support.tail := by
          have := congr_arg Walk.support hq_split
          rw [Walk.support_append] at this
          exact this.symm
        have hcount_first : List.count y q_first.support = 1 :=
          q.count_support_takeUntil_eq_one hy_in_q
        have hcount_split : List.count y q.support =
            List.count y q_first.support + List.count y q_rest.support.tail := by
          rw [hsplit_supp, List.count_append]
        have hcount_tail : 1 ≤ List.count y q_rest.support.tail := by omega
        have hmem_tail : y ∈ q_rest.support.tail := List.count_pos_iff.mp (by omega)
        have hpos : 0 < q_rest.support.tail.length :=
          List.length_pos_of_mem hmem_tail
        have hsl : q_rest.support.length = q_rest.length + 1 := q_rest.length_support
        have htl : q_rest.support.tail.length = q_rest.length := by
          rw [List.length_tail, hsl]; omega
        omega
      -- Both α.length, β.length < n.
      have hβ_lt : β.length < n := by
        -- α.length ≥ 1, so β.length ≤ n - 1 < n.
        have : α.length ≥ 1 := by rw [hα_len]; omega
        omega
      have hα_lt : α.length < n := by
        -- β.length ≥ 1, so α.length ≤ n - 1 < n.
        rw [hβ_len] at hq_rest_pos
        omega
      -- One of α, β is odd. Since α.length + β.length = n is odd:
      have hodd_n : Odd n := hwn ▸ hodd
      have hodd_split : Odd α.length ∨ Odd β.length := by
        rcases Nat.even_or_odd α.length with hα_even | hα_odd
        · right
          have hodd_sum : Odd (α.length + β.length) := hsum ▸ hodd_n
          rcases hodd_sum with ⟨k, hk⟩
          rcases hα_even with ⟨m, hm⟩
          refine ⟨k - m, ?_⟩; omega
        · left; exact hα_odd
      -- Apply IH to whichever is odd.
      have hsupp_α : ∀ x ∈ α.support, x ∈ w.support := by
        intro x hx
        -- α.support = y :: q_first.support, q_first ⊆ q.support.
        -- q.support ⊆ w'.support. w'.support has same elements as w.support (rotation perm).
        have h1 : x ∈ (Walk.cons h_b q_first).support := hx
        rw [Walk.support_cons, List.mem_cons] at h1
        rcases h1 with rfl | h2
        · -- x = y
          exact hy_mem
        · have : x ∈ q.support := q.support_takeUntil_subset_support hy_in_q h2
          have : x ∈ (Walk.cons h_b q).support := by
            rw [Walk.support_cons]; exact List.mem_cons.mpr (Or.inr this)
          have hxw' : x ∈ w'.support := by rw [hw'_eq]; exact this
          rw [Walk.mem_support_rotate_iff] at hxw'
          exact hxw'
      have hsupp_β : ∀ x ∈ β.support, x ∈ w.support := by
        intro x hx
        have h1 : x ∈ q_rest.support := hx
        have h2 : x ∈ q.support := q.support_dropUntil_subset_support hy_in_q h1
        have : x ∈ (Walk.cons h_b q).support := by
          rw [Walk.support_cons]; exact List.mem_cons.mpr (Or.inr h2)
        have hxw' : x ∈ w'.support := by rw [hw'_eq]; exact this
        rw [Walk.mem_support_rotate_iff] at hxw'
        exact hxw'
      rcases hodd_split with hα_odd | hβ_odd
      · obtain ⟨v', c', hc', hc'_odd, hc'_len, hc'_supp⟩ :=
          ih α.length hα_lt α rfl hα_odd
        refine ⟨v', c', hc', hc'_odd, hc'_len.trans hα_lt.le, ?_⟩
        intro x hx
        exact hsupp_α _ (hc'_supp x hx)
      · obtain ⟨v', c', hc', hc'_odd, hc'_len, hc'_supp⟩ :=
          ih β.length hβ_lt β rfl hβ_odd
        refine ⟨v', c', hc', hc'_odd, hc'_len.trans hβ_lt.le, ?_⟩
        intro x hx
        exact hsupp_β _ (hc'_supp x hx)

/--
For finite induced subgraphs, non-bipartite implies the existence of a short odd cycle
(length at most the number of vertices). The proof: bipartite ↔ all closed walks even
(`two_colorable_iff_forall_loop_even`), so non-bipartite gives an odd closed walk;
then `exists_isCycle_of_odd_closedWalk` extracts an odd cycle of length ≤ walk length;
the cycle's support has nodup tail of size = cycle length, all in `↑X`, hence bounded
by `X.card`.
-/
theorem finite_nonbipartite_induce_has_short_odd_cycle
    {V : Type u}
    (G : SimpleGraph V) (X : Finset V)
    (h : ¬ (G.induce ((↑X : Set V))).IsBipartite) :
    ∃ (v : ((↑X : Set V) : Type u))
      (w : (G.induce ((↑X : Set V))).Walk v v),
        w.IsCycle ∧ Odd w.length ∧ w.length ≤ X.card := by
  classical
  -- Get an odd closed walk in (G.induce ↑X).
  have h2 : ¬ (G.induce ((↑X : Set V))).Colorable 2 := h
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at h2
  push Not at h2
  obtain ⟨u, w, hw_not_even⟩ := h2
  rw [Nat.not_even_iff_odd] at hw_not_even
  -- Apply helper to get an odd cycle.
  obtain ⟨v, c, hcyc, hodd, hlen, hsupp⟩ :=
    exists_isCycle_of_odd_closedWalk w.length w rfl hw_not_even
  refine ⟨v, c, hcyc, hodd, ?_⟩
  -- Bound the length by X.card. The cycle's support tail is nodup of length = c.length,
  -- all elements in ↑X (a Finset of size X.card). So c.length ≤ X.card.
  have htail_nodup : c.support.tail.Nodup := hcyc.support_nodup
  -- c.support.tail has length = c.length.
  have htail_len : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]; omega
  -- The tail elements are all in ↑X.
  -- Map to V via Subtype.val.
  -- We can show the tail.toFinset has size = c.length, embedded in X (as Finset).
  -- toFinset card = length when nodup. And toFinset ⊆ X (the underlying Finset).
  have hsub : (c.support.tail.map (·.val) : List V).toFinset ⊆ X := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact a.property
  have hmap_nodup : (c.support.tail.map (·.val) : List V).Nodup := by
    rw [List.nodup_map_iff_inj_on htail_nodup]
    intros _ _ _ _ heq; exact Subtype.ext heq
  have hcard : (c.support.tail.map (·.val) : List V).toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hmap_nodup, List.length_map, htail_len]
  have : (c.support.tail.map (·.val) : List V).toFinset.card ≤ X.card :=
    Finset.card_le_card hsub
  omega

/-- **Helper.** `(genMyc s G).induce (↑X \ {apex})` is bipartite when
`(G.induce ↑(projFinset X))` is bipartite. This is the `T = ∅` case of
`liftedDeletion_survivor_isBipartite`. -/
private lemma genMyc_induce_diff_apex_isBipartite {V : Type u} [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (X : Finset (MycVerts s V))
    (hbip : (G.induce ((↑(projFinset X) : Set V))).IsBipartite) :
    ((genMyc s G).induce
        ((↑X : Set (MycVerts s V)) \ ({apex s V} : Set (MycVerts s V)))).IsBipartite := by
  classical
  have key := liftedDeletion_survivor_isBipartite G X ∅ (Finset.empty_subset _) (by
    rw [Finset.coe_empty, Set.sdiff_empty]; exact hbip)
  -- Show ↑X \ ↑(liftedDeletion X ∅) = ↑X \ {apex s V}
  have hset : ((↑X : Set (MycVerts s V)) \ (↑(liftedDeletion X ∅) : Set (MycVerts s V)))
      = ((↑X : Set (MycVerts s V)) \ ({apex s V} : Set (MycVerts s V))) := by
    ext a
    simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hX, hND⟩
      refine ⟨hX, ?_⟩
      intro hap
      apply hND
      rw [mem_liftedDeletion]
      exact ⟨hX, Or.inr hap⟩
    · rintro ⟨hX, hap⟩
      refine ⟨hX, ?_⟩
      intro hin
      rw [mem_liftedDeletion] at hin
      obtain ⟨_, h⟩ := hin
      rcases h with ⟨_, _, hT, _⟩ | hap'
      · exact (Finset.notMem_empty _ hT).elim
      · exact hap hap'
  rw [hset] at key
  exact key

/-! ### Helpers used by `finite_oct_profile` -/

/-- The function `m ↦ (g m - 1) / s` is monotone whenever `g` is. -/
private lemma h_monotone {g : ℕ → ℕ} (hg : Monotone g) (s : ℕ) :
    Monotone (fun m => (g m - 1) / s) := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.sub_le_sub_right (hg hab) 1)

/-- The function `m ↦ (g m - 1) / s` tends to infinity whenever `g` does. -/
private lemma h_tendsto {g : ℕ → ℕ} (hg : Tendsto g atTop atTop) {s : ℕ} (hs : 0 < s) :
    Tendsto (fun m => (g m - 1) / s) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro K
  rw [Filter.tendsto_atTop_atTop] at hg
  obtain ⟨N, hN⟩ := hg (s * K + 1)
  refine ⟨N, fun m hm => ?_⟩
  have h := hN m hm
  have h1 : s * K ≤ g m - 1 := by omega
  exact (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; exact h1)

/-- For `r ≥ 2`, the recursive class predicate at `r + 1` follows from a witness at `r`. -/
private lemma IsRecursivelyBuiltMr_succ_of_genMyc {V : Type u} {W : Type u}
    {r : ℕ} (hr : 2 ≤ r)
    {H_inner : SimpleGraph W} {s : ℕ} (hs : 1 ≤ s)
    (h_inner : IsRecursivelyBuiltMr r H_inner)
    {G : SimpleGraph V} (hG_iso : Nonempty (G ≃g genMyc s H_inner)) :
    IsRecursivelyBuiltMr (r + 1) G := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  -- Now `r + 1 = (k + 2) + 1 = k + 3`.
  change IsRecursivelyBuiltMr (k + 3) G
  exact ⟨W, H_inner, s, hs, h_inner, hG_iso⟩

/-- `K₂ = completeGraph (Fin 2)` is bipartite. -/
private lemma completeGraphFin2_isBipartite :
    (completeGraph (Fin 2)).IsBipartite := by
  refine ⟨Coloring.mk id ?_⟩
  intro v w h
  exact h

/-- `(projFinset X).card ≤ X.card`. -/
private lemma projFinset_card_le {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) :
    (projFinset X).card ≤ X.card := by
  classical
  unfold projFinset
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum (s := X) (f := fun a =>
      (match a with | Sum.inl (_, v) => ({v} : Finset V) | Sum.inr () => (∅ : Finset V)).card)
    (g := fun _ => 1) (h := fun a _ => ?_)) ?_
  · match a with
    | Sum.inl (_, v) => simp
    | Sum.inr () => simp
  · simp

/-- **Theorem 4.1 (Finite local oct profile).** For every nondecreasing unbounded
`g : ℕ → ℕ` and every `r ≥ 2`, there exists a finite graph `H` in the recursively
built class `Mᵣ` such that every nonempty induced subgraph `H[X]` satisfies
`oct(H[X]) ≤ g(|X|)`.

In particular `χ(H) = r` (combine `stiebitz_lower_bound` with `genMyc_chromaticNumber_le_succ`).
-/
theorem finite_oct_profile (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := by
  classical
  -- Induction on `r ≥ 2`. The induction motive is parameterized over `g` so the IH
  -- can be applied to a different (rescaled) function in the inductive step.
  induction r, hr using Nat.le_induction generalizing g with
  | base =>
      -- Base: r = 2. Take H := completeGraph (Fin 2).
      refine ⟨Fin 2, inferInstance, inferInstance, completeGraph (Fin 2), ?_, ?_⟩
      · -- IsRecursivelyBuiltMr 2 (completeGraph (Fin 2))
        change Nonempty ((completeGraph (Fin 2)) ≃g (completeGraph (Fin 2)))
        exact ⟨(SimpleGraph.Iso.refl : completeGraph (Fin 2) ≃g completeGraph (Fin 2))⟩
      · -- For every nonempty X, oct K₂ X = 0 ≤ g X.card.
        intro X _hX
        have hK2 : (completeGraph (Fin 2)).IsBipartite := completeGraphFin2_isBipartite
        obtain ⟨c⟩ := hK2
        have hbip : ((completeGraph (Fin 2)).induce
            ((↑X : Set (Fin 2)))).IsBipartite := by
          refine ⟨Coloring.mk (fun a => c a.val) ?_⟩
          intro a b hab
          exact c.valid hab
        have hoct0 : oct (completeGraph (Fin 2)) X = 0 := by
          rw [oct_eq_zero_iff]; exact hbip
        rw [hoct0]; exact Nat.zero_le _
  | succ r hr IH =>
      -- Inductive step: given hypothesis at r, produce a witness at r + 1.
      -- Step 1: choose a threshold N₀ with g m ≥ 1 for m ≥ N₀.
      have hg_top' := hg_top
      rw [Filter.tendsto_atTop_atTop] at hg_top'
      obtain ⟨N₀, hN₀⟩ := hg_top' 1
      -- Step 2: set s := N₀ + 2 (so 2s+1 > N₀ and s ≥ 1).
      set s : ℕ := N₀ + 2 with hs_def
      have hs_pos : 0 < s := by omega
      have hs_ge_one : 1 ≤ s := by omega
      -- Step 3: define h := fun m => (g m - 1) / s.
      set h : ℕ → ℕ := fun m => (g m - 1) / s with hh_def
      have hh_mono : Monotone h := h_monotone hg_mono s
      have hh_top : Tendsto h atTop atTop := h_tendsto hg_top hs_pos
      -- Step 4: apply IH at (h, r).
      obtain ⟨V_inner, _Vfin, _Vdec, G_inner, hRec, hOct_inner⟩ :=
        IH h hh_mono hh_top
      -- Step 5: set H := genMyc s G_inner.
      let H : SimpleGraph (MycVerts s V_inner) := genMyc s G_inner
      refine ⟨MycVerts s V_inner, inferInstance, inferInstance, H, ?_, ?_⟩
      · -- IsRecursivelyBuiltMr (r + 1) H.
        exact IsRecursivelyBuiltMr_succ_of_genMyc hr hs_ge_one hRec
          ⟨(SimpleGraph.Iso.refl : H ≃g H)⟩
      · -- The OCT bound.
        intro X hXne
        set P : Finset V_inner := projFinset X with hP_def
        -- Bound `oct G_inner P` by `h X.card`.
        have hCardP_le : P.card ≤ X.card := projFinset_card_le X
        have hOctP_le_hX : oct G_inner P ≤ h X.card := by
          by_cases hPne : P.Nonempty
          · exact le_trans (hOct_inner P hPne) (hh_mono hCardP_le)
          · -- P = ∅, so oct G_inner P = 0 ≤ h X.card.
            rw [Finset.not_nonempty_iff_eq_empty] at hPne
            rw [hPne]
            simp
        -- Apply Lemma 3.1.
        have hL31 : oct H X ≤ s * oct G_inner P + (if apex s V_inner ∈ X then 1 else 0) :=
          oct_genMyc_le s G_inner X
        by_cases hCase : 1 ≤ g X.card
        · -- Case 1: g X.card ≥ 1.
          -- s * h X.card + 1 ≤ g X.card.
          have hKey : s * h X.card + 1 ≤ g X.card := by
            have : h X.card * s ≤ g X.card - 1 := Nat.div_mul_le_self _ _
            have hge : g X.card ≥ 1 := hCase
            calc s * h X.card + 1 = h X.card * s + 1 := by ring
              _ ≤ (g X.card - 1) + 1 := by omega
              _ = g X.card := by omega
          have hifle : (if apex s V_inner ∈ X then 1 else 0) ≤ 1 := by
            split_ifs <;> simp
          calc oct H X ≤ s * oct G_inner P + (if apex s V_inner ∈ X then 1 else 0) := hL31
            _ ≤ s * h X.card + 1 := by
                refine add_le_add (Nat.mul_le_mul_left s hOctP_le_hX) hifle
            _ ≤ g X.card := hKey
        · -- Case 2: g X.card = 0.
          push Not at hCase
          have hg0 : g X.card = 0 := by omega
          -- From g X.card = 0, deduce X.card < N₀ (else g X.card ≥ 1 would hold).
          have hCardLt : X.card < N₀ := by
            by_contra hcontra
            push Not at hcontra
            have := hN₀ X.card hcontra
            omega
          have hCardLt2s : X.card < 2 * s + 1 := by omega
          -- h X.card = 0 since g X.card = 0.
          have hhX0 : h X.card = 0 := by
            simp [hh_def, hg0]
          -- oct G_inner P ≤ h X.card = 0.
          have hOctP0 : oct G_inner P = 0 := by
            have := hOctP_le_hX
            rw [hhX0] at this
            omega
          -- (G_inner).induce ↑P is bipartite.
          have hPbip : (G_inner.induce ((↑P : Set V_inner))).IsBipartite := by
            rw [← oct_eq_zero_iff]
            exact hOctP0
          -- (genMyc s G_inner).induce (↑X \ {apex}) is bipartite.
          have hHdiffBip :
              (H.induce ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))).IsBipartite :=
            genMyc_induce_diff_apex_isBipartite G_inner X hPbip
          -- Show H.induce ↑X is bipartite.
          suffices hbip : (H.induce ((↑X : Set (MycVerts s V_inner)))).IsBipartite by
            have hoctH0 : oct H X = 0 := by
              rw [oct_eq_zero_iff]; exact hbip
            rw [hoctH0]; exact Nat.zero_le _
          -- Suppose not. Get an odd cycle of length ≤ X.card.
          by_contra hnotbip
          obtain ⟨v, w, hwcycle, hwodd, hwlen⟩ :=
            finite_nonbipartite_induce_has_short_odd_cycle H X hnotbip
          have hwlen2s : w.length < 2 * s + 1 := lt_of_le_of_lt hwlen hCardLt2s
          -- Step A: apex s V_inner ∈ X.
          have hApexInX : apex s V_inner ∈ X := by
            by_contra hapex
            -- If apex ∉ X, then ↑X \ {apex} = ↑X, so the whole induce is bipartite.
            have hsetEq : ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))
                = (↑X : Set (MycVerts s V_inner)) := by
              ext a
              simp only [Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
              refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
              intro hap; subst hap
              exact hapex h
            rw [hsetEq] at hHdiffBip
            exact hnotbip hHdiffBip
          -- Map w through the embedding induce ↑X ↪ H.
          set f : H.induce (↑X : Set (MycVerts s V_inner)) ↪g H := Embedding.induce _ with hf_def
          set wH : H.Walk v.val v.val := Walk.map f.toHom w with hwH_def
          have hwHlen : wH.length = w.length := Walk.length_map f.toHom w
          have hwHsupp : wH.support = w.support.map f := Walk.support_map f.toHom w
          -- Step B: apex must lie on the support of wH (the lifted walk).
          have hApexInSupport : apex s V_inner ∈ wH.support := by
            by_contra hnot
            -- All vertices of wH are in (↑X \ {apex}).
            have hsupp_in : ∀ x ∈ wH.support, x ∈ ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner))) := by
              intro x hx
              rw [hwHsupp, List.mem_map] at hx
              obtain ⟨y, hy_supp, hxy⟩ := hx
              refine ⟨?_, ?_⟩
              · rw [← hxy]
                show f y ∈ (↑X : Set (MycVerts s V_inner))
                exact y.prop
              · intro hap
                apply hnot
                rw [hwHsupp, List.mem_map]
                exact ⟨y, hy_supp, hxy.trans hap⟩
            -- Use Walk.induce to lift wH to a walk in H.induce (↑X \ {apex}).
            let wDiff := wH.induce ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner))) hsupp_in
            -- wDiff has the same length as wH via `map_induce` + `length_map`.
            have hwDifflen : wDiff.length = wH.length := by
              have hmap := Walk.map_induce (s := ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))) wH hsupp_in
              have := congrArg Walk.length hmap
              simp only [Walk.length_map] at this
              exact this
            have hwDifflen' : wDiff.length = w.length := by rw [hwDifflen, hwHlen]
            -- wDiff is a closed walk in a bipartite graph, so it has even length.
            obtain ⟨c⟩ := hHdiffBip
            let c' : (H.induce ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))).Coloring Bool :=
              SimpleGraph.recolorOfEquiv _ finTwoEquiv c
            have heven : Even wDiff.length := (c'.even_length_iff_congr wDiff).mpr Iff.rfl
            rw [hwDifflen'] at heven
            exact (Nat.not_odd_iff_even.mpr heven) hwodd
          -- Step C: rotate wH to start/end at apex.
          set wApex : H.Walk (apex s V_inner) (apex s V_inner) :=
            wH.rotate (apex s V_inner) hApexInSupport with hwApex_def
          -- Length-rotate via the dart-rotation lemma.
          have hwApexlen : wApex.length = wH.length := by
            have hd : wApex.darts ~r wH.darts :=
              Walk.rotate_darts wH (apex s V_inner) hApexInSupport
            have := hd.perm.length_eq
            rw [Walk.length_darts, Walk.length_darts] at this
            exact this
          have hwApexLen2 : wApex.length = w.length := by rw [hwApexlen, hwHlen]
          have hwApexOdd : Odd wApex.length := by rw [hwApexLen2]; exact hwodd
          have hwApexLt : wApex.length < 2 * s + 1 := by rw [hwApexLen2]; exact hwlen2s
          -- Apply Lemma 3.2.
          have := genMyc_oddClosedWalk_through_apex_long hs_ge_one G_inner wApex hwApexOdd
          omega

/-- **Chromatic upper bound for recursively built `Mᵣ`-graphs.** By induction on the
recursive construction: `K₂` has chromatic number `2`, and each `genMyc s` step
contributes at most `+1` to the chromatic number (`genMyc_chromaticNumber_le_succ`).
The matching lower bound `(r : ℕ∞) ≤ G.chromaticNumber` is `stiebitz_lower_bound`,
giving `χ(G) = r` exactly when combined. -/
private lemma chromaticNumber_le_of_isRecursivelyBuiltMr :
    ∀ (r : ℕ) {V : Type u} (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G → G.chromaticNumber ≤ (r : ℕ∞) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro V G hRec
    match r, hRec with
    | 0, h => exact h.elim
    | 1, h => exact h.elim
    | 2, ⟨iso⟩ =>
        -- G ≃g K₂. K₂.chromaticNumber = 2.
        have hK2 : (completeGraph (Fin 2)).chromaticNumber = 2 := by
          rw [chromaticNumber_top]; simp
        have hhom : G →g (completeGraph (Fin 2)) := iso.toHom
        calc G.chromaticNumber ≤ (completeGraph (Fin 2)).chromaticNumber :=
              chromaticNumber_mono_of_hom hhom
          _ = 2 := hK2
          _ = ((2 : ℕ) : ℕ∞) := by norm_cast
    | r + 3, ⟨W, H, s, _hs, hRecH, ⟨iso⟩⟩ =>
        have hH : H.chromaticNumber ≤ ((r + 2 : ℕ) : ℕ∞) :=
          ih (r + 2) (by omega) H hRecH
        have hgM : (genMyc s H).chromaticNumber ≤ ((r + 3 : ℕ) : ℕ∞) := by
          have h1 := genMyc_chromaticNumber_le_succ s H
          calc (genMyc s H).chromaticNumber
              ≤ H.chromaticNumber + 1 := h1
            _ ≤ ((r + 2 : ℕ) : ℕ∞) + 1 := by gcongr
            _ = ((r + 3 : ℕ) : ℕ∞) := by push_cast; ring
        have hhom : G →g (genMyc s H) := iso.toHom
        exact (chromaticNumber_mono_of_hom hhom).trans hgM

/-- **Corollary of `finite_oct_profile` and Stiebitz.** Strengthens `finite_oct_profile`
to additionally assert `G.chromaticNumber = r` exactly. The chromatic-number equality
uses `stiebitz_lower_bound` (lower bound) combined with
`chromaticNumber_le_of_isRecursivelyBuiltMr` (upper bound), so this corollary depends
on the Stiebitz hypothesis. The OCT profile itself does not need that hypothesis. -/
theorem finite_oct_profile_with_chromatic (stiebitz_lower_bound : StiebitzLowerBound)
    (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G ∧
      G.chromaticNumber = (r : ℕ∞) ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := by
  obtain ⟨V, instFin, instDec, G, hRec, hOct⟩ :=
    finite_oct_profile g hg_mono hg_top r hr
  refine ⟨V, instFin, instDec, G, hRec, ?_, hOct⟩
  exact le_antisymm
    (chromaticNumber_le_of_isRecursivelyBuiltMr r G hRec)
    (stiebitz_lower_bound G r hRec)

/-! ## §5. Infinite construction -/

/-! ### Helpers for `infinite_chromatic_local_oct` -/

/-- The rescaled function `gᵣ(m) := g(m) / 2^(r+2)` is monotone whenever `g` is. -/
private lemma g_div_pow_monotone {g : ℕ → ℕ} (hg : Monotone g) (r : ℕ) :
    Monotone (fun m => g m / 2 ^ (r + 2)) := fun _ _ hab =>
  Nat.div_le_div_right (hg hab)

/-- The rescaled function `gᵣ(m) := g(m) / 2^(r+2)` tends to infinity whenever `g` does. -/
private lemma g_div_pow_tendsto {g : ℕ → ℕ} (hg : Tendsto g atTop atTop) (r : ℕ) :
    Tendsto (fun m => g m / 2 ^ (r + 2)) atTop atTop := by
  have hpos : 0 < 2 ^ (r + 2) := Nat.two_pow_pos _
  rw [Filter.tendsto_atTop_atTop]
  intro K
  rw [Filter.tendsto_atTop_atTop] at hg
  obtain ⟨N, hN⟩ := hg (2 ^ (r + 2) * K)
  refine ⟨N, fun m hm => ?_⟩
  have hbig : 2 ^ (r + 2) * K ≤ g m := hN m hm
  exact (Nat.le_div_iff_mul_le hpos).mpr (by rw [Nat.mul_comm]; exact hbig)

/-- Geometric sum bound: `∑_{r ∈ R} n / 2^(r+2) ≤ n`. The total tail of the series
`1/4 + 1/8 + ...` is `1/2 ≤ 1`. -/
private lemma sum_div_two_pow_le (R : Finset ℕ) (n : ℕ) :
    ∑ r ∈ R, n / 2 ^ (r + 2) ≤ n := by
  -- Auxiliary: stronger bound over `Finset.range N`.
  have key : ∀ N : ℕ,
      (∑ r ∈ Finset.range N, n / 2 ^ (r + 2)) + n / 2 ^ (N + 1) ≤ n := by
    intro N
    induction N with
    | zero => simpa using Nat.div_le_self n 2
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have hkey : 2 * (n / 2 ^ (k + 2)) ≤ n / 2 ^ (k + 1) := by
          have h2 : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
          rw [show (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) from by ring]
          rw [Nat.mul_comm, Nat.le_div_iff_mul_le h2, Nat.mul_assoc]
          exact Nat.div_mul_le_self _ _
        have h_sum_add : n / 2 ^ (k + 2) + n / 2 ^ ((k + 1) + 1)
            = 2 * (n / 2 ^ (k + 2)) := by
          have : (k + 1) + 1 = k + 2 := by ring
          rw [this]; ring
        calc (∑ r ∈ Finset.range k, n / 2 ^ (r + 2)) + n / 2 ^ (k + 2)
              + n / 2 ^ ((k + 1) + 1)
            = (∑ r ∈ Finset.range k, n / 2 ^ (r + 2))
                + (n / 2 ^ (k + 2) + n / 2 ^ ((k + 1) + 1)) := by ring
          _ = (∑ r ∈ Finset.range k, n / 2 ^ (r + 2)) + 2 * (n / 2 ^ (k + 2)) := by
                rw [h_sum_add]
          _ ≤ (∑ r ∈ Finset.range k, n / 2 ^ (r + 2)) + n / 2 ^ (k + 1) :=
                Nat.add_le_add_left hkey _
          _ ≤ n := ih
  by_cases hR : R = ∅
  · simp [hR]
  have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hR
  have hsub : R ⊆ Finset.range (R.max' hRne + 1) := by
    intro r hr
    simp only [Finset.mem_range]
    have : r ≤ R.max' hRne := Finset.le_max' R r hr
    omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _)).trans
    (Nat.le_of_add_right_le (key (R.max' hRne + 1)))

/--
**Theorem 1.1 (PDF / paper).** For every nondecreasing unbounded `g : ℕ → ℕ`, there
exists a graph `G` with infinite chromatic number such that every finite induced
subgraph `F` has `oct(F) ≤ g(|V(F)|)`.

The witness is a disjoint union of finite `Hᵣ` from `finite_oct_profile`, each
calibrated against `gᵣ(m) := ⌊g(m) / 2^(r+2)⌋`. The global vertex type is `ℕ × ℕ`,
where component `r` lives at `{r} × Fin (Fintype.card Vᵣ)` (lifted to `ℕ × ℕ`),
and remaining vertices `(r, i)` with `i ≥ card Vᵣ` are isolated.
-/
theorem infinite_chromatic_local_oct (stiebitz_lower_bound : StiebitzLowerBound)
    (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := by
  classical
  -- Step 1. For each `r : ℕ`, extract a per-component graph from `finite_oct_profile`.
  -- We choose data uniformly via `Classical.choose`.
  have mk : ∀ r : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V), IsRecursivelyBuiltMr (r + 2) G ∧
        ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card / 2 ^ (r + 2) := by
    intro r
    exact finite_oct_profile (fun m => g m / 2 ^ (r + 2))
      (g_div_pow_monotone hg_mono r) (g_div_pow_tendsto hg_top r) (r + 2) (by omega)
  choose Vᵣ Vᵣ_fintype Vᵣ_deceq Hᵣ Hᵣ_rec Hᵣ_oct using mk
  -- Equivalence Vᵣ ≃ Fin (card Vᵣ)
  let eᵣ : ∀ r, Vᵣ r ≃ Fin (Fintype.card (Vᵣ r)) := fun r =>
    @Fintype.equivFin (Vᵣ r) (Vᵣ_fintype r)
  -- Step 2. Define the global graph G on ℕ × ℕ.
  let G : SimpleGraph (ℕ × ℕ) := {
    Adj := fun p q => ∃ (r : ℕ) (u v : Vᵣ r),
      p = (r, (eᵣ r u).val) ∧ q = (r, (eᵣ r v).val) ∧ (Hᵣ r).Adj u v
    symm := ⟨by
      rintro p q ⟨r, u, v, hp, hq, hadj⟩
      exact ⟨r, v, u, hq, hp, hadj.symm⟩⟩
    loopless := ⟨by
      rintro p ⟨r, u, v, hp, hq, hadj⟩
      rw [hp] at hq
      have hval : (eᵣ r u).val = (eᵣ r v).val := ((Prod.mk.injEq _ _ _ _).mp hq).2
      have huv : eᵣ r u = eᵣ r v := Fin.eq_of_val_eq hval
      rw [(eᵣ r).injective huv] at hadj
      exact (Hᵣ r).irrefl hadj⟩
  }
  -- Component homomorphism Hᵣ →g G.
  let φᵣ : ∀ r, (Hᵣ r) →g G := fun r => ⟨fun u => (r, (eᵣ r u).val),
    fun {u v} huv => ⟨r, u, v, rfl, rfl, huv⟩⟩
  -- We will use both directions: we also need the inverse of (eᵣ r) restricted to
  -- "vertices at component r in X". For (r, i) with i < card (Vᵣ r), the corresponding
  -- vertex is `(eᵣ r).symm ⟨i, hi⟩`.
  refine ⟨ℕ × ℕ, inferInstance, G, ?_, ?_⟩
  · -- Step 3: prove G.chromaticNumber = ⊤.
    by_contra hne
    have hne' : G.chromaticNumber ≠ ⊤ := hne
    rw [SimpleGraph.chromaticNumber_ne_top_iff_exists] at hne'
    obtain ⟨n, hcol⟩ := hne'
    -- The component Hₙ is colorable with n colors via φₙ.
    have hcolHn : (Hᵣ n).Colorable n := SimpleGraph.Colorable.of_hom (φᵣ n) hcol
    have hbound : ((n + 2 : ℕ) : ℕ∞) ≤ (Hᵣ n).chromaticNumber :=
      stiebitz_lower_bound (Hᵣ n) (n + 2) (Hᵣ_rec n)
    have hcolBound : (Hᵣ n).chromaticNumber ≤ (n : ℕ∞) :=
      hcolHn.chromaticNumber_le
    have habs : ((n + 2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := hbound.trans hcolBound
    -- Contradiction since n + 2 > n.
    have h_lt : (n : ℕ∞) < ((n + 2 : ℕ) : ℕ∞) := by
      have h : n < n + 2 := by omega
      exact_mod_cast h
    exact absurd (lt_of_lt_of_le h_lt habs) (lt_irrefl _)
  · -- Step 4: prove the local OCT bound.
    intro X hXne
    -- For each r ∈ ℕ, define the per-component vertex set and transversal.
    -- Yᵣ r is the set of u : Vᵣ r such that (r, (eᵣ r u).val) ∈ X.
    set Y : ∀ r, Finset (Vᵣ r) := fun r =>
      (Finset.univ : Finset (Vᵣ r)).filter (fun u => (r, (eᵣ r u).val) ∈ X)
      with hY_def
    -- Witness Tᵣ : Finset (Vᵣ r) from oct_witness on Hᵣ.
    let Tdata : ∀ r, { T : Finset (Vᵣ r) // T ⊆ Y r ∧ T.card = oct (Hᵣ r) (Y r) ∧
        ((Hᵣ r).induce ((↑(Y r) : Set (Vᵣ r)) \ ↑T)).IsBipartite } := fun r =>
      ⟨(oct_witness (Hᵣ r) (Y r)).choose,
        ((oct_witness (Hᵣ r) (Y r)).choose_spec)⟩
    set T : ∀ r, Finset (Vᵣ r) := fun r => (Tdata r).1 with hT_def
    have hTsub : ∀ r, T r ⊆ Y r := fun r => (Tdata r).2.1
    have hTcard : ∀ r, (T r).card = oct (Hᵣ r) (Y r) := fun r => (Tdata r).2.2.1
    have hTbip : ∀ r, ((Hᵣ r).induce
        ((↑(Y r) : Set (Vᵣ r)) \ ↑(T r))).IsBipartite := fun r => (Tdata r).2.2.2
    -- The global deletion set: union of liftings of Tᵣ for r ∈ R.
    let R : Finset ℕ := X.image Prod.fst
    let lift : ∀ r, Vᵣ r → ℕ × ℕ := fun r u => (r, (eᵣ r u).val)
    set Tglob : Finset (ℕ × ℕ) :=
      R.biUnion (fun r => (T r).image (lift r))
      with hTglob_def
    -- Tglob ⊆ X.
    have hTglob_sub : Tglob ⊆ X := by
      intro a ha
      rw [hTglob_def, Finset.mem_biUnion] at ha
      obtain ⟨r, _hrR, ha'⟩ := ha
      rw [Finset.mem_image] at ha'
      obtain ⟨u, huT, hu_eq⟩ := ha'
      have huY : u ∈ Y r := hTsub r huT
      rw [hY_def, Finset.mem_filter] at huY
      rw [← hu_eq]; exact huY.2
    -- Tglob.card bounded: each lift fiber is injective, so the biUnion gives the sum.
    have hlift_inj : ∀ r, Function.Injective (lift r) := by
      intro r u v huv
      have hval : (eᵣ r u).val = (eᵣ r v).val := ((Prod.mk.injEq _ _ _ _).mp huv).2
      exact (eᵣ r).injective (Fin.eq_of_val_eq hval)
    have h_lift_disj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ →
        Disjoint ((T r₁).image (lift r₁)) ((T r₂).image (lift r₂)) := by
      intro r₁ _ r₂ _ hne
      rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      rw [Finset.mem_image] at ha₁ ha₂
      obtain ⟨u, _, hu⟩ := ha₁
      obtain ⟨v, _, hv⟩ := ha₂
      rw [← hu] at hv
      exact hne (((Prod.mk.injEq _ _ _ _).mp hv).1).symm
    have hTglob_card : Tglob.card = ∑ r ∈ R, (T r).card := by
      rw [hTglob_def]
      rw [Finset.card_biUnion (fun r₁ hr₁ r₂ hr₂ hne => h_lift_disj r₁ hr₁ r₂ hr₂ hne)]
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.card_image_of_injective _ (hlift_inj r)
    -- Each (T r).card ≤ g X.card / 2^(r+2).
    have hYcard_le_X : ∀ r, (Y r).card ≤ X.card := by
      intro r
      -- The map u ↦ (r, (eᵣ r u).val) sends Y r injectively into X.
      have hinj_card : (Y r).card = ((Y r).image (lift r)).card :=
        (Finset.card_image_of_injective (Y r) (hlift_inj r)).symm
      rw [hinj_card]
      apply Finset.card_le_card
      · intro a ha
        rw [Finset.mem_image] at ha
        obtain ⟨u, huY, huEq⟩ := ha
        rw [hY_def, Finset.mem_filter] at huY
        rw [← huEq]; exact huY.2
    have hTr_le : ∀ r, (T r).card ≤ g X.card / 2 ^ (r + 2) := by
      intro r
      rw [hTcard]
      by_cases hYne : (Y r).Nonempty
      · refine le_trans (Hᵣ_oct r (Y r) hYne) ?_
        exact g_div_pow_monotone hg_mono r (hYcard_le_X r)
      · rw [Finset.not_nonempty_iff_eq_empty] at hYne
        rw [hYne]; simp
    -- Sum bound: ∑ r ∈ R, (T r).card ≤ g X.card.
    have hsum_le : ∑ r ∈ R, (T r).card ≤ g X.card := by
      refine le_trans (Finset.sum_le_sum (fun r _ => hTr_le r)) ?_
      exact sum_div_two_pow_le R (g X.card)
    have hTglob_card_le : Tglob.card ≤ g X.card := by
      rw [hTglob_card]; exact hsum_le
    -- Show survivor (G.induce (↑X \ ↑Tglob)) is bipartite.
    have hsurv_bip :
        (G.induce ((↑X : Set (ℕ × ℕ)) \ (↑Tglob : Set (ℕ × ℕ)))).IsBipartite := by
      classical
      -- Per-component bipartite colorings from `hTbip`.
      let cᵣ : ∀ r, ((Hᵣ r).induce
          ((↑(Y r) : Set (Vᵣ r)) \ ↑(T r))).Coloring (Fin 2) :=
        fun r => Classical.choice (hTbip r)
      -- A "compute" function for a vertex (r, i) ∈ ℕ × ℕ. Returns a Fin 2 if `(r,i)` is in
      -- `X` and `i < card (Vᵣ r)` and the corresponding `Vᵣ r` element is in `Y r \ T r`;
      -- returns 0 otherwise.
      let getColor : ℕ × ℕ → Fin 2 := fun p =>
        if hi : p.2 < Fintype.card (Vᵣ p.1) then
          let u := (eᵣ p.1).symm ⟨p.2, hi⟩
          if hYT : u ∈ Y p.1 ∧ u ∉ T p.1 then
            cᵣ p.1 ⟨u, ⟨hYT.1, hYT.2⟩⟩
          else 0
        else 0
      -- Key fact: getColor (r, (eᵣ r u).val) = cᵣ r ⟨u, _⟩ when u ∈ Y r \ T r.
      have hget_eq : ∀ r (u : Vᵣ r) (huY : u ∈ Y r) (huT : u ∉ T r),
          getColor (r, (eᵣ r u).val) = cᵣ r ⟨u, ⟨huY, huT⟩⟩ := by
        intro r u huY huT
        show getColor (r, (eᵣ r u).val) = cᵣ r ⟨u, ⟨huY, huT⟩⟩
        have hlt : (eᵣ r u).val < Fintype.card (Vᵣ r) := (eᵣ r u).isLt
        -- Compute (eᵣ r).symm at this index — equals u.
        have hsymm : (eᵣ r).symm ⟨(eᵣ r u).val, hlt⟩ = u := by
          conv_rhs => rw [← (eᵣ r).symm_apply_apply u]
        -- Unfold getColor
        change (if hi : (eᵣ r u).val < Fintype.card (Vᵣ r) then
              if hYT : (eᵣ r).symm ⟨(eᵣ r u).val, hi⟩ ∈ Y r ∧
                       (eᵣ r).symm ⟨(eᵣ r u).val, hi⟩ ∉ T r then
                cᵣ r ⟨(eᵣ r).symm ⟨(eᵣ r u).val, hi⟩, ⟨hYT.1, hYT.2⟩⟩
              else 0
            else 0) = cᵣ r ⟨u, ⟨huY, huT⟩⟩
        rw [dif_pos hlt]
        rw [dif_pos (show (eᵣ r).symm ⟨(eᵣ r u).val, hlt⟩ ∈ Y r ∧
                          (eᵣ r).symm ⟨(eᵣ r u).val, hlt⟩ ∉ T r by
                       rw [hsymm]; exact ⟨huY, huT⟩)]
        congr
      let color : ((↑X : Set (ℕ × ℕ)) \ ↑Tglob : Set _) → Fin 2 :=
        fun a => getColor a.val
      refine ⟨Coloring.mk color ?_⟩
      rintro ⟨a, haX, haT⟩ ⟨b, hbX, hbT⟩ hab
      have hGab : G.Adj a b := hab
      obtain ⟨r, u, v, hau, hbv, huv⟩ := hGab
      have ha_eq : a = (r, (eᵣ r u).val) := hau
      have hb_eq : b = (r, (eᵣ r v).val) := hbv
      have huY : u ∈ Y r := by
        rw [hY_def, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← ha_eq]; exact haX
      have hvY : v ∈ Y r := by
        rw [hY_def, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hb_eq]; exact hbX
      have hr_in_R : r ∈ R := by
        change r ∈ X.image Prod.fst
        rw [Finset.mem_image]
        exact ⟨a, haX, by rw [ha_eq]⟩
      have huT : u ∉ T r := by
        intro huT
        apply haT
        rw [hTglob_def]
        rw [Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨r, hr_in_R, ?_⟩
        rw [Finset.mem_image]
        exact ⟨u, huT, ha_eq.symm⟩
      have hvT : v ∉ T r := by
        intro hvT
        apply hbT
        rw [hTglob_def]
        rw [Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨r, hr_in_R, ?_⟩
        rw [Finset.mem_image]
        exact ⟨v, hvT, hb_eq.symm⟩
      -- Compute the colors.
      change getColor a ≠ getColor b
      rw [ha_eq, hb_eq, hget_eq r u huY huT, hget_eq r v hvY hvT]
      exact (cᵣ r).valid (show ((Hᵣ r).induce ((↑(Y r) : Set (Vᵣ r)) \ ↑(T r))).Adj
        ⟨u, ⟨huY, huT⟩⟩ ⟨v, ⟨hvY, hvT⟩⟩ from huv)
    -- Apply oct_le_of_delete.
    exact oct_le_of_delete hTglob_sub hTglob_card_le hsurv_bip

/-! ### Helpers for `erdos_750_independence` -/

/-- A choice of threshold function: for each `k`, picks an `n` such that for every
`m ≥ n`, `(k : NNReal) ≤ f m`.  Existence is guaranteed by `Tendsto f atTop atTop`. -/
private noncomputable def thresholdSeq (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (k : ℕ) : ℕ :=
  (show ∃ n, ∀ m, n ≤ m → (k : NNReal) ≤ f m from
    (Filter.tendsto_atTop_atTop.mp hf) (k : NNReal)).choose

private lemma thresholdSeq_spec (f : ℕ → NNReal) (hf : Tendsto f atTop atTop) (k : ℕ) :
    ∀ m, thresholdSeq f hf k ≤ m → (k : NNReal) ≤ f m :=
  (show ∃ n, ∀ m, n ≤ m → (k : NNReal) ≤ f m from
    (Filter.tendsto_atTop_atTop.mp hf) (k : NNReal)).choose_spec

/-- The minorant: the largest `k ≤ m` for which the threshold `thresholdSeq f hf k`
is already `≤ m`.  By construction, `(g f hf m : NNReal) ≤ f m`, hence
`(g f hf m : ℝ) ≤ 2 * (f m : ℝ)`. -/
private noncomputable def gMinorant (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (m : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => thresholdSeq f hf k ≤ m) m

private lemma gMinorant_le_self (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (m : ℕ) : gMinorant f hf m ≤ m := by
  classical
  unfold gMinorant
  exact Nat.findGreatest_le m

private lemma gMinorant_le_f (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (m : ℕ) : ((gMinorant f hf m : ℕ) : NNReal) ≤ f m := by
  classical
  set k := gMinorant f hf m with hk_def
  by_cases hk : k = 0
  · rw [hk]
    have : ((0 : ℕ) : NNReal) = 0 := by norm_cast
    rw [this]
    exact zero_le
  · have h : thresholdSeq f hf k ≤ m := by
      unfold gMinorant at hk_def
      have := Nat.findGreatest_of_ne_zero (P := fun k => thresholdSeq f hf k ≤ m)
        (n := m) hk_def.symm hk
      exact this
    exact thresholdSeq_spec f hf k m h

private lemma gMinorant_monotone (f : ℕ → NNReal) (hf : Tendsto f atTop atTop) :
    Monotone (gMinorant f hf) := by
  classical
  intro m m' hmm'
  unfold gMinorant
  -- We need: gMinorant m ≤ gMinorant m'.
  set k := Nat.findGreatest (fun k => thresholdSeq f hf k ≤ m) m with hk_def
  by_cases hk : k = 0
  · rw [hk]; exact Nat.zero_le _
  · have hP : thresholdSeq f hf k ≤ m :=
      Nat.findGreatest_of_ne_zero (P := fun k => thresholdSeq f hf k ≤ m)
        (n := m) hk_def.symm hk
    have hkm : k ≤ m := by rw [hk_def]; exact Nat.findGreatest_le m
    have hkm' : k ≤ m' := hkm.trans hmm'
    have hP' : thresholdSeq f hf k ≤ m' := hP.trans hmm'
    exact Nat.le_findGreatest hkm' hP'

private lemma gMinorant_tendsto (f : ℕ → NNReal) (hf : Tendsto f atTop atTop) :
    Tendsto (gMinorant f hf) atTop atTop := by
  classical
  rw [Filter.tendsto_atTop_atTop]
  intro K
  refine ⟨max K (thresholdSeq f hf K), ?_⟩
  intro m hm
  have hKm : K ≤ m := (le_max_left _ _).trans hm
  have hTm : thresholdSeq f hf K ≤ m := (le_max_right _ _).trans hm
  unfold gMinorant
  exact Nat.le_findGreatest hKm hTm

/--
**Corollary 1.2 / The Erdős problem (#750).** For every `f : ℕ → ℝ≥0` with
`f(m) → ∞`, there exists a graph `G` of infinite chromatic number such that every
finite induced subgraph `F` on `m` vertices has an independent set of size at least
`m / 2 - f(m)`.

This is the right-hand side of `formal-conjectures`'
`FormalConjectures/ErdosProblems/750.lean`.
-/
theorem erdos_750_independence (stiebitz_lower_bound : StiebitzLowerBound) :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m / 2 : ℝ) - f m ≤ I.ncard := by
  classical
  intro f hf
  -- Build the integer minorant `g` of `f` and apply `infinite_chromatic_local_oct`.
  obtain ⟨V, _decV, G, hChrom, hOct⟩ :=
    infinite_chromatic_local_oct stiebitz_lower_bound (gMinorant f hf) (gMinorant_monotone f hf)
      (gMinorant_tendsto f hf)
  refine ⟨V, G, hChrom, ?_⟩
  intro m S hm hScard
  -- `S` is finite since `S.ncard = m` with `0 < m`.
  have hSfin : S.Finite := by
    by_contra hSinf
    rw [Set.not_finite] at hSinf
    rw [hSinf.ncard] at hScard
    omega
  -- Convert to Finset.
  set Sfin : Finset V := hSfin.toFinset with hSfin_def
  have hSfin_card : Sfin.card = m := by
    rw [hSfin_def, ← Set.ncard_eq_toFinset_card S hSfin]
    exact hScard
  have hSfin_coe : (↑Sfin : Set V) = S := by
    rw [hSfin_def]; exact hSfin.coe_toFinset
  -- Apply oct_witness on `G` and `Sfin`.
  obtain ⟨T, hTsub, hTcard, hTbip⟩ := oct_witness G Sfin
  -- The OCT bound from Theorem 1.1.
  have hSfin_ne : Sfin.Nonempty := by
    rw [← Finset.card_pos, hSfin_card]; exact hm
  have hOctBound : oct G Sfin ≤ gMinorant f hf m :=
    by have := hOct Sfin hSfin_ne; rw [hSfin_card] at this; exact this
  -- Pick a 2-coloring of the survivor and define the two color classes.
  obtain ⟨c⟩ := hTbip
  -- Survivor vertex set as Finset.
  set Surv : Finset V := Sfin \ T with hSurv_def
  -- Sanity: ↑Surv = (↑Sfin : Set V) \ ↑T
  have hSurv_coe : (↑Surv : Set V) = (↑Sfin : Set V) \ (↑T : Set V) := by
    rw [hSurv_def, Finset.coe_sdiff]
  -- The coloring `c` is on the subtype `(↑Sfin : Set V) \ (↑T : Set V)`. For `v ∈ Surv`,
  -- we need to compute `c ⟨v, _⟩ : Fin 2`.
  -- Define the two color-class Finsets inside `Surv`.
  let class0 : Finset V := Surv.filter (fun v =>
    if h : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) then c ⟨v, h⟩ = 0 else False)
  let class1 : Finset V := Surv.filter (fun v =>
    if h : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) then c ⟨v, h⟩ = 1 else False)
  -- Each vertex of Surv is in exactly one of class0, class1.
  have hclass_partition : class0 ∪ class1 = Surv := by
    apply Finset.ext
    intro v
    simp only [Finset.mem_union, Finset.mem_filter, class0, class1]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      have hvSurv : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
        rw [← hSurv_coe]; exact hv
      -- c ⟨v, hvSurv⟩ : Fin 2 takes value 0 or 1.
      have h2 : c ⟨v, hvSurv⟩ = 0 ∨ c ⟨v, hvSurv⟩ = 1 := by
        have hlt : (c ⟨v, hvSurv⟩).val < 2 := (c ⟨v, hvSurv⟩).isLt
        have : (c ⟨v, hvSurv⟩).val = 0 ∨ (c ⟨v, hvSurv⟩).val = 1 := by
          have := hlt
          omega
        rcases this with hv | hv
        · left
          apply Fin.ext
          show (c ⟨v, hvSurv⟩).val = (0 : Fin 2).val
          rw [hv]; rfl
        · right
          apply Fin.ext
          show (c ⟨v, hvSurv⟩).val = (1 : Fin 2).val
          rw [hv]; rfl
      rcases h2 with h2 | h2
      · left
        refine ⟨hv, ?_⟩
        rw [dif_pos hvSurv]; exact h2
      · right
        refine ⟨hv, ?_⟩
        rw [dif_pos hvSurv]; exact h2
  have hclass_disj : Disjoint class0 class1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    simp only [Finset.mem_filter, class0, class1] at hv0 hv1
    obtain ⟨hv, hc0⟩ := hv0
    obtain ⟨_, hc1⟩ := hv1
    have hvSurv : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
      rw [← hSurv_coe]; exact hv
    rw [dif_pos hvSurv] at hc0 hc1
    have : (0 : Fin 2) = 1 := hc0.symm.trans hc1
    exact absurd this (by decide)
  -- |class0| + |class1| = |Surv|.
  have hclass_card : class0.card + class1.card = Surv.card := by
    rw [← Finset.card_union_of_disjoint hclass_disj, hclass_partition]
  -- One of class0, class1 has size ≥ Surv.card / 2 (and ≥ ⌈Surv.card/2⌉ ≥ Surv.card - Surv.card/2).
  -- Specifically, max(class0.card, class1.card) ≥ Surv.card / 2 (real divide).
  -- Using ℕ-arithmetic: 2 * max(a,b) ≥ a + b, so max ≥ (a+b)/2 (in ℕ, max ≥ (a+b)/2 — and a+b -
  -- max ≥ ... )
  -- Pick the larger one.
  let I_finset : Finset V := if class0.card ≥ class1.card then class0 else class1
  have hI_subset_surv : I_finset ⊆ Surv := by
    by_cases hge : class0.card ≥ class1.card
    · simp only [I_finset, hge, if_true]
      intro v hv
      simp only [Finset.mem_filter, class0] at hv
      exact hv.1
    · simp only [I_finset, hge, if_false]
      intro v hv
      simp only [Finset.mem_filter, class1] at hv
      exact hv.1
  -- I.ncard ≥ Surv.card / 2  (where Surv.card = m - oct G Sfin).
  have hSurv_card : Surv.card = Sfin.card - T.card := by
    rw [hSurv_def, Finset.card_sdiff_of_subset hTsub]
  have hI_card_lb : 2 * I_finset.card ≥ Surv.card := by
    by_cases hge : class0.card ≥ class1.card
    · simp only [I_finset, hge, if_true]
      have : 2 * class0.card ≥ class0.card + class1.card := by
        have h1 : class1.card ≤ class0.card := hge
        omega
      rw [hclass_card] at this
      exact this
    · simp only [I_finset, hge, if_false]
      push Not at hge
      have : 2 * class1.card ≥ class0.card + class1.card := by
        have h1 : class0.card ≤ class1.card := le_of_lt hge
        omega
      rw [hclass_card] at this
      exact this
  -- Define the resulting independent set.
  let I : Set V := (↑I_finset : Set V)
  refine ⟨I, ?_, ?_, ?_⟩
  · -- I ⊆ S
    have hI_sub_Sfin : I_finset ⊆ Sfin := hI_subset_surv.trans Finset.sdiff_subset
    intro v hv
    rw [← hSfin_coe]
    exact hI_sub_Sfin hv
  · -- G.IsIndepSet I
    intro v hv w hw hvw
    simp only [I, Finset.mem_coe] at hv hw
    have hvSurv : v ∈ Surv := hI_subset_surv hv
    have hwSurv : w ∈ Surv := hI_subset_surv hw
    have hvSurvSet : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
      rw [← hSurv_coe]; exact hvSurv
    have hwSurvSet : w ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
      rw [← hSurv_coe]; exact hwSurv
    intro hadj
    -- Same color → not adjacent in G.induce.
    have hadj_induce : (G.induce ((↑Sfin : Set V) \ (↑T : Set V))).Adj
        ⟨v, hvSurvSet⟩ ⟨w, hwSurvSet⟩ := hadj
    -- Both have the same color (call it `i`).
    have hsame_color : c ⟨v, hvSurvSet⟩ = c ⟨w, hwSurvSet⟩ := by
      by_cases hge : class0.card ≥ class1.card
      · -- I = class0, both colored 0
        have hv' : v ∈ class0 := by simp only [I_finset, hge, if_true] at hv; exact hv
        have hw' : w ∈ class0 := by simp only [I_finset, hge, if_true] at hw; exact hw
        simp only [Finset.mem_filter, class0] at hv' hw'
        have hvc : c ⟨v, hvSurvSet⟩ = 0 := by
          have := hv'.2; rw [dif_pos hvSurvSet] at this; exact this
        have hwc : c ⟨w, hwSurvSet⟩ = 0 := by
          have := hw'.2; rw [dif_pos hwSurvSet] at this; exact this
        rw [hvc, hwc]
      · -- I = class1, both colored 1
        have hv' : v ∈ class1 := by simp only [I_finset, hge, if_false] at hv; exact hv
        have hw' : w ∈ class1 := by simp only [I_finset, hge, if_false] at hw; exact hw
        simp only [Finset.mem_filter, class1] at hv' hw'
        have hvc : c ⟨v, hvSurvSet⟩ = 1 := by
          have := hv'.2; rw [dif_pos hvSurvSet] at this; exact this
        have hwc : c ⟨w, hwSurvSet⟩ = 1 := by
          have := hw'.2; rw [dif_pos hwSurvSet] at this; exact this
        rw [hvc, hwc]
    exact c.valid hadj_induce hsame_color
  · -- (m / 2 : ℝ) - f m ≤ I.ncard
    have hI_ncard : (I.ncard : ℝ) = (I_finset.card : ℝ) := by
      simp [I, Set.ncard_coe_finset]
    rw [hI_ncard]
    -- I.card ≥ Surv.card / 2 = (m - oct) / 2 ≥ (m - g m) / 2 ≥ (m - 2 f m) / 2 = m/2 - f m.
    have h_surv : (Surv.card : ℝ) ≤ 2 * (I_finset.card : ℝ) := by
      have h := hI_card_lb
      exact_mod_cast h
    have h_card_eq : Surv.card = m - T.card := by
      rw [hSurv_card, hSfin_card]
    have h_T_le : T.card ≤ gMinorant f hf m := by
      rw [hTcard]; exact hOctBound
    have h_T_le' : T.card ≤ m := h_T_le.trans (gMinorant_le_self f hf m)
    have h_surv_real : (Surv.card : ℝ) = (m : ℝ) - (T.card : ℝ) := by
      rw [h_card_eq]
      push_cast [Nat.cast_sub h_T_le']
      ring
    -- The real bound `gMinorant f hf m ≤ f m`
    have h_gM_le_f : ((gMinorant f hf m : ℕ) : ℝ) ≤ (f m : ℝ) := by
      have h := gMinorant_le_f f hf m
      exact_mod_cast (NNReal.coe_le_coe.mpr h)
    have h_T_real_le : (T.card : ℝ) ≤ (f m : ℝ) := by
      have : (T.card : ℝ) ≤ ((gMinorant f hf m : ℕ) : ℝ) := by exact_mod_cast h_T_le
      exact this.trans h_gM_le_f
    -- Now: 2 * I.card ≥ Surv.card = m - T.card ≥ m - f m, so I.card ≥ (m - f m)/2 = m/2 - f m / 2
    -- ≥ m/2 - f m.
    -- We want (m/2 : ℝ) - f m ≤ I.card.
    -- From 2 I.card ≥ Surv.card = m - T.card ≥ m - f m,
    -- so I.card ≥ (m - f m)/2 = m/2 - f m/2 ≥ m/2 - f m.
    have h_chain : (m : ℝ) - (f m : ℝ) ≤ 2 * (I_finset.card : ℝ) := by
      calc (m : ℝ) - (f m : ℝ)
          ≤ (m : ℝ) - (T.card : ℝ) := by linarith
        _ = (Surv.card : ℝ) := h_surv_real.symm
        _ ≤ 2 * (I_finset.card : ℝ) := h_surv
    -- Now derive m/2 - f m ≤ I_finset.card.
    have h_NN : (0 : ℝ) ≤ (f m : ℝ) := (f m).coe_nonneg
    linarith

/--
**Upstream-shape wrapper** matching `formal-conjectures`'s
[`FormalConjectures/ErdosProblems/750.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/750.lean)
exact syntax: `m / 2 - f m ≤ I.ncard`. With Lean's default elaboration, `f m : ℝ≥0`
forces the subtraction into NNReal, which makes `m / 2` *real division* in NNReal
(`(↑m : ℝ≥0) / 2`), and the subtraction is NNReal-truncated. Implied by the
real-valued form `erdos_750_independence` proved above. -/
theorem erdos_750_independence_FC_form (stiebitz_lower_bound : StiebitzLowerBound) :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : NNReal) / 2 - f m ≤ (I.ncard : NNReal) := by
  intro f hf
  obtain ⟨V, G, hChrom, hWit⟩ := erdos_750_independence stiebitz_lower_bound f hf
  refine ⟨V, G, hChrom, ?_⟩
  intro m S hm hScard
  obtain ⟨I, hI_sub, hI_indep, hI_real⟩ := hWit m S hm hScard
  refine ⟨I, hI_sub, hI_indep, ?_⟩
  -- `hI_real : (m / 2 : ℝ) - f m ≤ I.ncard`. Translate to NNReal-truncated form.
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_sub_def]
  -- Goal: max (((m : NNReal) / 2 : ℝ) - ((f m : NNReal) : ℝ)) 0 ≤ ((I.ncard : NNReal) : ℝ)
  push_cast
  refine max_le ?_ ?_
  · -- (m : ℝ) / 2 - (f m : ℝ) ≤ (I.ncard : ℝ)
    linarith
  · -- 0 ≤ (I.ncard : ℝ)
    exact_mod_cast Nat.zero_le _

/--
**`formal-conjectures` upstream form (`True ↔ ...`).** Discharges
[`FormalConjectures/ErdosProblems/750.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/750.lean)
under `answer := True`. The body matches FC's `erdos_750` essentially literally:
`f : ℕ → ℝ≥0`, `atTop.Tendsto f atTop`, and `m / 2 - f m ≤ I.ncard` elaborates as
`(↑m : ℝ≥0) / 2 - f m` (NNReal real division and truncated subtraction).

The witness is stated in `Type`, as in the imported proof, because its concrete
vertex type is `ℕ × ℕ`.

Forward direction is `erdos_750_independence_FC_form`; backward direction is
trivial. -/
theorem erdos_750_FC (stiebitz_lower_bound : StiebitzLowerBound) :
    True ↔ ∀ (f : ℕ → ℝ≥0) (_hf : atTop.Tendsto f atTop),
      ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ m / 2 - f m ≤ I.ncard :=
  ⟨fun _ => erdos_750_independence_FC_form stiebitz_lower_bound, fun _ => trivial⟩

end Erdos750.Conditional
