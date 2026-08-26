-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.AmalgHelpers

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Closure of obligatory triple systems under one-point amalgamation

This file proves `lem:obligatory-closure` (the one-point amalgamation part):
if `F` and `G` are obligatory finite triple systems, then so is their one-point
amalgamation `F.amalgamate G x y`.

The proof is elementary apart from the de Bruijn–Erdős compactness theorem
(`Erdos1177.colorable_of_forall_finite`) and the finite-graph degeneracy
colouring toolkit in `ErdosProblems.Erdos1177.AmalgHelpers`.
-/

open Cardinal SimpleGraph

namespace Erdos1177

universe u

/-
**Amalgam embedding from two copies meeting only at the glue point.**  If a
copy `f` of `F` and a copy `g` of `G` in a host `H` satisfy `f x = g y` and their
images meet *only* at that point, then the amalgamation `F.amalgamate G x y`
embeds into `H`.
-/
theorem amalgamate_embeds_of_copies {W : Type u} {H : Hypergraph W} {F G : FTS}
    (x : F.V) (y : G.V)
    (f : F.V → W) (hf : Function.Injective f) (hfe : ∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges)
    (g : G.V → W) (hg : Function.Injective g) (hge : ∀ e ∈ G.edges, g '' (↑e : Set G.V) ∈ H.edges)
    (hglue : f x = g y)
    (hmeet : ∀ a b, f a = g b → a = x ∧ b = y) :
    (F.amalgamate G x y).Embeds H := by
  refine' ⟨ fun v => Sum.elim f ( fun b => g b.1 ) v, _, _ ⟩ <;> simp +decide;
  · intro a b hab;
    cases a <;> cases b <;> simp_all +decide [ hf.eq_iff, hg.eq_iff ]; all_goals grind;
  · -- By definition of amalgamation, we can split the goal into two cases: when the edge is from F and when it is from G.
    intro e he
    simp [FTS.amalgamate] at he;
    rcases he with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp +decide [ *, Finset.map_eq_image ];
    · convert! hfe a ha using 1 ; ext ; aesop;
    · convert! hge a ha using 1;
      grind

/-- **Rerouting isolated vertices.**  Any copy `g` of `G` can be modified, keeping
its values on non-isolated vertices (hence on all edges), so that the images of
the isolated vertices avoid a prescribed finite set `Avoid` and the non-isolated
images, while remaining injective. -/
theorem reroute_isolated {W : Type u} [Infinite W] {G : FTS} (g : G.V → W)
    (hg : Function.Injective g) (Avoid : Set W) (hAvoid : Avoid.Finite) :
    ∃ g' : G.V → W, Function.Injective g' ∧
      (∀ b, ¬ G.Isolated b → g' b = g b) ∧
      (∀ b, G.Isolated b → g' b ∉ Avoid ∧ g' b ∉ g '' {b' : G.V | ¬ G.Isolated b'}) := by
  classical
  set Bad : Set W := Avoid ∪ g '' {b' : G.V | ¬ G.Isolated b'} with hBad_def
  have hBad : Bad.Finite := Set.Finite.union hAvoid (Set.Finite.image _ (Set.toFinite _))
  have hcompl : Set.Infinite (Set.univ \ Bad) := Set.infinite_univ.diff hBad
  obtain ⟨iso, hiso_inj, hiso_mem⟩ :
      ∃ iso : {b : G.V // G.Isolated b} → W, Function.Injective iso ∧ ∀ t, iso t ∉ Bad := by
    obtain ⟨t, ht₁, ht₂⟩ := hcompl.exists_subset_card_eq (Nat.card {b : G.V // G.Isolated b})
    have hfin : Fintype {b : G.V // G.Isolated b} := Set.Finite.fintype (Set.toFinite _)
    have e : {b : G.V // G.Isolated b} ≃ (t : Type _) :=
      Fintype.equivOfCardEq (by rw [Fintype.card_coe, ht₂, Nat.card_eq_fintype_card])
    refine ⟨fun s => (e s : W), ?_, ?_⟩
    · exact Subtype.val_injective.comp e.injective
    · intro s; exact (ht₁ (Finset.mem_coe.mpr (e s).2)).2
  refine ⟨fun b => if h : G.Isolated b then iso ⟨b, h⟩ else g b, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : G.Isolated a <;> by_cases hb : G.Isolated b
    · simp only [dif_pos ha, dif_pos hb] at hab
      exact congrArg Subtype.val (hiso_inj hab)
    · simp only [dif_pos ha, dif_neg hb] at hab
      exact absurd (Set.mem_union_right _ (Set.mem_image_of_mem g hb)) (hab ▸ hiso_mem ⟨a, ha⟩)
    · simp only [dif_neg ha, dif_pos hb] at hab
      exact absurd (Set.mem_union_right _ (Set.mem_image_of_mem g ha)) (hab.symm ▸ hiso_mem ⟨b, hb⟩)
    · simp only [dif_neg ha, dif_neg hb] at hab
      exact hg hab
  · intro b hb; simp only [dif_neg hb]
  · intro b hb
    simp only [dif_pos hb]
    exact ⟨fun hA => hiso_mem ⟨b, hb⟩ (Set.mem_union_left _ hA),
      fun hI => hiso_mem ⟨b, hb⟩ (Set.mem_union_right _ hI)⟩

/-- The set of host vertices that can serve as the image of the root `x` in a
copy of `F` (the set `B` of the paper's proof). -/
def RootSetF {W : Type u} (H : Hypergraph W) (F : FTS) (x : F.V) : Set W :=
  {v | ∃ f : F.V → W, Function.Injective f ∧
    (∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges) ∧ f x = v}

/-- If the root `x` is non-isolated, the complement of the root set carries no
copy of `F`. -/
theorem rootSetF_compl_Ffree {W : Type u} (H : Hypergraph W) {F : FTS} (x : F.V)
    (hx : ¬ F.Isolated x) : ¬ F.Embeds (H.restrict (RootSetF H F x)ᶜ) := by
  rintro ⟨g, hg_inj, hg_e⟩
  obtain ⟨e0, he0, hxe0⟩ : ∃ e ∈ F.edges, x ∈ e := by
    by_contra hc; push_neg at hc; exact hx hc
  have hmem := hg_e e0 he0
  have hsub : g '' (↑e0 : Set F.V) ⊆ (RootSetF H F x)ᶜ := hmem.2
  have hgx : g x ∈ g '' (↑e0 : Set F.V) := ⟨x, Finset.mem_coe.mpr hxe0, rfl⟩
  have hgxB : g x ∈ RootSetF H F x := ⟨g, hg_inj, fun e he => (hg_e e he).1, rfl⟩
  exact (hsub hgx) hgxB

/-
**Each colour class is `G`-free.**  If the glue root `y` is non-isolated, `C`
is contained in the root set `B`, each `v ∈ C` carries a chosen copy `K v` of `F`
rooted at `v`, and no non-root vertex of `K v` lies in `C`, then a copy of `G`
in `C` combined with `K v` would produce a copy of the amalgam — impossible when
`H` is amalgam-free.  Hence `C` carries no copy of `G`.
-/
theorem class_Gfree {W : Type u} [Infinite W] {H : Hypergraph W}
    {F G : FTS} {x : F.V} {y : G.V} (hy : ¬ G.Isolated y)
    (hcon : ¬ (F.amalgamate G x y).Embeds H)
    (K : W → F.V → W)
    (hKinj : ∀ v ∈ RootSetF H F x, Function.Injective (K v))
    (hKe : ∀ v ∈ RootSetF H F x, ∀ e ∈ F.edges, (K v) '' (↑e : Set F.V) ∈ H.edges)
    (hKx : ∀ v ∈ RootSetF H F x, K v x = v)
    (C : Set W) (hCB : C ⊆ RootSetF H F x)
    (hdisj : ∀ v ∈ C, ∀ a : F.V, a ≠ x → K v a ∉ C) :
    ¬ G.Embeds (H.restrict C) := by
  contrapose! hcon;
  obtain ⟨g, hg_inj, hg_e⟩ := hcon;
  obtain ⟨v, hvC⟩ : ∃ v ∈ C, g y = v := by
    simp_all +decide [ Hypergraph.restrict ];
    simp_all +decide [ FTS.Isolated ];
    exact hg_e _ hy.choose_spec.1 |>.2 hy.choose_spec.2;
  obtain ⟨g', hg'inj, hg'0, hg'1⟩ : ∃ g' : G.V → W, Function.Injective g' ∧ (∀ b, ¬ G.Isolated b → g' b = g b) ∧ (∀ b, G.Isolated b → g' b ∉ Set.range (K v) ∧ g' b ∉ g '' {b' : G.V | ¬ G.Isolated b'}) := by
    apply reroute_isolated g hg_inj (Set.range (K v)) (Set.finite_range _);
  apply amalgamate_embeds_of_copies x y (K v) (hKinj v (hCB hvC.left)) (hKe v (hCB hvC.left)) g' hg'inj (by
  intro e he
  have h_image : g' '' (↑e : Set G.V) = g '' (↑e : Set G.V) := by
    ext w; simp;
    constructor <;> rintro ⟨ x, hx, rfl ⟩ <;> use x <;> simp_all +decide [ FTS.Isolated ];
    · rw [ hg'0 x e he hx ];
    · exact hg'0 x e he hx
  rw [h_image]
  exact (hg_e e he).1) (by
  rw [ hKx v ( hCB hvC.1 ), hg'0 y hy, hvC.2 ]) (by
  intro a b hab;
  by_cases hb : G.Isolated b <;> simp_all +decide;
  have h_contra : g b ∈ C := by
    obtain ⟨ e, he ⟩ := not_forall.mp hb;
    simp +zetaDelta at *;
    exact hg_e e he.1 |>.2 ( Set.mem_image_of_mem _ he.2 );
  grind +suggestions)

/-- **Amalgamation closure, main case.**  If the two glue roots are non-isolated,
the one-point amalgamation of obligatory systems is obligatory. -/
theorem amalgamate_obligatory_of_nonisolated {F G : FTS} (x : F.V) (y : G.V)
    (hx : ¬ F.Isolated x) (hy : ¬ G.Isolated y)
    (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  intro W H htri huc
  by_contra hcon
  haveI : Infinite W := huc.infinite htri
  classical
  refine huc ?_
  -- Chosen copies of `F` rooted at each vertex of the root set.
  have hKex : ∀ v : ↑(RootSetF H F x), ∃ f : F.V → W, Function.Injective f ∧
      (∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges) ∧ f x = v.1 := fun v => v.2
  choose K0 hK0inj hK0e hK0x using hKex
  set K : W → F.V → W := fun w => if h : w ∈ RootSetF H F x then K0 ⟨w, h⟩ else (fun _ => w)
    with hKdef
  have hKinj : ∀ v ∈ RootSetF H F x, Function.Injective (K v) := by
    intro v hv; simp only [hKdef, dif_pos hv]; exact hK0inj ⟨v, hv⟩
  have hKe : ∀ v ∈ RootSetF H F x, ∀ e ∈ F.edges, (K v) '' (↑e : Set F.V) ∈ H.edges := by
    intro v hv e he; simp only [hKdef, dif_pos hv]; exact hK0e ⟨v, hv⟩ e he
  have hKx : ∀ v ∈ RootSetF H F x, K v x = v := by
    intro v hv; simp only [hKdef, dif_pos hv]; exact hK0x ⟨v, hv⟩
  -- Auxiliary graph and its out-orientation.
  set d : ℕ := Fintype.card F.V - 1 with hddef
  set out : W → Finset W := fun v =>
    if v ∈ RootSetF H F x then (Finset.univ.image (K v)).erase v else ∅ with houtdef
  have hout : ∀ v, (out v).card ≤ d := by
    intro v; simp only [houtdef]
    by_cases hv : v ∈ RootSetF H F x
    · rw [if_pos hv]
      have hvmem : v ∈ Finset.univ.image (K v) :=
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hKx v hv⟩
      have hcard : (Finset.univ.image (K v)).card = Fintype.card F.V := by
        rw [Finset.card_image_of_injective _ (hKinj v hv), Finset.card_univ]
      rw [Finset.card_erase_of_mem hvmem, hcard]
    · rw [if_neg hv]; simp
  set D : SimpleGraph W := SimpleGraph.fromRel (fun v w => w ∈ out v) with hDdef
  have hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w := by
    intro v w h; rw [hDdef, SimpleGraph.fromRel_adj] at h; exact h.2
  haveI : DecidableRel D.Adj := fun _ _ => Classical.dec _
  obtain ⟨χ, hχ⟩ := colorable_of_out D d out hout hcov
  -- Partition the host into the complement of the root set and the colour classes.
  set part : W → Option (Fin (2 * d + 1)) :=
    fun w => if h : w ∈ RootSetF H F x then some (χ w) else none with hpartdef
  apply colorableBy_of_finite_parts H part
  intro i
  cases i with
  | none =>
    have hset : part ⁻¹' {none} = (RootSetF H F x)ᶜ := by
      ext w
      simp only [hpartdef, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
      by_cases h : w ∈ RootSetF H F x <;> simp [h]
    rw [hset]
    exact restrict_colorable_of_obligatory htri hF (rootSetF_compl_Ffree H x hx)
  | some c =>
    have hmemCc : ∀ w, w ∈ part ⁻¹' {some c} ↔ ∃ h : w ∈ RootSetF H F x, χ w = c := by
      intro w
      simp only [hpartdef, Set.mem_preimage, Set.mem_singleton_iff]
      by_cases hb : w ∈ RootSetF H F x
      · simp only [dif_pos hb, Option.some.injEq]; exact ⟨fun h => ⟨hb, h⟩, fun h => h.2⟩
      · simp only [dif_neg hb]; exact ⟨fun h => absurd h (by simp), fun h => h.elim (fun hh => absurd hh hb)⟩
    have hCcB : part ⁻¹' {some c} ⊆ RootSetF H F x := fun w hw => ((hmemCc w).mp hw).choose
    have hdisj : ∀ v ∈ part ⁻¹' {some c}, ∀ a : F.V, a ≠ x → K v a ∉ part ⁻¹' {some c} := by
      intro v hv a ha hKva
      obtain ⟨hvB, hvc⟩ := (hmemCc v).mp hv
      obtain ⟨hwB, hwc⟩ := (hmemCc _).mp hKva
      have hne : K v a ≠ v := fun h => ha (hKinj v hvB (by rw [h, hKx v hvB]))
      have hadj : D.Adj v (K v a) := by
        rw [hDdef, SimpleGraph.fromRel_adj]
        refine ⟨Ne.symm hne, Or.inl ?_⟩
        simp only [houtdef, if_pos hvB, Finset.mem_erase]
        exact ⟨hne, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
      have hcol := hχ v (K v a) hadj
      rw [hvc, hwc] at hcol
      exact hcol rfl
    exact restrict_colorable_of_obligatory htri hG
      (class_Gfree hy hcon K hKinj hKe hKx (part ⁻¹' {some c}) hCcB hdisj)

/-
**Symmetry of one-point amalgamation.**
-/
theorem amalgamate_symm_iso {F G : FTS} (x : F.V) (y : G.V) :
    FTS.Iso (F.amalgamate G x y) (G.amalgamate F y x) := by
  -- Construct the equivalence map `φ : (F.amalgamate G x y).V ≃ (G.amalgamate F y x).V` by swapping the roles of `F` and `G`.
  let φ : (F.V ⊕ {b : G.V // b ≠ y}) ≃ (G.V ⊕ {a : F.V // a ≠ x}) :=
    { toFun := fun v => match v with
      | Sum.inl a => if h : a = x then Sum.inl y else Sum.inr ⟨a, h⟩
      | Sum.inr ⟨b, hb⟩ => Sum.inl b,
      invFun := fun v => match v with
      | Sum.inl b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩
      | Sum.inr ⟨a, ha⟩ => Sum.inl a,
      left_inv := by
        grind,
      right_inv := by
        grind +qlia };
  all_goals generalize_proofs at *;
  refine' ⟨ φ, fun e => _ ⟩;
  constructor <;> intro he <;> simp_all +decide [ FTS.amalgamate ];
  · rcases he with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ );
    · right;
      simp +decide [ Finset.map_map, Function.Embedding.inl ];
      grind +suggestions;
    · left;
      use a;
      simp +decide [ Finset.map_map ];
      refine' ⟨ ha, Finset.map_injective _ _ ⟩;
      exact F.V ⊕ { b : G.V // ¬b = y };
      exact ⟨ fun v => φ.symm v, φ.symm.injective ⟩;
      ext; simp [φ];
      congr! 2;
      split_ifs <;> simp +decide [ * ];
  · rcases he with ( ⟨ a, ha, he ⟩ | ⟨ a, ha, he ⟩ );
    · refine' Or.inr ⟨ a, ha, _ ⟩;
      convert! congr_arg ( Finset.map ( show ( G.V ⊕ { a // a ≠ x } ) ↪ ( F.V ⊕ { b // b ≠ y } ) from ⟨ φ.symm, by
                                        exact φ.symm.injective ⟩ ) ) he using 1
      generalize_proofs at *;
      · ext; simp [φ];
      · simp +decide [Finset.map_map]
    · left;
      use a;
      simp +decide [ Finset.ext_iff ] at he ⊢;
      refine' ⟨ ha, _, _ ⟩;
      · intro b; specialize he; have := he.2 b; by_cases hb : b = x <;> simp_all +decide ;
        · convert! he.1 y using 1;
          · grind;
          · simp +decide [ φ ];
        · convert! he.2 b hb using 1;
          grind;
      · intro b hb; specialize he; have := he.1 b; simp_all +decide [ φ ] ;
        specialize he ; replace he := he.1 b ; aesop

/-
**Amalgamation closure, isolated-root case.**  If the root `x` is isolated in
`F`, the amalgamation of obligatory systems is obligatory.
-/
theorem amalgamate_obligatory_of_isolated {F G : FTS} (x : F.V) (y : G.V)
    (hx : F.Isolated x) (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  intro W H htri huc;
  obtain ⟨g, hg_inj, hg_e⟩ := hG H htri huc;
  haveI : Infinite W := huc.infinite htri
  set v := g y
  set S := Set.range g
  have hS : S.Finite := Set.finite_range g;
  -- Restriction of H off `S`: The hypergraph `H1 := ⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩` is uncountably chromatic by `restrict_uc htri huc hS` (this lemma is now available), and a triple system by `fun e he => htri e he.1`.
  set H1 : Hypergraph W := ⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩
  have hH1_uc : H1.UncountablyChromatic := by
    convert! restrict_uc htri huc hS using 1
  have hH1_tri : H1.IsTripleSystem := by
    exact fun e he => htri e he.1;
  -- Copy of F in H1: `obtain ⟨f0, hf0_inj, hf0_e⟩ := hF H1 hH1_tri hH1_uc`; for `e ∈ F.edges`, `hf0_e e he` gives `f0 '' ↑e ∈ H.edges` (`.1`) and `f0 '' ↑e ⊆ Sᶜ` (`.2`).
  obtain ⟨f0, hf0_inj, hf0_e⟩ := hF H1 hH1_tri hH1_uc;
  -- Reroute isolated vertices of `f0` off `S`: `obtain ⟨f1, hf1_inj, hf1_0, hf1_1⟩ := reroute_isolated f0 hf0_inj S hS`, where `hf1_0 : ∀ a, ¬ F.Isolated a → f1 a = f0 a` and `hf1_1 : ∀ a, F.Isolated a → f1 a ∉ S ∧ f1 a ∉ f0 '' {a' | ¬ F.Isolated a'}`.
  obtain ⟨f1, hf1_inj, hf1_0, hf1_1⟩ := reroute_isolated f0 hf0_inj S hS;
  have hf1_avoid : ∀ a, f1 a ∉ S := by
    intro a; by_cases ha : F.Isolated a <;> simp_all +decide ;
    obtain ⟨ e, he ⟩ := not_forall.mp ha;
    exact fun h => by have := hf0_e e ( by tauto ) |>.2 ( Set.mem_image_of_mem _ ( by tauto : a ∈ e ) ) ; aesop;;
  have hf1_e : ∀ e ∈ F.edges, f1 '' (↑e : Set F.V) ∈ H.edges := by
    intro e he
    have h_image : f1 '' (↑e : Set F.V) = f0 '' (↑e : Set F.V) := by
      ext w;
      constructor <;> rintro ⟨ a, ha, rfl ⟩;
      · by_cases ha' : F.Isolated a <;> simp_all +decide;
        · exact False.elim ( ha' e he ha );
        · exact ⟨ a, ha, rfl ⟩;
      · by_cases ha' : F.Isolated a <;> simp_all +decide [ Set.image ];
        · exact False.elim ( ha' e he ha );
        · exact ⟨ a, ha, hf1_0 a ha' ⟩;
    exact h_image.symm ▸ hf0_e e he |>.1;
  apply amalgamate_embeds_of_copies x y (Function.update f1 x v) (by
  intro a b hab;
  grind) (by
  intro e he
  have h_image : (Function.update f1 x v) '' (↑e : Set F.V) = f1 '' (↑e : Set F.V) := by
    have h_image : ∀ a ∈ e, a ≠ x := by
      exact fun a ha => by rintro rfl; exact hx e he ha;
    exact Set.image_congr fun a ha => by rw [ Function.update_of_ne ( h_image a ha ) ] ;
  rw [h_image]
  exact hf1_e e he) g hg_inj hg_e (by
  grind +splitImp) (by
  grind +qlia)

/-- **Closure of obligatory triple systems under one-point amalgamation**
(`lem:obligatory-closure`). -/
theorem amalgamate_obligatory {F G : FTS} (x : F.V) (y : G.V)
    (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  by_cases hx : F.Isolated x
  · exact amalgamate_obligatory_of_isolated x y hx hF hG
  · by_cases hy : G.Isolated y
    · exact obligatory_iso (amalgamate_symm_iso y x)
        (amalgamate_obligatory_of_isolated y x hy hG hF)
    · exact amalgamate_obligatory_of_nonisolated x y hx hy hF hG

end Erdos1177
