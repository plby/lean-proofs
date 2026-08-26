-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Calibration

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Consequences of the classification (§ "Compatibility" and Problem #1177(2))

This file collects the remaining stated results of arXiv:2606.24882 that follow
from the classification (`thm:classification`), the exact-spectrum dichotomy
(`thm:spectrum`) and the external interface theorems.  In particular it discharges
**Problem #1177 part (2)** (`cor:intro-1177`(2)), the only headline assertion that
uses the Hajnal–Komjáth input **E5** (the linearly obligatory loose `7`-cycle).

Everything here is `sorry`-free modulo the carried literature inputs E2–E5.
-/

open Cardinal

namespace Erdos1177

universe u

/-! ### The system `G` = two triples sharing a pair -/

/-- `G` = **two triples sharing a pair**: vertices `{0,1,2,3}`, edges
`{0,1,2}` and `{0,1,3}`.  It is nonlinear (the two edges meet in `{0,1}`). -/
def twoTriplesSharingPair : FTS where
  V := Fin 4
  edges := {{0, 1, 2}, {0, 1, 3}}
  card3 := by decide

/-- `twoTriplesSharingPair` is nonlinear. -/
theorem twoTriples_not_linear : ¬ twoTriplesSharingPair.Linear := by
  unfold FTS.Linear twoTriplesSharingPair
  decide

/-- Being nonlinear, `G` is not in `B`. -/
theorem not_bclass_twoTriples : ¬ Bclass twoTriplesSharingPair :=
  fun h => twoTriples_not_linear (bclass_intrinsic h).1

/-
**A nonlinear triple-system host contains two triples sharing a pair.**  If a
triple system `K` is not linear, then `twoTriplesSharingPair` embeds into it.
-/
theorem twoTriples_embeds_of_not_linear {W : Type u} (K : Hypergraph W)
    (htri : K.IsTripleSystem) (hnl : ¬ K.Linear) :
    twoTriplesSharingPair.Embeds K := by
  contrapose! hnl; simp_all +decide [ Hypergraph.Linear ] ;
  contrapose! hnl; simp_all +decide [ twoTriplesSharingPair, FTS.Embeds ] ;
  obtain ⟨e₁, he₁, e₂, he₂, hne, hcap⟩ := hnl
  obtain ⟨a, b, hab⟩ : ∃ a b : W, a ≠ b ∧ a ∈ e₁ ∧ b ∈ e₁ ∧ a ∈ e₂ ∧ b ∈ e₂ := by
    obtain ⟨ a, ha, b, hb, hab ⟩ := hcap; use a, b; aesop;
  obtain ⟨c, hc⟩ : ∃ c : W, c ∈ e₁ ∧ c ∉ ({a, b} : Set W) := by
    have := htri e₁ he₁; rw [ Set.ncard_eq_three ] at this; obtain ⟨ x, y, z, h ⟩ := this; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
    grind +ring
  obtain ⟨d, hd⟩ : ∃ d : W, d ∈ e₂ ∧ d ∉ ({a, b} : Set W) := by
    have := htri e₂ he₂; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
    exact Exists.imp ( by aesop ) ( Set.exists_of_ssubset ( lt_of_le_of_ne ( Set.insert_subset hab.2.2.2.1 ( Set.singleton_subset_iff.mpr hab.2.2.2.2 ) ) ( Ne.symm <| by aesop ) ) )
  use ![a, b, c, d];
  have h_card : e₁.ncard = 3 ∧ e₂.ncard = 3 := by
    exact ⟨ htri e₁ he₁, htri e₂ he₂ ⟩
  have h_eq : e₁ = {a, b, c} ∧ e₂ = {a, b, d} := by
    have h_eq : ∀ {s : Set W}, s.ncard = 3 → ∀ {x y z : W}, x ∈ s → y ∈ s → z ∈ s → x ≠ y → x ≠ z → y ≠ z → s = {x, y, z} := by
      intros s hs x y z hx hy hz hxy hxz hyz; rw [ Set.ncard_eq_three ] at hs; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := hs; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
      grind +qlia;
    grind
  simp_all +decide [ Set.ncard_eq_toFinset_card' ];
  simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def, Function.Injective, Fin.forall_fin_succ ];
  simp_all +decide [ Set.image_insert_eq, Set.image_singleton ];
  grind +ring

/-! ### The loose `7`-cycle is not in `B` -/

/-- The natural odd (length-`7`) Berge cycle of the loose `7`-cycle, with
point-nodes `x_i = Sum.inl i` and hyperedge-nodes `e_i = {x_i, x_{i+1}, y_i}`. -/
noncomputable def looseCycle7_bergeCycle : BergeCycle looseCycle7 where
  m := 7
  hm := by norm_num
  v := fun i => Sum.inl i
  e := fun i => ⟨{Sum.inl i, Sum.inl (i + 1), Sum.inr i}, by
    simp only [looseCycle7, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨i, rfl⟩⟩
  vinj := fun a b h => Sum.inl_injective h
  einj := by
    intro a b h
    simp only [Subtype.mk.injEq] at h
    have hmem : (Sum.inr a : Fin 7 ⊕ Fin 7) ∈
        ({Sum.inl b, Sum.inl (b + 1), Sum.inr b} : Finset (Fin 7 ⊕ Fin 7)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact Sum.inr_injective h1
  mem_left := by intro i; simp
  mem_right := by intro i; simp

/-- Having an odd Berge cycle, the loose `7`-cycle is not in `B`. -/
theorem not_bclass_looseCycle7 : ¬ Bclass looseCycle7 := by
  intro h
  have : Even (looseCycle7_bergeCycle).m := (bclass_intrinsic h).2.2 looseCycle7_bergeCycle
  exact (by decide : ¬ Even 7) this

/-! ### Erdős Problem #1177, part (2) -/

/-- **Erdős Problem #1177, part (2)** (`cor:intro-1177`(2)).  There are finite
triple systems `G, H` for which both `F_G(ℵ₁)` and `F_H(ℵ₁)` are nonempty but
their intersection is empty: no exact-`ℵ₁`-chromatic triple system is
simultaneously `G`-free and `H`-free.  We take `G` = two triples sharing a pair
and `H` = the loose `7`-cycle.

The nonemptiness of each family is the spectrum dichotomy applied to the
non-`B` systems `G` and `H`; the empty intersection follows because every
uncountably chromatic triple system is either nonlinear (hence contains `G`) or
linear (hence contains `H = C_7^{(3)}` by the Hajnal–Komjáth input **E5**). -/
theorem problem_1177_part2 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K := by
  refine ⟨twoTriplesSharingPair, looseCycle7, ?_, ?_, ?_⟩
  · exact ((spectrum_dichotomy_of_E3 hexp h3 hE2 twoTriplesSharingPair
      (Order.succ ℵ₀)).mpr ⟨not_bclass_twoTriples, Order.lt_succ _⟩).2
  · exact ((spectrum_dichotomy_of_E3 hexp h3 hE2 looseCycle7
      (Order.succ ℵ₀)).mpr ⟨not_bclass_looseCycle7, Order.lt_succ _⟩).2
  · rintro ⟨W, K, htri, hchr, hGf, hHf⟩
    have huc : K.UncountablyChromatic := hchr.2 ℵ₀ (Order.lt_succ _)
    by_cases hlin : K.Linear
    · exact hHf (hE5 K htri hlin huc)
    · exact hGf (twoTriples_embeds_of_not_linear K htri hlin)

/-! ### Obstruction trichotomy (`cor:obstruction-trichotomy`) -/

/-- **Obstruction trichotomy** (`cor:obstruction-trichotomy`).  A finite triple
system `F` fails to lie in `B` if and only if exactly one of the following
sequentially exclusive alternatives holds for its isolated-vertex reduction
`F° = F.reduce`:

* (i) `F°` is nonlinear;
* (ii) `F°` is linear but some hyperedge-node has no incident bridge;
* (iii) `F°` is linear, every hyperedge-node has an incident bridge, and `F°`
  has an odd Berge cycle.

The alternatives are mutually exclusive since each later one includes the
negations of the earlier ones.  This is the De Morgan expansion of the finite
bridge decomposition `prop:finite-decomposition`. -/
theorem obstruction_trichotomy (F : FTS) :
    ¬ Bclass F ↔
      (¬ F.reduce.Linear) ∨
      (F.reduce.Linear ∧ ∃ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
          ∀ w ∈ ed.1, ¬ IsBridgeInc F.reduce w ed) ∨
      (F.reduce.Linear ∧
          (∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
            ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed) ∧
          ∃ c : BergeCycle F.reduce, ¬ Even c.m) := by
  rw [not_congr (finiteDecomposition_holds F), FTS.IntrinsicObligatory]
  constructor
  · intro h
    by_cases hL : F.reduce.Linear
    · by_cases hB : ∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
          ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed
      · refine Or.inr (Or.inr ⟨hL, hB, ?_⟩)
        by_contra hc; push_neg at hc; exact h ⟨hL, hB, hc⟩
      · push_neg at hB; exact Or.inr (Or.inl ⟨hL, hB⟩)
    · exact Or.inl hL
  · rintro (h | ⟨hL, ed, hed⟩ | ⟨hL, _, c, hc⟩) ⟨hLin, hBr, hEv⟩
    · exact h hLin
    · obtain ⟨w, hw, hb⟩ := hBr ed; exact hed w hw hb
    · exact hc (hEv c)

/-! ### Compatibility with the known theory (`cor:compatibility`) -/

/-- A finite triple system is **strongly tripartite** if its vertex set can be
partitioned into three classes so that every edge meets each class exactly once. -/
def FTS.StronglyTripartite (F : FTS) : Prop :=
  ∃ col : F.V → Fin 3, ∀ e ∈ F.edges, ∀ i : Fin 3, (e.filter (fun v => col v = i)).card = 1

/-- Edgeless systems are (vacuously) strongly tripartite. -/
theorem stronglyTripartite_edgeless {F : FTS} (h : F.edges = ∅) : F.StronglyTripartite := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he; rw [h] at he; exact absurd he (Finset.notMem_empty e)

/-
Strong tripartiteness transfers across isomorphism.
-/
theorem stronglyTripartite_iso {F G : FTS} (h : FTS.Iso F G)
    (hF : F.StronglyTripartite) : G.StronglyTripartite := by
  rcases h with ⟨ φ, hφ ⟩;
  obtain ⟨ colF, hcolF ⟩ := hF;
  refine' ⟨ fun w => colF ( φ.symm w ), fun e he => _ ⟩;
  intro i; specialize hcolF ( Finset.map φ.symm.toEmbedding e ) ; simp_all +decide [ Finset.filter_map ] ;
  convert! hcolF _ i using 1;
  convert! he using 1 ; ext ; aesop

/-
The private-vertex expansion of a `2`-colourable graph is strongly
tripartite: the two colour classes of `J` and the private vertices form the
three classes.
-/
theorem stronglyTripartite_expansion {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] (hJ : J.Colorable 2) :
    (graphExpansion J).StronglyTripartite := by
  obtain ⟨ f, hf ⟩ := hJ;
  refine' ⟨ _, _ ⟩;
  exact fun x => x.elim ( fun x => Fin.castSucc ( f x ) ) fun x => 2;
  intro e he i; rcases expansion_edge_cases J he with ⟨ a, rfl ⟩ ; simp +decide [ Finset.filter_insert, Finset.filter_singleton ] ;
  have := Quot.out_eq ( a : Sym2 VJ ) ; ( rcases h' : Quot.out ( a : Sym2 VJ ) with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.eq_swap ] ; );
  grind +suggestions

/-
Strong tripartiteness is preserved under disjoint union.
-/
theorem stronglyTripartite_disjUnion {F G : FTS}
    (hF : F.StronglyTripartite) (hG : G.StronglyTripartite) :
    (F.disjUnion G).StronglyTripartite := by
  -- Obtain colorings for F and G from hF and hG.
  obtain ⟨colF, hcolF⟩ := hF
  obtain ⟨colG, hcolG⟩ := hG;
  refine' ⟨ fun v => v.elim ( fun v => colF v ) fun v => colG v, _ ⟩;
  intro e he i; unfold FTS.disjUnion at he; simp_all +decide [ Finset.filter_map ] ;
  rcases he with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ Finset.filter_map ];
  · convert! hcolF a ha i using 1;
  · convert! hcolG a ha i using 1

/-
Strong tripartiteness is preserved under one-point amalgamation: permute the
three class names in one factor so the two identified points lie in
corresponding classes.
-/
theorem stronglyTripartite_amalgamate {F G : FTS} (x : F.V) (y : G.V)
    (hF : F.StronglyTripartite) (hG : G.StronglyTripartite) :
    (F.amalgamate G x y).StronglyTripartite := by
  -- Choose a permutation `π : Equiv.Perm (Fin 3)` with `π (colG y) = colF x`.
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 3), π (hG.choose y) = hF.choose x := by
    exact ⟨ Equiv.swap ( hG.choose y ) ( hF.choose x ), by simp +decide ⟩;
  refine' ⟨ fun v => v.elim ( fun a => hF.choose a ) fun b => π ( hG.choose b.1 ), _ ⟩ ; simp +decide [ FTS.amalgamate ];
  rintro e ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) i <;> simp_all +decide [ Finset.filter_map ];
  · convert! hF.choose_spec a ha i using 1;
  · convert! hG.choose_spec a ha ( π.symm i ) using 1;
    congr! 1;
    grind

/-- **Every member of `B` is strongly tripartite.**  (`cor:compatibility`(1),
induction on the construction of `B`.) -/
theorem bclass_stronglyTripartite {F : FTS} (h : Bclass F) : F.StronglyTripartite := by
  induction h with
  | edgeless F hF => exact stronglyTripartite_edgeless hF
  | expansion J hJ => exact stronglyTripartite_expansion J hJ
  | iso hiso _ ih => exact stronglyTripartite_iso hiso ih
  | union _ _ ihF ihG => exact stronglyTripartite_disjUnion ihF ihG
  | amalg x y _ _ ihF ihG => exact stronglyTripartite_amalgamate x y ihF ihG

/-- **Compatibility (1): every obligatory finite triple system is strongly
tripartite.**  (`cor:compatibility`(1); this recovers Komjáth's necessary
condition.) -/
theorem obligatory_stronglyTripartite (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  bclass_stronglyTripartite ((classification_of_E3 hexp h3 hE2 F).1.mp hobl)

/-- **Compatibility (4): the loose cycle `C_7^+ = C_7^{(3)}` is linearly
obligatory but not obligatory.**  (`cor:compatibility`(4).)  Linear obligatoriness
is the Hajnal–Komjáth input **E5**; non-obligatoriness is `not_bclass_looseCycle7`
transported across the classification. -/
theorem C7_linearlyObligatory_not_obligatory (hexp : ReiherExpansion.{u})
    (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 := by
  refine ⟨hE5, fun hobl => ?_⟩
  exact not_bclass_looseCycle7 ((classification_of_E3 hexp h3 hE2 looseCycle7).1.mp hobl)

/-! ### Compatibility (3): `C_n^+` is obligatory iff `n` is even -/

/-
For odd `n ≥ 3`, the private-vertex cycle expansion `C_n^+` has an odd Berge
cycle (the `n`-cycle running through its core vertices).
-/
theorem cycleExpansion_oddBergeCycle (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ c : BergeCycle (graphExpansion (SimpleGraph.cycleGraph n)), ¬ Even c.m := by
  obtain ⟨ k, rfl ⟩ : ∃ k, n = k + 3 := ⟨ n - 3, by omega ⟩;
  refine' ⟨ _, _ ⟩;
  use k + 3, by omega;
  exact fun i => Sum.inl i;
  use fun i => ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_attach _ ⟨ s(i, i + 1), by
    simp +decide [ SimpleGraph.cycleGraph, SimpleGraph.mem_edgeSet ] ⟩ ) ⟩
  all_goals generalize_proofs at *;
  · exact Sum.inl_injective;
  · intro i j hij; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    cases hij.2 <;> simp_all +decide [ add_assoc ];
  · intro i; have := Quot.out_eq ( s(i, i + 1) : Sym2 ( ZMod ( k + 3 ) ) ) ; simp_all +decide [ Sym2.eq_swap ] ;
    have := Quot.out_eq ( s(i, i + 1) : Sym2 ( ZMod ( k + 3 ) ) ) ; rw [ Sym2.eq_iff ] at this; aesop;
  · intro i; have := Quot.out_eq ( s(i, i + 1) : Sym2 ( ZMod ( k + 3 ) ) ) ; simp_all +decide [ Sym2.eq_swap ] ;
    have := Quot.out_eq ( s(i, i + 1) : Sym2 ( ZMod ( k + 3 ) ) ) ; rcases h' : Quot.out ( s(i, i + 1) : Sym2 ( ZMod ( k + 3 ) ) ) with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
    lia;
  · exact hodd.elim fun m hm => by simp +decide [ hm ] ;

/-- **Compatibility (3): for every `n ≥ 3`, the private-vertex cycle expansion
`C_n^+` is obligatory if and only if `n` is even.**  (`cor:compatibility`(3).)  If
`n` is even, `C_n` is bipartite, so `C_n^+` is a generator of `B` and hence
obligatory; if `n` is odd, `C_n^+` has an odd Berge cycle, so it is not in `B` and
hence not obligatory. -/
theorem cycleExpansion_obligatory_iff (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (n : ℕ) (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n := by
  constructor
  · intro hobl
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨c, hc⟩ := cycleExpansion_oddBergeCycle n hn hodd
    have hB : Bclass (graphExpansion (SimpleGraph.cycleGraph n)) :=
      (classification_of_E3 hexp h3 hE2 _).1.mp hobl
    exact hc ((bclass_intrinsic hB).2.2 c)
  · intro heven
    have hcol : (SimpleGraph.cycleGraph n).Colorable 2 := by
      have := (SimpleGraph.cycleGraph.bicoloring_of_even n heven).colorable
      simpa using! this.mono (by norm_num)
    have hB : Bclass (graphExpansion (SimpleGraph.cycleGraph n)) :=
      Bclass.expansion (SimpleGraph.cycleGraph n) hcol
    intro W H htri huc
    exact bclass_obligatory hexp _ hB H htri huc

/-! ### Compatibility (2): finite triple-system forests are obligatory -/

/-- Union of all edges of rank strictly below `ed`. -/
def lowerRankUnion (F : FTS) (rank : {e : Finset F.V // e ∈ F.edges} → ℕ)
    (ed : {e : Finset F.V // e ∈ F.edges}) : Finset F.V :=
  (Finset.univ.filter (fun ed' : {e : Finset F.V // e ∈ F.edges} => rank ed' < rank ed)).sup
    (fun ed' => ed'.1)

/-- A finite triple system is a **forest** if its edges admit a rank order in
which every edge meets the union of the lower-ranked edges in at most one vertex
(the running-intersection condition of `cor:compatibility`). -/
def FTS.Forest (F : FTS) : Prop :=
  ∃ rank : {e : Finset F.V // e ∈ F.edges} → ℕ, Function.Injective rank ∧
    ∀ ed : {e : Finset F.V // e ∈ F.edges}, (ed.1 ∩ lowerRankUnion F rank ed).card ≤ 1

/-
A forest is linear: any two distinct edges meet in at most one vertex.
-/
theorem forest_linear {F : FTS} (h : F.Forest) : F.Linear := by
  obtain ⟨ rank, hrank₁, hrank₂ ⟩ := h; intro e₁ he₁ e₂ he₂ hne; have := hrank₁; simp_all +decide [ FTS.Linear ] ;
  -- Without loss of generality, assume `rank ⟨e₁, he₁⟩ < rank ⟨e₂, he₂⟩`.
  wlog hlt : rank ⟨e₁, he₁⟩ < rank ⟨e₂, he₂⟩ generalizing e₁ e₂;
  · grind +suggestions;
  · refine' le_trans _ ( hrank₂ e₂ he₂ );
    refine' Finset.card_le_card _;
    simp +decide [ Finset.subset_iff, lowerRankUnion ];
    exact fun x hx₁ hx₂ => ⟨ hx₂, e₁, ⟨ he₁, hlt ⟩, hx₁ ⟩

/-
A forest has no Berge cycle: the maximal-rank edge of a putative Berge cycle
would meet the union of the lower-ranked edges in its two cycle vertices.
-/
theorem forest_no_bergeCycle {F : FTS} (h : F.Forest) (c : BergeCycle F) : False := by
  obtain ⟨ rank, hrank₁, hrank₂ ⟩ := h;
  -- Choose `a : ZMod c.m` maximizing `fun i => rank (c.e i)`.
  obtain ⟨a, ha⟩ : ∃ a : ZMod c.m, ∀ i : ZMod c.m, rank (c.e i) ≤ rank (c.e a) := by
    haveI := Fact.mk ( show 1 < c.m from by linarith [ c.hm ] );
    simpa using! Finset.exists_max_image Finset.univ ( fun i => rank ( c.e i ) ) ⟨ 0, Finset.mem_univ 0 ⟩;
  -- Consider the two neighbours `a - 1` and `a + 1`.
  have h_neighbours : rank (c.e (a - 1)) < rank (c.e a) ∧ rank (c.e (a + 1)) < rank (c.e a) := by
    have h_neighbours : c.e (a - 1) ≠ c.e a ∧ c.e (a + 1) ≠ c.e a := by
      haveI := Fact.mk ( show 1 < c.m from by linarith [ c.hm ] ) ; simp +decide [ sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg, c.einj.eq_iff ] ;
    exact ⟨ lt_of_le_of_ne ( ha _ ) ( hrank₁.ne h_neighbours.1 ), lt_of_le_of_ne ( ha _ ) ( hrank₁.ne h_neighbours.2 ) ⟩;
  -- Therefore `c.e (a-1)` and `c.e (a+1)` lie in `Finset.univ.filter (fun ed' => rank ed' < rank ed)`, so their underlying edge sets are `⊆ lowerRankUnion F rank ed`.
  have h_subset : (c.e (a - 1)).1 ⊆ lowerRankUnion F rank (c.e a) ∧ (c.e (a + 1)).1 ⊆ lowerRankUnion F rank (c.e a) := by
    exact ⟨ Finset.subset_iff.mpr fun x hx => Finset.mem_sup.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_neighbours.1 ⟩, hx ⟩, Finset.subset_iff.mpr fun x hx => Finset.mem_sup.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_neighbours.2 ⟩, hx ⟩ ⟩;
  have h_card : 2 ≤ ( ( c.e a ).1 ∩ lowerRankUnion F rank ( c.e a ) ).card := by
    refine' Finset.one_lt_card.mpr ⟨ c.v a, _, c.v ( a + 1 ), _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact ⟨ c.mem_left a, h_subset.1 ( by simpa using! c.mem_right ( a - 1 ) ) ⟩;
    · exact ⟨ c.mem_right a, h_subset.2 ( c.mem_left _ ) ⟩;
    · haveI := Fact.mk ( show 1 < c.m from by linarith [ c.hm ] ) ; exact c.vinj.ne ( by simp +decide [ ZMod.natCast_eq_natCast_iff' ] ) ;
  linarith [ hrank₂ ( c.e a ) ]

/-- A forest satisfies the intrinsic obligatoriness condition: it is linear,
every hyperedge-node has an incident bridge (there being no Berge cycles at all),
and every Berge cycle is even (vacuously). -/
theorem forest_intrinsic {F : FTS} (h : F.Forest) : F.IntrinsicObligatory := by
  refine ⟨forest_linear h, ?_, ?_⟩
  · intro ed
    have hcard : ed.1.card = 3 := F.card3 ed.1 ed.2
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < ed.1.card)
    exact ⟨w, hw, hw, fun hcyc => forest_no_bergeCycle h hcyc.choose⟩
  · intro c; exact (forest_no_bergeCycle h c).elim

/-- **Compatibility (2): every finite triple-system forest is obligatory.**
(`cor:compatibility`(2).)  A forest lies in `B` (its running-intersection order
builds it from single triples by disjoint unions and one-point amalgamations),
so it is obligatory. -/
theorem forest_obligatory (hexp : ReiherExpansion.{u}) {F : FTS} (h : F.Forest) :
    FTS.Obligatory.{u} F := by
  have hB : Bclass F := intrinsic_bclass F (forest_intrinsic h)
  intro W H htri huc
  exact bclass_obligatory hexp _ hB H htri huc

end Erdos1177
