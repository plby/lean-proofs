import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.ProfileForest
import ErdosProblems.Erdos550.KovariSosTuran

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# EFRS bipartite tree-Ramsey asymptotic

For fixed positive `a,b`, this module proves the bipartite instance of the
uniform Erdős–Faudree–Rousseau–Schelp asymptotic:

> `R(T, K_{a,b}) = n + o(n)` uniformly over all `n`-vertex trees `T`.

The upper bound follows from the **Kővári–Sós–Turán** bound
`ex(N, K_{a,b}) = o(N²)` combined with the **greedy tree embedding**
`rooted_forest_embedding` (a graph of minimum degree `≥ n − 1` contains every
`n`-vertex tree).  The lower bound is the elementary blow-up construction (red
`K_{n−1}`, blue empty).

The lower bound is the elementary red-clique construction.  The resulting
theorem is `efrs_bipartite`.
-/

open SimpleGraph Finset

namespace Erdos550

/-- A nonempty complete bipartite graph is `2`-chromatic. -/
theorem chromaticNumber_Kbip (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Kbip a b).chromaticNumber = 2 := by
  have h_colorable : (Kbip a b).Colorable 2 := by
    use fun x => x.elim (fun x => 0) (fun x => 1);
    aesop;
  refine' le_antisymm ( h_colorable.chromaticNumber_le ) _;
  refine' le_ciInf fun n => _;
  by_cases hn : (Kbip a b).Colorable n <;> simp_all +decide;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ SimpleGraph.Colorable ];
  · obtain ⟨ f ⟩ := hn;
    exact Fin.elim0 ( f ( Sum.inl ⟨ 0, ha ⟩ ) );
  · obtain ⟨ c ⟩ := hn;
    have := c.valid ( show ( Kbip a b ).Adj ( Sum.inl ⟨ 0, ha ⟩ ) ( Sum.inr ⟨ 0, hb ⟩ ) from by simp +decide [ Kbip ] ) ; simp_all +decide [ Fin.eq_zero ] ;

/-! ## Greedy tree embedding into a high-minimum-degree graph -/

open Classical in
/-- Parent of `v` towards the root `r`: a neighbour of `v` strictly closer to
`r`.  The root (and any vertex with no closer neighbour) maps to `none`. -/
noncomputable def rparent {V : Type*} (T : SimpleGraph V) (r v : V) : Option V :=
  if h : ∃ u, T.Adj v u ∧ T.dist r u < T.dist r v then some h.choose else none

/-- If `rparent T r v = some u` then `u` is a neighbour of `v` strictly closer to
`r`. -/
theorem rparent_adj {V : Type*} (T : SimpleGraph V) (r v u : V)
    (h : rparent T r v = some u) : T.Adj v u ∧ T.dist r u < T.dist r v := by
  classical
  have hex : ∃ w, T.Adj v w ∧ T.dist r w < T.dist r v := by
    by_contra hc
    rw [rparent, dif_neg hc] at h
    exact absurd h (by simp)
  rw [rparent, dif_pos hex] at h
  have hu : hex.choose = u := by simpa using! h
  subst hu
  exact ⟨(hex.choose_spec).1, (hex.choose_spec).2⟩

/-
In a tree, every edge is a parent edge in exactly one direction (towards the
root `r`).
-/
theorem rparent_edge {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (hT : T.IsTree) (r : V) {a b : V} (hab : T.Adj a b) :
    rparent T r a = some b ∨ rparent T r b = some a := by
  by_contra h_contra;
  simp_all +decide [ rparent ];
  grind +suggestions

/-- **Greedy tree embedding.**  A tree `T` on `V` embeds (as a subgraph copy)
into any finite host graph `J` whose minimum degree is at least `|V| − 1`.
Proved by encoding `T` as a rooted forest (parent = the neighbour towards an
arbitrary fixed root) and applying `rooted_forest_embedding`. -/
theorem tree_minDeg_embed {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    {W : Type*} [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj]
    (hcard : Fintype.card V ≤ Fintype.card W)
    (hdeg : ∀ w, Fintype.card V - 1 ≤ J.degree w) : T ⊑ J := by
  classical
  have hne : Nonempty V := hT.1.nonempty
  obtain ⟨r⟩ := hne
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hrank : ∀ a b, rparent T r a = some b → T.dist r b < T.dist r a :=
    fun a b h => (rparent_adj T r a b h).2
  obtain ⟨f, hfinj, hf_root, hf_edge⟩ :=
    rooted_forest_embedding J (rparent T r) (fun v => T.dist r v) hrank hdeg e e.injective
  refine ⟨ SimpleGraph.Copy.mk ⟨f, fun {a b} h => ?_⟩ hfinj ⟩
  rcases rparent_edge hT r h with hpa | hpb
  · exact hf_edge a b hpa
  · exact (hf_edge b a hpb).symm

/-! ## The deletion lemma -/

/-- **Deletion lemma (pure counting).**  If, after removing the set `BAD` of
vertices whose *complement*-degree exceeds `K`, at least `n + K` vertices remain,
then there is a vertex set `S` of size `≥ n` in which every vertex has at least
`n − 1` `J`-neighbours inside `S`. -/
theorem exists_high_minDeg_set {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (n K : ℕ)
    (hbad : (Finset.univ.filter (fun v => K < (Jᶜ).degree v)).card + n + K
              ≤ Fintype.card W) :
    ∃ S : Finset W, n ≤ S.card ∧
      ∀ v ∈ S, n - 1 ≤ ((J.neighborFinset v) ∩ S).card := by
  classical
  set S : Finset W := Finset.univ.filter fun v => K ≥ Jᶜ.degree v with hS
  have hScard : S.card = Fintype.card W
      - (Finset.univ.filter fun v => K < Jᶜ.degree v).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W)) (fun v => K < Jᶜ.degree v)
    have hSeq : S = Finset.univ.filter (fun v => ¬ K < Jᶜ.degree v) := by
      rw [hS]; ext v; simp []
    rw [hSeq]
    simp only [Finset.card_univ] at hpart ⊢
    omega
  refine ⟨ S, by omega, ?_ ⟩
  intro v hv
  have hvmem : K ≥ Jᶜ.degree v := (Finset.mem_filter.mp hv).2
  have hvK : (Jᶜ.neighborFinset v ∩ S).card ≤ K := by
    refine le_trans (Finset.card_le_card (Finset.inter_subset_left)) ?_
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hvmem
  have hcover : S \ {v} ⊆ (J.neighborFinset v ∩ S) ∪ (Jᶜ.neighborFinset v ∩ S) := by
    intro w hw
    have hwS : w ∈ S := (Finset.mem_sdiff.mp hw).1
    have hwv : w ≠ v := by
      intro h; exact (Finset.mem_sdiff.mp hw).2 (by simp [h])
    by_cases hadj : J.Adj v w
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset J v w).mpr hadj, hwS⟩)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨?_, hwS⟩)
      exact (SimpleGraph.mem_neighborFinset Jᶜ v w).mpr
        ((SimpleGraph.compl_adj J v w).mpr ⟨fun h => hwv h.symm, hadj⟩)
  have hunion := Finset.card_union_le (J.neighborFinset v ∩ S) (Jᶜ.neighborFinset v ∩ S)
  have hmono := Finset.card_le_card hcover
  have hsv : (S \ {v}).card = S.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hv]
  omega

/-
The number of vertices of complement-degree `> K`, times `K + 1`, is at most
twice the number of complement-edges.
-/
theorem bad_le_edges {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (K : ℕ) :
    (Finset.univ.filter (fun v => K < J.degree v)).card * (K + 1)
      ≤ 2 * J.edgeFinset.card := by
  have h_sum_degrees : ∑ v ∈ Finset.univ.filter (fun v => K < J.degree v), J.degree v ≤ 2 * J.edgeFinset.card := by
    have := SimpleGraph.sum_degrees_eq_twice_card_edges J;
    exact this ▸ Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ );
  exact le_trans ( by simpa using! Finset.sum_le_sum fun v ( hv : v ∈ Finset.filter ( fun v => K < J.degree v ) Finset.univ ) => Nat.succ_le_of_lt ( Finset.mem_filter.mp hv |>.2 ) ) h_sum_degrees

/-! ## Lower-bound construction -/

/-
`K_{a,b}` (with `a, b ≥ 1`) is not contained in the empty graph.
-/
theorem Kbip_not_contained_bot {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {W : Type*} : ¬ (Kbip a b ⊑ (⊥ : SimpleGraph W)) := by
  rintro ⟨ f, hf ⟩;
  exact absurd ( f.map_adj ( show ( Kbip a b ).Adj ( Sum.inl ⟨ 0, ha ⟩ ) ( Sum.inr ⟨ 0, hb ⟩ ) from by simp +decide [ Kbip ] ) ) ( by simp +decide [  ] )

/-
A tree `T` on `V` is not contained in any graph on fewer than `|V|` vertices.
In particular, on `Fin N` with `N < |V|`, the all-red colouring `⊤` (blue `⊥`)
contains no red `T` and no blue `K_{a,b}`, so `N` does not witness the Ramsey
number.
-/
theorem not_ramseyGood_of_lt {V : Type*} [Fintype V]
    (T : SimpleGraph V) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {N : ℕ} (hN : N < Fintype.card V) :
    N ∉ RamseyGood T (Kbip a b) := by
  -- To show N ∉ RamseyGood, we need to show ∃ G, ¬(T ⊑ G) ∧ ¬(Kbip a b ⊑ Gᶜ).
  -- Take G := (⊤ : SimpleGraph (Fin N)).
  -- Then Gᶜ = ⊥ (compl_top).
  intro hN_mem
  apply absurd (hN_mem ⊤);
  simp +decide [ Erdos550.Kbip_not_contained_bot ha hb ];
  constructor;
  rintro ⟨ f, hf ⟩;
  exact absurd ( Fintype.card_le_of_injective f hf ) ( by simpa using! hN )

/-! ## The bipartite EFRS asymptotic -/

/-- If the red graph `G` on `Fin N` has so few *blue* (complement) edges that,
after deleting the vertices of blue-degree `> K`, at least `n + K` vertices
remain, then `G` contains the `n`-vertex tree `T`. -/
theorem tree_in_red_of_sparse {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (K : ℕ)
    (hbad : (Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card + Fintype.card V + K ≤ N) :
    T ⊑ G := by
  classical
  have hN : Fintype.card (Fin N) = N := Fintype.card_fin N
  obtain ⟨S, hScard, hSdeg⟩ :=
    exists_high_minDeg_set G (Fintype.card V) K (by rw [hN]; exact hbad)
  have hcard : Fintype.card V ≤ Fintype.card (↑S : Set (Fin N)) := by
    have heq : Fintype.card (↑S : Set (Fin N)) = S.card := by simp
    rw [heq]; exact hScard
  have hdeg : ∀ w : (↑S : Set (Fin N)), Fintype.card V - 1 ≤ (G.induce (↑S)).degree w := by
    rintro ⟨v, hv⟩
    rw [induce_degree_eq G S v hv]
    exact hSdeg v hv
  have hsub : T ⊑ G.induce (↑S : Set (Fin N)) := tree_minDeg_embed T hT _ hcard hdeg
  exact hsub.trans ⟨(SimpleGraph.Embedding.induce (↑S : Set (Fin N))).toCopy⟩

set_option maxHeartbeats 800000 in
/-- The witness step: for every tolerance `θ > 0` there is `n₀` so that for every
`n`-vertex tree `T` with `n ≥ n₀` there is `N` with `n ≤ N ≤ (1+θ)n` such that
*every* red/blue colouring of `K_N` contains a red `T` or a blue `K_{a,b}`. -/
theorem efrs_bip_mem (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (θ : ℝ) (hθ : 0 < θ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → Fintype.card V = n →
      ∃ N : ℕ, n ≤ N ∧ (N : ℝ) ≤ (1 + θ) * n ∧ N ∈ RamseyGood T (Kbip a b) := by
  classical
  obtain ⟨NKST, hKST⟩ := kovari_sos_turan a b ha hb ((min θ 1)^2 / 256) (by positivity)
  refine ⟨NKST + Nat.ceil (4 / min θ 1) + 1, fun n hn V _ T hT hcard => ?_⟩
  set t : ℝ := min θ 1 with ht
  have htpos : 0 < t := lt_min hθ one_pos
  have htle1 : t ≤ 1 := min_le_right _ _
  have htleθ : t ≤ θ := min_le_left _ _
  set K : ℕ := ⌊t * n / 2⌋₊ with hK
  have hKle : (K : ℝ) ≤ t * n / 2 := Nat.floor_le (by positivity)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  refine ⟨n + 2 * K, Nat.le_add_right _ _, ?_, ?_⟩
  · push_cast
    nlinarith [hKle, htleθ, hn0, htpos.le]
  · intro G
    by_cases hfree : Kbip a b ⊑ Gᶜ
    · exact Or.inr hfree
    · refine Or.inl ?_
      -- arithmetic: n ≥ 4/t
      have hceil : Nat.ceil (4 / t) ≤ n := by omega
      have hn4t : (4 : ℝ) / t ≤ n :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
      have h4 : (4 : ℝ) ≤ n * t := (div_le_iff₀ htpos).mp hn4t
      have hKge : t * n / 4 ≤ (K : ℝ) := by
        have h1 : t * n / 2 - 1 ≤ (K : ℝ) := le_of_lt (Nat.sub_one_lt_floor _)
        nlinarith [h1, h4]
      have hNle2n : ((n + 2 * K : ℕ) : ℝ) ≤ 2 * n := by
        push_cast; nlinarith [hKle, htle1, hn0, htpos.le]
      have hN0 : (0 : ℝ) ≤ ((n + 2 * K : ℕ) : ℝ) := by positivity
      -- KST edge bound
      have hNcard : NKST ≤ Fintype.card (Fin (n + 2 * K)) := by
        rw [Fintype.card_fin]; omega
      have hedge : (Gᶜ.edgeFinset.card : ℝ)
          ≤ (t ^ 2 / 256) * (Fintype.card (Fin (n + 2 * K)) : ℝ) ^ 2 :=
        hKST Gᶜ hfree hNcard
      rw [Fintype.card_fin] at hedge
      -- bad-vertex counting
      have hbe : (Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card * (K + 1)
          ≤ 2 * Gᶜ.edgeFinset.card := bad_le_edges (W := Fin (n + 2 * K)) Gᶜ K
      have hbeR : ((Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card : ℝ) * (K + 1)
          ≤ 2 * (t ^ 2 / 256) * ((n : ℝ) + 2 * K) ^ 2 := by
        have hbe' : ((Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card : ℝ) * (K + 1)
            ≤ 2 * (Gᶜ.edgeFinset.card : ℝ) := by exact_mod_cast hbe
        have hcast : ((n + 2 * K : ℕ) : ℝ) = (n : ℝ) + 2 * K := by push_cast; ring
        rw [hcast] at hedge
        nlinarith [hbe', hedge]
      -- the key inequality 2εN² ≤ K(K+1)
      have hAsq : ((n : ℝ) + 2 * K) ^ 2 ≤ (2 * n) ^ 2 := by
        have := hNle2n; push_cast at this
        nlinarith [this, hN0, (by push_cast at hN0; linarith : (0:ℝ) ≤ (n:ℝ) + 2 * K)]
      have hKsq : (t * n / 4) ^ 2 ≤ (K : ℝ) ^ 2 := by
        have hKge0 : (0 : ℝ) ≤ t * n / 4 := by positivity
        nlinarith [hKge, hKge0]
      have hKK : 2 * (t ^ 2 / 256) * ((n : ℝ) + 2 * K) ^ 2 ≤ (K : ℝ) * (K + 1) := by
        have hc : (0 : ℝ) ≤ 2 * (t ^ 2 / 256) := by positivity
        have hstep1 : 2 * (t ^ 2 / 256) * ((n : ℝ) + 2 * K) ^ 2
            ≤ 2 * (t ^ 2 / 256) * (2 * n) ^ 2 := mul_le_mul_of_nonneg_left hAsq hc
        have hmid : 2 * (t ^ 2 / 256) * (2 * (n : ℝ)) ^ 2 ≤ (t * n) ^ 2 / 16 := by
          nlinarith [sq_nonneg (t * n)]
        have hKsq' : (t * n) ^ 2 / 16 ≤ (K : ℝ) ^ 2 := by nlinarith [hKsq]
        have hKK1 : (K : ℝ) ^ 2 ≤ (K : ℝ) * (K + 1) := by nlinarith [hk0]
        linarith [hstep1, hmid, hKsq', hKK1]
      have hbadle : ((Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card : ℝ) ≤ K := by
        have hpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
        have hchain : ((Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card : ℝ) * (K + 1)
            ≤ (K : ℝ) * (K + 1) := le_trans hbeR hKK
        exact le_of_mul_le_mul_right (by linarith [hchain]) hpos
      have hbadleN : (Finset.univ.filter (fun v => K < (Gᶜ).degree v)).card ≤ K := by
        exact_mod_cast hbadle
      apply tree_in_red_of_sparse T hT G K
      rw [hcard]
      omega

theorem efrs_bipartite (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (θ : ℝ) (hθ : 0 < θ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → Fintype.card V = n →
      |(ramsey T (Kbip a b) : ℝ) - n| ≤ θ * n := by
  obtain ⟨n₀, h⟩ := efrs_bip_mem a b ha hb θ hθ
  refine ⟨n₀, fun n hn V _ T hT hcard => ?_⟩
  obtain ⟨N, hnN, hNle, hmem⟩ := h n hn T hT hcard
  have hup : ramsey T (Kbip a b) ≤ N := ramsey_le_of_mem _ _ hmem
  have hne : (RamseyGood T (Kbip a b)).Nonempty := ⟨N, hmem⟩
  have hmem' : ramsey T (Kbip a b) ∈ RamseyGood T (Kbip a b) := ramsey_mem _ _ hne
  have hlow : n ≤ ramsey T (Kbip a b) := by
    by_contra hlt
    push_neg at hlt
    have hlt' : ramsey T (Kbip a b) < Fintype.card V := by rw [hcard]; exact hlt
    exact not_ramseyGood_of_lt T ha hb hlt' hmem'
  rw [abs_le]
  have hlowR : (n : ℝ) ≤ ramsey T (Kbip a b) := by exact_mod_cast hlow
  have hupR : (ramsey T (Kbip a b) : ℝ) ≤ N := by exact_mod_cast hup
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · nlinarith [mul_nonneg hθ.le hn0]
  · nlinarith [hNle, hupR]

end Erdos550
