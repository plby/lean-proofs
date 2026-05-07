/-
# Erdős Problem 923

For every `n` there exists `f(n)` such that any graph `G` with `χ(G) ≥ f(n)`
has a triangle-free subgraph `H` with `χ(H) ≥ n`.

## Reference

Vojtěch Rödl (1977), "On the chromatic number of subgraphs of a given graph",
_Proceedings of the AMS_ Volume 64, Number 2, pp. 370-371.
-/
import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false

namespace Rodl

open SimpleGraph

/-! ## Zykov's Proposition (Product Coloring)

If two graphs G₁, G₂ on V are p-colorable and q-colorable respectively,
then G₁ ⊔ G₂ is (p*q)-colorable. The proof uses the product coloring:
map v to (c₁(v), c₂(v)) ∈ Fin p × Fin q ≃ Fin (p*q). -/

theorem colorable_sup {V : Type*} {G₁ G₂ : SimpleGraph V} {p q : ℕ}
    (h₁ : G₁.Colorable p) (h₂ : G₂.Colorable q) :
    (G₁ ⊔ G₂).Colorable (p * q) := by
  -- Use the product coloring: define f(v) = finProdFinEquiv (c₁ v, c₂ v) : Fin (p*q).
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  exact ⟨fun v ↦ finProdFinEquiv (c₁ v, c₂ v), by aesop⟩

/-- Generalized product coloring for `Fin k`-indexed families of graphs. -/
theorem colorable_iSup_fin {V : Type*} {c : ℕ} :
    ∀ {k : ℕ} {G : Fin k → SimpleGraph V},
    (∀ i, (G i).Colorable c) → (⨆ i, G i).Colorable (c ^ k) := fun {k G} hG ↦ by
  induction k with
  | zero => exact ⟨fun _ ↦ 0, by simp⟩
  | succ k ih =>
    convert colorable_sup (hG (Fin.last k)) (ih fun i ↦ hG (Fin.castSucc i)) using 1
    · ext v w; simp [Fin.exists_iff]
      exact ⟨fun ⟨i, hi, h⟩ ↦
        if hi' : i = k then Or.inl (by simpa [hi'] using h) else Or.inr ⟨i, hi.lt_of_ne hi', h⟩,
        fun h ↦ h.elim (fun h ↦ ⟨k, le_rfl, h⟩) fun ⟨i, hi, h⟩ ↦ ⟨i, hi.le, h⟩⟩
    · rw [pow_succ']

/-! ## Definition of φ(m,n)

The function φ(m,n) from Rödl's proof:
- φ(2, n) = 2
- φ(m+1, n) = (n-1)^(φ(m,n)-1) + 1 for m ≥ 2
-/

def phi : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | 2, _ => 2
  | m + 3, n => (n - 1) ^ (phi (m + 2) n - 1) + 1

@[simp] lemma phi_two (n : ℕ) : phi 2 n = 2 := rfl

lemma phi_succ (m n : ℕ) (hm : 2 ≤ m) : phi (m + 1) n = (n - 1) ^ (phi m n - 1) + 1 := by
  match m, hm with
  | 2, _ => rfl
  | m + 3, _ => rfl

/-! ## Left Neighborhood

Given a graph G on a linearly ordered type V, the left neighborhood L(v,G)
is the induced subgraph on {w : V | w < v ∧ G.Adj w v}. -/

section LeftNeighborhood
variable {V : Type*} [LinearOrder V]

/-- The left neighborhood of v in G: the induced subgraph on vertices w < v adjacent to v. -/
def leftNbhd (G : SimpleGraph V) (v : V) : SimpleGraph {w : V // w < v ∧ G.Adj w v} :=
  G.induce _

/-- If G is (m+1)-clique-free then every left neighborhood is m-clique-free. -/
theorem leftNbhd_cliqueFree {G : SimpleGraph V} {v : V} {m : ℕ}
    (hcf : G.CliqueFree (m + 1)) :
    (leftNbhd G v).CliqueFree m := fun T hT ↦ by
  apply hcf (Finset.image Subtype.val T ∪ {v})
  simp_all [isNClique_iff, adj_comm]
  refine ⟨fun x hx y hy hxy ↦ ?_, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy; exact hT.1 hu hv (by aesop)
  · rw [Finset.card_image_of_injective _ Subtype.coe_injective, hT.2]

end LeftNeighborhood

/-! ## Lifting Subgraphs

Given a graph H on a subtype ↑S, we can lift it to a graph on V
by keeping only edges between vertices in S. -/

section Lifting
variable {V : Type*}

/-- Lift a graph on a subtype to a graph on the full type. -/
def spanSubgraph {S : Set V} (H : SimpleGraph S) : SimpleGraph V where
  Adj a b := ∃ (ha : a ∈ S) (hb : b ∈ S), H.Adj ⟨a, ha⟩ ⟨b, hb⟩
  symm a b := by rintro ⟨ha, hb, hab⟩; exact ⟨hb, ha, hab.symm⟩
  loopless := ⟨fun a ↦ by rintro ⟨ha, _, hab⟩; exact hab.ne rfl⟩

theorem spanSubgraph_le_of_induce {S : Set V} {H : SimpleGraph S} {G : SimpleGraph V}
    (hle : H ≤ G.induce S) : spanSubgraph H ≤ G := fun a b h ↦ by
  obtain ⟨ha, hb, hab⟩ := h; have := hle hab; aesop

theorem spanSubgraph_cliqueFree {S : Set V} {H : SimpleGraph S} {k : ℕ}
    (hk : 2 ≤ k) (hcf : H.CliqueFree k) : (spanSubgraph H).CliqueFree k := fun s hs ↦ by
  rw [isNClique_iff] at hs
  -- Since $s$ is a clique in $spanSubgraph H$, all vertices in $s$ must be in $S$.
  have hs_subset_S (v) (hv : v ∈ s) : v ∈ S := by
    have := hs.1 hv; rcases Finset.exists_mem_ne (by linarith) v with ⟨w, hw, hne⟩; have := hs.1 hw hv; simp_all [spanSubgraph]
    tauto
  classical apply hcf (Finset.subtype (· ∈ S) s)
  rw [isNClique_iff, Finset.subtype]
  simp_all [Set.Pairwise, Finset.filter_true_of_mem]
  unfold spanSubgraph at hs; aesop

theorem chromaticNumber_le_spanSubgraph {S : Set V} (H : SimpleGraph S) :
    H.chromaticNumber ≤ (spanSubgraph H).chromaticNumber := by
  refine le_ciInf fun n ↦ ?_
  by_cases hn : n ∈ setOf (spanSubgraph H).Colorable <;> simp_all
  -- Since $H$ is a subgraph of $spanSubgraph H$, and $spanSubgraph H$ is $n$-colorable, $H$ must also be $n$-colorable.
  have hH_colorable : H.Colorable n := by
    obtain ⟨f, hf⟩ := hn
    exact ⟨(f ·.1), fun {a b} hab ↦ hf ⟨a.2, b.2, hab⟩⟩
  exact hH_colorable.chromaticNumber_le

end Lifting

/-! ## Edge Partition

Given a linear order on V and a proper coloring of each left neighborhood L(v,G)
with ≤ k colors, we partition E(G) into k triangle-free subgraphs. -/

section Partition
variable {V : Type*} [LinearOrder V]

/-- The i-th partition graph: edge {a,b} with a < b belongs to partition i
    iff a has color i in the coloring of L(b,G). -/
def partGraph (G : SimpleGraph V) (k : ℕ)
    (c : (v : V) → (leftNbhd G v).Coloring (Fin k)) (i : Fin k) :
    SimpleGraph V where
  Adj a b := ∃ (h : G.Adj a b),
    (∃ hlt : a < b, c b ⟨a, hlt, h⟩ = i) ∨ (∃ hlt : b < a, c a ⟨b, hlt, h.symm⟩ = i)
  symm a b := by
    rintro ⟨h, disj⟩
    exact ⟨h.symm, disj.symm⟩
  loopless := ⟨by simp⟩

theorem partGraph_le {G : SimpleGraph V} {k : ℕ}
    {c : (v : V) → (leftNbhd G v).Coloring (Fin k)} {i : Fin k} :
    partGraph G k c i ≤ G := fun _ _ hab ↦ hab.1

theorem partGraph_sup {G : SimpleGraph V} {k : ℕ}
    {c : (v : V) → (leftNbhd G v).Coloring (Fin k)} (_hk : 0 < k) :
    G ≤ ⨆ i, partGraph G k c i := fun v w hvw ↦ by
  cases lt_trichotomy v w <;> simp_all [partGraph]
  aesop

theorem partGraph_cliqueFree_three {G : SimpleGraph V} {k : ℕ}
    {col : (v : V) → (leftNbhd G v).Coloring (Fin k)} {i : Fin k} :
    (partGraph G k col i).CliqueFree 3 := by
  simp [CliqueFree]
  intro t ht; have := ht.card_eq; simp_all [isNClique_iff]
  obtain ⟨a, b, c, habc⟩ : ∃ a b c, a ∈ t ∧ b ∈ t ∧ c ∈ t ∧ a < b ∧ b < c := by
    rcases Finset.card_eq_three.mp this with ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩
    cases lt_trichotomy a b <;> cases lt_trichotomy b c <;> cases lt_trichotomy a c <;> simp_all
  have h_adj : G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
    ⟨(ht habc.1 habc.2.1 habc.2.2.2.1.ne).1, (ht habc.2.1 habc.2.2.1 habc.2.2.2.2.ne).1,
      ((ht habc.1 habc.2.2.1) (habc.2.2.2.1.trans habc.2.2.2.2).ne).1⟩
  have h_color : col c ⟨a, habc.2.2.2.1.trans habc.2.2.2.2, h_adj.2.2⟩ = i ∧
      col c ⟨b, habc.2.2.2.2, h_adj.2.1⟩ = i := by
    generalize_proofs at *
    have := ht habc.1 habc.2.2.1; have := ht habc.2.1 habc.2.2.1; simp_all [partGraph]
    exact ⟨Or.resolve_right (‹¬a = c → _› (ne_of_lt (by tauto))) (by rintro ⟨h, _⟩; exact lt_asymm h (by tauto)), Or.resolve_right (‹¬b = c → _› (ne_of_lt (by tauto))) (by rintro ⟨h, _⟩; exact lt_asymm h (by tauto))⟩
  generalize_proofs at *
  have := col c |>.valid (show (leftNbhd G c).Adj ⟨a, ‹_›⟩ ⟨b, ‹_›⟩ from by exact h_adj.1)
  aesop

end Partition

/-! ## Auxiliary lemmas about chromatic number -/

theorem not_colorable_of_le_chromaticNumber {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (h : ↑(n + 1) ≤ G.chromaticNumber) : ¬G.Colorable n := fun hc ↦
  absurd (h.trans hc.chromaticNumber_le) (by push Not; exact_mod_cast Nat.lt_succ_of_le le_rfl)

theorem le_chromaticNumber_of_not_colorable {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (h : ¬G.Colorable n) : ↑(n + 1) ≤ G.chromaticNumber := by
  contrapose! h
  rw [← chromaticNumber_le_iff_colorable]
  rwa [Nat.cast_add_one, ENat.lt_add_one_iff (by simp)] at h

/-! ## Helper lemmas for the main proof -/

/-- Base case: χ(G) ≥ 2 implies G has an edge (is not 2-clique-free). -/
private theorem rodl_base (n : ℕ) (V : Type*) (G : SimpleGraph V)
    (hχ : ↑(phi 2 n) ≤ G.chromaticNumber) :
    ¬G.CliqueFree 2 := by
  contrapose! hχ; simp_all [CliqueFree]
  -- Since G is edgeless, it is 1-colorable.
  have h_one_colorable : G.Colorable 1 := by
    classical
    refine ⟨fun _ ↦ 0, fun {v w} h ↦ ?_⟩
    specialize hχ {v, w}
    simp_all [isNClique_iff]
    exact hχ (Finset.card_pair h.ne)
  exact (chromaticNumber_le_iff_colorable.mpr h_one_colorable).trans_lt (by norm_num)

/-- Case 2 of the inductive step: all left neighborhoods have small chromatic number.
Partition edges by color classes and use the generalized Zykov. -/
private theorem rodl_case2 {m n : ℕ} (hm : 2 ≤ m)
    {V : Type*} [LinearOrder V] (G : SimpleGraph V)
    (hχ : ↑(phi (m + 1) n) ≤ G.chromaticNumber)
    (hsmall : ∀ v : V, (leftNbhd G v).chromaticNumber < ↑(phi m n)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ ↑n ≤ H.chromaticNumber := by
  -- From hsmall, each leftNbhd G v has chromaticNumber < phi m n, so each is (phi m n - 1)-colorable. Set k = phi m n - 1.
  obtain ⟨k, hk⟩ : ∃ k, phi m n = k + 1 := by
    rcases m with _ | _ | _ | m <;> simp [phi] at *
  have hk_pos : 0 < k := by
    contrapose! hsmall; rcases m with _ | _ | m <;> simp_all [phi_succ]
    -- Since $G$ has chromatic number at least 2, there must be at least one edge in $G$.
    obtain ⟨v, w, hvw⟩ : ∃ v w, G.Adj v w := by
      grind +suggestions
    -- Without loss of generality, assume $v < w$.
    wlog hlt : v < w generalizing v w
    · exact this w v hvw.symm (by grind [hvw.ne])
    · refine ⟨w, le_csInf ?_ ?_⟩ <;> norm_num
      · exact ⟨_, ⟨2, rfl⟩⟩
      · rintro (_ | _ | a) <;> simp_all [leftNbhd]
        exact ⟨v, hlt, hvw⟩
  have hcolorable (v : V) : (leftNbhd G v).Colorable k := by
    specialize hsmall v
    have hcolorable : (leftNbhd G v).Colorable k := by
      contrapose! hsmall
      exact le_chromaticNumber_of_not_colorable hsmall |> le_trans (by simp [hk])
    exact hcolorable
  -- Choose colorings: for each v, choose c(v) : (leftNbhd G v).Coloring (Fin k) using choice.
  let c (v) : (leftNbhd G v).Coloring (Fin k) := (hcolorable v).some
  -- By contradiction: if all partGraph i were (n-1)-colorable, then (⊔ i, partGraph i) would be (n-1)^k-colorable (by colorable_iSup_fin). Since G ≤ ⊔ i partGraph i, G is also (n-1)^k-colorable (by Colorable.mono_left). But phi (m+1) n = (n-1)^k + 1, and hχ says chromaticNumber G ≥ (n-1)^k + 1 = phi (m+1) n, meaning G is NOT (n-1)^k-colorable. Contradiction.
  by_contra h_contra
  have h_union_colorable : G.Colorable ((n - 1) ^ k) := by
    have h_union_colorable (i) : (partGraph G k c i).Colorable (n - 1) := by
      by_cases hcolorable_i : (partGraph G k c i).Colorable (n - 1)
      · exact hcolorable_i
      · refine (h_contra ⟨partGraph G k c i, partGraph_le, partGraph_cliqueFree_three, ?_⟩).elim
        rcases n with _ | _ | n <;> simp_all [chromaticNumber]
        · intro i hi; rcases i with _ | _ | i <;> simp_all
        · exact fun x hx ↦ mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge fun h ↦ hcolorable_i <| hx.mono h)
    have h_union_colorable : (⨆ i, partGraph G k c i).Colorable ((n - 1) ^ k) :=
      colorable_iSup_fin h_union_colorable
    exact Colorable.mono_left (partGraph_sup hk_pos) h_union_colorable
  -- But phi (m+1) n = (n-1)^k + 1, and hχ says chromaticNumber G ≥ (n-1)^k + 1 = phi (m+1) n, meaning G is NOT (n-1)^k-colorable. Contradiction.
  have h_contradiction : phi (m + 1) n = (n - 1) ^ k + 1 := by
    rcases m with _ | _ | m <;> simp_all [phi_succ]
  exact not_lt_of_ge hχ ((chromaticNumber_le_iff_colorable.mpr h_union_colorable).trans_lt (WithTop.coe_lt_coe.mpr (by simp [h_contradiction])))

/-! ## Main Theorem -/

/-- **Rödl's Theorem.** For m ≥ 2, any graph G with χ(G) ≥ φ(m,n) either contains
a complete subgraph K_m (i.e., is not m-clique-free), or admits a triangle-free
spanning subgraph H with χ(H) ≥ n. -/
theorem rodl : ∀ (m n : ℕ), 2 ≤ m →
    ∀ (V : Type*) (G : SimpleGraph V), ↑(phi m n) ≤ G.chromaticNumber →
      ¬G.CliqueFree m ∨ ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ ↑n ≤ H.chromaticNumber
  | 2, n, _, V, G, hχ => .inl (rodl_base n V G hχ)
  | m + 3, n, _, V, G, hχ => by
    by_cases hcf : G.CliqueFree (m + 3)
    · right
      classical
      letI : LinearOrder V := linearOrderOfSTO WellOrderingRel
      by_cases! hcase : ∃ v, ↑(phi (m + 2) n) ≤ (leftNbhd G v).chromaticNumber
      · -- Case 1: some left neighborhood has large χ
        obtain ⟨v, hv⟩ := hcase
        rcases rodl (m + 2) n (by lia) _ (leftNbhd G v) hv with habs | ⟨H', hle', hcf', hchi'⟩
        · exact absurd (leftNbhd_cliqueFree hcf) habs
        · exact ⟨spanSubgraph H', spanSubgraph_le_of_induce hle',
            spanSubgraph_cliqueFree (by lia) hcf',
            hchi'.trans (chromaticNumber_le_spanSubgraph H')⟩
      · exact rodl_case2 (by lia) G hχ hcase
    · exact .inl hcf

end Rodl

namespace TriangleFreeChromatic

open SimpleGraph

/-! ## Mycielskian Construction

The Mycielskian of a graph G on vertex set V is a graph on V ⊕ V ⊕ Unit.
- The original vertices (inl v) retain their edges.
- Each copy vertex (inr (inl v)) is adjacent to the same original vertices as v.
- All copy vertices are adjacent to the apex vertex (inr (inr ())).
-/

/-- Adjacency relation for the Mycielskian. -/
def mycielskianAdj {V : Type*} (G : SimpleGraph V) : V ⊕ V ⊕ Unit → V ⊕ V ⊕ Unit → Prop
  | .inl v, .inl w => G.Adj v w
  | .inl v, .inr (.inl w) => G.Adj v w
  | .inr (.inl v), .inl w => G.Adj v w
  | .inr (.inl _), .inr (.inr ()) => True
  | .inr (.inr ()), .inr (.inl _) => True
  | _, _ => False

lemma mycielskianAdj_symm {V : Type*} (G : SimpleGraph V) (x y : V ⊕ V ⊕ Unit) :
    mycielskianAdj G x y → mycielskianAdj G y x := by
  rcases x with v | v | ⟨⟩ <;> rcases y with w | w | ⟨⟩ <;>
    simp [mycielskianAdj, adj_comm]

lemma mycielskianAdj_irrefl {V : Type*} (G : SimpleGraph V) (x : V ⊕ V ⊕ Unit) :
    ¬mycielskianAdj G x x := by
  rcases x with v | v | ⟨⟩ <;> simp [mycielskianAdj]

/-- The Mycielskian of a simple graph. -/
def mycielskian {V : Type*} (G : SimpleGraph V) : SimpleGraph (V ⊕ V ⊕ Unit) where
  Adj := mycielskianAdj G
  symm {x y} h := mycielskianAdj_symm G x y h
  loopless := ⟨fun x h ↦ mycielskianAdj_irrefl G x h⟩

/-- If G is triangle-free, then the Mycielskian of G is triangle-free. -/
lemma mycielskian_cliqueFree {V : Type*} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (mycielskian G).CliqueFree 3 := fun t ht ↦ by
  classical
  obtain ⟨x, y, z, hxy, hyz, hxz⟩ := Finset.card_eq_three.mp ht.card_eq
  simp_all [isNClique_iff]
  rcases x with x | x | x <;> rcases y with y | y | y <;> rcases z with z | z | z <;> simp_all [mycielskian]
  all_goals unfold mycielskianAdj at ht; simp_all
  · contrapose! hG
    unfold CliqueFree; simp_all [isNClique_iff]
    use {x, y, z}; aesop
  all_goals
    have := hG {x, y, z}; simp_all [isNClique_iff]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at this <;> aesop

/-- If G is not k-colorable, then the Mycielskian of G is not (k+1)-colorable. -/
lemma mycielskian_not_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : ¬G.Colorable k) : ¬(mycielskian G).Colorable (k + 1) := by
  rintro ⟨c, hc⟩
  -- Let $j = c(\text{inr}(\text{inr}()))$ be the color of the apex vertex.
  set j := c (Sum.inr (Sum.inr ())) with hj
  -- Define $c'$ : V → Fin (k + 1) by $c'(v) = if c(inl v) = j then c(inr (inl v)) else c(inl v)$.
  set c' : V → Fin (k + 1) := fun v ↦ if c (Sum.inl v) = j then c (Sum.inr (Sum.inl v)) else c (Sum.inl v) with hc'
  -- Then $c'$ is a proper coloring of $G$: if $G.Adj v w$, then $c'(v) \neq c'(w)$.
  have hc'_proper {v w} (hvw : G.Adj v w) : c' v ≠ c' w := by
    contrapose! hvw; simp_all [mycielskian]
    split_ifs at hvw <;> simp_all [mycielskianAdj]
    · exact fun h ↦ hc.1 v |>.1 w h (by aesop)
    · grind
    · exact fun h ↦ hc.1 v |>.2 w h hvw
    · exact fun h ↦ hc.1 v |>.1 w h hvw
  -- Since $c'$ avoids color $j$, it takes values in $\text{Fin} (k + 1) \setminus \{j\}$, which has cardinality $k$.
  have hc'_card : Set.range c' ⊆ Finset.univ.erase j := by
    rintro _ ⟨v, rfl⟩; simp [hc']
    split_ifs <;> simp_all [adj_comm]
    exact hc.2.1 v |>.2.2 _ (by tauto)
  -- Use the fact that there's an embedding/equiv {i : Fin (k + 1) | i ≠ j} ≃ Fin k to convert c' into a Fin k-valued coloring.
  let f : Finset.univ.erase j ≃ Fin k := Fintype.equivOfCardEq (by simp)
  refine hG ⟨fun v ↦ f ⟨c' v, hc'_card ⟨v, rfl⟩⟩, ?_⟩
  exact fun {a b} hab ↦ f.injective.ne (by aesop)

/-- The complete graph on Fin 2 is triangle-free. -/
lemma completeGraph_fin2_cliqueFree : (completeGraph (Fin 2)).CliqueFree 3 := by
  simp +decide [CliqueFree]

/-- The complete graph on Fin 2 is not 1-colorable. -/
lemma completeGraph_fin2_not_colorable_one : ¬(completeGraph (Fin 2)).Colorable 1 := by
  rintro ⟨f, hf⟩
  simp_all [Fin.eq_zero]

/-- There exist triangle-free graphs with arbitrarily large chromatic number. -/
theorem exists_triangle_free_large_chromatic (k : ℕ) :
    ∃ (V : Type) (G : SimpleGraph V), G.CliqueFree 3 ∧ ¬G.Colorable k := by
  induction k with
  | zero => refine ⟨PUnit, ⊤, ?_, ?_⟩ <;> simp +decide [CliqueFree]
  | succ k ih =>
    obtain ⟨V, G, hG₁, hG₂⟩ := ih
    -- Let's choose the Mycielskian of G as our new graph.
    exact ⟨_, _, mycielskian_cliqueFree hG₁, mycielskian_not_colorable hG₂⟩

/-- Fintype version: there exist triangle-free graphs on finite types
    with arbitrarily large chromatic number. -/
theorem exists_triangle_free_large_chromatic_fintype (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ ¬G.Colorable k := by
  induction k with
  | zero => exact ⟨PUnit, inferInstance, inferInstance, ⊤, by simp +decide [CliqueFree], by simp⟩
  | succ k ih =>
    obtain ⟨V, hfin, hdeq, G, hG₁, hG₂⟩ := ih
    exact ⟨V ⊕ V ⊕ Unit, inferInstance, inferInstance, mycielskian G,
      mycielskian_cliqueFree hG₁, mycielskian_not_colorable hG₂⟩

end TriangleFreeChromatic

/-! ## Push-forward of a Graph Along an Injection -/

section Pushforward

open SimpleGraph

variable {W V : Type*}

/-- Push-forward of a graph along an injection: edges of `T` are mapped via `f`. -/
def pushforward (T : SimpleGraph W) (f : W ↪ V) : SimpleGraph V where
  Adj a b := ∃ (i j : W), f i = a ∧ f j = b ∧ T.Adj i j
  symm a b := by rintro ⟨i, j, hi, hj, h⟩; exact ⟨j, i, hj, hi, h.symm⟩
  loopless := ⟨fun a ⟨i, j, hi, hj, h⟩ ↦ h.ne (f.injective (hi ▸ hj.symm))⟩

theorem pushforward_le_of_isClique_range (T : SimpleGraph W) (f : W ↪ V)
    (G : SimpleGraph V) (hclique : G.IsClique (Set.range f)) :
    pushforward T f ≤ G := by
  intro a b hab; cases hab; aesop

theorem pushforward_cliqueFree_three (T : SimpleGraph W) (f : W ↪ V)
    (hcf : T.CliqueFree 3) : (pushforward T f).CliqueFree 3 := by
  intro s hs
  obtain ⟨s', hs'⟩ := hs
  -- Since $s$ is a clique in the pushforward, all vertices in $s$ must be in the range of $f$.
  have h_range (v) (hv : v ∈ s) : ∃ w, f w = v := by
    obtain ⟨w, hw⟩ := Finset.exists_mem_ne (by linarith) v
    have := s' hv hw.1 hw.2.symm; unfold pushforward at this; aesop
  choose g hg using h_range
  -- Since $s$ is a clique in the pushforward, the image of $s$ under $g$ must be a clique in $T$.
  have h_clique : T.IsClique (Set.range (fun v : s ↦ g v v.2)) := by
    intro v hv w hw hne; obtain ⟨x, hx⟩ := hv; obtain ⟨y, hy⟩ := hw; simp_all [IsClique]
    have := s' x.2 y.2; simp_all [pushforward]
    grind +splitImp
  have h_card : (Set.range (fun v : s ↦ g v v.2)).ncard = 3 := by
    rw [Set.ncard_eq_toFinset_card _]
    convert hs' using 1
    apply Finset.card_bij (fun x hx ↦ f x) <;> aesop
  contrapose! hcf
  rw [CliqueFree]
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq (show 3 ≤ Set.ncard (Set.range fun v : s ↦ g v v.2) from h_card.ge)
  obtain ⟨u, hu⟩ := Set.Finite.exists_finset_coe (show Set.Finite t from Set.finite_of_ncard_pos (by lia))
  simp_all [isNClique_iff]
  exact ⟨u, by simpa [← hu] using h_clique.subset ht.1, by simpa [← hu] using ht.2⟩

theorem not_colorable_pushforward (T : SimpleGraph W) (f : W ↪ V) {n : ℕ}
    (h : ¬T.Colorable n) : ¬(pushforward T f).Colorable n :=
  fun ⟨c, hc⟩ ↦ h ⟨c ∘ f, fun {a b} hab ↦ hc ⟨a, b, rfl, rfl, hab⟩⟩

theorem isClique_range_completeGraph_embedding {α β : Type*}
    {G : SimpleGraph α} (e : completeGraph β ↪g G) : G.IsClique (Set.range e) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact e.map_adj_iff.mpr (by aesop)

end Pushforward

/-- There exists `f(n)` such that any graph `G` with `χ(G) ≥ f(n)`
has a triangle-free subgraph `H` with `χ(H) ≥ n`. -/
theorem erdos923 {V : Type*} (n : ℕ) :
    ∃ k : ℕ, ∀ G : SimpleGraph V, k ≤ G.chromaticNumber →
    ∃ H ≤ G, n ≤ H.chromaticNumber ∧ H.CliqueFree 3 := by
  classical
  open SimpleGraph Rodl in
  -- Obtain a triangle-free graph on a finite type that is not n-colorable.
  obtain ⟨W, hfin, hdeq, T, hT_cf, hT_nc⟩ :=
    TriangleFreeChromatic.exists_triangle_free_large_chromatic_fintype n
  haveI := hfin; haveI := hdeq
  -- Set m = Fintype.card W + 2 (ensuring m ≥ 2).
  set m := Fintype.card W + 2
  -- The witness: k = φ(m, n).
  refine ⟨phi m n, fun G hχ ↦ ?_⟩
  -- Apply Rödl's theorem: either G has an m-clique, or the desired H exists.
  rcases rodl m n (by omega) V G hχ with h_not_cf | ⟨H, hle, hcf, hchi⟩
  · -- Case: G has an m-clique. Embed T into it.
    rw [not_cliqueFree_iff] at h_not_cf
    obtain ⟨e⟩ := h_not_cf
    -- Get injection W ↪ Fin m (since card W ≤ m).
    have hcard : Fintype.card W ≤ Fintype.card (Fin m) := by simp; omega
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
    -- Compose to get f : W ↪ V.
    set f : W ↪ V := g.trans e.toEmbedding
    -- G.IsClique (range e) since e embeds the complete graph.
    have hclique_e := isClique_range_completeGraph_embedding e
    -- range f ⊆ range e, so G.IsClique (range f).
    have hrange : Set.range f ⊆ Set.range e := by
      rintro _ ⟨w, rfl⟩; exact ⟨g w, rfl⟩
    have hclique_f : G.IsClique (Set.range f) := Set.Pairwise.mono hrange hclique_e
    -- Construct the pushforward and verify properties.
    refine ⟨pushforward T f, pushforward_le_of_isClique_range T f G hclique_f,
      ?_, pushforward_cliqueFree_three T f hT_cf⟩
    -- χ(pushforward T f) ≥ n follows from ¬Colorable n.
    exact le_trans (by exact_mod_cast Nat.le_succ n)
      (le_chromaticNumber_of_not_colorable (not_colorable_pushforward T f hT_nc))
  · -- Case: Rödl gives us the desired H directly.
    exact ⟨H, hle, hchi, hcf⟩

#print axioms erdos923
