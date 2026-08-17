import ErdosProblems.Erdos182.Chevalley
import ErdosProblems.Erdos182.Foundations
import ErdosProblems.Erdos182.Konig
import ErdosProblems.Erdos182.KonigThinning
import ErdosProblems.Erdos182.PRSEntry
import ErdosProblems.Erdos182.Roof

/-!
# The dense half-regular endpoint in the Pyber--Rödl--Szemerédi argument

This file turns a balanced half-regular bipartite graph whose regular degree is
sufficiently close to its maximum degree into a regular subgraph.  The proof is
the finite Alon--Friedland--Kalai argument needed here: thin the graph by
Kőnig's line-colouring theorem, use Chevalley--Warning to find a divisible
edge set, and finally split a regular bipartite graph into perfect matchings.
-/

open scoped Classical

namespace Erdos182

namespace BipartiteGraph

variable {A B : Type*}

/-- The ordinary simple graph on `Sum A B` associated to a two-sorted
bipartite graph. -/
def incidenceGraph (G : BipartiteGraph A B) : SimpleGraph (Sum A B) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inr b => G.Adj a b
    | Sum.inr b, Sum.inl a => G.Adj a b
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp_all⟩

@[simp] theorem incidenceGraph_adj_inl_inr (G : BipartiteGraph A B) (a : A) (b : B) :
    G.incidenceGraph.Adj (.inl a) (.inr b) ↔ G.Adj a b := Iff.rfl

@[simp] theorem incidenceGraph_adj_inr_inl (G : BipartiteGraph A B) (a : A) (b : B) :
    G.incidenceGraph.Adj (.inr b) (.inl a) ↔ G.Adj a b := Iff.rfl

@[simp] theorem incidenceGraph_adj_inl_inl (G : BipartiteGraph A B) (a a' : A) :
    ¬G.incidenceGraph.Adj (.inl a) (.inl a') := by simp [incidenceGraph]

@[simp] theorem incidenceGraph_adj_inr_inr (G : BipartiteGraph A B) (b b' : B) :
    ¬G.incidenceGraph.Adj (.inr b) (.inr b') := by simp [incidenceGraph]

theorem incidenceGraph_mono {G H : BipartiteGraph A B} (h : H ≤ G) :
    H.incidenceGraph ≤ G.incidenceGraph := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' => exact False.elim hxy
      | inr b => exact h hxy
  | inr b =>
      cases y with
      | inl a => exact h hxy
      | inr b' => exact False.elim hxy

section Finite

variable [Fintype A] [Fintype B]

private def incidenceNeighborEquivInl (G : BipartiteGraph A B) (a : A) :
    G.incidenceGraph.neighborSet (.inl a) ≃ G.rightNeighbors a where
  toFun x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl a' => simp at hx
    | inr b => exact ⟨b, by simpa using hx⟩
  invFun b := ⟨.inr b, (mem_rightNeighbors G a b).mp b.property⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl a' => simp at hx
    | inr b => rfl
  right_inv b := by ext; rfl

private def incidenceNeighborEquivInr (G : BipartiteGraph A B) (b : B) :
    G.incidenceGraph.neighborSet (.inr b) ≃ G.leftNeighbors b where
  toFun x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl a => exact ⟨a, by simpa using hx⟩
    | inr b' => simp at hx
  invFun a := ⟨.inl a, (mem_leftNeighbors G a b).mp a.property⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl a => rfl
    | inr b' => simp at hx
  right_inv a := by ext; rfl

theorem incidenceGraph_degree_inl (G : BipartiteGraph A B) (a : A) :
    G.incidenceGraph.degree (.inl a) = G.leftDegree a := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (incidenceNeighborEquivInl G a)]
  exact Fintype.card_coe _

theorem incidenceGraph_degree_inr (G : BipartiteGraph A B) (b : B) :
    G.incidenceGraph.degree (.inr b) = G.rightDegree b := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (incidenceNeighborEquivInr G b)]
  exact Fintype.card_coe _

theorem incidenceGraph_edgeFinset_card (G : BipartiteGraph A B) :
    G.incidenceGraph.edgeFinset.card = G.edgeCount := by
  classical
  have h := G.incidenceGraph.sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  simp_rw [incidenceGraph_degree_inl, incidenceGraph_degree_inr] at h
  rw [← G.edgeCount_eq_sum_leftDegree] at h
  have h' : G.edgeCount + G.edgeCount = 2 * G.incidenceGraph.edgeFinset.card := by
    simpa only [edgeCount] using h
  rw [← Nat.mul_left_cancel_iff (by omega : 0 < 2)]
  simpa [two_mul] using h'.symm

theorem exists_incidenceGraph_thinning (G : BipartiteGraph A B) {D T : ℕ}
    (hleft : ∀ a, G.leftDegree a ≤ D)
    (hright : ∀ b, G.rightDegree b ≤ D) (hT : T ≤ D) :
    ∃ J : SimpleGraph (Sum A B),
      J ≤ G.incidenceGraph ∧ (∀ v, J.degree v ≤ T) ∧
        T * G.incidenceGraph.edgeFinset.card ≤ D * J.edgeFinset.card := by
  obtain ⟨H, hHG, hHl, hHr, hHE⟩ :=
    G.exists_bipartite_thinning hleft hright hT
  refine ⟨H.incidenceGraph, incidenceGraph_mono hHG, ?_, ?_⟩
  · intro v
    cases v with
    | inl a => simpa only [incidenceGraph_degree_inl] using hHl a
    | inr b => simpa only [incidenceGraph_degree_inr] using hHr b
  · simpa only [incidenceGraph_edgeFinset_card] using hHE

theorem incidenceGraph_isBipartiteWith (G : BipartiteGraph A B) :
    G.incidenceGraph.IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨a, rfl⟩ ⟨b, h⟩
    simp at h
  · intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' => simp at hxy
        | inr b => exact Or.inl ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    | inr b =>
        cases y with
        | inl a => exact Or.inr ⟨⟨b, rfl⟩, ⟨a, rfl⟩⟩
        | inr b' => simp at hxy

/-- Forget all same-side adjacencies of a simple graph on a sum. -/
def ofSumGraph (H : SimpleGraph (Sum A B)) : BipartiteGraph A B :=
  ⟨fun a b ↦ H.Adj (.inl a) (.inr b)⟩

@[simp] theorem ofSumGraph_adj (H : SimpleGraph (Sum A B)) (a : A) (b : B) :
    (ofSumGraph H).Adj a b ↔ H.Adj (.inl a) (.inr b) := Iff.rfl

theorem incidenceGraph_ofSumGraph_eq {G : BipartiteGraph A B}
    {H : SimpleGraph (Sum A B)} (hHG : H ≤ G.incidenceGraph) :
    (ofSumGraph H).incidenceGraph = H := by
  ext x y
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          constructor
          · simp
          · intro h; simpa using hHG h
      | inr b => simp [incidenceGraph, ofSumGraph]
  | inr b =>
      cases y with
      | inl a => simp [incidenceGraph, ofSumGraph, H.adj_comm]
      | inr b' =>
          constructor
          · simp
          · intro h; simpa using hHG h

theorem ofSumGraph_leftDegree {G : BipartiteGraph A B}
    {H : SimpleGraph (Sum A B)} (hHG : H ≤ G.incidenceGraph) (a : A) :
    (ofSumGraph H).leftDegree a = H.degree (.inl a) := by
  rw [← incidenceGraph_degree_inl, incidenceGraph_ofSumGraph_eq hHG]

theorem ofSumGraph_rightDegree {G : BipartiteGraph A B}
    {H : SimpleGraph (Sum A B)} (hHG : H ≤ G.incidenceGraph) (b : B) :
    (ofSumGraph H).rightDegree b = H.degree (.inr b) := by
  rw [← incidenceGraph_degree_inr, incidenceGraph_ofSumGraph_eq hHG]

/-- A nonempty, genuinely `k`-regular two-sorted subgraph.  The support sets
are explicit so that isolated ambient vertices do not enter the statement. -/
def ContainsRegularBipartiteSubgraph (G : BipartiteGraph A B) (k : ℕ) : Prop :=
  ∃ A₁ : Finset A, ∃ B₁ : Finset B, ∃ H : BipartiteGraph A B,
    H ≤ G ∧ H.SupportedOn A₁ B₁ ∧ A₁.Nonempty ∧ B₁.Nonempty ∧
      (∀ a ∈ A₁, H.leftDegree a = k) ∧
      (∀ b ∈ B₁, H.rightDegree b = k)

/-- The two parts have equal cardinality and every vertex on the right has
degree `d`.  This is the balanced half-regular situation at the end of the
PRS switching argument. -/
def IsBalancedRightRegular (G : BipartiteGraph A B) (d : ℕ) : Prop :=
  Fintype.card A = Fintype.card B ∧ 0 < Fintype.card B ∧
    ∀ b, G.rightDegree b = d

/-- Both one-sided degrees are bounded by `D`. -/
def MaxDegreeLE (G : BipartiteGraph A B) (D : ℕ) : Prop :=
  (∀ a, G.leftDegree a ≤ D) ∧ ∀ b, G.rightDegree b ≤ D

theorem incidenceGraph_degree_le_iff (G : BipartiteGraph A B) (D : ℕ) :
    (∀ v, G.incidenceGraph.degree v ≤ D) ↔ G.MaxDegreeLE D := by
  constructor
  · intro h
    exact ⟨fun a ↦ by simpa [incidenceGraph_degree_inl] using h (.inl a),
      fun b ↦ by simpa [incidenceGraph_degree_inr] using h (.inr b)⟩
  · rintro ⟨hA, hB⟩ v
    cases v with
    | inl a => simpa [incidenceGraph_degree_inl] using hA a
    | inr b => simpa [incidenceGraph_degree_inr] using hB b

theorem twice_edgeCount_eq_degree_mul_card_of_balancedRightRegular
    {G : BipartiteGraph A B} {d : ℕ} (hG : G.IsBalancedRightRegular d) :
    2 * G.edgeCount = d * Fintype.card (Sum A B) := by
  rw [edgeCount, Fintype.card_sum, hG.1]
  simp_rw [hG.2.2]
  simp
  ring

theorem ofSumGraph_le {G : BipartiteGraph A B} {H : SimpleGraph (Sum A B)}
    (hHG : H ≤ G.incidenceGraph) : ofSumGraph H ≤ G := by
  intro a b hab
  exact hHG hab

theorem ofSumGraph_supportedOn_support
    (H : SimpleGraph (Sum A B)) :
    (ofSumGraph H).SupportedOn
      (Finset.univ.filter fun a ↦ 0 < H.degree (.inl a))
      (Finset.univ.filter fun b ↦ 0 < H.degree (.inr b)) := by
  classical
  intro a b hab
  constructor <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · exact (H.degree_pos_iff_exists_adj _).2 ⟨_, hab⟩
  · exact (H.degree_pos_iff_exists_adj _).2 ⟨_, hab.symm⟩

theorem containsRegularBipartiteSubgraph_of_degree_zero_or
    {G : BipartiteGraph A B} {H : SimpleGraph (Sum A B)} {k : ℕ}
    (hHG : H ≤ G.incidenceGraph) (hH : H ≠ ⊥)
    (hdeg : ∀ v, H.degree v = 0 ∨ H.degree v = k) :
    G.ContainsRegularBipartiteSubgraph k := by
  classical
  let A₁ : Finset A := Finset.univ.filter fun a ↦ 0 < H.degree (.inl a)
  let B₁ : Finset B := Finset.univ.filter fun b ↦ 0 < H.degree (.inr b)
  let K : BipartiteGraph A B := ofSumGraph H
  have hedge : ∃ a b, H.Adj (.inl a) (.inr b) := by
    rw [SimpleGraph.ne_bot_iff_exists_adj] at hH
    obtain ⟨x, y, hxy⟩ := hH
    have hinc := hHG hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' => simp at hinc
        | inr b => exact ⟨a, b, hxy⟩
    | inr b =>
        cases y with
        | inl a => exact ⟨a, b, hxy.symm⟩
        | inr b' => simp at hinc
  obtain ⟨a, b, hab⟩ := hedge
  have ha : a ∈ A₁ := by
    simp [A₁, (H.degree_pos_iff_exists_adj _).2 ⟨_, hab⟩]
  have hb : b ∈ B₁ := by
    simp [B₁, (H.degree_pos_iff_exists_adj _).2 ⟨_, hab.symm⟩]
  refine ⟨A₁, B₁, K, ofSumGraph_le hHG,
    ofSumGraph_supportedOn_support H, ⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
  · intro x hx
    rw [ofSumGraph_leftDegree hHG]
    exact (hdeg (.inl x)).resolve_left (Nat.ne_of_gt (by simpa [A₁] using hx))
  · intro y hy
    rw [ofSumGraph_rightDegree hHG]
    exact (hdeg (.inr y)).resolve_left (Nat.ne_of_gt (by simpa [B₁] using hy))

/-- Chevalley--Warning after a `2p-1`-colour thinning.  This formulation
separates the algebraic endpoint from the Kőnig line-colouring lemma which
produces `J`. -/
theorem exists_degree_zero_or_prime_of_bipartite_thinning
    {G : BipartiteGraph A B} {p D : ℕ} (hp : p.Prime) (hD : 0 < D)
    (hdense : (2 * p - 2) * D * Fintype.card (Sum A B) <
      (2 * p - 1) * (2 * G.edgeCount))
    (J : SimpleGraph (Sum A B))
    (hJG : J ≤ G.incidenceGraph)
    (hJdeg : ∀ v, J.degree v ≤ 2 * p - 1)
    (hJedges : (2 * p - 1) * G.incidenceGraph.edgeFinset.card ≤
      D * J.edgeFinset.card) :
    ∃ H : SimpleGraph (Sum A B),
      H ≤ G.incidenceGraph ∧ H ≠ ⊥ ∧
      ∀ v, H.degree v = 0 ∨ H.degree v = p := by
  classical
  have hp1 : 1 ≤ p := hp.one_le
  have htwo : 2 * p - 2 = 2 * (p - 1) := by omega
  have hE : (p - 1) * Fintype.card (Sum A B) < J.edgeFinset.card := by
    rw [incidenceGraph_edgeFinset_card] at hJedges
    have hmul : (2 * D) * ((p - 1) * Fintype.card (Sum A B)) <
        (2 * D) * J.edgeFinset.card := by
      calc
        (2 * D) * ((p - 1) * Fintype.card (Sum A B)) =
            (2 * p - 2) * D * Fintype.card (Sum A B) := by
              rw [htwo]; ring
        _ < (2 * p - 1) * (2 * G.edgeCount) := hdense
        _ = 2 * ((2 * p - 1) * G.edgeCount) := by ring
        _ ≤ 2 * (D * J.edgeFinset.card) := Nat.mul_le_mul_left 2 hJedges
        _ = (2 * D) * J.edgeFinset.card := by ring
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2 * D)).mp hmul
  have hwindow : ∀ v, J.degree v < 2 * p := by
    intro v
    exact (hJdeg v).trans_lt (by omega)
  have hE' : (p - 1) * Fintype.card (Sum A B) <
      (@SimpleGraph.edgeFinset _ J (finiteEdgeSet J)).card := by
    convert hE
  have hwindow' : ∀ v,
      @SimpleGraph.degree _ J v (finiteNeighborSet J v) < 2 * p := by
    intro v
    convert hwindow v
  obtain ⟨H, hHJ, hHne, hHdeg, _⟩ :=
    exists_nonempty_subgraph_degree_zero_or_prime J hp hE' hwindow'
  refine ⟨H, hHJ.trans hJG, hHne, ?_⟩
  intro v
  convert hHdeg v

theorem containsPrimeRegularBipartiteSubgraph_of_thinning
    {G : BipartiteGraph A B} {p D : ℕ} (hp : p.Prime) (hD : 0 < D)
    (hdense : (2 * p - 2) * D * Fintype.card (Sum A B) <
      (2 * p - 1) * (2 * G.edgeCount))
    (J : SimpleGraph (Sum A B))
    (hJG : J ≤ G.incidenceGraph)
    (hJdeg : ∀ v, J.degree v ≤ 2 * p - 1)
    (hJedges : (2 * p - 1) * G.incidenceGraph.edgeFinset.card ≤
      D * J.edgeFinset.card) :
    G.ContainsRegularBipartiteSubgraph p := by
  obtain ⟨H, hHG, hHne, hHdeg⟩ :=
    exists_degree_zero_or_prime_of_bipartite_thinning hp hD hdense
      J hJG hJdeg hJedges
  exact containsRegularBipartiteSubgraph_of_degree_zero_or hHG hHne hHdeg

theorem degree_map_embedding {V W : Type*} [Fintype V] [Fintype W]
    (K : SimpleGraph V) (f : V ↪ W) (v : V) :
    (K.map f).degree (f v) = K.degree v := by
  let e₁ : K.neighborSet v ≃ f '' K.neighborSet v :=
    Equiv.Set.image f (K.neighborSet v) f.injective
  let e₂ : f '' K.neighborSet v ≃ (K.map f).neighborSet (f v) :=
    Equiv.setCongr (SimpleGraph.neighborSet_map K f v).symm
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (e₁.trans e₂)).symm

/-- Support-relative form of the regular-factor theorem.  Isolated ambient
vertices are retained as isolated vertices; on the nonempty support, the
output is exactly `k`-regular. -/
theorem exists_degree_zero_or_regular_factor
    {V : Type*} [Fintype V] {H : SimpleGraph V} {s t : Set V} {p k : ℕ}
    (hHne : H ≠ ⊥) (hbip : H.IsBipartiteWith s t)
    (hdeg : ∀ v, H.degree v = 0 ∨ H.degree v = p)
    (hkpos : 0 < k) (hkp : k ≤ p) :
    ∃ K : SimpleGraph V, K ≤ H ∧ K ≠ ⊥ ∧
      ∀ v, K.degree v = 0 ∨ K.degree v = k := by
  classical
  let S : Set V := H.support
  let HS : SimpleGraph S := H.induce S
  have hSne : S.Nonempty := by
    obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hHne
    exact ⟨u, v, huv⟩
  have hSreg : HS.IsRegularOfDegree p := by
    intro v
    calc
      HS.degree v = H.degree v := by
        simpa [HS, S] using H.degree_induce_support v
      _ = p := (hdeg v).resolve_left <| Nat.ne_of_gt <|
        (H.degree_pos_iff_exists_adj v).mpr v.property
  let sS : Set S := {v | (v : V) ∈ s}
  let tS : Set S := {v | (v : V) ∈ t}
  have hbipS : HS.IsBipartiteWith sS tS := by
    refine ⟨?_, ?_⟩
    · exact Set.disjoint_left.mpr fun v hs ht ↦
        Set.disjoint_left.mp hbip.disjoint hs ht
    · intro u v huv
      have huvH : H.Adj u v := huv
      rcases hbip.mem_of_adj huvH with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨K₀, hK₀, hK₀reg⟩ :=
    Konig.exists_regular_subgraph_of_le hSreg hbipS hkp
  let f : S ↪ V := Function.Embedding.subtype _
  have hKH : K₀.map f ≤ H := by
    intro x y hxy
    rw [SimpleGraph.map_adj] at hxy
    obtain ⟨x', y', hxy, rfl, rfl⟩ := hxy
    exact hK₀ hxy
  have hKne : K₀.map f ≠ ⊥ := by
    obtain ⟨v, hv⟩ := hSne
    let vS : S := ⟨v, hv⟩
    have hpos : 0 < K₀.degree vS := by rw [hK₀reg.degree_eq]; exact hkpos
    obtain ⟨w, hvw⟩ := (K₀.degree_pos_iff_exists_adj vS).mp hpos
    rw [SimpleGraph.ne_bot_iff_exists_adj]
    refine ⟨f vS, f w, ?_⟩
    change (K₀.map f).Adj (f vS) (f w)
    exact SimpleGraph.map_adj_apply.mpr hvw
  refine ⟨K₀.map f, hKH, hKne, fun v ↦ ?_⟩
  by_cases hv : v ∈ Set.range f
  · obtain ⟨v, rfl⟩ := hv
    right
    convert (degree_map_embedding K₀ f v).trans (hK₀reg.degree_eq v) using 1
    unfold SimpleGraph.degree
    apply congrArg Finset.card
    ext w
    simp
  · left
    apply Nat.eq_zero_of_not_pos
    rw [(K₀.map f).degree_pos_iff_exists_adj]
    rintro ⟨w, hvw⟩
    apply hv
    rw [SimpleGraph.map_adj] at hvw
    obtain ⟨v', _w', _, hv', _⟩ := hvw
    exact ⟨v', hv'⟩

/-- Prime AFK endpoint followed by König factorization down to `k`. -/
theorem containsRegularBipartiteSubgraph_of_prime_thinning
    {G : BipartiteGraph A B} {p k D : ℕ} (hp : p.Prime)
    (hkpos : 0 < k) (hkp : k ≤ p) (hD : 0 < D)
    (hdense : (2 * p - 2) * D * Fintype.card (Sum A B) <
      (2 * p - 1) * (2 * G.edgeCount))
    (J : SimpleGraph (Sum A B))
    (hJG : J ≤ G.incidenceGraph)
    (hJdeg : ∀ v, J.degree v ≤ 2 * p - 1)
    (hJedges : (2 * p - 1) * G.incidenceGraph.edgeFinset.card ≤
      D * J.edgeFinset.card) :
    G.ContainsRegularBipartiteSubgraph k := by
  obtain ⟨H, hHG, hHne, hHdeg⟩ :=
    exists_degree_zero_or_prime_of_bipartite_thinning hp hD hdense
      J hJG hJdeg hJedges
  have hbipH : H.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := {
    disjoint := G.incidenceGraph_isBipartiteWith.disjoint
    mem_of_adj := fun _ _ hadj ↦
      G.incidenceGraph_isBipartiteWith.mem_of_adj (hHG hadj)
  }
  obtain ⟨K, hKH, hKne, hKdeg⟩ :=
    exists_degree_zero_or_regular_factor hHne hbipH hHdeg hkpos hkp
  exact containsRegularBipartiteSubgraph_of_degree_zero_or
    (hKH.trans hHG) hKne hKdeg

private theorem ratio_step {a b d D : ℕ} (hab : a ≤ b) (hdD : d ≤ D)
    (h : b * D < (b + 1) * d) : a * D < (a + 1) * d := by
  have hbd : b * d ≤ b * D := Nat.mul_le_mul_left b hdD
  have hsub : b * (D - d) < d := by
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.add_mul, one_mul] at h
    omega
  have hasub : a * (D - d) < d :=
    lt_of_le_of_lt (Nat.mul_le_mul_right (D - d) hab) hsub
  calc
    a * D = a * (d + (D - d)) := by rw [Nat.add_sub_of_le hdD]
    _ = a * d + a * (D - d) := by rw [Nat.mul_add]
    _ < a * d + d := Nat.add_lt_add_left hasub _
    _ = (a + 1) * d := by rw [Nat.add_mul, one_mul]

/-- The complete Bertrand and constant calculation, parameterized only by
the exact Kőnig thinning conclusion. -/
theorem finalFactor_of_thinning_le
    {G : BipartiteGraph A B} {r q d D : ℕ}
    (hr : 0 < r) (hrq : r ≤ q) (hq : 3 ≤ q)
    (hbal : G.IsBalancedRightRegular d)
    (hmax : G.MaxDegreeLE D) (hD : 4 * q - 3 ≤ D)
    (hclose : (4 * q - 4) * D < (4 * q - 3) * d)
    (hthin : ∀ T, T ≤ D →
      ∃ J : SimpleGraph (Sum A B),
        J ≤ G.incidenceGraph ∧ (∀ v, J.degree v ≤ T) ∧
          T * G.incidenceGraph.edgeFinset.card ≤ D * J.edgeFinset.card) :
    G.ContainsRegularBipartiteSubgraph r := by
  classical
  obtain ⟨p, hp, hqp, hp2q⟩ := Nat.bertrand q (by omega)
  have hp_lt : p < 2 * q := by
    refine lt_of_le_of_ne hp2q ?_
    intro heq
    have hp_even : Even p := ⟨q, by omega⟩
    have : p = 2 := hp.even_iff.mp hp_even
    omega
  have hT : 2 * p - 1 ≤ D := by omega
  obtain ⟨J, hJG, hJdeg, hJedges⟩ := hthin (2 * p - 1) hT
  let b : B := Fintype.card_pos_iff.mp hbal.2.1 |> Classical.choice
  have hdD : d ≤ D := by
    rw [← hbal.2.2 b]
    exact hmax.2 b
  have hcoef : (2 * p - 2) * D < (2 * p - 1) * d := by
    have hab : 2 * p - 2 ≤ 4 * q - 4 := by omega
    have hclose' : (4 * q - 4) * D < ((4 * q - 4) + 1) * d := by
      have hs : (4 * q - 4) + 1 = 4 * q - 3 := by omega
      rw [hs]
      exact hclose
    have := ratio_step hab hdD hclose'
    have hs : (2 * p - 2) + 1 = 2 * p - 1 := by omega
    rw [hs] at this
    exact this
  have hcard : 0 < Fintype.card (Sum A B) := by
    have hBcard := hbal.2.1
    rw [Fintype.card_sum]
    omega
  have hdense : (2 * p - 2) * D * Fintype.card (Sum A B) <
      (2 * p - 1) * (2 * G.edgeCount) := by
    rw [twice_edgeCount_eq_degree_mul_card_of_balancedRightRegular hbal]
    calc
      (2 * p - 2) * D * Fintype.card (Sum A B) <
          ((2 * p - 1) * d) * Fintype.card (Sum A B) :=
        Nat.mul_lt_mul_of_pos_right hcoef hcard
      _ = (2 * p - 1) * (d * Fintype.card (Sum A B)) := by ring
  exact containsRegularBipartiteSubgraph_of_prime_thinning hp hr
    (hrq.trans hqp.le) (by omega) hdense J hJG hJdeg hJedges

theorem finalFactor_of_thinning
    {G : BipartiteGraph A B} {k d D : ℕ}
    (hk : 3 ≤ k) (hbal : G.IsBalancedRightRegular d)
    (hmax : G.MaxDegreeLE D) (hD : 4 * k - 3 ≤ D)
    (hclose : (4 * k - 4) * D < (4 * k - 3) * d)
    (hthin : ∀ T, T ≤ D →
      ∃ J : SimpleGraph (Sum A B), J ≤ G.incidenceGraph ∧
        (∀ v, J.degree v ≤ T) ∧
        T * G.incidenceGraph.edgeFinset.card ≤ D * J.edgeFinset.card) :
    G.ContainsRegularBipartiteSubgraph k :=
  finalFactor_of_thinning_le (by omega) le_rfl hk hbal hmax hD hclose hthin

theorem finalFactorPositive_of_thinning
    {G : BipartiteGraph A B} {k d D : ℕ}
    (hk : 0 < k) (hbal : G.IsBalancedRightRegular d)
    (hmax : G.MaxDegreeLE D) (hD : 4 * max 3 k - 3 ≤ D)
    (hclose : (4 * max 3 k - 4) * D < (4 * max 3 k - 3) * d)
    (hthin : ∀ T, T ≤ D →
      ∃ J : SimpleGraph (Sum A B), J ≤ G.incidenceGraph ∧
        (∀ v, J.degree v ≤ T) ∧
        T * G.incidenceGraph.edgeFinset.card ≤ D * J.edgeFinset.card) :
    G.ContainsRegularBipartiteSubgraph k :=
  finalFactor_of_thinning_le hk (Nat.le_max_right 3 k) (Nat.le_max_left 3 k)
    hbal hmax hD hclose hthin

/-- Unconditional balanced final-factor lemma, using Kőnig thinning. -/
theorem finalFactorPositive
    {G : BipartiteGraph A B} {k d D : ℕ}
    (hk : 0 < k) (hbal : G.IsBalancedRightRegular d)
    (hmax : G.MaxDegreeLE D) (hD : 4 * max 3 k - 3 ≤ D)
    (hclose : (4 * max 3 k - 4) * D < (4 * max 3 k - 3) * d) :
    G.ContainsRegularBipartiteSubgraph k :=
  finalFactorPositive_of_thinning hk hbal hmax hD hclose fun _T hT ↦
    exists_incidenceGraph_thinning G hmax.1 hmax.2 hT

/-- The stated `k ≥ 3` form of the balanced final-factor lemma. -/
theorem finalFactor
    {G : BipartiteGraph A B} {k d D : ℕ}
    (hk : 3 ≤ k) (hbal : G.IsBalancedRightRegular d)
    (hmax : G.MaxDegreeLE D) (hD : 4 * k - 3 ≤ D)
    (hclose : (4 * k - 4) * D < (4 * k - 3) * d) :
    G.ContainsRegularBipartiteSubgraph k := by
  have hm : max 3 k = k := max_eq_right hk
  have hD' : 4 * max 3 k - 3 ≤ D := by simpa only [hm] using hD
  have hclose' : (4 * max 3 k - 4) * D < (4 * max 3 k - 3) * d := by
    simpa only [hm] using hclose
  exact finalFactorPositive (G := G) (k := k) (d := d) (D := D)
    (by omega) hbal hmax hD' hclose'

def restrictToFinsets (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) :
    BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀} where
  Adj a b := G.Adj a b

@[simp] theorem restrictToFinsets_adj (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (a) (b) :
    (G.restrictToFinsets A₀ B₀).Adj a b ↔ G.Adj a b := Iff.rfl

private noncomputable def restrictRightNeighborEquiv
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (hs : G.SupportedOn A₀ B₀) (a : {a // a ∈ A₀}) :
    {b // b ∈ (G.restrictToFinsets A₀ B₀).rightNeighbors a} ≃
      {b // b ∈ G.rightNeighbors (a : A)} := by
  let f : {b // b ∈ (G.restrictToFinsets A₀ B₀).rightNeighbors a} →
      {b // b ∈ G.rightNeighbors (a : A)} := fun b ↦
    ⟨(b.1 : B), G.mem_rightNeighbors _ _ |>.2 <|
      (G.restrictToFinsets A₀ B₀).mem_rightNeighbors _ _ |>.1 b.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val hxy
  · intro b
    have hab : G.Adj a b := (G.mem_rightNeighbors _ _).1 b.2
    let b' : {b // b ∈ B₀} := ⟨b, (hs hab).2⟩
    refine ⟨⟨b', (G.restrictToFinsets A₀ B₀).mem_rightNeighbors _ _ |>.2 hab⟩, ?_⟩
    apply Subtype.ext
    rfl

private noncomputable def restrictLeftNeighborEquiv
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (hs : G.SupportedOn A₀ B₀) (b : {b // b ∈ B₀}) :
    {a // a ∈ (G.restrictToFinsets A₀ B₀).leftNeighbors b} ≃
      {a // a ∈ G.leftNeighbors (b : B)} := by
  let f : {a // a ∈ (G.restrictToFinsets A₀ B₀).leftNeighbors b} →
      {a // a ∈ G.leftNeighbors (b : B)} := fun a ↦
    ⟨(a.1 : A), G.mem_leftNeighbors _ _ |>.2 <|
      (G.restrictToFinsets A₀ B₀).mem_leftNeighbors _ _ |>.1 a.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val hxy
  · intro a
    have hab : G.Adj a b := (G.mem_leftNeighbors _ _).1 a.2
    let a' : {a // a ∈ A₀} := ⟨a, (hs hab).1⟩
    refine ⟨⟨a', (G.restrictToFinsets A₀ B₀).mem_leftNeighbors _ _ |>.2 hab⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem restrictToFinsets_leftDegree (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (hs : G.SupportedOn A₀ B₀)
    (a : {a // a ∈ A₀}) :
    (G.restrictToFinsets A₀ B₀).leftDegree a = G.leftDegree a := by
  simpa only [leftDegree, Fintype.card_coe] using
    Fintype.card_congr (restrictRightNeighborEquiv G A₀ B₀ hs a)

theorem restrictToFinsets_rightDegree (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (hs : G.SupportedOn A₀ B₀)
    (b : {b // b ∈ B₀}) :
    (G.restrictToFinsets A₀ B₀).rightDegree b = G.rightDegree b := by
  simpa only [rightDegree, Fintype.card_coe] using
    Fintype.card_congr (restrictLeftNeighborEquiv G A₀ B₀ hs b)

/-- Extend a graph on subtype parts back to the ambient parts, keeping all
vertices outside the displayed finite sets isolated. -/
def extendFromFinsets {A₀ : Finset A} {B₀ : Finset B}
    (H : BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀}) : BipartiteGraph A B where
  Adj a b := ∃ a' b', H.Adj a' b' ∧ (a' : A) = a ∧ (b' : B) = b

@[simp] theorem extendFromFinsets_adj {A₀ : Finset A} {B₀ : Finset B}
    (H : BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀}) (a : A) (b : B) :
    H.extendFromFinsets.Adj a b ↔
      ∃ a' b', H.Adj a' b' ∧ (a' : A) = a ∧ (b' : B) = b := Iff.rfl

private noncomputable def extendRightNeighborEquiv
    {A₀ : Finset A} {B₀ : Finset B}
    (H : BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀}) (a : {a // a ∈ A₀}) :
    {b // b ∈ H.rightNeighbors a} ≃
      {b // b ∈ H.extendFromFinsets.rightNeighbors (a : A)} := by
  let f : {b // b ∈ H.rightNeighbors a} →
      {b // b ∈ H.extendFromFinsets.rightNeighbors (a : A)} := fun b ↦
    ⟨(b.1 : B), H.extendFromFinsets.mem_rightNeighbors _ _ |>.2
      ⟨a, b.1, H.mem_rightNeighbors _ _ |>.1 b.2, rfl, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val hxy
  · intro b
    rcases (H.extendFromFinsets.mem_rightNeighbors _ _).1 b.2 with
      ⟨a', b', hab, ha, hb⟩
    have haa : a' = a := Subtype.ext ha
    subst a'
    refine ⟨⟨b', H.mem_rightNeighbors _ _ |>.2 hab⟩, ?_⟩
    apply Subtype.ext
    exact hb

private noncomputable def extendLeftNeighborEquiv
    {A₀ : Finset A} {B₀ : Finset B}
    (H : BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀}) (b : {b // b ∈ B₀}) :
    {a // a ∈ H.leftNeighbors b} ≃
      {a // a ∈ H.extendFromFinsets.leftNeighbors (b : B)} := by
  let f : {a // a ∈ H.leftNeighbors b} →
      {a // a ∈ H.extendFromFinsets.leftNeighbors (b : B)} := fun a ↦
    ⟨(a.1 : A), H.extendFromFinsets.mem_leftNeighbors _ _ |>.2
      ⟨a.1, b, H.mem_leftNeighbors _ _ |>.1 a.2, rfl, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val hxy
  · intro a
    rcases (H.extendFromFinsets.mem_leftNeighbors _ _).1 a.2 with
      ⟨a', b', hab, ha, hb⟩
    have hbb : b' = b := Subtype.ext hb
    subst b'
    refine ⟨⟨a', H.mem_leftNeighbors _ _ |>.2 hab⟩, ?_⟩
    apply Subtype.ext
    exact ha

theorem extendFromFinsets_leftDegree {A₀ : Finset A} {B₀ : Finset B}
    (H : BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀}) (a : {a // a ∈ A₀}) :
    H.extendFromFinsets.leftDegree (a : A) = H.leftDegree a := by
  simpa only [leftDegree, Fintype.card_coe] using
    (Fintype.card_congr (extendRightNeighborEquiv H a)).symm

theorem extendFromFinsets_rightDegree {A₀ : Finset A} {B₀ : Finset B}
    (H : BipartiteGraph {a // a ∈ A₀} {b // b ∈ B₀}) (b : {b // b ∈ B₀}) :
    H.extendFromFinsets.rightDegree (b : B) = H.rightDegree b := by
  simpa only [rightDegree, Fintype.card_coe] using
    (Fintype.card_congr (extendLeftNeighborEquiv H b)).symm

theorem containsRegularBipartiteSubgraph_of_restrictToFinsets
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) {k : ℕ}
    (h : (G.restrictToFinsets A₀ B₀).ContainsRegularBipartiteSubgraph k) :
    G.ContainsRegularBipartiteSubgraph k := by
  classical
  rcases h with ⟨A₁, B₁, H, hHG, hs, hA₁, hB₁, hAreg, hBreg⟩
  let eA : {a // a ∈ A₀} ↪ A := Function.Embedding.subtype _
  let eB : {b // b ∈ B₀} ↪ B := Function.Embedding.subtype _
  let A₂ : Finset A := A₁.map eA
  let B₂ : Finset B := B₁.map eB
  refine ⟨A₂, B₂, H.extendFromFinsets, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rcases hab with ⟨a', b', hab, rfl, rfl⟩
    exact hHG hab
  · intro a b hab
    rcases hab with ⟨a', b', hab, rfl, rfl⟩
    have hm := hs hab
    constructor
    · simp only [A₂, Finset.mem_map]
      exact ⟨a', hm.1, rfl⟩
    · simp only [B₂, Finset.mem_map]
      exact ⟨b', hm.2, rfl⟩
  · obtain ⟨a, ha⟩ := hA₁
    refine ⟨a, ?_⟩
    simp only [A₂, Finset.mem_map]
    exact ⟨a, ha, rfl⟩
  · obtain ⟨b, hb⟩ := hB₁
    refine ⟨b, ?_⟩
    simp only [B₂, Finset.mem_map]
    exact ⟨b, hb, rfl⟩
  · intro a ha
    simp only [A₂, Finset.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    change H.extendFromFinsets.leftDegree (a' : A) = k
    rw [extendFromFinsets_leftDegree]
    exact hAreg a' ha'
  · intro b hb
    simp only [B₂, Finset.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    change H.extendFromFinsets.rightDegree (b' : B) = k
    rw [extendFromFinsets_rightDegree]
    exact hBreg b' hb'

/-- A regular two-sorted subgraph on active subsets of two disjoint parts is
a regular subgraph of the original one-sorted graph. -/
theorem containsRegularSubgraph_of_containsRegularBipartiteSubgraph
    {V : Type*} [Fintype V] {G : SimpleGraph V} {A B : Finset V}
    (hAB : Disjoint (A : Set V) (B : Set V))
    {K : BipartiteGraph A B} (hKG : K ≤ PRSEntry.fromSimpleGraph G A B)
    {k : ℕ} (hK : K.ContainsRegularBipartiteSubgraph k) :
    ContainsRegularSubgraph G k := by
  classical
  rcases hK with ⟨A₁, B₁, H, hHK, hs, hA₁, _hB₁, hleft, hright⟩
  let L := H.restrictToFinsets A₁ B₁
  have hLleft : ∀ a, L.leftDegree a = k := by
    intro a
    change (H.restrictToFinsets A₁ B₁).leftDegree a = k
    rw [restrictToFinsets_leftDegree H A₁ B₁ hs]
    exact hleft a a.2
  have hLright : ∀ b, L.rightDegree b = k := by
    intro b
    change (H.restrictToFinsets A₁ B₁).rightDegree b = k
    rw [restrictToFinsets_rightDegree H A₁ B₁ hs]
    exact hright b b.2
  let f : Sum {a // a ∈ A₁} {b // b ∈ B₁} ↪ V := {
    toFun := fun x ↦ Sum.elim (fun a ↦ (a.1 : V)) (fun b ↦ (b.1 : V)) x
    inj' := by
      intro x y hxy
      cases x with
      | inl a =>
          cases y with
          | inl a' =>
              congr 1
              apply Subtype.ext
              apply Subtype.ext
              exact hxy
          | inr b =>
              exfalso
              have habval : (a.1 : V) = (b.1 : V) := by simpa using hxy
              have haB : (a.1 : V) ∈ B := habval.symm ▸ b.1.2
              exact Set.disjoint_left.mp hAB a.1.2 haB
      | inr b =>
          cases y with
          | inl a =>
              exfalso
              have hbaval : (b.1 : V) = (a.1 : V) := by simpa using hxy
              have haB : (a.1 : V) ∈ B := hbaval ▸ b.1.2
              exact Set.disjoint_left.mp hAB a.1.2 haB
          | inr b' =>
              congr 1
              apply Subtype.ext
              apply Subtype.ext
              exact hxy
  }
  let C : SimpleGraph.Copy L.incidenceGraph G := {
    toHom := {
      toFun := f
      map_rel' := by
        intro x y hxy
        cases x with
        | inl a =>
            cases y with
            | inl a' => exact False.elim hxy
            | inr b => exact hKG (hHK hxy)
        | inr b =>
            cases y with
            | inl a => exact G.symm.symm _ _ (hKG (hHK hxy))
            | inr b' => exact False.elim hxy
    }
    injective' := f.injective
  }
  have hsource : L.incidenceGraph.IsRegularOfDegree k := by
    intro x
    cases x with
    | inl a => exact (incidenceGraph_degree_inl L a).trans (hLleft a)
    | inr b => exact (incidenceGraph_degree_inr L b).trans (hLright b)
  let S : G.Subgraph := C.toSubgraph
  have hSne : S.verts.Nonempty := by
    obtain ⟨a, ha⟩ := hA₁
    let x : Sum {a // a ∈ A₁} {b // b ∈ B₁} := Sum.inl ⟨a, ha⟩
    exact ⟨C x, by simp [S, SimpleGraph.Copy.toSubgraph]⟩
  refine ⟨S, hSne, ?_⟩
  intro v
  let e : L.incidenceGraph ≃g S.coe := C.isoToSubgraph
  let x := e.symm v
  have hdeg : S.coe.degree v = k := by
    have he := e.degree_eq x
    rw [e.apply_symm_apply v] at he
    exact he.trans (hsource x)
  change PRSEntry.degreeNumber S.coe v = k
  exact (PRSEntry.degreeNumber_eq_degree S.coe v).trans hdeg

/-- Active-set form of the final factor lemma, still parameterized by the
precise thinning conclusion. -/
theorem finalFactorOnPositive_of_thinning
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) {k d D : ℕ}
    (hk : 0 < k) (hs : G.SupportedOn A₀ B₀)
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (hcard : A₀.card = B₀.card)
    (hright : G.IsRightRegularOn B₀ d)
    (hleft : ∀ a ∈ A₀, G.leftDegree a ≤ D) (hdD : d ≤ D)
    (hD : 4 * max 3 k - 3 ≤ D)
    (hclose : (4 * max 3 k - 4) * D < (4 * max 3 k - 3) * d)
    (hthin : ∀ T, T ≤ D →
      ∃ J : SimpleGraph
          (Sum {a // a ∈ A₀} {b // b ∈ B₀}),
        J ≤ (G.restrictToFinsets A₀ B₀).incidenceGraph ∧
          (∀ v, J.degree v ≤ T) ∧
          T * (G.restrictToFinsets A₀ B₀).incidenceGraph.edgeFinset.card ≤
            D * J.edgeFinset.card) :
    G.ContainsRegularBipartiteSubgraph k := by
  let R := G.restrictToFinsets A₀ B₀
  have hbal : R.IsBalancedRightRegular d := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Fintype.card_coe] using hcard
    · simpa only [Fintype.card_coe] using hB₀.card_pos
    · intro b
      change (G.restrictToFinsets A₀ B₀).rightDegree b = d
      rw [restrictToFinsets_rightDegree G A₀ B₀ hs]
      exact hright b b.2
  have hmax : R.MaxDegreeLE D := by
    constructor
    · intro a
      change (G.restrictToFinsets A₀ B₀).leftDegree a ≤ D
      rw [restrictToFinsets_leftDegree G A₀ B₀ hs]
      exact hleft a a.2
    · intro b
      change (G.restrictToFinsets A₀ B₀).rightDegree b ≤ D
      rw [restrictToFinsets_rightDegree G A₀ B₀ hs, hright b b.2]
      exact hdD
  apply containsRegularBipartiteSubgraph_of_restrictToFinsets G A₀ B₀
  exact finalFactorPositive_of_thinning hk hbal hmax hD hclose hthin

/-- Final PRS/AFK factor lemma on explicit active parts. -/
theorem finalFactorOnPositive
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) {k d D : ℕ}
    (hk : 0 < k) (hs : G.SupportedOn A₀ B₀)
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (hcard : A₀.card = B₀.card)
    (hright : G.IsRightRegularOn B₀ d)
    (hleft : ∀ a ∈ A₀, G.leftDegree a ≤ D) (hdD : d ≤ D)
    (hD : 4 * max 3 k - 3 ≤ D)
    (hclose : (4 * max 3 k - 4) * D < (4 * max 3 k - 3) * d) :
    G.ContainsRegularBipartiteSubgraph k := by
  refine finalFactorOnPositive_of_thinning G A₀ B₀ hk hs hA₀ hB₀ hcard
    hright hleft hdD hD hclose ?_
  intro T hT
  apply exists_incidenceGraph_thinning
  · intro a
    rw [restrictToFinsets_leftDegree G A₀ B₀ hs]
    exact hleft a a.2
  · intro b
    rw [restrictToFinsets_rightDegree G A₀ B₀ hs, hright b b.2]
    exact hdD
  · exact hT

end Finite

end BipartiteGraph

end Erdos182
