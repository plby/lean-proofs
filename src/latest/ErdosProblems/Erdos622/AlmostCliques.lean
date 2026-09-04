/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib
import ErdosProblems.Erdos58.Structural.SpliceConstruction
import ErdosProblems.Erdos622.Assembly
import ErdosProblems.Erdos622.Concentration
import ErdosProblems.Erdos622.Regimes
import ErdosProblems.Erdos622.TailoredTrichotomy
import ErdosProblems.Erdos622.TwoCliqueHamiltonicity

/-!
# Deterministic tools for the almost-two-cliques case of Erdős 622

The first half of this file is the exact deterministic gluing statement used
in the almost-two-cliques branch: Hamilton paths through the two parts and two
vertex-disjoint crossing edges splice to a Hamilton cycle.

The second half gives a finitary large-crossing-matching tool.  It is phrased
with an explicit integer scale, so later asymptotic arguments do not have to
reason with rounded square roots.
-/

open Filter Finset Set
open scoped SimpleGraph

namespace Erdos622.AlmostCliques

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- A path traverses a part exactly when it is simple and its support is that
part.  This formulation is independent of the induced-subgraph subtype and is
therefore convenient for splicing paths back into the ambient graph. -/
def IsHamiltonPathOn (A : Set V) {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ v, v ∈ p.support ↔ v ∈ A

/-- Every ordered pair of distinct vertices of `A` can be joined by a path
whose support is exactly `A`. -/
def IsHamiltonConnectedOn (G : SimpleGraph V) (A : Set V) : Prop :=
  ∀ (a b : A), (a : V) ≠ b →
    ∃ p : G.Walk (a : V) (b : V), IsHamiltonPathOn A p

private lemma IsHamiltonPathOn.length_add_one_eq_ncard
    {A : Set V} {a b : V} {p : G.Walk a b}
    (hp : IsHamiltonPathOn A p) :
    p.length + 1 = A.ncard := by
  have hs : {v : V | v ∈ p.support} = A := Set.ext fun v ↦ hp.2 v
  rw [← hs, Set.ncard_eq_toFinset_card']
  have hfin : ({v : V | v ∈ p.support} : Set V).toFinset = p.support.toFinset := by
    ext v
    simp
  rw [hfin, List.toFinset_card_of_nodup hp.1.support_nodup]
  exact (SimpleGraph.Walk.length_support p).symm

/-- Two disjoint cross edges close Hamilton paths in two disjoint parts to a
Hamilton cycle.  The graph may have arbitrary additional edges. -/
theorem isHamiltonian_of_two_cross_edges
    (A B : Set V) (hAB : Disjoint A B) (hcover : A ∪ B = Set.univ)
    {a₁ a₂ b₁ b₂ : V}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (hab₁ : G.Adj a₁ b₁) (hab₂ : G.Adj a₂ b₂)
    {c : G.Walk a₁ a₂} (hc : IsHamiltonPathOn A c)
    {d : G.Walk b₁ b₂} (hd : IsHamiltonPathOn B d) :
    G.IsHamiltonian := by
  let L : Erdos58.TwoLinkage G A B :=
    { a₁ := a₁
      a₂ := a₂
      b₁ := b₁
      b₂ := b₂
      p := hab₁.toWalk
      q := hab₂.toWalk
      p_isPath := hab₁.isPath_toWalk
      q_isPath := hab₂.isPath_toWalk
      a₁_mem := ha₁
      a₂_mem := ha₂
      b₁_mem := hb₁
      b₂_mem := hb₂
      disjoint_support := by
        rw [SimpleGraph.Adj.support_toWalk, SimpleGraph.Adj.support_toWalk,
          List.disjoint_left]
        intro x hxP hxQ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxP hxQ
        rcases hxP with rfl | rfl <;> rcases hxQ with rfl | rfl
        · exact ha rfl
        · exact Set.disjoint_left.1 hAB ha₁ hb₂
        · exact Set.disjoint_left.1 hAB ha₂ hb₁
        · exact hb rfl
      p_interior := by simp [SimpleGraph.Adj.support_toWalk]
      q_interior := by simp [SimpleGraph.Adj.support_toWalk] }
  let w : G.Walk a₁ a₁ := Erdos58.SpliceData.close L.p d L.q c
  have hwCycle : w.IsCycle := by
    exact Erdos58.Structural.linkage_close_isCycle L hAB c d hc.1 hd.1
      (fun x hx ↦ (hc.2 x).mp hx) (fun x hx ↦ (hd.2 x).mp hx)
  have hcard : Fintype.card V = A.ncard + B.ncard := by
    calc
      Fintype.card V = (Set.univ : Set V).ncard := by simp
      _ = (A ∪ B).ncard := by rw [hcover]
      _ = A.ncard + B.ncard := Set.ncard_union_eq hAB
  have hcLen := hc.length_add_one_eq_ncard
  have hdLen := hd.length_add_one_eq_ncard
  have hpLen : L.p.length = 1 := by simp [L]
  have hqLen : L.q.length = 1 := by simp [L]
  intro _
  refine ⟨a₁, w, (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq).2
    ⟨hwCycle, ?_⟩⟩
  simp only [w, Erdos58.SpliceData.length_close, SimpleGraph.Adj.length_toWalk]
  rw [hpLen, hqLen, hcard]
  omega

/-- Hamilton connectivity of each side packages the preceding splice lemma
into the criterion used in the almost-two-cliques branch. -/
theorem isHamiltonian_of_hamiltonConnected_parts
    (A B : Set V) (hAB : Disjoint A B) (hcover : A ∪ B = Set.univ)
    (hA : IsHamiltonConnectedOn G A) (hB : IsHamiltonConnectedOn G B)
    {a₁ a₂ b₁ b₂ : V}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (hab₁ : G.Adj a₁ b₁) (hab₂ : G.Adj a₂ b₂) :
    G.IsHamiltonian := by
  obtain ⟨c, hc⟩ := hA ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ ha
  obtain ⟨d, hd⟩ := hB ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ hb
  exact isHamiltonian_of_two_cross_edges A B hAB hcover ha₁ ha₂ hb₁ hb₂
    ha hb hab₁ hab₂ hc hd

/-! ## Crossing matchings in regular graphs -/

/-- The number of ordered adjacent pairs with first endpoint in `S` and
second endpoint in `T`.  For disjoint sets this is the ordinary number of
edges between the two sets. -/
def pairCount (G : SimpleGraph V) (S T : Finset V) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then (1 : ℕ) else 0

lemma pairCount_empty_left (G : SimpleGraph V) (T : Finset V) :
    pairCount G ∅ T = 0 := by simp [pairCount]

lemma pairCount_empty_right (G : SimpleGraph V) (S : Finset V) :
    pairCount G S ∅ = 0 := by simp [pairCount]

lemma pairCount_union_left {S T U : Finset V} (hST : Disjoint S T) :
    pairCount G (S ∪ T) U = pairCount G S U + pairCount G T U := by
  simp [pairCount, Finset.sum_union hST]

lemma pairCount_union_right {S T U : Finset V} (hST : Disjoint S T) :
    pairCount G U (S ∪ T) = pairCount G U S + pairCount G U T := by
  unfold pairCount
  simp_rw [Finset.sum_union hST]
  exact Finset.sum_add_distrib

lemma pairCount_mono_left {S T U : Finset V} (hST : S ⊆ T) :
    pairCount G S U ≤ pairCount G T U := by
  unfold pairCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ ↦ Nat.zero_le _)

lemma pairCount_mono_right {S T U : Finset V} (hST : S ⊆ T) :
    pairCount G U S ≤ pairCount G U T := by
  unfold pairCount
  apply Finset.sum_le_sum
  intro x hx
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ ↦ Nat.zero_le _)

lemma pairCount_le_card_mul (G : SimpleGraph V) (S T : Finset V) :
    pairCount G S T ≤ S.card * T.card := by
  unfold pairCount
  calc
    (∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then (1 : ℕ) else 0) ≤
        ∑ _x ∈ S, T.card := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        (∑ y ∈ T, if G.Adj x y then (1 : ℕ) else 0) ≤
            ∑ _y ∈ T, (1 : ℕ) := by
          exact Finset.sum_le_sum fun _ _ ↦ by split <;> simp
        _ = T.card := by simp
    _ = S.card * T.card := by simp

lemma pairCount_eq_zero_of_forall_not_adj
    {S T : Finset V} (h : ∀ x ∈ S, ∀ y ∈ T, ¬G.Adj x y) :
    pairCount G S T = 0 := by
  unfold pairCount
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  simp [h x hx y hy]

lemma pairCount_symm (G : SimpleGraph V) (S T : Finset V) :
    pairCount G S T = pairCount G T S := by
  simp only [pairCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [G.adj_comm]

lemma pairCount_univ (G : SimpleGraph V) (S : Finset V) :
    pairCount G S Finset.univ = ∑ x ∈ S, G.degree x := by
  unfold pairCount
  apply Finset.sum_congr rfl
  intro x hx
  rw [← G.card_neighborFinset_eq_degree x, Finset.card_eq_sum_ones]
  have hnf : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by
    ext y
    simp
  rw [hnf, Finset.sum_filter]

lemma pairCount_univ_of_regular
    {d : ℕ} (hreg : G.IsRegularOfDegree d) (S : Finset V) :
    pairCount G S Finset.univ = S.card * d := by
  rw [pairCount_univ]
  simp [hreg.degree_eq]

lemma pairCount_add_compl (G : SimpleGraph V) (S : Finset V) :
    pairCount G S S + pairCount Gᶜ S S = S.card * (S.card - 1) := by
  unfold pairCount
  simp only [SimpleGraph.compl_adj]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ x ∈ S, ((∑ y ∈ S, if G.Adj x y then 1 else 0) +
        ∑ y ∈ S, if Gᶜ.Adj x y then 1 else 0) =
        ∑ _x ∈ S, (S.card - 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_add_distrib]
      calc
        ∑ y ∈ S, ((if G.Adj x y then 1 else 0) +
            if Gᶜ.Adj x y then 1 else 0) =
            ∑ y ∈ S, if x ≠ y then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hxy : x = y
          · subst y
            simp
          · by_cases h : G.Adj x y <;> simp [h, hxy]
        _ = S.card - 1 := by
          rw [← Finset.card_filter]
          have heq : S.filter (x ≠ ·) = S.erase x := by
            ext y
            simp [eq_comm, and_comm]
          rw [heq, Finset.card_erase_of_mem hx]
    _ = S.card * (S.card - 1) := by simp

lemma pairCount_cast_eq_edgeCount (G : SimpleGraph V) (S T : Finset V) :
    (pairCount G S T : ℝ) = Trichotomy.edgeCount G S T := by
  rw [Trichotomy.edgeCount_eq_sum_degreeInto]
  unfold pairCount
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  rw [Trichotomy.degreeInto_eq_card_filter]
  have hnat : (∑ y ∈ T, if G.Adj x y then (1 : ℕ) else 0) =
      (T.filter (G.Adj x)).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  exact_mod_cast hnat

/-- The missing edges of an induced graph are bounded by the ordered missing
pairs in its ambient vertex set.  We deliberately keep the harmless factor
two, since it makes monotonicity under further sampling immediate. -/
lemma card_compl_edgeFinset_induce_le_pairCount
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (G.induce (S : Set V))ᶜ.edgeFinset.card ≤ pairCount Gᶜ S S := by
  have hdeg : ∑ x : (S : Set V), (G.induce (S : Set V))ᶜ.degree x =
      pairCount Gᶜ S S := by
    unfold pairCount
    conv_rhs => rw [← Finset.sum_attach]
    have hattach : S.attach = Finset.univ := by
      ext x
      simp
    rw [hattach]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← (G.induce (S : Set V))ᶜ.card_neighborFinset_eq_degree
      ⟨x, x.property⟩]
    rw [Finset.card_eq_sum_ones]
    have hnf : (G.induce (S : Set V))ᶜ.neighborFinset ⟨x, x.property⟩ =
        S.attach.filter fun y ↦ x ≠ y ∧ ¬G.Adj x y := by
      ext y
      simp
    rw [hnf, Finset.sum_filter]
    simpa using (Finset.sum_attach S (fun y : V ↦
      if x ≠ y ∧ ¬G.Adj x y then (1 : ℕ) else 0))
  have htwice := (G.induce (S : Set V))ᶜ.sum_degrees_eq_twice_card_edges
  rw [hdeg] at htwice
  omega

lemma pairCount_self_le_card_mul_pred
    (G : SimpleGraph V) (S : Finset V) :
    pairCount G S S ≤ S.card * (S.card - 1) := by
  unfold pairCount
  calc
    (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then (1 : ℕ) else 0) ≤
        ∑ _x ∈ S, (S.card - 1) := by
      apply Finset.sum_le_sum
      intro x hx
      have hproper : S.filter (G.Adj x) ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have : x ∈ S.filter (G.Adj x) := heq.symm ▸ hx
        exact G.loopless.irrefl x (Finset.mem_filter.mp this).2
      have hlt := Finset.card_lt_card hproper
      calc
        (∑ y ∈ S, if G.Adj x y then (1 : ℕ) else 0) =
            (S.filter (G.Adj x)).card := by
          rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        _ ≤ S.card - 1 := by omega
    _ = S.card * (S.card - 1) := by simp

/-- A finite set of pairwise vertex-disjoint edges. -/
def EdgeMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
    (M : Set (Sym2 V)).Pairwise fun e f ↦ Disjoint (e : Set V) (f : Set V)

/-- A maximum-cardinality matching is inclusion-maximal in the only form
needed below: every outside edge meets an edge of the matching. -/
lemma exists_maximal_edgeMatching (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Sym2 V), EdgeMatching G M ∧
      ∀ e ∈ G.edgeFinset, e ∉ M →
        ∃ m ∈ M, ¬ Disjoint (e : Set V) (m : Set V) := by
  classical
  let good := G.edgeFinset.powerset.filter fun (M : Finset (Sym2 V)) ↦
    (M : Set (Sym2 V)).Pairwise fun e f ↦ Disjoint (e : Set V) (f : Set V)
  have hgood : good.Nonempty := ⟨∅, by simp [good]⟩
  obtain ⟨M, hMgood, hMmax⟩ := good.exists_max_image Finset.card hgood
  have hMsub : M ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMgood).1
  have hMpair : (M : Set (Sym2 V)).Pairwise
      (fun e f ↦ Disjoint (e : Set V) (f : Set V)) :=
    (Finset.mem_filter.mp hMgood).2
  refine ⟨M, ⟨hMsub, hMpair⟩, ?_⟩
  intro e heG heM
  by_contra hdisj
  push_neg at hdisj
  have hpairInsert : ((insert e M : Finset (Sym2 V)) : Set (Sym2 V)).Pairwise
      (fun p q ↦ Disjoint (p : Set V) (q : Set V)) := by
    rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hMpair, ?_⟩
    intro m hm hem
    exact ⟨hdisj m hm, (hdisj m hm).symm⟩
  have hinsGood : insert e M ∈ good := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, hpairInsert⟩
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heG
    · exact hMsub hf
  have hle := hMmax (insert e M) hinsGood
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

/-- The graph obtained by retaining exactly the edges crossing `A`. -/
def crossingGraph (G : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A))
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
      (fun h ↦ Or.inl ⟨h.2, h.1⟩)⟩
  loopless := by
    constructor
    intro x h
    exact G.loopless.irrefl x h.1

noncomputable instance crossingGraph.instDecidableRel
    (G : SimpleGraph V) (A : Set V) : DecidableRel (crossingGraph G A).Adj :=
  Classical.decRel _

@[simp] lemma crossingGraph_adj {A : Set V} {x y : V} :
    (crossingGraph G A).Adj x y ↔
      G.Adj x y ∧ ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := Iff.rfl

/-- A balanced cut in an `(n+1)`-regular graph cannot have a crossing-edge
cover which is small on both sides.  The explicit inequalities are the
integer form of the square-root threshold in DKM Lemma 3.6. -/
theorem no_small_crossing_cover_of_regular_balanced
    (n : ℕ) (A B C : Finset V)
    (hAB : Disjoint A B) (hABuniv : A ∪ B = Finset.univ)
    (hAcard : A.card = n) (hBcard : B.card = n)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hC : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y → x ∈ C ∨ y ∈ C)
    (hsmallA : (A ∩ C).card * ((A ∩ C).card + 3) < 2 * n)
    (hsmallB : (B ∩ C).card * ((B ∩ C).card + 3) < 2 * n) :
    False := by
  let CA := A ∩ C
  let A₀ := A \ C
  let CB := B ∩ C
  let B₀ := B \ C
  have hCA₀ : Disjoint CA A₀ := by
    exact (Finset.disjoint_sdiff_inter A C).symm
  have hCB₀ : Disjoint CB B₀ := by
    exact (Finset.disjoint_sdiff_inter B C).symm
  have hAsplit : CA ∪ A₀ = A := by
    ext x
    simp only [CA, A₀, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hBsplit : CB ∪ B₀ = B := by
    ext x
    simp only [CB, B₀, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hA₀B₀ : Disjoint A₀ B₀ := by
    apply Finset.disjoint_of_subset_left Finset.sdiff_subset
    apply Finset.disjoint_of_subset_right Finset.sdiff_subset
    exact hAB
  have hno : ∀ x ∈ A₀, ∀ y ∈ B₀, ¬G.Adj x y := by
    intro x hx y hy hxy
    have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
    have hxC : x ∉ C := (Finset.mem_sdiff.mp hx).2
    have hyB : y ∈ B := (Finset.mem_sdiff.mp hy).1
    have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
    rcases hC x hxA y hyB hxy with hx' | hy'
    · exact hxC hx'
    · exact hyC hy'
  have hzero : pairCount G A₀ B₀ = 0 :=
    pairCount_eq_zero_of_forall_not_adj hno
  have hcardA : CA.card + A₀.card = n := by
    rw [← hAcard, ← hAsplit, Finset.card_union_of_disjoint hCA₀]
  have hcardB : CB.card + B₀.card = n := by
    rw [← hBcard, ← hBsplit, Finset.card_union_of_disjoint hCB₀]
  have hboundA : pairCount G CA A₀ + pairCount G CA B₀ ≤ CA.card * (n + 1) := by
    calc
      pairCount G CA A₀ + pairCount G CA B₀ = pairCount G CA (A₀ ∪ B₀) :=
        (pairCount_union_right hA₀B₀).symm
      _ ≤ pairCount G CA Finset.univ := pairCount_mono_right (Finset.subset_univ _)
      _ = CA.card * (n + 1) := pairCount_univ_of_regular hreg CA
  have hboundB : pairCount G CB B₀ + pairCount G CB A₀ ≤ CB.card * (n + 1) := by
    calc
      pairCount G CB B₀ + pairCount G CB A₀ = pairCount G CB (B₀ ∪ A₀) :=
        (pairCount_union_right hA₀B₀.symm).symm
      _ ≤ pairCount G CB Finset.univ := pairCount_mono_right (Finset.subset_univ _)
      _ = CB.card * (n + 1) := pairCount_univ_of_regular hreg CB
  have hdegreeA₀ :
      A₀.card * (n + 1) =
        pairCount G A₀ A₀ + pairCount G A₀ CA + pairCount G A₀ CB := by
    rw [← pairCount_univ_of_regular hreg A₀]
    calc
      pairCount G A₀ Finset.univ = pairCount G A₀ (A ∪ B) := by rw [hABuniv]
      _ = pairCount G A₀ A + pairCount G A₀ B := pairCount_union_right hAB
      _ = pairCount G A₀ (CA ∪ A₀) + pairCount G A₀ (CB ∪ B₀) := by
        rw [hAsplit, hBsplit]
      _ = (pairCount G A₀ CA + pairCount G A₀ A₀) +
          (pairCount G A₀ CB + pairCount G A₀ B₀) := by
        rw [pairCount_union_right hCA₀, pairCount_union_right hCB₀]
      _ = pairCount G A₀ A₀ + pairCount G A₀ CA + pairCount G A₀ CB := by
        rw [hzero]
        omega
  have hdegreeB₀ :
      B₀.card * (n + 1) =
        pairCount G B₀ B₀ + pairCount G B₀ CB + pairCount G B₀ CA := by
    rw [← pairCount_univ_of_regular hreg B₀]
    calc
      pairCount G B₀ Finset.univ = pairCount G B₀ (A ∪ B) := by rw [hABuniv]
      _ = pairCount G B₀ A + pairCount G B₀ B := pairCount_union_right hAB
      _ = pairCount G B₀ (CA ∪ A₀) + pairCount G B₀ (CB ∪ B₀) := by
        rw [hAsplit, hBsplit]
      _ = (pairCount G B₀ CA + pairCount G B₀ A₀) +
          (pairCount G B₀ CB + pairCount G B₀ B₀) := by
        rw [pairCount_union_right hCA₀, pairCount_union_right hCB₀]
      _ = pairCount G B₀ B₀ + pairCount G B₀ CB + pairCount G B₀ CA := by
        rw [pairCount_symm G B₀ A₀, hzero]
        omega
  have hintA := pairCount_self_le_card_mul_pred G A₀
  have hintB := pairCount_self_le_card_mul_pred G B₀
  have hsymA : pairCount G A₀ CA = pairCount G CA A₀ := pairCount_symm G _ _
  have hsymB : pairCount G B₀ CB = pairCount G CB B₀ := pairCount_symm G _ _
  have hcross : pairCount G A₀ CB = pairCount G CB A₀ := pairCount_symm G _ _
  have hcross' : pairCount G B₀ CA = pairCount G CA B₀ := pairCount_symm G _ _
  have hsmallCA : CA.card * (CA.card + 3) < 2 * n := by
    simpa [CA] using hsmallA
  have hsmallCB : CB.card * (CB.card + 3) < 2 * n := by
    simpa [CB] using hsmallB
  have hA₀pos : 0 < A₀.card := by
    by_contra h
    have hz : A₀.card = 0 := by omega
    nlinarith only [hsmallCA, hcardA, hz]
  have hB₀pos : 0 < B₀.card := by
    by_contra h
    have hz : B₀.card = 0 := by omega
    nlinarith only [hsmallCB, hcardB, hz]
  have hpredA : A₀.card - 1 + 1 = A₀.card := Nat.sub_add_cancel hA₀pos
  have hpredB : B₀.card - 1 + 1 = B₀.card := Nat.sub_add_cancel hB₀pos
  by_cases horient : pairCount G CB A₀ ≤ pairCount G CA B₀
  · rw [hsymA, hcross] at hdegreeA₀
    nlinarith only [hsmallCA, hcardA, hboundA, hdegreeA₀, hintA, horient, hpredA]
  · have horient' : pairCount G CA B₀ ≤ pairCount G CB A₀ :=
      Nat.le_of_lt (Nat.lt_of_not_ge horient)
    rw [hsymB, hcross'] at hdegreeB₀
    nlinarith only [hsmallCB, hcardB, hboundB, hdegreeB₀, hintB, horient', hpredB]

/-- The vertices incident with at least one edge of a finite matching. -/
def matchingVertices (M : Finset (Sym2 V)) : Finset V :=
  M.biUnion Sym2.toFinset

lemma card_matchingVertices_le (M : Finset (Sym2 V)) :
    (matchingVertices M).card ≤ 2 * M.card := by
  unfold matchingVertices
  calc
    (M.biUnion Sym2.toFinset).card ≤ ∑ e ∈ M, e.toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ M, 2 := by
      apply Finset.sum_le_sum
      intro e he
      rw [Sym2.card_toFinset]
      split <;> omega
    _ = 2 * M.card := by simp [Nat.mul_comm]

/-- The endpoint set of an inclusion-maximal matching covers every edge. -/
lemma matchingVertices_cover_of_maximal
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V))
    (hmax : ∀ e ∈ H.edgeFinset, e ∉ M →
      ∃ m ∈ M, ¬ Disjoint (e : Set V) (m : Set V))
    {x y : V} (hxy : H.Adj x y) :
    x ∈ matchingVertices M ∨ y ∈ matchingVertices M := by
  have heH : s(x, y) ∈ H.edgeFinset := by simpa using hxy
  by_cases heM : s(x, y) ∈ M
  · left
    exact Finset.mem_biUnion.mpr ⟨s(x, y), heM, by simp⟩
  · obtain ⟨m, hmM, hem⟩ := hmax s(x, y) heH heM
    obtain ⟨z, hze, hzm⟩ := Set.not_disjoint_iff.mp hem
    have hz : z ∈ matchingVertices M :=
      Finset.mem_biUnion.mpr ⟨m, hmM, Sym2.mem_toFinset.mpr hzm⟩
    change z ∈ s(x, y) at hze
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz

/-- A crossing edge has at most one endpoint on either fixed side of the
cut.  Consequently a set of crossing edges contributes at most one endpoint
per edge to either side. -/
lemma card_inter_matchingVertices_le_of_crossing
    (A S : Finset V) (M : Finset (Sym2 V))
    (hside : (S : Set V) ⊆ (A : Set V) ∨
      Disjoint (S : Set V) (A : Set V))
    (hM : M ⊆ (crossingGraph G (A : Set V)).edgeFinset) :
    (S ∩ matchingVertices M).card ≤ M.card := by
  have hinter : S ∩ matchingVertices M ⊆
      M.biUnion (fun e ↦ S ∩ e.toFinset) := by
    intro x hx
    obtain ⟨hxS, hxM⟩ := Finset.mem_inter.mp hx
    obtain ⟨e, heM, hxe⟩ := Finset.mem_biUnion.mp hxM
    exact Finset.mem_biUnion.mpr ⟨e, heM, Finset.mem_inter.mpr ⟨hxS, hxe⟩⟩
  calc
    (S ∩ matchingVertices M).card ≤
        (M.biUnion (fun e ↦ S ∩ e.toFinset)).card :=
      Finset.card_le_card hinter
    _ ≤ ∑ e ∈ M, (S ∩ e.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ M, 1 := by
      apply Finset.sum_le_sum
      intro e heM
      rw [Finset.card_le_one]
      intro x hx y hy
      obtain ⟨hxS, hxe⟩ := Finset.mem_inter.mp hx
      obtain ⟨hyS, hye⟩ := Finset.mem_inter.mp hy
      by_contra hxy
      have heq : e = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp
        ⟨Sym2.mem_toFinset.mp hxe, Sym2.mem_toFinset.mp hye⟩
      have hadj : (crossingGraph G (A : Set V)).Adj x y := by
        have he := hM heM
        rw [SimpleGraph.mem_edgeFinset, heq, SimpleGraph.mem_edgeSet] at he
        exact he
      rcases hside with hsub | hdisj
      · have hxA := hsub hxS
        have hyA := hsub hyS
        rcases hadj.2 with h | h
        · exact h.2 hyA
        · exact h.1 hxA
      · have hxA : x ∉ (A : Set V) := fun hxA ↦
          Set.disjoint_left.mp hdisj hxS hxA
        have hyA : y ∉ (A : Set V) := fun hyA ↦
          Set.disjoint_left.mp hdisj hyS hyA
        rcases hadj.2 with h | h
        · exact hxA h.1
        · exact hyA h.2
    _ = M.card := by simp

private lemma pairCount_singleton_self_le_pred
    (A : Finset V) {x : V} (hx : x ∈ A) :
    pairCount G {x} A ≤ A.card - 1 := by
  unfold pairCount
  simp only [Finset.sum_singleton]
  have hproper : A.filter (G.Adj x) ⊂ A := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have : x ∈ A.filter (G.Adj x) := heq.symm ▸ hx
    exact G.loopless.irrefl x (Finset.mem_filter.mp this).2
  have hlt := Finset.card_lt_card hproper
  calc
    (∑ y ∈ A, if G.Adj x y then (1 : ℕ) else 0) =
        (A.filter (G.Adj x)).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    _ ≤ A.card - 1 := by omega

private lemma pairCount_singleton_le_cover
    (B C : Finset V) {x : V}
    (h : ∀ y ∈ B, G.Adj x y → y ∈ C) :
    pairCount G {x} B ≤ (B ∩ C).card := by
  unfold pairCount
  simp only [Finset.sum_singleton]
  calc
    (∑ y ∈ B, if G.Adj x y then (1 : ℕ) else 0) ≤
        ∑ y ∈ B, if y ∈ C then (1 : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hxy : G.Adj x y
      · simp [hxy, h y hy hxy]
      · simp [hxy]
    _ = (B ∩ C).card := by
      have heq : B.filter (fun y ↦ y ∈ C) = B ∩ C := by
        ext y
        simp
      rw [← heq, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Explicit large crossing matching for a balanced cut.  At any integer
scale `k` satisfying `(2k)(2k+3) < 2n`, every `(n+1)`-regular graph on a
balanced partition has a crossing matching of at least `k` edges.  Thus one
may take any fixed sufficiently small integer multiple of `√n`, without
introducing real-number rounding into later arguments. -/
theorem exists_large_crossing_matching_of_regular_balanced
    (n k : ℕ) (A B : Finset V)
    (hAB : Disjoint A B) (hABuniv : A ∪ B = Finset.univ)
    (hAcard : A.card = n) (hBcard : B.card = n)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hscale : (2 * k) * (2 * k + 3) < 2 * n) :
    ∃ M : Finset (Sym2 V),
      EdgeMatching (crossingGraph G (A : Set V)) M ∧ k ≤ M.card := by
  obtain ⟨M, hM, hmax⟩ := exists_maximal_edgeMatching (crossingGraph G (A : Set V))
  refine ⟨M, hM, ?_⟩
  by_contra hk
  have hMlt : M.card < k := Nat.lt_of_not_ge hk
  let C := matchingVertices M
  have hCcard : C.card < 2 * k := by
    have hle : C.card ≤ 2 * M.card := by
      simpa [C] using card_matchingVertices_le M
    omega
  have hAC : (A ∩ C).card < 2 * k :=
    lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_right) hCcard
  have hBC : (B ∩ C).card < 2 * k :=
    lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_right) hCcard
  have hsmallA : (A ∩ C).card * ((A ∩ C).card + 3) < 2 * n := by
    nlinarith only [hAC, hscale]
  have hsmallB : (B ∩ C).card * ((B ∩ C).card + 3) < 2 * n := by
    nlinarith only [hBC, hscale]
  apply no_small_crossing_cover_of_regular_balanced n A B C hAB hABuniv
    hAcard hBcard hreg
  · intro x hx y hy hxy
    have hyA : y ∉ A := fun hyA ↦ Finset.disjoint_left.mp hAB hyA hy
    exact matchingVertices_cover_of_maximal (crossingGraph G (A : Set V)) M hmax
      ⟨hxy, Or.inl ⟨hx, hyA⟩⟩
  · exact hsmallA
  · exact hsmallB

/-- A version of the crossing-cover obstruction for an arbitrary cut.  A
large imbalance is ruled out directly by the degree of a vertex outside the
cover.  If the imbalance is smaller than `k`, moving the imbalance into the
cover gives a balanced cut whose cover has fewer than `2k` vertices on each
side. -/
theorem no_small_crossing_cover_of_regular_partition
    (n k : ℕ) (A B C : Finset V)
    (hAB : Disjoint A B) (hABuniv : A ∪ B = Finset.univ)
    (hVcard : Fintype.card V = 2 * n)
    (hAk : k ≤ A.card) (hBk : k ≤ B.card)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hC : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y → x ∈ C ∨ y ∈ C)
    (hAC : (A ∩ C).card < k) (hBC : (B ∩ C).card < k)
    (hscale : (2 * k) * (2 * k + 3) < 2 * n) : False := by
  have hkpos : 0 < k := by omega
  have hcards : A.card + B.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hAB, hABuniv, Finset.card_univ, hVcard]
  have hfarA : ¬ A.card + k ≤ n := by
    intro hfar
    have hnsub : ¬ A ⊆ C := by
      intro hsub
      have heq : A ∩ C = A := Finset.inter_eq_left.mpr hsub
      rw [heq] at hAC
      omega
    obtain ⟨x, hxA, hxC⟩ := Finset.not_subset.mp hnsub
    have hxcover : ∀ y ∈ B, G.Adj x y → y ∈ C := by
      intro y hy hxy
      rcases hC x hxA y hy hxy with hx | hy
      · exact (hxC hx).elim
      · exact hy
    have htotal : pairCount G {x} Finset.univ = n + 1 := by
      simpa using pairCount_univ_of_regular hreg ({x} : Finset V)
    have hsplit : pairCount G {x} Finset.univ =
        pairCount G {x} A + pairCount G {x} B := by
      rw [← hABuniv, pairCount_union_right hAB]
    have hinside := pairCount_singleton_self_le_pred (G := G) A hxA
    have hcross := pairCount_singleton_le_cover (G := G) B C hxcover
    omega
  have hfarB : ¬ B.card + k ≤ n := by
    intro hfar
    have hnsub : ¬ B ⊆ C := by
      intro hsub
      have heq : B ∩ C = B := Finset.inter_eq_left.mpr hsub
      rw [heq] at hBC
      omega
    obtain ⟨y, hyB, hyC⟩ := Finset.not_subset.mp hnsub
    have hycover : ∀ x ∈ A, G.Adj y x → x ∈ C := by
      intro x hx hyx
      rcases hC x hx y hyB hyx.symm with hx | hy
      · exact hx
      · exact (hyC hy).elim
    have htotal : pairCount G {y} Finset.univ = n + 1 := by
      simpa using pairCount_univ_of_regular hreg ({y} : Finset V)
    have hsplit : pairCount G {y} Finset.univ =
        pairCount G {y} B + pairCount G {y} A := by
      rw [← hABuniv, pairCount_union_right hAB, Nat.add_comm]
    have hinside := pairCount_singleton_self_le_pred (G := G) B hyB
    have hcross := pairCount_singleton_le_cover (G := G) A C hycover
    omega
  by_cases hAn : A.card ≤ n
  · let r := n - A.card
    have hrk : r < k := by omega
    have hrB : r ≤ B.card := by omega
    obtain ⟨R, hRB, hRcard⟩ := Finset.exists_subset_card_eq hrB
    let A' := A ∪ R
    let B' := B \ R
    let C' := C ∪ R
    have hAR : Disjoint A R := hAB.mono_right hRB
    have hA'B' : Disjoint A' B' := by
      dsimp [A', B']
      rw [Finset.disjoint_union_left]
      exact ⟨hAB.mono_right Finset.sdiff_subset, Finset.disjoint_sdiff⟩
    have hA'B'univ : A' ∪ B' = Finset.univ := by
      ext x
      have hx : x ∈ A ∨ x ∈ B := by
        have : x ∈ A ∪ B := by rw [hABuniv]; simp
        simpa using this
      simp only [A', B', Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
        iff_true]
      tauto
    have hA'card : A'.card = n := by
      dsimp [A']
      rw [Finset.card_union_of_disjoint hAR, hRcard]
      omega
    have hB'card : B'.card = n := by
      dsimp [B']
      rw [Finset.card_sdiff_of_subset hRB, hRcard]
      omega
    have hC' : ∀ x ∈ A', ∀ y ∈ B', G.Adj x y → x ∈ C' ∨ y ∈ C' := by
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hxA | hxR
      · have hyB := (Finset.mem_sdiff.mp hy).1
        rcases hC x hxA y hyB hxy with hxC | hyC
        · exact Or.inl (Finset.mem_union_left _ hxC)
        · exact Or.inr (Finset.mem_union_left _ hyC)
      · exact Or.inl (Finset.mem_union_right _ hxR)
    have hA'C'lt : (A' ∩ C').card < 2 * k := by
      have hsub : A' ∩ C' ⊆ (A ∩ C) ∪ R := by
        intro x hx
        simp only [A', C', Finset.mem_inter, Finset.mem_union] at hx ⊢
        tauto
      calc
        (A' ∩ C').card ≤ ((A ∩ C) ∪ R).card := Finset.card_le_card hsub
        _ ≤ (A ∩ C).card + R.card := Finset.card_union_le (A ∩ C) R
        _ < 2 * k := by omega
    have hB'C'lt : (B' ∩ C').card < 2 * k := by
      have hsub : B' ∩ C' ⊆ B ∩ C := by
        intro x hx
        simp only [B', C', Finset.mem_inter, Finset.mem_sdiff,
          Finset.mem_union] at hx ⊢
        tauto
      have hle := Finset.card_le_card hsub
      omega
    have hsmallA : (A' ∩ C').card * ((A' ∩ C').card + 3) < 2 * n := by
      nlinarith only [hA'C'lt, hscale]
    have hsmallB : (B' ∩ C').card * ((B' ∩ C').card + 3) < 2 * n := by
      nlinarith only [hB'C'lt, hscale]
    exact no_small_crossing_cover_of_regular_balanced n A' B' C' hA'B' hA'B'univ
      hA'card hB'card hreg hC' hsmallA hsmallB
  · have hnA : n ≤ A.card := by omega
    let r := A.card - n
    have hrk : r < k := by omega
    have hrA : r ≤ A.card := Nat.sub_le _ _
    obtain ⟨R, hRA, hRcard⟩ := Finset.exists_subset_card_eq hrA
    let A' := A \ R
    let B' := B ∪ R
    let C' := C ∪ R
    have hBR : Disjoint B R := hAB.symm.mono_right hRA
    have hA'B' : Disjoint A' B' := by
      dsimp [A', B']
      rw [Finset.disjoint_union_right]
      exact ⟨hAB.mono_left Finset.sdiff_subset, Finset.sdiff_disjoint⟩
    have hA'B'univ : A' ∪ B' = Finset.univ := by
      ext x
      have hx : x ∈ A ∨ x ∈ B := by
        have : x ∈ A ∪ B := by rw [hABuniv]; simp
        simpa using this
      simp only [A', B', Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
        iff_true]
      tauto
    have hA'card : A'.card = n := by
      dsimp [A']
      rw [Finset.card_sdiff_of_subset hRA, hRcard]
      omega
    have hB'card : B'.card = n := by
      dsimp [B']
      rw [Finset.card_union_of_disjoint hBR, hRcard]
      omega
    have hC' : ∀ x ∈ A', ∀ y ∈ B', G.Adj x y → x ∈ C' ∨ y ∈ C' := by
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hy with hyB | hyR
      · have hxA := (Finset.mem_sdiff.mp hx).1
        rcases hC x hxA y hyB hxy with hxC | hyC
        · exact Or.inl (Finset.mem_union_left _ hxC)
        · exact Or.inr (Finset.mem_union_left _ hyC)
      · exact Or.inr (Finset.mem_union_right _ hyR)
    have hA'C'lt : (A' ∩ C').card < 2 * k := by
      have hsub : A' ∩ C' ⊆ A ∩ C := by
        intro x hx
        simp only [A', C', Finset.mem_inter, Finset.mem_sdiff,
          Finset.mem_union] at hx ⊢
        tauto
      have hle := Finset.card_le_card hsub
      omega
    have hB'C'lt : (B' ∩ C').card < 2 * k := by
      have hsub : B' ∩ C' ⊆ (B ∩ C) ∪ R := by
        intro x hx
        simp only [B', C', Finset.mem_inter, Finset.mem_union] at hx ⊢
        tauto
      calc
        (B' ∩ C').card ≤ ((B ∩ C) ∪ R).card := Finset.card_le_card hsub
        _ ≤ (B ∩ C).card + R.card := Finset.card_union_le (B ∩ C) R
        _ < 2 * k := by omega
    have hsmallA : (A' ∩ C').card * ((A' ∩ C').card + 3) < 2 * n := by
      nlinarith only [hA'C'lt, hscale]
    have hsmallB : (B' ∩ C').card * ((B' ∩ C').card + 3) < 2 * n := by
      nlinarith only [hB'C'lt, hscale]
    exact no_small_crossing_cover_of_regular_balanced n A' B' C' hA'B' hA'B'univ
      hA'card hB'card hreg hC' hsmallA hsmallB

/-- Explicit form of the large crossing-matching lemma for an arbitrary
partition.  It applies uniformly to every cut whose two sides have at least
`k` vertices; the displayed polynomial condition is a finite, rounding-free
replacement for the phrase "for all sufficiently large `n`". -/
theorem exists_large_crossing_matching_of_regular_partition
    (n k : ℕ) (A B : Finset V)
    (hAB : Disjoint A B) (hABuniv : A ∪ B = Finset.univ)
    (hVcard : Fintype.card V = 2 * n)
    (hAk : k ≤ A.card) (hBk : k ≤ B.card)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hscale : (2 * k) * (2 * k + 3) < 2 * n) :
    ∃ M : Finset (Sym2 V),
      EdgeMatching (crossingGraph G (A : Set V)) M ∧ k ≤ M.card := by
  obtain ⟨M, hM, hmax⟩ := exists_maximal_edgeMatching (crossingGraph G (A : Set V))
  refine ⟨M, hM, ?_⟩
  by_contra hk
  have hMlt : M.card < k := Nat.lt_of_not_ge hk
  let C := matchingVertices M
  have hAC : (A ∩ C).card < k := by
    apply lt_of_le_of_lt _ hMlt
    exact card_inter_matchingVertices_le_of_crossing A A M
      (Or.inl (Set.Subset.rfl)) hM.1
  have hBC : (B ∩ C).card < k := by
    apply lt_of_le_of_lt _ hMlt
    exact card_inter_matchingVertices_le_of_crossing A B M
      (Or.inr (by exact_mod_cast hAB.symm)) hM.1
  have hcover : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y → x ∈ C ∨ y ∈ C := by
    intro x hx y hy hxy
    have hyA : y ∉ A := fun hyA ↦ Finset.disjoint_left.mp hAB hyA hy
    exact matchingVertices_cover_of_maximal (crossingGraph G (A : Set V)) M hmax
      ⟨hxy, Or.inl ⟨hx, hyA⟩⟩
  exact no_small_crossing_cover_of_regular_partition n k A B C hAB hABuniv
    hVcard hAk hBk hreg hcover hAC hBC hscale

/-! ## Uniform-powerset estimates used by the almost-two-cliques case -/

private def halfProbability (_ : V) : ℝ := 1 / 2

/-- Number of sampled vertices in a fixed test set. -/
def sampleIntersectionCount (C S : Finset V) : ℝ := ((S ∩ C).card : ℝ)

private lemma sampleIntersectionCount_sum_indicator (C S : Finset V) :
    sampleIntersectionCount C S =
      ∑ v ∈ C, if v ∈ S then (1 : ℝ) else 0 := by
  have heq : S ∩ C = C.filter (fun v ↦ v ∈ S) := by
    ext v
    simp [and_comm]
  simp only [sampleIntersectionCount, heq, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_filter]

lemma bernoulliExpectation_half_sampleIntersectionCount (C : Finset V) :
    Erdos76.FiniteNibble.bernoulliExpectation (Finset.univ : Finset V)
        halfProbability (sampleIntersectionCount C) = (C.card : ℝ) / 2 := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation]
  simp_rw [sampleIntersectionCount_sum_indicator, mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ v ∈ C, ∑ S ∈ (Finset.univ : Finset V).powerset,
        Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S *
          (if v ∈ S then (1 : ℝ) else 0) =
        ∑ _v ∈ C, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      calc
        ∑ S ∈ (Finset.univ : Finset V).powerset,
            Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S *
              (if v ∈ S then (1 : ℝ) else 0) =
            ∑ S ∈ (Finset.univ : Finset V).powerset with v ∈ S,
              Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S hS
          by_cases hvS : v ∈ S <;> simp [hvS]
        _ = 1 / 2 := by
          simpa [halfProbability] using
            (Erdos76.FiniteNibble.sum_bernoulliMass_filter_mem
              (U := (Finset.univ : Finset V)) (p := halfProbability)
              (e := v) (Finset.mem_univ v))
    _ = (C.card : ℝ) / 2 := by simp; ring

lemma sampleIntersectionCount_hasBoundedDifferences (C : Finset V) :
    Erdos76.FiniteNibble.HasBoundedDifferences (Finset.univ : Finset V)
      (sampleIntersectionCount C) (fun v ↦ if v ∈ C then 1 else 0) := by
  intro v _ T hT
  have hvT : v ∉ T := by
    intro hvT
    exact (Finset.mem_erase.mp (hT hvT)).1 rfl
  by_cases hvC : v ∈ C
  · have hnot : v ∉ T ∩ C := fun h ↦ hvT (Finset.mem_inter.mp h).1
    simp [sampleIntersectionCount, hvC, hnot]
  · have heq : insert v T ∩ C = T ∩ C := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hwT, hwC⟩
        · exact (hvC hwC).elim
        · exact ⟨hwT, hwC⟩
      · rintro ⟨hwT, hwC⟩
        exact ⟨Or.inr hwT, hwC⟩
    simp [sampleIntersectionCount, hvC, heq]

private lemma sum_sampleIntersection_lipschitz_sq (C : Finset V) :
    (∑ v ∈ (Finset.univ : Finset V),
        (if v ∈ C then (1 : ℝ) else 0) ^ 2) = C.card := by
  simp

/-- Exact two-sided Hoeffding count for intersection with a fixed test set. -/
theorem sampleIntersectionCount_twoSided (C : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        t ≤ |sampleIntersectionCount C S - (C.card : ℝ) / 2|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card V * Real.exp (-2 * t ^ 2 / C.card) := by
  let U : Finset V := Finset.univ
  let F : Finset V → ℝ := sampleIntersectionCount C
  let c : V → ℝ := fun v ↦ if v ∈ C then 1 else 0
  let A := U.powerset.filter fun S ↦
    Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S
  let B := U.powerset.filter fun S ↦
    F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t
  have hsub : U.powerset.filter (fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|) ⊆
        A ∪ B := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, A, B] at hS ⊢
    rcases le_abs.mp hS.2 with h | h
    · exact Or.inl ⟨hS.1, by linarith⟩
    · exact Or.inr ⟨hS.1, by linarith⟩
  have hcard : (U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card ≤
      A.card + B.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  have hA := Concentration.countEvent_upperTail_le
    (U := U) (F := F) (c := c) (t := t)
    (sampleIntersectionCount_hasBoundedDifferences C) ht
  have hB := Concentration.countEvent_lowerTail_le
    (U := U) (F := F) (c := c) (t := t)
    (sampleIntersectionCount_hasBoundedDifferences C) ht
  change ((U.powerset.filter fun S ↦
      Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S).card : ℝ) ≤
      (2 : ℝ) ^ U.card * Real.exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) at hA
  change ((U.powerset.filter fun S ↦
      F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t).card : ℝ) ≤
      (2 : ℝ) ^ U.card * Real.exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) at hB
  have hcardR : ((U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  have hmean : Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F =
      (C.card : ℝ) / 2 := by
    simpa [U, F] using bernoulliExpectation_half_sampleIntersectionCount C
  have hvariance : (∑ v ∈ U, c v ^ 2) = (C.card : ℝ) := by
    simpa [U, c] using sum_sampleIntersection_lipschitz_sq C
  rw [hmean] at hcardR hA hB
  rw [hvariance] at hA hB
  change ((U.powerset.filter fun S ↦
      t ≤ |F S - (C.card : ℝ) / 2|).card : ℝ) ≤ _
  calc
    ((U.powerset.filter fun S ↦
        t ≤ |F S - (C.card : ℝ) / 2|).card : ℝ) ≤
        (A.card : ℝ) + (B.card : ℝ) := hcardR
    _ ≤ 2 * (2 : ℝ) ^ Fintype.card V *
        Real.exp (-2 * t ^ 2 / C.card) := by
      dsimp [A, B, U, F] at hA hB ⊢
      rw [hmean]
      norm_num at hA hB ⊢
      nlinarith

/-- Union bound for the intersection-count deviations of an arbitrary finite
family of test sets.  The common ambient denominator is what makes the bound
uniform even when some tests are empty. -/
theorem card_familyBadSamples_le [Nonempty V]
    (family : Finset (Finset V)) {t : ℝ} (ht : 0 < t) :
    ((family.biUnion fun C ↦
        (Finset.univ : Finset V).powerset.filter fun S ↦
          t ≤ |sampleIntersectionCount C S - (C.card : ℝ) / 2|).card : ℝ) ≤
      (family.card : ℝ) *
        (2 * (2 : ℝ) ^ Fintype.card V *
          Real.exp (-2 * t ^ 2 / Fintype.card V)) := by
  let bad : Finset V → Finset (Finset V) := fun C ↦
    (Finset.univ : Finset V).powerset.filter fun S ↦
      t ≤ |sampleIntersectionCount C S - (C.card : ℝ) / 2|
  have hcardNat : (family.biUnion bad).card ≤ ∑ C ∈ family, (bad C).card :=
    Finset.card_biUnion_le
  have hcard : ((family.biUnion bad).card : ℝ) ≤
      ∑ C ∈ family, ((bad C).card : ℝ) := by
    exact_mod_cast hcardNat
  change ((family.biUnion bad).card : ℝ) ≤ _
  calc
    ((family.biUnion bad).card : ℝ) ≤
        ∑ C ∈ family, ((bad C).card : ℝ) := hcard
    _ ≤ ∑ _C ∈ family,
        2 * (2 : ℝ) ^ Fintype.card V *
          Real.exp (-2 * t ^ 2 / Fintype.card V) := by
      apply Finset.sum_le_sum
      intro C hC
      by_cases hCempty : C = ∅
      · subst C
        simp only [neg_mul]
        positivity
      · have hCpos : (0 : ℝ) < C.card := by
          exact_mod_cast (Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hCempty))
        have hCleNat : C.card ≤ Fintype.card V := Finset.card_le_univ C
        have hCle : (C.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hCleNat
        have hfrac : t ^ 2 / (Fintype.card V : ℝ) ≤
            t ^ 2 / (C.card : ℝ) :=
          div_le_div_of_nonneg_left (sq_nonneg t) hCpos hCle
        have hexp :
            Real.exp (-2 * t ^ 2 / (C.card : ℝ)) ≤
              Real.exp (-2 * t ^ 2 / Fintype.card V) := by
          apply Real.exp_le_exp.mpr
          calc
            -2 * t ^ 2 / (C.card : ℝ) =
                -2 * (t ^ 2 / (C.card : ℝ)) := by ring
            _ ≤ -2 * (t ^ 2 / Fintype.card V) :=
              mul_le_mul_of_nonpos_left hfrac (by norm_num)
            _ = -2 * t ^ 2 / Fintype.card V := by ring
        have hsingle := sampleIntersectionCount_twoSided C ht.le
        change ((bad C).card : ℝ) ≤ _ at hsingle
        exact hsingle.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    _ = (family.card : ℝ) *
        (2 * (2 : ℝ) ^ Fintype.card V *
          Real.exp (-2 * t ^ 2 / Fintype.card V)) := by simp

/-- The tests needed in the two-clique case: the two side sizes and every
internal neighbourhood. -/
def internalTestFamily (G : SimpleGraph V) (A B : Finset V) :
    Finset (Finset V) :=
  insert A <| insert B <|
    (Finset.univ : Finset V).image fun v ↦
      if v ∈ A then G.neighborFinset v ∩ A else G.neighborFinset v ∩ B

def internalBadSamples (G : SimpleGraph V) (A B : Finset V) (t : ℝ) :
    Finset (Finset V) :=
  (internalTestFamily G A B).biUnion fun C ↦
    (Finset.univ : Finset V).powerset.filter fun S ↦
      t ≤ |sampleIntersectionCount C S - (C.card : ℝ) / 2|

lemma card_internalTestFamily_le (G : SimpleGraph V) (A B : Finset V) :
    (internalTestFamily G A B).card ≤ Fintype.card V + 2 := by
  unfold internalTestFamily
  calc
    (insert A (insert B ((Finset.univ : Finset V).image fun v ↦
        if v ∈ A then G.neighborFinset v ∩ A else
          G.neighborFinset v ∩ B))).card ≤
        ((Finset.univ : Finset V).image fun v ↦
          if v ∈ A then G.neighborFinset v ∩ A else
            G.neighborFinset v ∩ B).card + 2 := by
      have hA := Finset.card_insert_le A
        (insert B ((Finset.univ : Finset V).image fun v ↦
          if v ∈ A then G.neighborFinset v ∩ A else
            G.neighborFinset v ∩ B))
      have hB := Finset.card_insert_le B
        ((Finset.univ : Finset V).image fun v ↦
          if v ∈ A then G.neighborFinset v ∩ A else
            G.neighborFinset v ∩ B)
      omega
    _ ≤ Fintype.card V + 2 := by
      have himage :
          ((Finset.univ : Finset V).image fun v ↦
            if v ∈ A then G.neighborFinset v ∩ A else
              G.neighborFinset v ∩ B).card ≤ Fintype.card V := by
        exact Finset.card_image_le.trans_eq Finset.card_univ
      omega

lemma test_typical_of_not_internalBad
    {G : SimpleGraph V} {A B S C : Finset V} {t : ℝ}
    (hS : S ∉ internalBadSamples G A B t)
    (hC : C ∈ internalTestFamily G A B) :
    |sampleIntersectionCount C S - (C.card : ℝ) / 2| < t := by
  by_contra h
  exact hS (Finset.mem_biUnion.mpr ⟨C, hC,
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S),
      le_of_not_gt h⟩⟩)

/-- At tolerance `n/100`, all tests needed for the two-clique case are
simultaneously typical outside a set of density less than `1/16`. -/
theorem eventually_internalBadSamples_density_lt :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin (2 * n))) (A B : Finset (Fin (2 * n))),
        ((internalBadSamples G A B ((n : ℝ) / 100)).card : ℝ) /
            (2 : ℝ) ^ (2 * n) < 1 / 16 := by
  have hevent := Concentration.eventually_linear_mul_exp_neg_lt
    (show (0 : ℝ) < 1 / 10000 by norm_num)
    (show (0 : ℝ) < 1 / 128 by norm_num)
  filter_upwards [eventually_ge_atTop 1, hevent] with n hn hdec
  intro G A B
  let : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  have ht : (0 : ℝ) < (n : ℝ) / 100 := by positivity
  have hcard := card_familyBadSamples_le (internalTestFamily G A B) ht
  change ((internalBadSamples G A B ((n : ℝ) / 100)).card : ℝ) ≤ _ at hcard
  have hcard' :
      ((internalBadSamples G A B ((n : ℝ) / 100)).card : ℝ) ≤
        ((internalTestFamily G A B).card : ℝ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            Real.exp (-2 * ((n : ℝ) / 100) ^ 2 / (2 * n : ℝ))) := by
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hcard
  have hfamily : ((internalTestFamily G A B).card : ℝ) ≤ 4 * n := by
    have h := card_internalTestFamily_le G A B
    simp only [Fintype.card_fin] at h
    exact_mod_cast (by omega : (internalTestFamily G A B).card ≤ 4 * n)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := by positivity
  calc
    ((internalBadSamples G A B ((n : ℝ) / 100)).card : ℝ) /
          (2 : ℝ) ^ (2 * n) ≤
        (((internalTestFamily G A B).card : ℝ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            Real.exp (-2 * ((n : ℝ) / 100) ^ 2 / (2 * n : ℝ)))) /
          (2 : ℝ) ^ (2 * n) :=
      div_le_div_of_nonneg_right hcard' hpow.le
    _ ≤ ((4 * n : ℝ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            Real.exp (-2 * ((n : ℝ) / 100) ^ 2 / (2 * n : ℝ)))) /
          (2 : ℝ) ^ (2 * n) := by
      gcongr
    _ = 8 * ((n : ℝ) * Real.exp (-(1 / 10000 : ℝ) * n)) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
      congr 2 <;> ring
    _ < 1 / 16 := by nlinarith

/-- Number of edges of `M` whose two endpoints are sampled. -/
def survivingEdgeCount (M : Finset (Sym2 V)) (S : Finset V) : ℝ :=
  ((M.filter fun e ↦ e.toFinset ⊆ S).card : ℝ)

private lemma edge_survival_mass
    {e : Sym2 V} (he : ¬e.IsDiag) :
    ∑ S ∈ (Finset.univ : Finset V).powerset with e.toFinset ⊆ S,
        Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S = 1 / 4 := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      have hvw : v ≠ w := by simpa [Sym2.mk_isDiag_iff] using he
      have h := Erdos76.FiniteNibble.sum_bernoulliMass_filter_mem_mem
        (U := (Finset.univ : Finset V)) (p := halfProbability)
        (e := v) (f := w) (Finset.mem_univ v) (Finset.mem_univ w) hvw
      calc
        ∑ S ∈ (Finset.univ : Finset V).powerset with s(v, w).toFinset ⊆ S,
            Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S =
            ∑ S ∈ (Finset.univ : Finset V).powerset with v ∈ S ∧ w ∈ S,
              Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S := by
          congr 2
          ext S
          rw [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff]
        _ = 1 / 4 := by
          rw [h]
          norm_num [halfProbability]

lemma bernoulliExpectation_half_survivingEdgeCount
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset) :
    Erdos76.FiniteNibble.bernoulliExpectation (Finset.univ : Finset V)
        halfProbability (survivingEdgeCount M) = (M.card : ℝ) / 4 := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation]
  have hcount (S : Finset V) :
      survivingEdgeCount M S =
        ∑ e ∈ M, if e.toFinset ⊆ S then (1 : ℝ) else 0 := by
    rw [survivingEdgeCount]
    simp [← Finset.sum_filter]
  calc
    ∑ S ∈ (Finset.univ : Finset V).powerset,
          Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S *
            survivingEdgeCount M S =
        ∑ S ∈ (Finset.univ : Finset V).powerset, ∑ e ∈ M,
          if e.toFinset ⊆ S then
            Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hcount, mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e.toFinset ⊆ S <;> simp [he]
    _ = ∑ e ∈ M, ∑ S ∈ (Finset.univ : Finset V).powerset,
          if e.toFinset ⊆ S then
            Erdos76.FiniteNibble.bernoulliMass Finset.univ halfProbability S else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e ∈ M, (1 / 4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e heM
      rw [← Finset.sum_filter]
      exact edge_survival_mass (H.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp (hM heM)))
    _ = (M.card : ℝ) / 4 := by simp; ring

lemma card_matchingVertices_eq_two_mul
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) (hM : EdgeMatching H M) :
    (matchingVertices M).card = 2 * M.card := by
  have hpair : (M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    have hd := hM.2 he hf hef
    exact Set.disjoint_left.mp hd (Sym2.mem_toFinset.mp hxe)
      (Sym2.mem_toFinset.mp hxf)
  rw [matchingVertices, Finset.card_biUnion hpair]
  calc
    ∑ e ∈ M, e.toFinset.card = ∑ _e ∈ M, 2 := by
      apply Finset.sum_congr rfl
      intro e heM
      rw [Sym2.card_toFinset_of_not_isDiag e]
      exact H.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp (hM.1 heM))
    _ = 2 * M.card := by simp [Nat.mul_comm]

lemma survivingEdgeCount_hasBoundedDifferences
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) (hM : EdgeMatching H M) :
    Erdos76.FiniteNibble.HasBoundedDifferences (Finset.univ : Finset V)
      (survivingEdgeCount M)
      (fun v ↦ if v ∈ matchingVertices M then 1 else 0) := by
  intro v _ T hT
  have hvT : v ∉ T := by
    intro hvT
    exact (Finset.mem_erase.mp (hT hvT)).1 rfl
  let A := M.filter fun e ↦ e.toFinset ⊆ insert v T
  let B := M.filter fun e ↦ e.toFinset ⊆ T
  have hBA : B ⊆ A := by
    intro e he
    simp only [B, A, Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans (Finset.subset_insert v T)⟩
  by_cases hvM : v ∈ matchingVertices M
  · let I := M.filter fun e ↦ v ∈ e.toFinset
    have hAI : A ⊆ B ∪ I := by
      intro e he
      simp only [A, B, I, Finset.mem_filter, Finset.mem_union] at he ⊢
      by_cases heT : e.toFinset ⊆ T
      · exact Or.inl ⟨he.1, heT⟩
      · right
        refine ⟨he.1, ?_⟩
        by_contra hve
        apply heT
        intro x hxe
        have hx := he.2 hxe
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxT
        · exact (hve hxe).elim
        · exact hxT
    have hI : I.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      simp only [I, Finset.mem_filter] at he hf
      by_contra hef
      have hd := hM.2 he.1 hf.1 hef
      exact Set.disjoint_left.mp hd (Sym2.mem_toFinset.mp he.2)
        (Sym2.mem_toFinset.mp hf.2)
    have hcardBA : B.card ≤ A.card := Finset.card_le_card hBA
    have hcardAI : A.card ≤ B.card + I.card :=
      (Finset.card_le_card hAI).trans (Finset.card_union_le B I)
    have hgoal : |(A.card : ℝ) - (B.card : ℝ)| ≤ (1 : ℝ) := by
      have hnonneg : 0 ≤ (A.card : ℝ) - (B.card : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast hcardBA)
      rw [abs_of_nonneg hnonneg]
      exact_mod_cast (by omega : A.card - B.card ≤ 1)
    simpa only [survivingEdgeCount, A, B, if_pos hvM] using hgoal
  · have hAB : A = B := by
      apply Finset.Subset.antisymm _ hBA
      intro e heA
      apply Finset.mem_filter.mpr
      have heM := (Finset.mem_filter.mp heA).1
      refine ⟨heM, ?_⟩
      intro x hxe
      have hx := (Finset.mem_filter.mp heA).2 hxe
      rw [Finset.mem_insert] at hx
      rcases hx with hxv | hxT
      · subst x
        exact (hvM (Finset.mem_biUnion.mpr ⟨e, heM, hxe⟩)).elim
      · exact hxT
    have hgoal : |(A.card : ℝ) - (B.card : ℝ)| ≤ (0 : ℝ) := by
      rw [hAB]
      simp
    simpa only [survivingEdgeCount, A, B, if_neg hvM] using hgoal

/-- One-sided finite-powerset concentration for survival of the edges of a
fixed matching. -/
theorem survivingEdgeCount_lowerTail
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) (hM : EdgeMatching H M)
    {t : ℝ} (ht : 0 ≤ t) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        survivingEdgeCount M S ≤ (M.card : ℝ) / 4 - t).card : ℝ)) ≤
      (2 : ℝ) ^ Fintype.card V * Real.exp (-t ^ 2 / M.card) := by
  have h := Concentration.countEvent_lowerTail_le
    (U := (Finset.univ : Finset V)) (F := survivingEdgeCount M)
    (c := fun v ↦ if v ∈ matchingVertices M then 1 else 0) (t := t)
    (survivingEdgeCount_hasBoundedDifferences H M hM) ht
  change ((((Finset.univ : Finset V).powerset.filter fun S ↦
      survivingEdgeCount M S ≤
        Erdos76.FiniteNibble.bernoulliExpectation Finset.univ halfProbability
          (survivingEdgeCount M) - t).card : ℝ)) ≤
      (2 : ℝ) ^ Fintype.card V * Real.exp
        (-2 * t ^ 2 / (∑ v ∈ (Finset.univ : Finset V),
          (if v ∈ matchingVertices M then (1 : ℝ) else 0) ^ 2)) at h
  rw [bernoulliExpectation_half_survivingEdgeCount H M hM.1] at h
  have hsum : (∑ v ∈ (Finset.univ : Finset V),
      (if v ∈ matchingVertices M then (1 : ℝ) else 0) ^ 2) =
      (2 * M.card : ℕ) := by
    simp only [ite_pow, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact_mod_cast card_matchingVertices_eq_two_mul H M hM
  rw [hsum] at h
  have hexp : -2 * t ^ 2 / ((2 * M.card : ℕ) : ℝ) =
      -t ^ 2 / (M.card : ℝ) := by
    norm_num [Nat.cast_mul]
    ring
  rw [hexp] at h
  exact h

/-! ## Quantitative deterministic consequences of the cleaned partition -/

/-- With the constants from `TailoredTrichotomy`, each cleaned side has at
most `n²/100` missing ordered pairs.  This deliberately loose rational bound
leaves room for the integer rounding used after sampling. -/
lemma compl_pairCount_parts_le
    (n : ℕ) (A B : Finset V)
    (hAB : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (hVcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hAlower : (n : ℝ) ≤ A.card)
    (hAupper : (A.card : ℝ) ≤ (321 / 320 : ℝ) * n)
    (hcross : (pairCount G A B : ℝ) ≤ (3 / 1280 : ℝ) * n ^ 2) :
    pairCount Gᶜ A A ≤ n * n / 100 ∧
      pairCount Gᶜ B B ≤ n * n / 100 := by
  have hcards : A.card + B.card = 2 * n := by
    rw [← hVcard, ← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hAB]
  have hdegA : pairCount G A A + pairCount G A B = A.card * (n + 1) := by
    calc
      pairCount G A A + pairCount G A B = pairCount G A (A ∪ B) :=
        (pairCount_union_right hAB).symm
      _ = pairCount G A Finset.univ := by rw [hcover]
      _ = A.card * (n + 1) := pairCount_univ_of_regular hreg A
  have hdegB : pairCount G B B + pairCount G B A = B.card * (n + 1) := by
    calc
      pairCount G B B + pairCount G B A = pairCount G B (B ∪ A) :=
        (pairCount_union_right hAB.symm).symm
      _ = pairCount G B Finset.univ := by rw [Finset.union_comm, hcover]
      _ = B.card * (n + 1) := pairCount_univ_of_regular hreg B
  have hcompA := pairCount_add_compl G A
  have hcompB := pairCount_add_compl G B
  have hcrossBA : pairCount G B A = pairCount G A B := pairCount_symm G _ _
  have hcardsR : (A.card : ℝ) + B.card = 2 * n := by exact_mod_cast hcards
  have hdegAR : (pairCount G A A : ℝ) + pairCount G A B =
      A.card * (n + 1) := by exact_mod_cast hdegA
  have hdegBR : (pairCount G B B : ℝ) + pairCount G B A =
      B.card * (n + 1) := by exact_mod_cast hdegB
  have hcompAR : (pairCount G A A : ℝ) + pairCount Gᶜ A A =
      A.card * (A.card - 1) := by
    by_cases hApos : 0 < A.card
    · have hcompAR' : (pairCount G A A : ℝ) + pairCount Gᶜ A A =
          ((A.card * (A.card - 1) : ℕ) : ℝ) := by exact_mod_cast hcompA
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ A.card)] at hcompAR'
      simpa only [Nat.cast_one] using hcompAR'
    · have hAzero : A.card = 0 := by omega
      simp [hAzero] at hcompA
      rcases hcompA with ⟨hGA, hcA⟩
      simp [hAzero, hGA, hcA]
  have hcompBR : (pairCount G B B : ℝ) + pairCount Gᶜ B B =
      B.card * (B.card - 1) := by
    by_cases hBpos : 0 < B.card
    · have hcompBR' : (pairCount G B B : ℝ) + pairCount Gᶜ B B =
          ((B.card * (B.card - 1) : ℕ) : ℝ) := by exact_mod_cast hcompB
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ B.card)] at hcompBR'
      simpa only [Nat.cast_one] using hcompBR'
    · have hBzero : B.card = 0 := by omega
      simp [hBzero] at hcompB
      rcases hcompB with ⟨hGB, hcB⟩
      simp [hBzero, hGB, hcB]
  have hBle : (B.card : ℝ) ≤ n := by nlinarith
  have hmissAreal : 100 * (pairCount Gᶜ A A : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((A.card : ℝ) - n), sq_nonneg (n : ℝ)]
  have hmissBreal : 100 * (pairCount Gᶜ B B : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hcrossBA] at hdegBR
    nlinarith [sq_nonneg ((B.card : ℝ) - n), sq_nonneg (n : ℝ)]
  constructor
  · apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 100)).2
    have : 100 * pairCount Gᶜ A A ≤ n ^ 2 := by
      exact_mod_cast hmissAreal
    simpa [pow_two, Nat.mul_comm] using this
  · apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 100)).2
    have : 100 * pairCount Gᶜ B B ≤ n ^ 2 := by
      exact_mod_cast hmissBreal
    simpa [pow_two, Nat.mul_comm] using this

private lemma sampled_sparse_arithmetic (n s : ℕ)
    (hn : 1000 ≤ n) (hs : 2 * n / 5 ≤ s) :
    2 * (n * n / 100) <
      (n / 10 - 1) * (s - n / 10 - 1) := by
  have hdiv10le : 10 * (n / 10) ≤ n := Nat.mul_div_le n 10
  have hlt10 : n < 10 * (n / 10 + 1) := Nat.lt_mul_div_succ n (by norm_num)
  have hdiv5le : 5 * (2 * n / 5) ≤ 2 * n := Nat.mul_div_le (2 * n) 5
  have hlt5 : 2 * n < 5 * (2 * n / 5 + 1) :=
    Nat.lt_mul_div_succ (2 * n) (by norm_num)
  have hdiv100 : 100 * (n * n / 100) ≤ n * n := Nat.mul_div_le (n * n) 100
  have hx : 9 * n ≤ 100 * (n / 10 - 1) := by omega
  have hy : 29 * n ≤ 100 * (s - n / 10 - 1) := by omega
  have hprod := Nat.mul_le_mul hx hy
  nlinarith

/-- A matching of at least 256 crossing edges leaves two sampled edges except
on a set of density less than `1/16`. -/
theorem matchingSurvivalBad_density_lt
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) (hM : EdgeMatching H M)
    (hMcard : 256 ≤ M.card) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        survivingEdgeCount M S < 2).card : ℝ) /
      (2 : ℝ) ^ Fintype.card V) < 1 / 16 := by
  let bad := (Finset.univ : Finset V).powerset.filter fun S ↦
    survivingEdgeCount M S < 2
  let tail := (Finset.univ : Finset V).powerset.filter fun S ↦
    survivingEdgeCount M S ≤ (M.card : ℝ) / 8
  have hsub : bad ⊆ tail := by
    intro S hS
    have hslt : survivingEdgeCount M S < 2 := (Finset.mem_filter.mp hS).2
    have hm : (2 : ℝ) ≤ (M.card : ℝ) / 8 := by
      have hmR : (256 : ℝ) ≤ M.card := by exact_mod_cast hMcard
      linarith
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1, hslt.le.trans hm⟩
  have ht := survivingEdgeCount_lowerTail H M hM
    (t := (M.card : ℝ) / 8) (by positivity)
  have htail : ((tail.card : ℝ)) ≤
      (2 : ℝ) ^ Fintype.card V * Real.exp (-(M.card : ℝ) / 64) := by
    have hevent :
        ((Finset.univ : Finset V).powerset.filter fun S ↦
          survivingEdgeCount M S ≤ (M.card : ℝ) / 4 - (M.card : ℝ) / 8) =
          tail := by
      ext S
      simp only [tail, Finset.mem_filter]
      constructor <;> rintro ⟨hS, h⟩ <;> refine ⟨hS, ?_⟩ <;> linarith
    rw [hevent] at ht
    have hm0 : (M.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : M.card ≠ 0)
    have hexponent : -((M.card : ℝ) / 8) ^ 2 / M.card =
        -(M.card : ℝ) / 64 := by
      field_simp
      ring
    rw [hexponent] at ht
    exact ht
  have hcardbad : (bad.card : ℝ) ≤ tail.card := by
    exact_mod_cast Finset.card_le_card hsub
  have hbad : (bad.card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card V * Real.exp (-(M.card : ℝ) / 64) :=
    hcardbad.trans htail
  have hexpmono : Real.exp (-(M.card : ℝ) / 64) ≤ Real.exp (-4) := by
    apply Real.exp_le_exp.mpr
    have : (256 : ℝ) ≤ M.card := by exact_mod_cast hMcard
    linarith
  have hexp4 : Real.exp (-4) < (1 / 16 : ℝ) := by
    have hp : Real.exp (-1) ^ 4 < (1 / 2 : ℝ) ^ 4 := by
      gcongr
      exact Real.exp_neg_one_lt_half
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  have hpow : (0 : ℝ) < (2 : ℝ) ^ Fintype.card V := by positivity
  change (bad.card : ℝ) / (2 : ℝ) ^ Fintype.card V < 1 / 16
  calc
    (bad.card : ℝ) / (2 : ℝ) ^ Fintype.card V ≤
        ((2 : ℝ) ^ Fintype.card V *
          Real.exp (-(M.card : ℝ) / 64)) /
            (2 : ℝ) ^ Fintype.card V :=
      div_le_div_of_nonneg_right hbad hpow.le
    _ = Real.exp (-(M.card : ℝ) / 64) := by field_simp
    _ ≤ Real.exp (-4) := hexpmono
    _ < 1 / 16 := hexp4

/-- Two surviving edges of a crossing matching have distinct endpoints on
both sides and therefore provide the splice edges. -/
lemma exists_two_sampled_cross_edges
    (A B S : Finset V) (hAB : Disjoint A B)
    (hcover : A ∪ B = Finset.univ)
    (M : Finset (Sym2 V))
    (hM : EdgeMatching (crossingGraph G (A : Set V)) M)
    (htwo : 2 ≤ (M.filter fun e ↦ e.toFinset ⊆ S).card) :
    ∃ a₁ a₂ b₁ b₂ : V,
      a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
      a₁ ∈ S ∧ a₂ ∈ S ∧ b₁ ∈ S ∧ b₂ ∈ S ∧
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ G.Adj a₁ b₁ ∧ G.Adj a₂ b₂ := by
  let N := M.filter fun e ↦ e.toFinset ⊆ S
  have hN : 1 < N.card := by dsimp [N]; omega
  obtain ⟨e, heN, f, hfN, hef⟩ := Finset.one_lt_card.mp hN
  have orient (q : Sym2 V) (hqN : q ∈ N) :
      ∃ a b : V, a ∈ A ∧ b ∈ B ∧ a ∈ S ∧ b ∈ S ∧
        G.Adj a b ∧ a ∈ (q : Set V) ∧ b ∈ (q : Set V) := by
    induction q using Sym2.inductionOn with
    | _ x y =>
        have hqM : s(x, y) ∈ M := (Finset.mem_filter.mp hqN).1
        have hqS : s(x, y).toFinset ⊆ S := (Finset.mem_filter.mp hqN).2
        have hadj : (crossingGraph G (A : Set V)).Adj x y := by
          simpa using (SimpleGraph.mem_edgeFinset.mp (hM.1 hqM))
        rcases hadj.2 with hxy | hyx
        · have hyB : y ∈ B := by
            have hyU : y ∈ A ∪ B := by rw [hcover]; simp
            exact (Finset.mem_union.mp hyU).resolve_left hxy.2
          refine ⟨x, y, hxy.1, hyB, hqS (by simp), hqS (by simp),
            hadj.1, by simp, by simp⟩
        · have hxB : x ∈ B := by
            have hxU : x ∈ A ∪ B := by rw [hcover]; simp
            exact (Finset.mem_union.mp hxU).resolve_left hyx.1
          refine ⟨y, x, hyx.2, hxB, hqS (by simp), hqS (by simp),
            hadj.1.symm, by simp, by simp⟩
  obtain ⟨a₁, b₁, ha₁A, hb₁B, ha₁S, hb₁S, hab₁, ha₁e, hb₁e⟩ := orient e heN
  obtain ⟨a₂, b₂, ha₂A, hb₂B, ha₂S, hb₂S, hab₂, ha₂f, hb₂f⟩ := orient f hfN
  have heM : e ∈ M := (Finset.mem_filter.mp heN).1
  have hfM : f ∈ M := (Finset.mem_filter.mp hfN).1
  have hdisj := hM.2 heM hfM hef
  have ha : a₁ ≠ a₂ := by
    intro h
    subst a₂
    exact Set.disjoint_left.mp hdisj ha₁e ha₂f
  have hb : b₁ ≠ b₂ := by
    intro h
    subst b₂
    exact Set.disjoint_left.mp hdisj hb₁e hb₂f
  exact ⟨a₁, a₂, b₁, b₂, ha₁A, ha₂A, hb₁B, hb₂B,
    ha₁S, ha₂S, hb₁S, hb₂S, ha, hb, hab₁, hab₂⟩

/-- Finset-facing wrapper around the sparse-complement Hamilton-path theorem.
It produces exactly the `IsSpannedByCycle` predicate used by Erdős 622. -/
theorem isSpannedByCycle_of_two_sparse_finset_parts
    (G : SimpleGraph V)
    (S A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = S)
    {a₁ a₂ b₁ b₂ : V}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (hab₁ : G.Adj a₁ b₁) (hab₂ : G.Adj a₂ b₂)
    (deltaA missA deltaB missB : ℕ)
    (hdeltaAtwo : 2 ≤ deltaA) (hdeltaAcard : 2 * deltaA ≤ A.card)
    (hminA : ∀ v : (A : Set V), deltaA ≤ (G.induce (A : Set V)).degree v)
    (hmissA : (G.induce (A : Set V))ᶜ.edgeFinset.card ≤ missA)
    (hsparseA : 2 * missA < (deltaA - 1) * (A.card - deltaA - 1))
    (hdeltaBtwo : 2 ≤ deltaB) (hdeltaBcard : 2 * deltaB ≤ B.card)
    (hminB : ∀ v : (B : Set V), deltaB ≤ (G.induce (B : Set V)).degree v)
    (hmissB : (G.induce (B : Set V))ᶜ.edgeFinset.card ≤ missB)
    (hsparseB : 2 * missB < (deltaB - 1) * (B.card - deltaB - 1)) :
    IsSpannedByCycle G S := by
  have hAS : A ⊆ S := by
    intro x hx
    rw [← hcover]
    exact Finset.mem_union_left _ hx
  have hBS : B ⊆ S := by
    intro x hx
    rw [← hcover]
    exact Finset.mem_union_right _ hx
  let a₁A : (A : Set V) := ⟨a₁, ha₁⟩
  let a₂A : (A : Set V) := ⟨a₂, ha₂⟩
  let b₁B : (B : Set V) := ⟨b₁, hb₁⟩
  let b₂B : (B : Set V) := ⟨b₂, hb₂⟩
  obtain ⟨pA, hpA⟩ :=
    TwoCliqueHamiltonicity.exists_hamiltonPath_of_sparse_complement
      (G.induce (A : Set V))
      (a := a₁A) (b := a₂A)
      (by intro h; exact ha (congrArg Subtype.val h))
      deltaA missA hdeltaAtwo (by simpa using hdeltaAcard)
      hminA hmissA (by simpa using hsparseA)
  obtain ⟨pB, hpB⟩ :=
    TwoCliqueHamiltonicity.exists_hamiltonPath_of_sparse_complement
      (G.induce (B : Set V))
      (a := b₁B) (b := b₂B)
      (by intro h; exact hb (congrArg Subtype.val h))
      deltaB missB hdeltaBtwo (by simpa using hdeltaBcard)
      hminB hmissB (by simpa using hsparseB)
  let H := G.induce (S : Set V)
  let AS : Set (S : Set V) := {x | (x : V) ∈ A}
  let BS : Set (S : Set V) := {x | (x : V) ∈ B}
  let a₁S : (S : Set V) := ⟨a₁, hAS ha₁⟩
  let a₂S : (S : Set V) := ⟨a₂, hAS ha₂⟩
  let b₁S : (S : Set V) := ⟨b₁, hBS hb₁⟩
  let b₂S : (S : Set V) := ⟨b₂, hBS hb₂⟩
  let eA : G.induce (A : Set V) ↪g H := G.induceHomOfLE hAS
  let eB : G.induce (B : Set V) ↪g H := G.induceHomOfLE hBS
  let qA : H.Walk a₁S a₂S := (pA.map eA.toHom).copy rfl rfl
  let qB : H.Walk b₁S b₂S := (pB.map eB.toHom).copy rfl rfl
  have hqA : IsHamiltonPathOn AS qA := by
    refine ⟨hpA.isPath.map eA.injective, ?_⟩
    intro x
    constructor
    · intro hx
      change x ∈ (pA.map eA.toHom).support at hx
      rw [SimpleGraph.Walk.support_map] at hx
      obtain ⟨z, -, hz⟩ := List.mem_map.mp hx
      subst x
      exact z.property
    · intro hx
      change x ∈ (pA.map eA.toHom).support
      rw [SimpleGraph.Walk.support_map]
      let z : (A : Set V) := ⟨x, hx⟩
      exact List.mem_map.mpr ⟨z, hpA.mem_support z, by rfl⟩
  have hqB : IsHamiltonPathOn BS qB := by
    refine ⟨hpB.isPath.map eB.injective, ?_⟩
    intro x
    constructor
    · intro hx
      change x ∈ (pB.map eB.toHom).support at hx
      rw [SimpleGraph.Walk.support_map] at hx
      obtain ⟨z, -, hz⟩ := List.mem_map.mp hx
      subst x
      exact z.property
    · intro hx
      change x ∈ (pB.map eB.toHom).support
      rw [SimpleGraph.Walk.support_map]
      let z : (B : Set V) := ⟨x, hx⟩
      exact List.mem_map.mpr ⟨z, hpB.mem_support z, by rfl⟩
  have hASBS : Disjoint AS BS := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact Finset.disjoint_left.mp hAB hxA hxB
  have hAScover : AS ∪ BS = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : (x : V) ∈ A ∪ B := by
      rw [hcover]
      exact x.property
    exact Finset.mem_union.mp hx
  have hham : H.IsHamiltonian :=
    isHamiltonian_of_two_cross_edges (G := H) AS BS hASBS hAScover
      (a₁ := a₁S) (a₂ := a₂S) (b₁ := b₁S) (b₂ := b₂S)
      ha₁ ha₂ hb₁ hb₂
      (by intro h; exact ha (congrArg Subtype.val h))
      (by intro h; exact hb (congrArg Subtype.val h))
      (by exact hab₁) (by exact hab₂) hqA hqB
  have hScard : 3 ≤ S.card := by
    have hAle : A.card ≤ S.card := Finset.card_le_card hAS
    omega
  exact (isSpannedByCycle_iff_isHamiltonian hScard).2 hham

/-- Every sample outside the two explicitly counted bad events is cyclic. -/
theorem good_sample_isSpannedByCycle
    (n : ℕ) (hn : 1000 ≤ n)
    (G : SimpleGraph V)
    (hVcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree (n + 1))
    (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (hAlower : (n : ℝ) ≤ A.card)
    (hAupper : (A.card : ℝ) ≤ (321 / 320 : ℝ) * n)
    (hcross : (pairCount G A B : ℝ) ≤ (3 / 1280 : ℝ) * n ^ 2)
    (hminA0 : Trichotomy.InternalMinDegree G A ((2 * n : ℝ) / 5))
    (hminB0 : Trichotomy.InternalMinDegree G B ((2 * n : ℝ) / 5))
    (M : Finset (Sym2 V))
    (hM : EdgeMatching (crossingGraph G (A : Set V)) M)
    (S : Finset V)
    (htyp : S ∉ internalBadSamples G A B ((n : ℝ) / 100))
    (hsurvive : 2 ≤ (M.filter fun e ↦ e.toFinset ⊆ S).card) :
    IsSpannedByCycle G S := by
  let SA := S ∩ A
  let SB := S ∩ B
  have hSA_A : SA ⊆ A := by exact Finset.inter_subset_right
  have hSB_B : SB ⊆ B := by exact Finset.inter_subset_right
  have hSAsplit : SA ∪ SB = S := by
    ext x
    simp only [SA, SB, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      have hxU : x ∈ A ∪ B := by rw [hcover]; simp
      rcases Finset.mem_union.mp hxU with hxA | hxB
      · exact Or.inl ⟨hx, hxA⟩
      · exact Or.inr ⟨hx, hxB⟩
  have hSAdisj : Disjoint SA SB := by
    exact Finset.disjoint_of_subset_left hSA_A
      (Finset.disjoint_of_subset_right hSB_B hAB)
  have hAtest : A ∈ internalTestFamily G A B := by
    simp [internalTestFamily]
  have hBtest : B ∈ internalTestFamily G A B := by
    simp [internalTestFamily]
  have hAtyp := test_typical_of_not_internalBad htyp hAtest
  have hBtyp := test_typical_of_not_internalBad htyp hBtest
  have hSAcount : sampleIntersectionCount A S = (SA.card : ℝ) := rfl
  have hSBcount : sampleIntersectionCount B S = (SB.card : ℝ) := rfl
  rw [hSAcount] at hAtyp
  rw [hSBcount] at hBtyp
  have hcards : A.card + B.card = 2 * n := by
    rw [← hVcard, ← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hAB]
  have hBlower : ((319 : ℝ) / 320) * n ≤ B.card := by
    have hcardsR : (A.card : ℝ) + B.card = 2 * n := by exact_mod_cast hcards
    nlinarith
  have hSAreal : (49 / 100 : ℝ) * n < SA.card := by
    have hl := (abs_lt.mp hAtyp).1
    nlinarith
  have hSBreal : (39 / 80 : ℝ) * n < SB.card := by
    have hl := (abs_lt.mp hBtyp).1
    nlinarith
  have hSAcard : 2 * n / 5 ≤ SA.card := by
    have hq : 5 * (2 * n / 5) ≤ 2 * n := Nat.mul_div_le (2 * n) 5
    have hqR : ((2 * n / 5 : ℕ) : ℝ) ≤ (2 : ℝ) * n / 5 := by
      have hqR' : (5 : ℝ) * (2 * n / 5 : ℕ) ≤ 2 * n := by
        exact_mod_cast hq
      linarith
    exact_mod_cast hqR.trans (by nlinarith : (2 : ℝ) * n / 5 ≤ SA.card)
  have hSBcard : 2 * n / 5 ≤ SB.card := by
    have hq : 5 * (2 * n / 5) ≤ 2 * n := Nat.mul_div_le (2 * n) 5
    have hqR : ((2 * n / 5 : ℕ) : ℝ) ≤ (2 : ℝ) * n / 5 := by
      have hqR' : (5 : ℝ) * (2 * n / 5 : ℕ) ≤ 2 * n := by
        exact_mod_cast hq
      linarith
    exact_mod_cast hqR.trans (by nlinarith : (2 : ℝ) * n / 5 ≤ SB.card)
  have hmissing := compl_pairCount_parts_le n A B hAB hcover hVcard hreg
    hAlower hAupper hcross
  have hmissSA : (G.induce (SA : Set V))ᶜ.edgeFinset.card ≤ n * n / 100 := by
    calc
      (G.induce (SA : Set V))ᶜ.edgeFinset.card ≤ pairCount Gᶜ SA SA :=
        card_compl_edgeFinset_induce_le_pairCount G SA
      _ ≤ pairCount Gᶜ A SA := pairCount_mono_left hSA_A
      _ ≤ pairCount Gᶜ A A := pairCount_mono_right hSA_A
      _ ≤ n * n / 100 := hmissing.1
  have hmissSB : (G.induce (SB : Set V))ᶜ.edgeFinset.card ≤ n * n / 100 := by
    calc
      (G.induce (SB : Set V))ᶜ.edgeFinset.card ≤ pairCount Gᶜ SB SB :=
        card_compl_edgeFinset_induce_le_pairCount G SB
      _ ≤ pairCount Gᶜ B SB := pairCount_mono_left hSB_B
      _ ≤ pairCount Gᶜ B B := pairCount_mono_right hSB_B
      _ ≤ n * n / 100 := hmissing.2
  have hminSA : ∀ v : (SA : Set V), n / 10 ≤ (G.induce (SA : Set V)).degree v := by
    intro v
    let C := G.neighborFinset (v : V) ∩ A
    have hCtest : C ∈ internalTestFamily G A B := by
      have hvA : (v : V) ∈ A := hSA_A v.property
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(v : V), Finset.mem_univ _, by simp [C, hvA]⟩
    have hCtyp := test_typical_of_not_internalBad htyp hCtest
    have hCmin : ((2 * n : ℝ) / 5) ≤ C.card := by
      simpa [C, Trichotomy.degreeInto] using hminA0 (v : V) (hSA_A v.property)
    have hl := (abs_lt.mp hCtyp).1
    have hd : 10 * (n / 10) ≤ n := Nat.mul_div_le n 10
    have hdR : ((n / 10 : ℕ) : ℝ) ≤ (n : ℝ) / 10 := by
      have hdR' : (10 : ℝ) * (n / 10 : ℕ) ≤ n := by exact_mod_cast hd
      linarith
    have hdeltaK : n / 10 ≤ (S ∩ C).card := by
      exact_mod_cast hdR.trans (by
        rw [sampleIntersectionCount] at hl
        nlinarith : (n : ℝ) / 10 ≤ ((S ∩ C).card : ℝ))
    let f : (S ∩ C : Set V) → (G.induce (SA : Set V)).neighborSet v := fun y ↦ by
      have hyS : (y : V) ∈ S := y.property.1
      have hyC : (y : V) ∈ C := y.property.2
      have hyN : (y : V) ∈ G.neighborFinset (v : V) :=
        (Finset.mem_inter.mp hyC).1
      have hyA : (y : V) ∈ A := (Finset.mem_inter.mp hyC).2
      exact ⟨⟨y, Finset.mem_inter.mpr ⟨hyS, hyA⟩⟩,
        (G.mem_neighborFinset (v : V) (y : V)).mp hyN⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : (G.induce (SA : Set V)).neighborSet v ↦
        ((z.1 : (SA : Set V)) : V)) hxy
    have hcard := Fintype.card_le_of_injective f hf
    have hKdegree : (S ∩ C).card ≤ (G.induce (SA : Set V)).degree v := by
      rw [Set.fintypeCard_eq_ncard, ← Finset.coe_inter,
        Set.ncard_coe_finset,
        (G.induce (SA : Set V)).card_neighborSet_eq_degree] at hcard
      exact hcard
    exact hdeltaK.trans hKdegree
  have hminSB : ∀ v : (SB : Set V), n / 10 ≤ (G.induce (SB : Set V)).degree v := by
    intro v
    let C := G.neighborFinset (v : V) ∩ B
    have hCtest : C ∈ internalTestFamily G A B := by
      have hvB : (v : V) ∈ B := hSB_B v.property
      have hvA : (v : V) ∉ A := fun hvA ↦
        Finset.disjoint_left.mp hAB hvA hvB
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(v : V), Finset.mem_univ _, by simp [C, hvA]⟩
    have hCtyp := test_typical_of_not_internalBad htyp hCtest
    have hCmin : ((2 * n : ℝ) / 5) ≤ C.card := by
      simpa [C, Trichotomy.degreeInto] using hminB0 (v : V) (hSB_B v.property)
    have hl := (abs_lt.mp hCtyp).1
    have hd : 10 * (n / 10) ≤ n := Nat.mul_div_le n 10
    have hdR : ((n / 10 : ℕ) : ℝ) ≤ (n : ℝ) / 10 := by
      have hdR' : (10 : ℝ) * (n / 10 : ℕ) ≤ n := by exact_mod_cast hd
      linarith
    have hdeltaK : n / 10 ≤ (S ∩ C).card := by
      exact_mod_cast hdR.trans (by
        rw [sampleIntersectionCount] at hl
        nlinarith : (n : ℝ) / 10 ≤ ((S ∩ C).card : ℝ))
    let f : (S ∩ C : Set V) → (G.induce (SB : Set V)).neighborSet v := fun y ↦ by
      have hyS : (y : V) ∈ S := y.property.1
      have hyC : (y : V) ∈ C := y.property.2
      have hyN : (y : V) ∈ G.neighborFinset (v : V) :=
        (Finset.mem_inter.mp hyC).1
      have hyB : (y : V) ∈ B := (Finset.mem_inter.mp hyC).2
      exact ⟨⟨y, Finset.mem_inter.mpr ⟨hyS, hyB⟩⟩,
        (G.mem_neighborFinset (v : V) (y : V)).mp hyN⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : (G.induce (SB : Set V)).neighborSet v ↦
        ((z.1 : (SB : Set V)) : V)) hxy
    have hcard := Fintype.card_le_of_injective f hf
    have hKdegree : (S ∩ C).card ≤ (G.induce (SB : Set V)).degree v := by
      rw [Set.fintypeCard_eq_ncard, ← Finset.coe_inter,
        Set.ncard_coe_finset,
        (G.induce (SB : Set V)).card_neighborSet_eq_degree] at hcard
      exact hcard
    exact hdeltaK.trans hKdegree
  obtain ⟨a₁, a₂, b₁, b₂, ha₁A, ha₂A, hb₁B, hb₂B,
      ha₁S, ha₂S, hb₁S, hb₂S, ha, hb, hab₁, hab₂⟩ :=
    exists_two_sampled_cross_edges A B S hAB hcover M hM hsurvive
  apply isSpannedByCycle_of_two_sparse_finset_parts G S SA SB hSAdisj hSAsplit
    (a₁ := a₁) (a₂ := a₂) (b₁ := b₁) (b₂ := b₂)
    (Finset.mem_inter.mpr ⟨ha₁S, ha₁A⟩) (Finset.mem_inter.mpr ⟨ha₂S, ha₂A⟩)
    (Finset.mem_inter.mpr ⟨hb₁S, hb₁B⟩) (Finset.mem_inter.mpr ⟨hb₂S, hb₂B⟩)
    ha hb hab₁ hab₂ (n / 10) (n * n / 100) (n / 10) (n * n / 100)
  · omega
  · omega
  · exact hminSA
  · exact hmissSA
  · exact sampled_sparse_arithmetic n SA.card hn hSAcard
  · omega
  · omega
  · exact hminSB
  · exact hmissSB
  · exact sampled_sparse_arithmetic n SB.card hn hSBcard

/-! ## The unconditional almost-two-cliques case-density theorem -/

def AlmostTwoCliquesRegime : GraphRegime := fun n G ↦
  Trichotomy.AlmostTwoCliques G n TailoredTrichotomy.epsilon0

/-- The almost-two-cliques branch actually makes a uniformly random subset
cyclic with probability bounded away from `1/2` (our loose constants give
`7/8`).  In particular it supplies the sharp `1/2-o(1)` case interface. -/
theorem uniformCaseDensityBound_almostTwoCliques :
    UniformCaseDensityBound AlmostTwoCliquesRegime := by
  intro epsilon hepsilon
  filter_upwards [eventually_ge_atTop 200000,
    eventually_internalBadSamples_density_lt] with n hn hinter
  intro G hreg hcase
  change Trichotomy.AlmostTwoCliques G n TailoredTrichotomy.epsilon0 at hcase
  obtain ⟨A, B, hAB, hcover, hAlower, hAupper0, hcross0, hminA, hminB⟩ := hcase
  have hAupper : (A.card : ℝ) ≤ (321 / 320 : ℝ) * n := by
    norm_num [TailoredTrichotomy.epsilon0] at hAupper0 ⊢
    nlinarith
  have hcross : (pairCount G A B : ℝ) ≤ (3 / 1280 : ℝ) * n ^ 2 := by
    rw [pairCount_cast_eq_edgeCount]
    norm_num [TailoredTrichotomy.epsilon0] at hcross0 ⊢
    nlinarith [sq_nonneg (n : ℝ)]
  have hcards : A.card + B.card = 2 * n := by
    calc
      A.card + B.card = (A ∪ B).card := (Finset.card_union_of_disjoint hAB).symm
      _ = Finset.univ.card := by rw [hcover]
      _ = 2 * n := by simp
  have hAk : 256 ≤ A.card := by
    have : (256 : ℝ) ≤ A.card := by
      have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    exact_mod_cast this
  have hBk : 256 ≤ B.card := by
    have hcardsR : (A.card : ℝ) + B.card = 2 * n := by exact_mod_cast hcards
    have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
    have : (256 : ℝ) ≤ B.card := by nlinarith
    exact_mod_cast this
  have hscale : (2 * 256) * (2 * 256 + 3) < 2 * n := by omega
  obtain ⟨M, hM, hMcard⟩ := exists_large_crossing_matching_of_regular_partition
    (G := G) n 256 A B hAB hcover (by simp) hAk hBk hreg hscale
  have hmatch := matchingSurvivalBad_density_lt
    (crossingGraph G (A : Set (Fin (2 * n)))) M hM hMcard
  let U := (Finset.univ : Finset (Fin (2 * n))).powerset
  let badI := internalBadSamples G A B ((n : ℝ) / 100)
  let badM := U.filter fun S ↦ survivingEdgeCount M S < 2
  let good := U \ (badI ∪ badM)
  have hbadIsub : badI ⊆ U := by
    intro S hS
    obtain ⟨C, hC, hSC⟩ := Finset.mem_biUnion.mp hS
    exact (Finset.mem_filter.mp hSC).1
  have hbadMsub : badM ⊆ U := Finset.filter_subset _ _
  have hgoodCycle : good ⊆ cycleSpannedSubsets G := by
    intro S hS
    have hSgood := Finset.mem_sdiff.mp hS
    have hnotI : S ∉ badI := fun hSI ↦ hSgood.2 (Finset.mem_union_left _ hSI)
    have hnotM : S ∉ badM := fun hSM ↦ hSgood.2 (Finset.mem_union_right _ hSM)
    have hnotM' : ¬survivingEdgeCount M S < 2 := by
      intro hlt
      exact hnotM (Finset.mem_filter.mpr ⟨hSgood.1, hlt⟩)
    have hsurvive : 2 ≤ (M.filter fun e ↦ e.toFinset ⊆ S).card := by
      have hr : (2 : ℝ) ≤ survivingEdgeCount M S := le_of_not_gt hnotM'
      rw [survivingEdgeCount] at hr
      exact_mod_cast hr
    rw [mem_cycleSpannedSubsets]
    exact good_sample_isSpannedByCycle n (by omega) G (by simp) hreg
      A B hAB hcover hAlower hAupper hcross hminA hminB M hM S hnotI hsurvive
  have hgoodCard : good.card ≤ (cycleSpannedSubsets G).card :=
    Finset.card_le_card hgoodCycle
  have hpartition : U.card ≤ good.card + badI.card + badM.card := by
    have hunion : U = good ∪ (badI ∪ badM) := by
      apply Finset.Subset.antisymm
      · intro S hS
        by_cases hb : S ∈ badI ∪ badM
        · exact Finset.mem_union_right _ hb
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hS, hb⟩)
      · intro S hS
        rcases Finset.mem_union.mp hS with hSg | hSb
        · exact (Finset.mem_sdiff.mp hSg).1
        · rcases Finset.mem_union.mp hSb with hSI | hSM
          · exact hbadIsub hSI
          · exact hbadMsub hSM
    rw [hunion]
    calc
      (good ∪ (badI ∪ badM)).card ≤ good.card + (badI ∪ badM).card :=
        Finset.card_union_le _ _
      _ ≤ good.card + (badI.card + badM.card) :=
        Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = good.card + badI.card + badM.card := by omega
  have htotalNat : 2 ^ (2 * n) ≤
      (cycleSpannedSubsets G).card + badI.card + badM.card := by
    have hU : U.card = 2 ^ (2 * n) := by simp [U]
    rw [← hU]
    omega
  have htotal : (2 : ℝ) ^ (2 * n) ≤
      ((cycleSpannedSubsets G).card : ℝ) + badI.card + badM.card := by
    exact_mod_cast htotalNat
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := by positivity
  have hbadI : (badI.card : ℝ) / (2 : ℝ) ^ (2 * n) < 1 / 16 := by
    simpa [badI] using hinter G A B
  have hbadM : (badM.card : ℝ) / (2 : ℝ) ^ (2 * n) < 1 / 16 := by
    simpa [badM, U] using hmatch
  have hbadI' : (badI.card : ℝ) < (1 / 16 : ℝ) * (2 : ℝ) ^ (2 * n) :=
    (div_lt_iff₀ hpow).mp hbadI
  have hbadM' : (badM.card : ℝ) < (1 / 16 : ℝ) * (2 : ℝ) ^ (2 * n) :=
    (div_lt_iff₀ hpow).mp hbadM
  apply (cyclicSubsetDensity_lower_iff_count_lower G ((1 / 2 : ℝ) - epsilon)).mpr
  nlinarith [mul_pos hepsilon hpow]

/-- Root-regime spelling used by `Regimes.uniform_regime_trichotomy`. -/
theorem uniformCaseDensityBound_almostTwoCliques_root :
    UniformCaseDensityBound Erdos622.AlmostTwoCliquesRegime := by
  have hregime : Erdos622.AlmostTwoCliquesRegime = AlmostTwoCliquesRegime := by
    funext n G
    rfl
  rw [hregime]
  exact uniformCaseDensityBound_almostTwoCliques

end

end Erdos622.AlmostCliques
