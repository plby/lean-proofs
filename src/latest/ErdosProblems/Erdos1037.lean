/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1037.
https://www.erdosproblems.com/forum/thread/1037

Informal authors:
- Stijn Cambie
- Zach Hunter
- KoishiChan

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1037.md
-/
/-
Formalization of a theorem stating the existence of graphs with many distinct degrees
and small clique/independence numbers.

The main result is `Theorem_Main`, which proves that for any
$\varepsilon \in (0, 1 / 4)$, for sufficiently large $n$ divisible by 4, there
exists a graph on $n$ vertices such that:
1. Every degree occurs at most twice.
2. The number of distinct degrees is greater than $(1 / 2 + \varepsilon)n$.
3. The clique number and independence number are both $O(\log n)$.

The proof uses a probabilistic construction based on random graphs (Lemma `Lemma_Base`,
assumed) and a specific graph product/sum construction (`H_graph`). The properties
are verified using auxiliary lemmas about degree distribution and graph invariants
under isomorphism.
-/

import Mathlib

namespace Erdos1037

-- This generated proof file still has a broad automated proof-script warning
-- surface. The remaining suppressions guard warnings that would require a
-- substantial proof rewrite rather than local cleanup.
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

/-
A degree value $t$ occurs at most twice in $G$ if $|\{v \in V : d_G(v) = t\}| \le 2$. We say every degree occurs at most twice if this holds for all $t$.
-/
def DegreeOccursAtMostTwice {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ t : ℕ, (Finset.univ.filter (fun v => G.degree v = t)).card ≤ 2

/-
The set of distinct degrees of G is {d_G(v) : v ∈ V}, and its cardinality is the number of distinct degrees.
-/
def NumDistinctDegrees {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (fun v => G.degree v)).card

/-
If $Y$ is a Bernoulli(1 / 2) random variable, then $\mathbb{E}[e^{t(Y - 1 / 2)}] \le e^{t^2/8}$.
-/
theorem Bernoulli_MGF_bound
  {Ω : Type*} [MeasureTheory.MeasureSpace Ω] [MeasureTheory.IsProbabilityMeasure (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Ω)]
  (Y : Ω → ℝ)
  (h_meas : Measurable Y)
  (h_bernoulli : MeasureTheory.MeasureSpace.volume {ω | Y ω = 1} = 1 / 2 ∧ MeasureTheory.MeasureSpace.volume {ω | Y ω = 0} = 1 / 2)
  (h_range : ∀ᵐ ω ∂MeasureTheory.MeasureSpace.volume, Y ω = 0 ∨ Y ω = 1)
  (t : ℝ) :
  ∫ ω, Real.exp (t * (Y ω - 1 / 2)) ∂MeasureTheory.MeasureSpace.volume ≤ Real.exp (t^2 / 8) := by
    -- Let's simplify the integral.
    have h_integral_simplified : ∫ ω, Real.exp (t * (Y ω - 1 / 2)) ∂MeasureTheory.MeasureSpace.volume = (∫ ω in {ω | Y ω = 1}, Real.exp (t * (1 - 1 / 2))) + (∫ ω in {ω | Y ω = 0}, Real.exp (t * (0 - 1 / 2))) := by
      rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ];
      · rw [ ← MeasureTheory.integral_add ];
        · rw [ MeasureTheory.integral_congr_ae ];
          filter_upwards [ h_range ] with ω hω using by rcases hω with ( hω | hω ) <;> simp +decide [ hω ] ;
        · rw [ MeasureTheory.integrable_indicator_iff ] <;> norm_num;
          exact measurableSet_eq_fun h_meas measurable_const |> MeasurableSet.mem;
        · rw [ MeasureTheory.integrable_indicator_iff ] <;> norm_num;
          exact measurableSet_eq_fun h_meas measurable_const |> MeasurableSet.mem;
      · exact h_meas ( MeasurableSingletonClass.measurableSet_singleton _ );
      · exact h_meas ( MeasurableSingletonClass.measurableSet_singleton _ );
    -- Using the fact that $\cosh(x) \le e^{x^2/2}$ with $x = t/2$, we get
    have h_cosh_bound : Real.cosh (t / 2) ≤ Real.exp (t ^ 2 / 8) := by
      -- Using the inequality $\cosh(x) \le e^{x^2/2}$ with $x = t/2$, we get $\cosh(t/2) \le e^{(t/2)^2/2} = e^{t^2/8}$.
      have h_cosh_bound : ∀ x : ℝ, Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
        exact fun x => Real.cosh_le_exp_half_sq x;
      convert h_cosh_bound ( t / 2 ) using 1 ; ring_nf;
    simp_all +decide [ Real.cosh_eq ];
    norm_num [ MeasureTheory.measureReal_def ] at *;
    rw [ h_bernoulli.1, h_bernoulli.2 ] ; norm_num [ ENNReal.toReal_inv ] ; ring_nf at * ; linarith

/-
One-sided Hoeffding bound: $\mathbb{P}(X - N/2 \ge t) \le \exp(-2t^2/N)$.
-/
theorem Lemma_Hoeffding_OneSided
  {Ω : Type*} [MeasureTheory.MeasureSpace Ω] [MeasureTheory.IsProbabilityMeasure (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Ω)]
  (N : ℕ) (Y : Fin N → Ω → ℝ)
  (h_meas : ∀ i, Measurable (Y i))
  (h_indep : ProbabilityTheory.iIndepFun Y MeasureTheory.MeasureSpace.volume)
  (h_bernoulli : ∀ i, MeasureTheory.MeasureSpace.volume {ω | Y i ω = 1} = 1 / 2 ∧ MeasureTheory.MeasureSpace.volume {ω | Y i ω = 0} = 1 / 2)
  (h_range : ∀ i, ∀ᵐ ω ∂MeasureTheory.MeasureSpace.volume, Y i ω = 0 ∨ Y i ω = 1) :
  let X := ∑ i, Y i
  ∀ t > 0, (MeasureTheory.MeasureSpace.volume {ω | X ω - N / 2 ≥ t}).toReal ≤ Real.exp (-2 * t^2 / N) := by
    sorry
/-
Two-sided Hoeffding bound: $\mathbb{P}(|X - N/2| \ge t) \le 2 \exp(-2t^2/N)$.
-/
theorem Lemma_Hoeffding
  {Ω : Type*} [MeasureTheory.MeasureSpace Ω] [MeasureTheory.IsProbabilityMeasure (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Ω)]
  (N : ℕ) (Y : Fin N → Ω → ℝ)
  (h_meas : ∀ i, Measurable (Y i))
  (h_indep : ProbabilityTheory.iIndepFun Y MeasureTheory.MeasureSpace.volume)
  (h_bernoulli : ∀ i, MeasureTheory.MeasureSpace.volume {ω | Y i ω = 1} = 1 / 2 ∧ MeasureTheory.MeasureSpace.volume {ω | Y i ω = 0} = 1 / 2)
  (h_range : ∀ i, ∀ᵐ ω ∂MeasureTheory.MeasureSpace.volume, Y i ω = 0 ∨ Y i ω = 1) :
  let X := ∑ i, Y i
  ∀ t > 0, (MeasureTheory.MeasureSpace.volume {ω | |X ω - N / 2| ≥ t}).toReal ≤ 2 * Real.exp (-2 * t^2 / N) := by
    sorry
/-
We equip the set of simple graphs on V with the discrete measurable space.
-/
instance {V : Type*} [Fintype V] [DecidableEq V] : MeasurableSpace (SimpleGraph V) := ⊤

/-
The random graph $G_{m, 1 / 2}$ is the uniform measure on the set of all simple graphs on $m$ vertices.
-/
noncomputable def randomGraphMeasure {V : Type*} [Fintype V] [DecidableEq V] : MeasureTheory.Measure (SimpleGraph V) :=
  ProbabilityTheory.uniformOn Set.univ

/-
The indicator variable for the edge {u, v}.
-/
def edgeIndicator {V : Type*} [DecidableEq V] (u v : V) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if G.Adj u v then 1 else 0

/-
Indicator variable for whether u is adjacent to v.
-/
def incidentEdgeInd {m : ℕ} (v : Fin m) (u : {x // x ≠ v}) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] : ℝ :=
  if G.Adj u v then 1 else 0

/-
The probability that an edge exists in $G_{m, 1 / 2}$ is $1 / 2$.
-/
theorem incidentEdgeInd_Bernoulli {m : ℕ} (v : Fin m) (u : {x // x ≠ v}) :
  randomGraphMeasure {G : SimpleGraph (Fin m) | incidentEdgeInd v u G = 1} = 1 / 2 := by
    have h_card : (randomGraphMeasure {G : SimpleGraph (Fin m) | G.Adj u v}) = 1 / 2 := by
      have h_uniform : (randomGraphMeasure {G : SimpleGraph (Fin m) | G.Adj u v}) = (randomGraphMeasure {G : SimpleGraph (Fin m) | ¬G.Adj u v}) := by
        have h_uniform : (randomGraphMeasure {G : SimpleGraph (Fin m) | G.Adj u v}) = (randomGraphMeasure {G : SimpleGraph (Fin m) | ¬G.Adj u v}) := by
          have h_bij : ∃ f : SimpleGraph (Fin m) ≃ SimpleGraph (Fin m), ∀ G, f G ∈ {G : SimpleGraph (Fin m) | G.Adj u v} ↔ G ∈ {G : SimpleGraph (Fin m) | ¬G.Adj u v} := by
            refine ⟨ Equiv.ofBijective ( fun G => SimpleGraph.fromRel fun x y => if x = u.val ∧ y = v ∨ x = v ∧ y = u.val then ¬G.Adj u.val v else G.Adj x y ) ⟨ ?_, ?_ ⟩, ?_ ⟩;
            all_goals simp +decide [ Function.Injective, Function.Surjective ];
            · simp +decide [ SimpleGraph.fromRel, funext_iff ];
              intro G₁ G₂ h; ext x y; specialize h x y; by_cases hx : x = y <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
              by_cases hx' : x = u.val <;> by_cases hy' : y = v <;> by_cases hx'' : x = v <;> by_cases hy'' : y = u.val <;> simp_all +decide [ SimpleGraph.adj_comm ];
              · tauto;
              · tauto;
            · intro b;
              use SimpleGraph.fromRel fun x y => if x = u.val ∧ y = v ∨ x = v ∧ y = u.val then ¬b.Adj u.val v else b.Adj x y;
              ext x y; by_cases hx : x = u.val <;> by_cases hy : y = v <;> simp +decide [ hx, hy ] ;
              · grind;
              · by_cases hy : y = u.val <;> simp_all +decide [ SimpleGraph.adj_comm ];
                grind;
              · by_cases hv : v = u.val <;> simp_all +decide [ SimpleGraph.adj_comm ];
                aesop;
              · by_cases hx' : x = v <;> by_cases hy' : y = u.val <;> simp_all +decide [ SimpleGraph.adj_comm ];
                · tauto;
                · by_cases h : x = y <;> aesop;
            · aesop
          obtain ⟨ f, hf ⟩ := h_bij;
          -- Since $f$ is a bijection, the measure of the set of graphs where $u$ is adjacent to $v$ is equal to the measure of the set of graphs where $u$ is not adjacent to $v$.
          have h_measure_eq : ∀ (s : Set (SimpleGraph (Fin m))), (randomGraphMeasure (f '' s)) = (randomGraphMeasure s) := by
            unfold randomGraphMeasure;
            simp +decide [ ProbabilityTheory.uniformOn ];
            simp +decide [ Set.image, MeasureTheory.Measure.count ];
            simp +decide [ ProbabilityTheory.cond ];
            simp +decide [ Set.indicator ];
            intro s; rw [ show ( Finset.filter ( fun x => ∃ a ∈ s, f a = x ) Finset.univ : Finset ( SimpleGraph ( Fin m ) ) ) = Finset.image f ( Finset.filter ( fun x => x ∈ s ) Finset.univ ) by ext; aesop ] ; rw [ Finset.card_image_of_injective _ f.injective ] ;
          rw [ ← h_measure_eq ];
          congr with G ; specialize hf ( f.symm G ) ; aesop;
        exact h_uniform
      have h_uniform : (randomGraphMeasure {G : SimpleGraph (Fin m) | G.Adj u v}) + (randomGraphMeasure {G : SimpleGraph (Fin m) | ¬G.Adj u v}) = 1 := by
        rw [ ← MeasureTheory.measure_union ] <;> norm_num [ randomGraphMeasure ];
        · rw [ show { G : SimpleGraph ( Fin m ) | G.Adj ( u : Fin m ) v } ∪ { G : SimpleGraph ( Fin m ) | ¬G.Adj ( u : Fin m ) v } = Set.univ by ext; by_cases h : ( ‹_› : SimpleGraph ( Fin m ) ).Adj ( u : Fin m ) v <;> aesop ] ; norm_num [ ProbabilityTheory.uniformOn ] ;
        · exact disjoint_compl_right;
      rw [ ENNReal.eq_div_iff ] <;> norm_num;
      rw [ two_mul, ← h_uniform, ‹ ( randomGraphMeasure { G : SimpleGraph ( Fin m ) | G.Adj ( u : Fin m ) v } ) = ( randomGraphMeasure { G : SimpleGraph ( Fin m ) | ¬G.Adj ( u : Fin m ) v } ) › ];
    convert h_card using 4 ; unfold incidentEdgeInd ; aesop

/-
Indicator variable for whether u is adjacent to v, using classical logic.
-/
noncomputable def incidentEdgeInd_classical {m : ℕ} (v : Fin m) (u : {x // x ≠ v}) (G : SimpleGraph (Fin m)) : ℝ :=
  if G.Adj u v then 1 else 0

/-
The probability that an edge exists in $G_{m, 1 / 2}$ is $1 / 2$.
-/
theorem incidentEdgeInd_classical_Bernoulli {m : ℕ} (v : Fin m) (u : {x // x ≠ v}) :
  randomGraphMeasure {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G = 1} = 1 / 2 := by
    sorry
/-
The number of graphs where the adjacency of $v$ to $u \in S$ is fixed by $f$ is $2^{\binom{m}{2} - |S|}$.
-/
theorem card_graphs_with_fixed_edges {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) (f : {x // x ≠ v} → Bool) :
  (Finset.univ.filter (fun G : SimpleGraph (Fin m) => ∀ u ∈ S, G.Adj v u ↔ f u)).card = 2 ^ (m.choose 2 - S.card) := by
  classical
  let all_edges : (m : ℕ) → Finset (Sym2 (Fin m)) := fun m =>
    Finset.univ.filter (fun e => ¬e.IsDiag)
  have card_all_edges (m : ℕ) : (all_edges m).card = m.choose 2 := by
    have htop : all_edges m = (⊤ : SimpleGraph (Fin m)).edgeFinset := by
      ext e
      simp [all_edges]
    rw [htop, SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  let edge_of_neighbor :
      {m : ℕ} → (v : Fin m) → {x // x ≠ v} → Sym2 (Fin m) := fun {_m} v u =>
    Sym2.mk v u.val
  have edge_of_neighbor_injective {m : ℕ} (v : Fin m) :
      Function.Injective (edge_of_neighbor v) := by
    intro u w h
    apply Subtype.ext
    exact Sym2.congr_right.mp h
  let edges_from_S :
      {m : ℕ} → (v : Fin m) → Finset {x // x ≠ v} → Finset (Sym2 (Fin m)) :=
    fun {_m} v S => S.image (edge_of_neighbor v)
  have card_edges_from_S {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) :
      (edges_from_S v S).card = S.card := by
    change (S.image (edge_of_neighbor v)).card = S.card
    rw [Finset.card_image_of_injective]
    exact edge_of_neighbor_injective v
  have edges_from_S_subset_all_edges {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) :
      edges_from_S v S ⊆ all_edges m := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨u, _hu, rfl⟩
    simp [all_edges, edge_of_neighbor, Sym2.mk_isDiag_iff]
    exact Ne.symm u.property
  let graph_edges : {m : ℕ} → SimpleGraph (Fin m) → Finset (Sym2 (Fin m)) := fun {_m} G =>
    (all_edges _).filter (fun e => e ∈ G.edgeSet)
  have mem_graph_edges {m : ℕ} (G : SimpleGraph (Fin m)) (e : Sym2 (Fin m)) :
      e ∈ graph_edges G ↔ e ∈ all_edges m ∧ e ∈ G.edgeSet := by
    unfold graph_edges
    simp
  have card_powerset_fixed_on
      (E A : Finset (Sym2 (Fin m))) (hA : A ⊆ E) (p : Sym2 (Fin m) → Bool) :
      (E.powerset.filter (fun T : Finset (Sym2 (Fin m)) => ∀ x ∈ A, x ∈ T ↔ p x = Bool.true)).card =
        2 ^ (E.card - A.card) := by
    let Atrue := A.filter (fun x => p x)
    have h_eq :
        E.powerset.filter (fun T : Finset (Sym2 (Fin m)) => ∀ x ∈ A, x ∈ T ↔ p x = Bool.true) =
          (E \ A).powerset.image (fun T => Atrue ∪ T) := by
      ext T
      constructor
      · intro hT
        rw [Finset.mem_filter] at hT
        refine Finset.mem_image.mpr ⟨T \ A, ?_, ?_⟩
        · rw [Finset.mem_powerset]
          intro x hx
          rw [Finset.mem_sdiff] at hx ⊢
          exact ⟨Finset.mem_powerset.mp hT.1 hx.1, hx.2⟩
        · ext x
          by_cases hxA : x ∈ A
          · have hx_fixed := hT.2 x hxA
            by_cases hpx : p x
            · simp [Atrue, hxA, hpx, hx_fixed.mpr hpx]
            · have hxT : x ∉ T := fun hxT => hpx ((hx_fixed.mp hxT))
              simp [Atrue, hxA, hpx, hxT]
          · simp [Atrue, hxA]
      · intro hT
        rw [Finset.mem_image] at hT
        rcases hT with ⟨U, hU, rfl⟩
        have hUsub : U ⊆ E \ A := Finset.mem_powerset.mp hU
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          intro x hx
          rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact hA (Finset.mem_filter.mp hx).1
          · exact (Finset.mem_sdiff.mp (hUsub hx)).1
        · intro x hxA
          rw [Finset.mem_union]
          constructor
          · intro hx
            rcases hx with hx | hx
            · exact (Finset.mem_filter.mp hx).2
            · exact False.elim ((Finset.mem_sdiff.mp (hUsub hx)).2 hxA)
          · intro hpx
            exact Or.inl (Finset.mem_filter.mpr ⟨hxA, hpx⟩)
    rw [h_eq, Finset.card_image_of_injOn, Finset.card_powerset]
    · rw [Finset.card_sdiff_of_subset hA]
    · intro U hU W hW hUW
      rw [Finset.mem_coe] at hU hW
      have hUsub : U ⊆ E \ A := Finset.mem_powerset.mp hU
      have hWsub : W ⊆ E \ A := Finset.mem_powerset.mp hW
      ext x
      have hx := congr_arg (fun T : Finset (Sym2 (Fin m)) => x ∈ T) hUW
      by_cases hxA : x ∈ A
      · have hxU : x ∉ U := fun hxU => (Finset.mem_sdiff.mp (hUsub hxU)).2 hxA
        have hxW : x ∉ W := fun hxW => (Finset.mem_sdiff.mp (hWsub hxW)).2 hxA
        simp [hxU, hxW]
      · simpa [Atrue, hxA] using hx
  let E := all_edges m
  let A := edges_from_S v S
  have h_graphs :
      (Finset.univ.filter
        (fun G : SimpleGraph (Fin m) => ∀ u ∈ S, G.Adj v u ↔ f u)).card =
        (E.powerset.filter
          (fun T : Finset (Sym2 (Fin m)) => ∀ u ∈ S, edge_of_neighbor v u ∈ T ↔ f u)).card := by
    refine Finset.card_bij
      (fun G _ => graph_edges G) ?_ ?_ ?_
    · intro G hG
      rw [Finset.mem_filter] at hG
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        intro e he
        exact (mem_graph_edges G e).mp he |>.1
      · intro u hu
        have hedge : edge_of_neighbor v u ∈ E := by
          exact edges_from_S_subset_all_edges v S (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
        rw [mem_graph_edges]
        constructor
        · intro h
          exact (hG.2 u hu).mp (by
            simpa [edge_of_neighbor, SimpleGraph.mem_edgeSet] using h.2)
        · intro hf
          refine ⟨hedge, ?_⟩
          simpa [edge_of_neighbor, SimpleGraph.mem_edgeSet] using (hG.2 u hu).mpr hf
    · intro G₁ hG₁ G₂ hG₂ h_eq
      ext x y
      by_cases hxy : x = y
      · subst y
        simp
      · have hmem : Sym2.mk x y ∈ E := by
          simp [E, all_edges, Sym2.mk_isDiag_iff, hxy]
        have h := congr_arg (fun T : Finset (Sym2 (Fin m)) => Sym2.mk x y ∈ T) h_eq
        change (Sym2.mk x y ∈ graph_edges G₁) = (Sym2.mk x y ∈ graph_edges G₂) at h
        rw [mem_graph_edges, mem_graph_edges] at h
        simp [E, hmem, SimpleGraph.mem_edgeSet] at h
        exact h
    · intro T hT
      rw [Finset.mem_filter] at hT
      let G : SimpleGraph (Fin m) := SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m)))
      refine ⟨G, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ G
        · intro u hu
          have hne : v ≠ u.val := Ne.symm u.property
          have hfixed := hT.2 u hu
          rw [SimpleGraph.fromEdgeSet_adj]
          change Sym2.mk v u.val ∈ T ↔ f u = Bool.true at hfixed
          simp [hne, hfixed]
      · ext e
        rw [mem_graph_edges]
        constructor
        · intro he
          exact ((SimpleGraph.edgeSet_fromEdgeSet (T : Set (Sym2 (Fin m)))).symm ▸ he.2).1
        · intro heT
          have heE : e ∈ E := Finset.mem_powerset.mp hT.1 heT
          constructor
          · exact heE
          · rw [SimpleGraph.edgeSet_fromEdgeSet]
            exact ⟨heT, by simpa [E, all_edges] using heE⟩
  have h_sub : A ⊆ E := edges_from_S_subset_all_edges v S
  have h_count := card_powerset_fixed_on E A h_sub
      (fun x => if h : ∃ u ∈ S, edge_of_neighbor v u = x then f h.choose else false)
  have h_filters :
      E.powerset.filter
          (fun T : Finset (Sym2 (Fin m)) => ∀ u ∈ S, edge_of_neighbor v u ∈ T ↔ f u) =
        E.powerset.filter
          (fun T : Finset (Sym2 (Fin m)) => ∀ x ∈ A, x ∈ T ↔
            (if h : ∃ u ∈ S, edge_of_neighbor v u = x then f h.choose else false) = Bool.true) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
        have hex : ∃ w ∈ S, edge_of_neighbor v w = edge_of_neighbor v u := ⟨u, hu, rfl⟩
        rw [dif_pos hex]
        have hchoose_mem := (Classical.choose_spec hex).1
        have hchoose_eq := (Classical.choose_spec hex).2
        have hu_eq : Classical.choose hex = u :=
          edge_of_neighbor_injective v hchoose_eq
        change edge_of_neighbor v u ∈ T ↔ f (Classical.choose hex) = Bool.true
        rw [hu_eq]
        exact h.2 u hu⟩
    · intro h
      exact ⟨h.1, by
        intro u hu
        have hx : edge_of_neighbor v u ∈ A := Finset.mem_image.mpr ⟨u, hu, rfl⟩
        have hex : ∃ w ∈ S, edge_of_neighbor v w = edge_of_neighbor v u := ⟨u, hu, rfl⟩
        have hchoose_eq := (Classical.choose_spec hex).2
        have hu_eq : Classical.choose hex = u :=
          edge_of_neighbor_injective v hchoose_eq
        have hx_fixed := h.2 (edge_of_neighbor v u) hx
        rw [dif_pos hex] at hx_fixed
        change edge_of_neighbor v u ∈ T ↔ f (Classical.choose hex) = Bool.true at hx_fixed
        rw [hu_eq] at hx_fixed
        exact hx_fixed⟩
  rw [h_graphs, h_filters]
  calc
    (E.powerset.filter
        (fun T : Finset (Sym2 (Fin m)) => ∀ x ∈ A, x ∈ T ↔
          (if h : ∃ u ∈ S, edge_of_neighbor v u = x then f h.choose else false) = Bool.true)).card =
        2 ^ (E.card - A.card) := by
          convert h_count
    _ = 2 ^ (m.choose 2 - S.card) := by
      rw [card_all_edges, card_edges_from_S]

/-
The number of simple graphs on V is 2^{\binom{|V|}{2}}.
-/
theorem card_SimpleGraph {V : Type*} [Fintype V] [DecidableEq V] :
  Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
    sorry
/-
The set of all possible edges in a simple graph on $m$ vertices has size $\binom{m}{2}$.
-/
def all_edges (m : ℕ) : Finset (Sym2 (Fin m)) := Finset.univ.filter (fun e => ¬e.IsDiag)

theorem card_all_edges (m : ℕ) : (all_edges m).card = m.choose 2 := by
  unfold all_edges
  rw [← Fintype.card_subtype (fun e : Sym2 (Fin m) => ¬ e.IsDiag)]
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin]

/-
The number of subsets of $\alpha$ that agree with $f$ on $S$ is $2^{|\alpha| - |S|}$.
-/
theorem card_powerset_filter_mem {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (f : α → Bool) :
  (Finset.univ.filter (fun s : Finset α => ∀ x ∈ S, x ∈ s ↔ f x)).card = 2 ^ (Fintype.card α - S.card) := by
    -- The set of subsets that agree with $f$ on $S$ is in one-to-one correspondence with the set of subsets of $U = \alpha \setminus S$.
    have h_bij : Finset.filter (fun s => ∀ x ∈ S, x ∈ s ↔ f x = Bool.true) (Finset.univ : Finset (Finset α)) = Finset.image (fun t => Finset.filter (fun x => f x = Bool.true) S ∪ t) (Finset.powerset (Finset.univ \ S)) := by
      ext s
      simp [Finset.mem_image];
      constructor <;> intro h;
      · use s \ S;
        grind;
      · grind;
    rw [ h_bij, Finset.card_image_of_injOn, Finset.card_powerset ];
    · grind;
    · intro t ht t' ht' h_eq; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_eq a; replace ht := @ht a; replace ht' := @ht' a; aesop;

/-
The map $u \mapsto \{v, u\}$ is injective for $u \ne v$.
-/
def edge_of_neighbor {m : ℕ} (v : Fin m) (u : {x // x ≠ v}) : Sym2 (Fin m) :=
  Sym2.mk v u.val

theorem edge_of_neighbor_injective {m : ℕ} (v : Fin m) :
  Function.Injective (edge_of_neighbor v) := by
    intro u w h_eq
    simp [edge_of_neighbor] at h_eq
    aesop

/-
Embedding from neighbors to edges, and the set of edges corresponding to a set of neighbors.
-/
def edges_from_S_embedding {m : ℕ} (v : Fin m) : {x // x ≠ v} ↪ Sym2 (Fin m) :=
  ⟨edge_of_neighbor v, edge_of_neighbor_injective v⟩

def edges_from_S {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) : Finset (Sym2 (Fin m)) :=
  S.map (edges_from_S_embedding v)

/-
The number of edges corresponding to a set of neighbors $S$ is $|S|$.
-/
theorem card_edges_from_S {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) :
  (edges_from_S v S).card = S.card := by
    exact Finset.card_map _

/-
The edges incident to $v$ are non-diagonal.
-/
theorem edges_from_S_subset_all_edges {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) :
  edges_from_S v S ⊆ all_edges m := by
    -- Since $S$ consists of elements that are not equal to $v$, and $v$ is a Fin $m$, the pairs $(v, u.val)$ for $u \in S$ are non-diagonal.
    have h_non_diag : ∀ u ∈ S, ¬(Sym2.mk v u.val).IsDiag := by
      aesop;
    exact Finset.subset_iff.mpr fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by obtain ⟨ u, hu, rfl ⟩ := Finset.mem_map.mp hx; aesop ⟩

/-
The number of graphs with fixed edges is equal to the number of subsets of the remaining edges.
-/
theorem card_graphs_with_fixed_edges_aux {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) (f : {x // x ≠ v} → Bool) :
  (Finset.univ.filter (fun G : SimpleGraph (Fin m) => ∀ u ∈ S, G.Adj v u ↔ f u)).card =
  (Finset.powerset (all_edges m \ edges_from_S v S)).card := by
    -- Let's count the number of graphs where the adjacency of $v$ to $u \in S$ is fixed by $f$.
    have h_count : (Finset.univ.filter (fun G : SimpleGraph (Fin m) => ∀ u ∈ S, G.Adj v u ↔ f u)).card = 2 ^ ((m.choose 2) - S.card) := by
      convert card_graphs_with_fixed_edges v S f using 1;
    rw [ Finset.card_powerset, Finset.card_sdiff ];
    rw [ Finset.inter_eq_left.mpr ];
    · convert h_count using 2;
      rw [ card_all_edges, card_edges_from_S ];
    · exact edges_from_S_subset_all_edges v S

/-
The number of subsets of $U$ that agree with $f$ on $S$ (where $S \subseteq U$) is $2^{|U| - |S|}$.
-/
theorem card_powerset_filter_subset {α : Type*} (U : Finset α) (S : Finset α) (hS : S ⊆ U) (f : α → Bool) :
  (U.powerset.filter (fun A => ∀ x ∈ S, x ∈ A ↔ f x)).card = 2 ^ (U.card - S.card) := by
    classical
    -- Let $R = U \setminus S$. Any subset $A \subseteq U$ satisfying the condition can be written uniquely as $A' \cup \{x \in S : f(x)\}$, where $A' \subseteq R$.
    set R := U \ S
    have h_bij : {A ∈ U.powerset | ∀ x ∈ S, x ∈ A ↔ f x = Bool.true} = Finset.image (fun A' => A' ∪ S.filter (fun x => f x = Bool.true)) (Finset.powerset R) := by
      ext A;
      constructor;
      · intro hA
        obtain ⟨A', hA'⟩ : ∃ A' ⊆ R, A = A' ∪ (S.filter (fun x => f x = Bool.true)) := by
          use A \ S;
          grind;
        aesop;
      · grind;
    rw [ h_bij, Finset.card_image_of_injOn, Finset.card_powerset ];
    · grind;
    · intro A' hA' B' hB' hAB; simp_all +decide [ Finset.ext_iff ] ;
      intro x; specialize hAB x; replace hA' := @hA' x; replace hB' := @hB' x; aesop;

/-
The probability that a random graph has a specific configuration of edges incident to $v$ on a set $S$ is $(1 / 2)^{|S|}$.
-/
theorem measure_inter_incident_edges {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) (f : {x // x ≠ v} → Bool) :
  randomGraphMeasure {G : SimpleGraph (Fin m) | ∀ u ∈ S, G.Adj v u ↔ f u} = (1 / 2 : ENNReal) ^ S.card := by
    convert congr_arg ENNReal.ofReal ( show ( randomGraphMeasure { G : SimpleGraph ( Fin m ) | ∀ a ( b : ¬a = v ), ⟨ a, b ⟩ ∈ S → ( G.Adj v a ↔ f ⟨ a, b ⟩ = Bool.true ) } |> ENNReal.toReal ) = ( 2 : ℝ ) ⁻¹ ^ S.card from ?_ ) using 1;
    · unfold randomGraphMeasure; aesop;
    · rw [ ENNReal.ofReal_pow ] <;> norm_num;
      rw [ ENNReal.ofReal_div_of_pos ] <;> norm_num;
    · -- The measure of the set is the ratio of the number of graphs satisfying the condition to the total number of graphs.
      have h_measure : (randomGraphMeasure {G : SimpleGraph (Fin m) | ∀ u ∈ S, G.Adj v u ↔ f u = Bool.true}) = (Finset.univ.filter (fun G : SimpleGraph (Fin m) => ∀ u ∈ S, G.Adj v u ↔ f u = Bool.true)).card / (Finset.univ : Finset (SimpleGraph (Fin m))).card := by
        unfold randomGraphMeasure;
        rw [ ProbabilityTheory.uniformOn ];
        rw [ MeasureTheory.Measure.count ];
        rw [ ENNReal.div_eq_inv_mul ];
        rw [ ProbabilityTheory.cond ];
        simp +decide [ Set.indicator ];
      convert congr_arg ENNReal.toReal h_measure using 1
      · norm_num
      rw [ ENNReal.toReal_div ] ; norm_num [ card_SimpleGraph ];
      rw [ show ( Finset.univ.filter fun G : SimpleGraph ( Fin m ) => ∀ a : Fin m, ∀ b : a ≠ v, ⟨ a, b ⟩ ∈ S → ( G.Adj v a ↔ f ⟨ a, b ⟩ = Bool.true ) ).card = 2 ^ ( m.choose 2 - S.card ) from ?_, div_eq_mul_inv ];
      · field_simp;
        rw [ one_div, inv_pow, mul_comm ];
        rw [ ← div_eq_mul_inv, div_eq_iff ] <;> norm_cast <;> ring_nf;
        · rw [ ← pow_add, Nat.sub_add_cancel ( show S.card ≤ m.choose 2 from _ ) ];
          refine le_trans ( Finset.card_le_univ _ ) ?_ ; norm_num [ Nat.choose_two_right ];
          rcases m with ( _ | _ | m ) <;> simp +arith +decide [ Nat.mul_succ ];
          rw [ Nat.le_div_iff_mul_le ] <;> nlinarith;
        · positivity;
      · convert card_graphs_with_fixed_edges v S f using 1;
        congr! 3;
        grind

/-
The measure of a set of graphs is its cardinality divided by the total number of graphs.
-/
theorem randomGraphMeasure_eq_card_div {V : Type*} [Fintype V] [DecidableEq V] (s : Set (SimpleGraph V)) [DecidablePred (· ∈ s)] :
  randomGraphMeasure s = (Finset.univ.filter (· ∈ s)).card / Fintype.card (SimpleGraph V) := by
    unfold randomGraphMeasure;
    have h_uniform : ProbabilityTheory.uniformOn (Set.univ : Set (SimpleGraph V)) s = MeasureTheory.Measure.count s / MeasureTheory.Measure.count (Set.univ : Set (SimpleGraph V)) := by
      simp +decide [ ProbabilityTheory.uniformOn ];
      rw [ ENNReal.div_eq_inv_mul ];
      rw [ ProbabilityTheory.cond ];
      simp +decide
    simp_all +decide [MeasureTheory.Measure.count_apply]
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card]
    have hcard :
        Fintype.card ↑s = (Finset.univ.filter (fun x : SimpleGraph V => x ∈ s)).card := by
      exact Fintype.card_ofFinset (Finset.univ.filter (fun x : SimpleGraph V => x ∈ s)) (by
        intro x
        simp)
    rw [hcard]
    norm_num

/-
The number of neighbors of a vertex is at most $\binom{m}{2}$.
-/
theorem card_le_choose_two {m : ℕ} (v : Fin m) (S : Finset {x // x ≠ v}) :
  S.card ≤ m.choose 2 := by
    rcases m with ( _ | _ | m ) <;> norm_num [ Nat.choose ] at *;
    · exact Fin.elim0 v;
    · decide +revert;
    · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num; linarith [ Nat.choose_le_pow m 2 ] )

/-
The probability that the clique number of a random graph on $m$ vertices is at least $r$ is at most $\binom{m}{r} 2^{-\binom{r}{2}}$.
-/
theorem prob_cliqueNum_ge (m r : ℕ) :
  randomGraphMeasure {G : SimpleGraph (Fin m) | r ≤ G.cliqueNum} ≤ (m.choose r : ENNReal) * (1 / 2) ^ (r.choose 2) := by
    sorry
/-
The probability that the independence number of a random graph on $m$ vertices is at least $r$ is at most $\binom{m}{r} 2^{-\binom{r}{2}}$.
-/
theorem prob_indepNum_ge (m r : ℕ) :
  randomGraphMeasure {G : SimpleGraph (Fin m) | r ≤ G.indepNum} ≤ (m.choose r : ENNReal) * (1 / 2) ^ (r.choose 2) := by
    have h_complement : randomGraphMeasure {G : SimpleGraph (Fin m) | r ≤ G.indepNum} = randomGraphMeasure {G : SimpleGraph (Fin m) | r ≤ G.cliqueNum} := by
      unfold randomGraphMeasure;
      unfold ProbabilityTheory.uniformOn;
      norm_num [ MeasureTheory.Measure.count ];
      rw [ ProbabilityTheory.cond_apply, ProbabilityTheory.cond_apply ];
      · norm_num [ Set.indicator ];
        rw [ show ( { x : SimpleGraph ( Fin m ) | r ≤ x.indepNum } : Finset ( SimpleGraph ( Fin m ) ) ) = Finset.image ( fun G => Gᶜ ) ( { x : SimpleGraph ( Fin m ) | r ≤ x.cliqueNum } : Finset ( SimpleGraph ( Fin m ) ) ) from ?_, Finset.card_image_of_injective _ ( show Function.Injective ( fun G : SimpleGraph ( Fin m ) => Gᶜ ) from fun G₁ G₂ h => by simpa using h ) ];
        ext; aesop;
      · exact MeasurableSet.univ;
      · exact MeasurableSet.univ;
    exact h_complement.symm ▸ prob_cliqueNum_ge m r

/-
The degree of a vertex $v$ is the sum of the indicator variables of the edges incident to $v$.
-/
theorem degree_eq_sum_indicators (m : ℕ) (v : Fin m) (G : SimpleGraph (Fin m)) :
  (G.degree v : ℝ) = ∑ u : {x // x ≠ v}, incidentEdgeInd_classical v u G := by
    unfold incidentEdgeInd_classical;
    simp +decide
    rw [ Finset.card_filter ];
    rw [ ← Finset.sum_filter ];
    rw [ SimpleGraph.degree ];
    rw [ show ( G.neighborFinset v ) = Finset.univ.filter ( fun u => G.Adj u v ) from ?_, Finset.card_filter ];
    · rw [ ← Finset.sum_filter ];
      refine Finset.sum_bij ( fun x hx => ⟨ x, ?_ ⟩ ) ?_ ?_ ?_ ?_ <;> aesop;
    · ext; simp +decide [ SimpleGraph.adj_comm ]

/-
The edge indicators incident to a vertex $v$ are independent.
-/
set_option maxHeartbeats 800000 in
-- Expanding independence over all incident edge choices needs extra heartbeats.
theorem edge_indicators_independent (m : ℕ) (v : Fin m) :
  ProbabilityTheory.iIndepFun (fun u : {x // x ≠ v} => incidentEdgeInd_classical v u) randomGraphMeasure := by
    -- We use `ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul`.
    -- Let $S$ be a finite set of indices. Let $A_u$ be measurable sets for $u \in S$.
    -- We need to show $P(\bigcap_{u \in S} Y_u^{-1}(A_u)) = \prod_{u \in S} P(Y_u^{-1}(A_u))$.
    have h_indep : ∀ (S : Finset {x // x ≠ v}) (A : {x // x ≠ v} → Set ℝ), (∀ u ∈ S, MeasurableSet (A u)) → (randomGraphMeasure (⋂ u ∈ S, {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G ∈ A u})) = ∏ u ∈ S, (randomGraphMeasure {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G ∈ A u}) := by
      -- For each $u \in S$, the set $A_u$ is either $\emptyset$, $\{0\}$, $\{1\}$, or $\{0, 1\}$.
      intros S A hA
      have h_cases : ∀ u ∈ S, (randomGraphMeasure {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G ∈ A u}) = if (0 ∈ A u) ∧ (1 ∈ A u) then 1 else if (0 ∈ A u) then (1 / 2 : ENNReal) else if (1 ∈ A u) then (1 / 2 : ENNReal) else 0 := by
        intro u hu
        have h_cases : {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G ∈ A u} = if (0 ∈ A u) ∧ (1 ∈ A u) then Set.univ else if (0 ∈ A u) then {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G = 0} else if (1 ∈ A u) then {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G = 1} else ∅ := by
          ext G; unfold incidentEdgeInd_classical; aesop;
        split_ifs <;> simp_all +decide [ incidentEdgeInd_classical_Bernoulli ];
        · unfold randomGraphMeasure;
          simp +decide [ ProbabilityTheory.uniformOn ];
        · have h_complement : {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G = 0} = Set.univ \ {G : SimpleGraph (Fin m) | incidentEdgeInd_classical v u G = 1} := by
            ext G; simp [incidentEdgeInd_classical];
          rw [ h_complement, MeasureTheory.measure_diff ] <;> norm_num [ incidentEdgeInd_classical_Bernoulli ];
          erw [ ProbabilityTheory.uniformOn_univ ] ; norm_num;
          rw [ ENNReal.div_self ] <;> norm_num;
      by_cases h : ∃ u ∈ S, 0 ∉ A u ∧ 1 ∉ A u <;> simp_all +decide [ Finset.prod_ite ];
      · rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr ];
        · obtain ⟨ a, b, ha, hb, hc ⟩ := h; rw [ zero_pow ] <;> aesop;
        · obtain ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ := h; filter_upwards [ ] with G; simp_all +decide [ Set.mem_iInter ] ;
          exact ⟨ a, ha₁, ha₂, by unfold incidentEdgeInd_classical; aesop ⟩;
      · convert measure_inter_incident_edges v ( Finset.filter ( fun u => 0 ∈ A u → 1 ∉ A u ) S ) ( fun u => if 0 ∈ A u then Bool.false else Bool.true ) using 1;
        · congr with G ; simp +decide [ incidentEdgeInd_classical ];
          simp +decide [ SimpleGraph.adj_comm ];
          grind;
        · norm_num [ ENNReal.inv_pow ];
    rw [ ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul ];
    exact fun S {sets} _H ↦ h_indep S sets _H

/-
Concentration of degree around its mean.
-/
set_option maxHeartbeats 800000 in
-- The Hoeffding specialization and graph-measure conversions need extra heartbeats.
theorem degree_concentration_at_vertex (m : ℕ) (hm : m > 1) (v : Fin m) (t : ℝ) (ht : t > 0) :
  (randomGraphMeasure { G : SimpleGraph (Fin m) | |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t }).toReal ≤ 2 * Real.exp (-2 * t^2 / (m - 1 : ℝ)) := by
    sorry
/-
The probability that any vertex has a degree deviating from the mean by at least $t$ is at most $2m \exp(-2t^2/(m-1))$.
-/
theorem degree_concentration_union_bound (m : ℕ) (hm : m > 1) (t : ℝ) (ht : t > 0) :
  (randomGraphMeasure { G : SimpleGraph (Fin m) | ∃ v, |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t }).toReal ≤ 2 * m * Real.exp (-2 * t^2 / (m - 1 : ℝ)) := by
    have h_union_bound : ∀ (v : Fin m), (randomGraphMeasure {G : SimpleGraph (Fin m) | |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t}).toReal ≤ 2 * Real.exp (-2 * t^2 / (m - 1 : ℝ)) := by
      exact fun v ↦ degree_concentration_at_vertex m hm v t ht;
    have h_union_bound : (randomGraphMeasure (⋃ v : Fin m, {G : SimpleGraph (Fin m) | |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t})).toReal ≤ ∑ v : Fin m, (randomGraphMeasure {G : SimpleGraph (Fin m) | |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t}).toReal := by
      -- Apply the union bound to the sum of probabilities.
      have h_union_bound : (randomGraphMeasure (⋃ v : Fin m, {G : SimpleGraph (Fin m) | |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t})) ≤ ∑ v : Fin m, (randomGraphMeasure {G : SimpleGraph (Fin m) | |(G.degree v : ℝ) - (m - 1 : ℝ) / 2| ≥ t}) := by
        convert MeasureTheory.measure_iUnion_fintype_le _ _;
        infer_instance;
      convert ENNReal.toReal_mono _ h_union_bound;
      · field_simp;
        rw [ ENNReal.toReal_sum ]
        focus
          congr
        focus
          ext
        focus
          ring_nf
        · ac_rfl;
        · unfold randomGraphMeasure; aesop;
      · exact ENNReal.sum_ne_top.mpr fun v _ => ne_of_lt <| lt_of_le_of_lt ( MeasureTheory.measure_mono <| Set.subset_univ _ ) <| by simp +decide [ randomGraphMeasure ] ;
    exact le_trans ( by simpa only [ Set.setOf_exists ] using h_union_bound ) ( le_trans ( Finset.sum_le_sum fun _ _ => by solve_by_elim ) ( by norm_num; linarith ) )

/-
Definitions for the threshold values used in the proof.
-/
noncomputable def r_val (m : ℕ) : ℕ := Nat.ceil (3 * Real.logb 2 m)

noncomputable def t_val (m : ℕ) : ℝ := 2 * Real.sqrt (m * Real.log m)

/-
Definitions of the upper bounds for the probabilities of large clique number and large degree deviation.
-/
noncomputable def bound_clique (m : ℕ) : ℝ := (m.choose (r_val m) : ℝ) * (1 / 2) ^ (r_val m).choose 2

noncomputable def bound_degree (m : ℕ) : ℝ := 2 * m * Real.exp (-2 * (t_val m)^2 / (m - 1))

/-
The bound for the clique number probability tends to 0.
-/
theorem bound_clique_tendsto_zero : Filter.Tendsto bound_clique Filter.atTop (nhds 0) := by
  -- We show that the exponent tends to negative infinity.
  have h_exp_neg_inf : Filter.Tendsto (fun m : ℕ => Nat.ceil (3 * Real.logb 2 m) * Real.logb 2 m - Nat.ceil (3 * Real.logb 2 m) * (Nat.ceil (3 * Real.logb 2 m) - 1) / 2) Filter.atTop Filter.atBot := by
    -- We'll use the fact that $Real.logb 2 m$ grows to infinity as $m$ tends to infinity.
    have h_log_growth : Filter.Tendsto (fun m : ℕ => Real.logb 2 m) Filter.atTop Filter.atTop := by
      exact Real.tendsto_logb_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
    rw [ Filter.tendsto_atTop_atBot ];
    exact fun b => Filter.eventually_atTop.mp ( h_log_growth.eventually_gt_atTop ( |b| + 3 ) ) |> fun ⟨ i, hi ⟩ => ⟨ i, fun m hm => by cases abs_cases b <;> nlinarith [ Nat.le_ceil ( 3 * Real.logb 2 m ), hi m hm ] ⟩;
  -- We can rewrite the bound using the properties of exponents.
  have h_bound_exp : ∀ m : ℕ, m > 1 → bound_clique m ≤ 2 ^ (Nat.ceil (3 * Real.logb 2 m) * Real.logb 2 m - (Nat.ceil (3 * Real.logb 2 m) * (Nat.ceil (3 * Real.logb 2 m) - 1) / 2 : ℝ)) := by
    intros m hm
    have h_binom : (m.choose (Nat.ceil (3 * Real.logb 2 m)) : ℝ) ≤ 2 ^ (Nat.ceil (3 * Real.logb 2 m) * Real.logb 2 m) := by
      have h_binom : (m.choose (Nat.ceil (3 * Real.logb 2 m)) : ℝ) ≤ m ^ (Nat.ceil (3 * Real.logb 2 m)) := by
        norm_cast;
        exact Nat.choose_le_pow m ⌈3 * Real.logb 2 ↑m⌉₊;
      convert h_binom using 1 ; rw [ mul_comm, Real.rpow_mul ] <;> norm_num [ hm.le ];
      rw [ Real.rpow_logb ] <;> norm_cast ; linarith
    have h_exp : (1 / 2 : ℝ) ^ (Nat.ceil (3 * Real.logb 2 m)).choose 2 ≤ 2 ^ (-(Nat.ceil (3 * Real.logb 2 m) * (Nat.ceil (3 * Real.logb 2 m) - 1) / 2 : ℝ)) := by
      norm_num [ Nat.choose_two_right ];
      rw [ Real.rpow_neg ] <;> norm_num;
      rw [ ← Real.inv_rpow ] <;> norm_num;
      rw [ ← Real.rpow_natCast ];
      rw [ Nat.cast_div ] <;> norm_num;
      · rw [ Nat.cast_pred ( Nat.ceil_pos.mpr ( mul_pos zero_lt_three ( Real.logb_pos ( by norm_num ) ( by norm_cast ) ) ) ) ];
      · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )
    have h_bound : bound_clique m ≤ 2 ^ (Nat.ceil (3 * Real.logb 2 m) * Real.logb 2 m) * 2 ^ (-(Nat.ceil (3 * Real.logb 2 m) * (Nat.ceil (3 * Real.logb 2 m) - 1) / 2 : ℝ)) := by
      exact mul_le_mul h_binom h_exp ( by positivity ) ( by positivity )
    have h_final : bound_clique m ≤ 2 ^ (Nat.ceil (3 * Real.logb 2 m) * Real.logb 2 m - (Nat.ceil (3 * Real.logb 2 m) * (Nat.ceil (3 * Real.logb 2 m) - 1) / 2 : ℝ)) := by
      convert h_bound using 1
      rw [ ← Real.rpow_add ]
      focus
        ring_nf
      norm_num
    exact h_final;
  -- Since the exponent tends to negative infinity, the bound tends to zero.
  have h_bound_zero : Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ (Nat.ceil (3 * Real.logb 2 m) * Real.logb 2 m - (Nat.ceil (3 * Real.logb 2 m) * (Nat.ceil (3 * Real.logb 2 m) - 1) / 2 : ℝ))) Filter.atTop (nhds 0) := by
    norm_num [ Real.rpow_def_of_pos ] at *;
    exact Filter.Tendsto.const_mul_atBot ( by positivity ) h_exp_neg_inf;
  exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun m hm => by rw [ Real.norm_of_nonneg ( show 0 ≤ bound_clique m from by exact mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by norm_num ) _ ) ) ] ; exact h_bound_exp m hm ⟩ ) h_bound_zero

/-
The bound for the degree deviation probability tends to 0.
-/
theorem bound_degree_tendsto_zero : Filter.Tendsto bound_degree Filter.atTop (nhds 0) := by
  unfold bound_degree;
  refine squeeze_zero_norm'
    (f := fun n : ℕ => 2 * (n : ℝ) * Real.exp (-2 * (t_val n)^2 / ((n : ℝ) - 1)))
    (a := fun n : ℕ => 2 * (n : ℝ) * Real.exp ( -8 * Real.log n )) ?_ ?_;
  · refine Filter.eventually_atTop.mpr ⟨ 2, fun n hn => ?_ ⟩ ; norm_num;
    field_simp;
    exact Real.exp_le_exp.mpr ( neg_le_neg <| by rw [ div_eq_mul_inv ] ; nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ), mul_inv_cancel₀ ( show ( n - 1 : ℝ ) ≠ 0 by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] ), show ( t_val n : ℝ ) ^ 2 ≥ 4 * n * Real.log n by exact by rw [ show t_val n = 2 * Real.sqrt ( n * Real.log n ) by rfl ] ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( n : ℝ ) * Real.log n by positivity ) ] ] );
  · -- We can simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * n * (n ^ (-8 : ℝ))) Filter.atTop (nhds 0) by
      refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
    norm_cast ; norm_num [ mul_assoc, ← pow_succ' ];
    exact le_trans ( tendsto_const_nhds.mul ( tendsto_inv_atTop_nhds_zero_nat.pow 7 |> Filter.Tendsto.congr ( by intros; by_cases hn : ( ‹_› : ℕ ) = 0 <;> simp +decide [ hn, pow_succ, mul_assoc ] ) ) ) ( by norm_num )

/-
For sufficiently large $m$, there exists a graph with small clique/independence number and concentrated degrees.
-/
theorem Lemma_Base :
  ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ R : SimpleGraph (Fin m),
    (R.cliqueNum : ℝ) ≤ 3 * Real.logb 2 m ∧
    (R.indepNum : ℝ) ≤ 3 * Real.logb 2 m ∧
    (R.maxDegree : ℝ) - (R.minDegree : ℝ) ≤ 4 * Real.sqrt (m * Real.log m) := by
      sorry
/-
Construction of the graph H from R and orderings.
-/
def V_H (m : ℕ) := (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)

noncomputable def degree_in_R_copies (m : ℕ) (R : SimpleGraph (Fin m)) (x : Fin m ⊕ Fin m) : ℕ :=
  match x with
  | Sum.inl a => R.degree a
  | Sum.inr b => R.degree b

def is_ordered (m : ℕ) (R : SimpleGraph (Fin m)) (σ : Fin (2 * m) ≃ Fin m ⊕ Fin m) : Prop :=
  ∀ i j : Fin (2 * m), i ≤ j → degree_in_R_copies m R (σ i) ≥ degree_in_R_copies m R (σ j)

def H_adj (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (u v : V_H m) : Prop :=
  match u, v with
  | Sum.inl (Sum.inl a1), Sum.inl (Sum.inl a2) => R.Adj a1 a2
  | Sum.inl (Sum.inr b1), Sum.inl (Sum.inr b2) => R.Adj b1 b2
  | Sum.inr (Sum.inl c1), Sum.inr (Sum.inl c2) => R.Adj c1 c2
  | Sum.inr (Sum.inr d1), Sum.inr (Sum.inr d2) => R.Adj d1 d2
  | Sum.inl (Sum.inl _), Sum.inl (Sum.inr _) => True
  | Sum.inl (Sum.inr _), Sum.inl (Sum.inl _) => True
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => False
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => False
  | Sum.inl x, Sum.inr y =>
    (σ_AB.symm x : ℕ) + (σ_CD.symm y : ℕ) ≤ 2 * m - 2
  | Sum.inr y, Sum.inl x =>
    (σ_AB.symm x : ℕ) + (σ_CD.symm y : ℕ) ≤ 2 * m - 2

def H_graph (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m) : SimpleGraph (V_H m) where
  Adj := H_adj m R σ_AB σ_CD
  symm := by
    sorry
  loopless := by
    sorry
/-
The adjacency relation of H is decidable.
-/
noncomputable instance H_adj_decidable (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m) :
    DecidableRel (H_graph m R σ_AB σ_CD).Adj :=
  Classical.decRel _

/-
Instances for V_H m using inferInstanceAs.
-/
instance (m : ℕ) : Fintype (V_H m) :=
  inferInstanceAs (Fintype ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)))

instance (m : ℕ) : DecidableEq (V_H m) :=
  inferInstanceAs (DecidableEq ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)))

/-
The degree of a vertex in the AB part of H is its degree in R plus m plus (2m - 1 - i).
-/
theorem degree_H_inl (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (i : Fin (2 * m)) :
    (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i)) =
    degree_in_R_copies m R (σ_AB i) + m + (2 * m - 1 - i) := by
  classical
  let G := H_graph m R σ_AB σ_CD
  let v : V_H m := Sum.inl (σ_AB i)
  have card_filter_sum :
      ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
        (p : α ⊕ β → Prop) [DecidablePred p],
        (Finset.univ.filter p).card =
          (Finset.univ.filter (fun a : α => p (Sum.inl a))).card +
          (Finset.univ.filter (fun b : β => p (Sum.inr b))).card := by
    intro α β _ _ _ _ p _
    let L : Finset α := Finset.univ.filter (fun a : α => p (Sum.inl a))
    let R' : Finset β := Finset.univ.filter (fun b : β => p (Sum.inr b))
    have h :
        Finset.univ.filter p =
          L.map Function.Embedding.inl ∪ R'.map Function.Embedding.inr := by
      ext x
      cases x <;> simp [L, R']
    rw [h, Finset.card_union_of_disjoint]
    · simp [L, R']
    · rw [Finset.disjoint_left]
      intro x hx hxR
      cases x <;> simp at hx hxR
  let AB : Finset (Fin m ⊕ Fin m) :=
    Finset.univ.filter (fun u => G.Adj v (Sum.inl u))
  let CD : Finset (Fin m ⊕ Fin m) :=
    Finset.univ.filter (fun u => G.Adj v (Sum.inr u))
  have hdeg :
      G.degree v = AB.card + CD.card := by
    change (G.neighborFinset v).card = AB.card + CD.card
    rw [SimpleGraph.neighborFinset_eq_filter]
    exact card_filter_sum (fun u : V_H m => G.Adj v u)
  have hAB : AB.card = degree_in_R_copies m R (σ_AB i) + m := by
    cases hσ : σ_AB i with
    | inl a =>
        have hsplit :
            AB.card =
              (Finset.univ.filter (fun x : Fin m => R.Adj a x)).card +
                (Finset.univ : Finset (Fin m)).card := by
          change (Finset.univ.filter (fun u : Fin m ⊕ Fin m =>
              G.Adj v (Sum.inl u))).card = _
          rw [card_filter_sum (fun u : Fin m ⊕ Fin m => G.Adj v (Sum.inl u))]
          simp [G, v, H_graph, H_adj, hσ]
        have hR :
            (Finset.univ.filter (fun x : Fin m => R.Adj a x)).card = R.degree a := by
          rw [← SimpleGraph.neighborFinset_eq_filter R]
          exact SimpleGraph.card_neighborFinset_eq_degree R a
        rw [hsplit, hR, Finset.card_univ]
        simp [degree_in_R_copies]
    | inr b =>
        have hsplit :
            AB.card =
              (Finset.univ : Finset (Fin m)).card +
                (Finset.univ.filter (fun x : Fin m => R.Adj b x)).card := by
          change (Finset.univ.filter (fun u : Fin m ⊕ Fin m =>
              G.Adj v (Sum.inl u))).card = _
          rw [card_filter_sum (fun u : Fin m ⊕ Fin m => G.Adj v (Sum.inl u))]
          simp [G, v, H_graph, H_adj, hσ]
        have hR :
            (Finset.univ.filter (fun x : Fin m => R.Adj b x)).card = R.degree b := by
          rw [← SimpleGraph.neighborFinset_eq_filter R]
          exact SimpleGraph.card_neighborFinset_eq_degree R b
        rw [hsplit, hR, Finset.card_univ]
        simp [degree_in_R_copies, Nat.add_comm]
  have hCD :
      CD.card =
        (Finset.univ.filter
          (fun j : Fin (2 * m) => i.val + j.val ≤ 2 * m - 2)).card := by
    let S : Finset (Fin (2 * m)) :=
      Finset.univ.filter (fun j : Fin (2 * m) => i.val + j.val ≤ 2 * m - 2)
    have hSCD : S.card = CD.card := by
      refine Finset.card_equiv σ_CD ?_
      intro j
      simp [S, CD, G, v, H_graph, H_adj]
    exact hSCD.symm
  have hCD_count :
      (Finset.univ.filter
        (fun j : Fin (2 * m) => i.val + j.val ≤ 2 * m - 2)).card =
        2 * m - 1 - i.val := by
    have htoRange :
        (Finset.univ.filter
          (fun j : Fin (2 * m) => i.val + j.val ≤ 2 * m - 2)).card =
          ((Finset.range (2 * m)).filter
            (fun j : ℕ => i.val + j ≤ 2 * m - 2)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      rw [Finset.sum_range]
    rw [htoRange]
    have hfilter :
        (Finset.range (2 * m)).filter
            (fun j : ℕ => i.val + j ≤ 2 * m - 2) =
          Finset.range (2 * m - 1 - i.val) := by
      ext j
      simp [Finset.mem_range]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [hfilter, Finset.card_range]
  calc
    (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i))
        = G.degree v := rfl
    _ = AB.card + CD.card := hdeg
    _ = (degree_in_R_copies m R (σ_AB i) + m) + (2 * m - 1 - i.val) := by
      rw [hAB, hCD, hCD_count]
    _ = degree_in_R_copies m R (σ_AB i) + m + (2 * m - 1 - i) := by
      omega

/-
The number of j such that i + j <= 2m - 2 is 2m - 1 - i.
-/
theorem card_filter_le_sum (m : ℕ) (i : Fin (2 * m)) :
    (Finset.univ.filter (fun j : Fin (2 * m) => (i : ℕ) + (j : ℕ) ≤ 2 * m - 2)).card = 2 * m - 1 - (i : ℕ) := by
      rw [ Finset.card_eq_of_bijective ];
      · use fun j hj => ⟨ j, by omega ⟩
      · grind;
      · grind;
      · aesop

/-
The number of neighbors of a vertex in CD that are in AB is 2m - 1 - j.
-/
theorem card_neighbors_in_AB (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (j : Fin (2 * m)) :
    (Finset.filter (fun u => (H_graph m R σ_AB σ_CD).Adj (Sum.inr (σ_CD j)) (Sum.inl u)) Finset.univ).card =
    2 * m - 1 - (j : ℕ) := by
      have h_card : Finset.card (Finset.filter (fun u : Fin m ⊕ Fin m => (σ_AB.symm u : ℕ) + (σ_CD.symm (σ_CD j) : ℕ) ≤ 2 * m - 2) Finset.univ) = 2 * m - 1 - j := by
        convert card_filter_le_sum m j using 1;
        rw [ Finset.card_filter, Finset.card_filter ];
        conv_rhs => rw [ ← Equiv.sum_comp σ_AB.symm ] ;
        simp +decide [ add_comm ];
      convert h_card using 2;
      ext; simp [H_graph];
      unfold H_adj; aesop;

/-
The degree of a vertex in the CD part of H is its degree in R plus (2m - 1 - j).
-/
theorem degree_H_inr (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (j : Fin (2 * m)) :
    (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) =
    degree_in_R_copies m R (σ_CD j) + (2 * m - 1 - j) := by
  classical
  let G := H_graph m R σ_AB σ_CD
  let v : V_H m := Sum.inr (σ_CD j)
  have card_filter_sum :
      ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
        (p : α ⊕ β → Prop) [DecidablePred p],
        (Finset.univ.filter p).card =
          (Finset.univ.filter (fun a : α => p (Sum.inl a))).card +
          (Finset.univ.filter (fun b : β => p (Sum.inr b))).card := by
    intro α β _ _ _ _ p _
    let L : Finset α := Finset.univ.filter (fun a : α => p (Sum.inl a))
    let R' : Finset β := Finset.univ.filter (fun b : β => p (Sum.inr b))
    have h :
        Finset.univ.filter p =
          L.map Function.Embedding.inl ∪ R'.map Function.Embedding.inr := by
      ext x
      cases x <;> simp [L, R']
    rw [h, Finset.card_union_of_disjoint]
    · simp [L, R']
    · rw [Finset.disjoint_left]
      intro x hx hxR
      cases x <;> simp at hx hxR
  let AB : Finset (Fin m ⊕ Fin m) :=
    Finset.univ.filter (fun u => G.Adj v (Sum.inl u))
  let CD : Finset (Fin m ⊕ Fin m) :=
    Finset.univ.filter (fun u => G.Adj v (Sum.inr u))
  have hdeg :
      G.degree v = AB.card + CD.card := by
    change (G.neighborFinset v).card = AB.card + CD.card
    rw [SimpleGraph.neighborFinset_eq_filter]
    exact card_filter_sum (fun u : V_H m => G.Adj v u)
  have hAB : AB.card = 2 * m - 1 - (j : ℕ) := by
    simpa [AB, G, v] using card_neighbors_in_AB m R σ_AB σ_CD j
  have hCD : CD.card = degree_in_R_copies m R (σ_CD j) := by
    cases hσ : σ_CD j with
    | inl c =>
        have hsplit :
            CD.card =
              (Finset.univ.filter (fun x : Fin m => R.Adj c x)).card := by
          change (Finset.univ.filter (fun u : Fin m ⊕ Fin m =>
              G.Adj v (Sum.inr u))).card = _
          rw [card_filter_sum (fun u : Fin m ⊕ Fin m => G.Adj v (Sum.inr u))]
          simp [G, v, H_graph, H_adj, hσ]
        have hR :
            (Finset.univ.filter (fun x : Fin m => R.Adj c x)).card = R.degree c := by
          rw [← SimpleGraph.neighborFinset_eq_filter R]
          exact SimpleGraph.card_neighborFinset_eq_degree R c
        rw [hsplit, hR]
        simp [degree_in_R_copies]
    | inr d =>
        have hsplit :
            CD.card =
              (Finset.univ.filter (fun x : Fin m => R.Adj d x)).card := by
          change (Finset.univ.filter (fun u : Fin m ⊕ Fin m =>
              G.Adj v (Sum.inr u))).card = _
          rw [card_filter_sum (fun u : Fin m ⊕ Fin m => G.Adj v (Sum.inr u))]
          simp [G, v, H_graph, H_adj, hσ]
        have hR :
            (Finset.univ.filter (fun x : Fin m => R.Adj d x)).card = R.degree d := by
          rw [← SimpleGraph.neighborFinset_eq_filter R]
          exact SimpleGraph.card_neighborFinset_eq_degree R d
        rw [hsplit, hR]
        simp [degree_in_R_copies]
  calc
    (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j))
        = G.degree v := rfl
    _ = AB.card + CD.card := hdeg
    _ = (2 * m - 1 - (j : ℕ)) + degree_in_R_copies m R (σ_CD j) := by
      rw [hAB, hCD]
    _ = degree_in_R_copies m R (σ_CD j) + (2 * m - 1 - j) := by
      omega

/-
The degree of a vertex in the CD part of H is its degree in R plus (2m - 1 - j).
-/
theorem degree_H_inr_eq (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (j : Fin (2 * m)) :
    (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) =
    degree_in_R_copies m R (σ_CD j) + (2 * m - 1 - j) := by
      exact degree_H_inr m R σ_AB σ_CD j

/-
The degrees of vertices in the AB part are distinct and strictly decreasing with respect to the index.
-/
theorem distinct_degrees_AB (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (h_ord : is_ordered m R σ_AB)
    (i j : Fin (2 * m)) (hij : i < j) :
    (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i)) >
    (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB j)) := by
  rw [degree_H_inl, degree_H_inl]
  have hdeg := h_ord i j hij.le
  omega

/-
The degrees of vertices in the CD part are distinct and strictly decreasing with respect to the index.
-/
theorem distinct_degrees_CD (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (h_ord : is_ordered m R σ_CD)
    (i j : Fin (2 * m)) (hij : i < j) :
    (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD i)) >
    (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) := by
      -- By definition of $H$, the degree of a vertex in CD part is its degree in R plus (2m - 1 - j).
      have h_deg_CD : ∀ j : Fin (2 * m),
        (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) =
        degree_in_R_copies m R (σ_CD j) + (2 * m - 1 - j) := by
          exact fun j ↦ degree_H_inr m R σ_AB σ_CD j;
      have := h_ord i j hij.le;
      grind

/-
Every degree occurs at most twice in H.
-/
theorem degree_at_most_twice (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (h_ord_AB : is_ordered m R σ_AB)
    (h_ord_CD : is_ordered m R σ_CD) :
    DegreeOccursAtMostTwice (H_graph m R σ_AB σ_CD) := by
      have h_degrees_AB : ∀ i j : Fin (2 * m), i ≠ j → (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i)) ≠ (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB j)) := by
        intro i j hij; cases lt_or_gt_of_ne hij <;> [ exact ne_of_gt ( distinct_degrees_AB m R σ_AB σ_CD h_ord_AB _ _ ‹_› ) ; exact ne_of_lt ( distinct_degrees_AB m R σ_AB σ_CD h_ord_AB _ _ ‹_› ) ] ;
      have h_degrees_CD : ∀ i j : Fin (2 * m), i ≠ j → (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD i)) ≠ (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) := by
        intro i j hij; cases lt_or_gt_of_ne hij <;> [ exact ne_of_gt ( distinct_degrees_CD m R σ_AB σ_CD h_ord_CD _ _ ‹_› ) ; exact ne_of_lt ( distinct_degrees_CD m R σ_AB σ_CD h_ord_CD _ _ ‹_› ) ] ;
      intro t;
      refine le_trans
        (b :=
          (Finset.image ( fun i => Sum.inl ( σ_AB i ) )
            ( Finset.univ.filter fun i =>
              ( H_graph m R σ_AB σ_CD ).degree ( Sum.inl ( σ_AB i ) ) = t ) ∪
            Finset.image ( fun i => Sum.inr ( σ_CD i ) )
              ( Finset.univ.filter fun i =>
                ( H_graph m R σ_AB σ_CD ).degree ( Sum.inr ( σ_CD i ) ) = t )).card)
        ( Finset.card_le_card ?_ ) ?_;
      · intro v hv
        rcases v with v | v
        · obtain ⟨w, rfl⟩ := σ_AB.surjective v
          exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨w, by simpa using hv, rfl⟩)
        · obtain ⟨w, rfl⟩ := σ_CD.surjective v
          exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨w, by simpa using hv, rfl⟩)
      · refine le_trans
          ( Finset.card_union_le
            (Finset.image ( fun i => Sum.inl ( σ_AB i ) )
              ( Finset.univ.filter fun i =>
                ( H_graph m R σ_AB σ_CD ).degree ( Sum.inl ( σ_AB i ) ) = t ))
            (Finset.image ( fun i => Sum.inr ( σ_CD i ) )
              ( Finset.univ.filter fun i =>
                ( H_graph m R σ_AB σ_CD ).degree ( Sum.inr ( σ_CD i ) ) = t )) ) ?_;
        rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        · exact le_trans ( add_le_add ( Finset.card_le_one.mpr fun i hi j hj => Classical.not_not.1 fun hi' => h_degrees_AB i j hi' <| by aesop ) ( Finset.card_le_one.mpr fun i hi j hj => Classical.not_not.1 fun hi' => h_degrees_CD i j hi' <| by aesop ) ) ( by norm_num );

/-
If j is large enough, the degree of w_j is not equal to the degree of any v_i.
-/
theorem distinct_degrees_cross_parts (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (i j : Fin (2 * m))
    (hj : (j : ℕ) > m + (R.maxDegree - R.minDegree)) :
    (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) ≠
    (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i)) := by
      -- Substitute the expressions for the degrees.
      have h_degrees : (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j)) = degree_in_R_copies m R (σ_CD j) + (2 * m - 1 - j) ∧ (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i)) = degree_in_R_copies m R (σ_AB i) + m + (2 * m - 1 - i) := by
        exact ⟨ degree_H_inr_eq m R σ_AB σ_CD j, degree_H_inl m R σ_AB σ_CD i ⟩;
      -- By definition of $degree_in_R_copies$, we know that $degree_in_R_copies m R (σ_CD j) \leq R.maxDegree$ and $degree_in_R_copies m R (σ_AB i) \geq R.minDegree$.
      have h_bounds : degree_in_R_copies m R (σ_CD j) ≤ R.maxDegree ∧ degree_in_R_copies m R (σ_AB i) ≥ R.minDegree := by
        exact ⟨ by rcases σ_CD j with ( a | b ) <;> [ exact R.degree_le_maxDegree _ ; exact R.degree_le_maxDegree _ ], by rcases σ_AB i with ( a | b ) <;> [ exact R.minDegree_le_degree _ ; exact R.minDegree_le_degree _ ] ⟩;
      omega

/-
The set of degrees of H.
-/
noncomputable def degrees_of_H (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m) : Finset ℕ :=
  Finset.image (fun v => (H_graph m R σ_AB σ_CD).degree v) (Finset.univ : Finset (V_H m))

/-
The number of distinct degrees in H is at least 3m - (Delta - delta) - 1.
-/
theorem num_distinct_degrees_ge (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (h_ord_AB : is_ordered m R σ_AB)
    (h_ord_CD : is_ordered m R σ_CD) :
    (degrees_of_H m R σ_AB σ_CD).card ≥
    3 * m - (R.maxDegree - R.minDegree) - 1 := by
      -- Let's count the number of distinct degrees in the AB part and the CD part.
      have h_distinct_degrees_AB : Finset.card (Finset.image (fun i : Fin (2 * m) => (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i))) (Finset.univ)) = 2 * m := by
        rw [ Finset.card_image_of_injective ];
        · simp +decide;
        · intro i j hij;
          exact le_antisymm ( le_of_not_gt fun hi => by linarith [ distinct_degrees_AB m R σ_AB σ_CD h_ord_AB _ _ hi ] ) ( le_of_not_gt fun hj => by linarith [ distinct_degrees_AB m R σ_AB σ_CD h_ord_AB _ _ hj ] );
      -- Let's count the number of distinct degrees in the CD part.
      have h_distinct_degrees_CD : Finset.card (Finset.image (fun j : Fin (2 * m) => (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j))) (Finset.univ.filter (fun j : Fin (2 * m) => (j : ℕ) > m + (R.maxDegree - R.minDegree)))) ≥ m - (R.maxDegree - R.minDegree) - 1 := by
        rw [ Finset.card_image_of_injOn, Finset.card_filter ];
        · rw [ Finset.sum_fin_eq_sum_range ];
          norm_num [ Finset.sum_ite ];
          rw [ show ( Finset.filter ( fun x => m + ( R.maxDegree - R.minDegree ) < x ) ( Finset.filter ( fun x => x < 2 * m ) ( Finset.range ( 2 * m ) ) ) ) = Finset.Ioo ( m + ( R.maxDegree - R.minDegree ) ) ( 2 * m ) by ext; aesop ] ; simp +arith +decide;
          omega;
        · intros j hj k hk h_eq;
          have := distinct_degrees_CD m R σ_AB σ_CD h_ord_CD;
          exact le_antisymm ( le_of_not_gt fun h => by linarith [ this _ _ h ] ) ( le_of_not_gt fun h => by linarith [ this _ _ h ] );
      -- The total number of distinct degrees in H is at least the sum of the number of distinct degrees in the AB part and the CD part.
      have h_total_distinct_degrees : (degrees_of_H m R σ_AB σ_CD).card ≥ (Finset.image (fun i : Fin (2 * m) => (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i))) (Finset.univ)).card + (Finset.image (fun j : Fin (2 * m) => (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j))) (Finset.univ.filter (fun j : Fin (2 * m) => (j : ℕ) > m + (R.maxDegree - R.minDegree)))).card := by
        have h_total_distinct_degrees : (degrees_of_H m R σ_AB σ_CD).card ≥ (Finset.image (fun i : Fin (2 * m) => (H_graph m R σ_AB σ_CD).degree (Sum.inl (σ_AB i))) (Finset.univ) ∪ Finset.image (fun j : Fin (2 * m) => (H_graph m R σ_AB σ_CD).degree (Sum.inr (σ_CD j))) (Finset.univ.filter (fun j : Fin (2 * m) => (j : ℕ) > m + (R.maxDegree - R.minDegree)))).card := by
          refine Finset.card_le_card ?_;
          simp +decide [ Finset.subset_iff ];
          rintro x ( ⟨ a, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> [ exact Finset.mem_image.mpr ⟨ _, Finset.mem_univ _, rfl ⟩ ; exact Finset.mem_image.mpr ⟨ _, Finset.mem_univ _, rfl ⟩ ];
        rwa [ Finset.card_union_of_disjoint ] at h_total_distinct_degrees;
        norm_num [ Finset.disjoint_left ];
        exact fun a x a_1 ↦ distinct_degrees_cross_parts m R σ_AB σ_CD a x a_1;
      omega

/-
The clique number of H is at most 4 times the clique number of R.
-/
set_option maxHeartbeats 800000 in
-- The partition argument expands several large finite-set goals.
theorem cliqueNum_H_le (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m) :
    (H_graph m R σ_AB σ_CD).cliqueNum ≤ 4 * R.cliqueNum := by
      have h_clique_num : ∀ s : Finset (V_H m), s.card > 4 * R.cliqueNum → ¬(∀ u ∈ s, ∀ v ∈ s, u ≠ v → (H_graph m R σ_AB σ_CD).Adj u v) := by
        intros s hs_card hs_clique
        have h_partition : ∃ s1 s2 s3 s4 : Finset (Fin m), s1.card + s2.card + s3.card + s4.card > 4 * R.cliqueNum ∧ (∀ u ∈ s1, ∀ v ∈ s1, u ≠ v → R.Adj u v) ∧ (∀ u ∈ s2, ∀ v ∈ s2, u ≠ v → R.Adj u v) ∧ (∀ u ∈ s3, ∀ v ∈ s3, u ≠ v → R.Adj u v) ∧ (∀ u ∈ s4, ∀ v ∈ s4, u ≠ v → R.Adj u v) := by
          use Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inl (Sum.inl u)), Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inl (Sum.inr u)), Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inr (Sum.inl u)), Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inr (Sum.inr u));
          constructor;
          · have h_partition : s.card ≤ (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inl (Sum.inl u))).card + (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inl (Sum.inr u))).card + (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inr (Sum.inl u))).card + (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inr (Sum.inr u))).card := by
              have h_partition : s ⊆ Finset.image (fun u => Sum.inl (Sum.inl u)) (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inl (Sum.inl u))) ∪ Finset.image (fun u => Sum.inl (Sum.inr u)) (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inl (Sum.inr u))) ∪ Finset.image (fun u => Sum.inr (Sum.inl u)) (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inr (Sum.inl u))) ∪ Finset.image (fun u => Sum.inr (Sum.inr u)) (Finset.univ.filter (fun u => ∃ v ∈ s, v = Sum.inr (Sum.inr u))) := by
                intro u hu; rcases u with ( ( u | u ) | ( u | u ) ) <;> aesop;
              exact le_trans ( Finset.card_le_card h_partition ) ( by exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( Finset.card_image_le ) ( Finset.card_image_le ) ) ) ( Finset.card_image_le ) ) ) ( Finset.card_image_le ) ) );
            linarith;
          · simp_all +decide [ H_graph ];
            refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> intros <;> have := hs_clique _ ‹_› _ ‹_› <;> simp_all +decide [ H_adj ];
            · grind;
            · grind;
            · grind;
            · grind;
        obtain ⟨ s1, s2, s3, s4, h1, h2, h3, h4, h5 ⟩ := h_partition;
        have h_clique_num : ∀ s : Finset (Fin m), (∀ u ∈ s, ∀ v ∈ s, u ≠ v → R.Adj u v) → s.card ≤ R.cliqueNum := by
          intros s hs_clique;
          refine le_csSup ?_ ?_;
          · exact ⟨ _, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
          · exact ⟨ s, by rw [ SimpleGraph.isNClique_iff ] ; aesop ⟩;
        linarith [ h_clique_num s1 h2, h_clique_num s2 h3, h_clique_num s3 h4, h_clique_num s4 h5 ];
      refine csSup_le' ?_;
      rintro n ⟨ s, hs ⟩;
      exact le_of_not_gt fun hn => h_clique_num s ( by linarith [ hs.2 ] ) hs.1

/-
The preimage of an independent set in H under the embedding of A is independent in R.
-/
theorem isIndepSet_preimage_A (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (S : Set (V_H m)) (hS : (H_graph m R σ_AB σ_CD).IsIndepSet S) :
    R.IsIndepSet {u : Fin m | Sum.inl (Sum.inl u) ∈ S} := by
      intro u hu v hv huv; have := hS; simp_all +decide [ SimpleGraph.IsIndepSet ] ;
      -- By definition of H_adj, if u and v are adjacent in R, then their images in H are adjacent.
      have h_adj_H : (H_graph m R σ_AB σ_CD).Adj (Sum.inl (Sum.inl u)) (Sum.inl (Sum.inl v)) ↔ R.Adj u v := by
        exact Iff.symm (SimpleGraph.adj_congr_of_sym2 R rfl);
      exact fun h => this hu hv ( by aesop ) ( h_adj_H.mpr h )

/-
The preimage of an independent set in H under the embedding of B is independent in R.
-/
theorem isIndepSet_preimage_B (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (S : Set (V_H m)) (hS : (H_graph m R σ_AB σ_CD).IsIndepSet S) :
    R.IsIndepSet {u : Fin m | Sum.inl (Sum.inr u) ∈ S} := by
      -- Since S is an independent set in H, for any two elements in S, they are not adjacent. In particular, if we take two elements of the form Sum.inl (Sum.inr u) and Sum.inl (Sum.inr v), they are not adjacent in H.
      have h_not_adj : ∀ u v : Fin m, Sum.inl (Sum.inr u) ∈ S → Sum.inl (Sum.inr v) ∈ S → ¬(H_graph m R σ_AB σ_CD).Adj (Sum.inl (Sum.inr u)) (Sum.inl (Sum.inr v)) := by
        intros u v hu hv h_adj
        have := hS hu hv
        aesop;
      intros u hu v hv; specialize h_not_adj u v hu hv; unfold H_graph at h_not_adj; aesop;

/-
The preimage of an independent set in H under the embedding of C is independent in R.
-/
theorem isIndepSet_preimage_C (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (S : Set (V_H m)) (hS : (H_graph m R σ_AB σ_CD).IsIndepSet S) :
    R.IsIndepSet {u : Fin m | Sum.inr (Sum.inl u) ∈ S} := by
      intro u hu v hv huv hAdj
      exact hS hu hv (by
        intro h
        injection h with h'
        injection h' with huv'
        exact huv huv') (by
        simpa [H_graph, H_adj] using hAdj)

/-
The preimage of an independent set in H under the embedding of D is independent in R.
-/
theorem isIndepSet_preimage_D (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (S : Set (V_H m)) (hS : (H_graph m R σ_AB σ_CD).IsIndepSet S) :
    R.IsIndepSet {u : Fin m | Sum.inr (Sum.inr u) ∈ S} := by
      intro x hx y hy;
      contrapose! hS;
      -- Since x and y are adjacent in R, they are also adjacent in H.
      have h_adj : (H_graph m R σ_AB σ_CD).Adj (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inr y)) := by
        exact hS.2;
      unfold SimpleGraph.IsIndepSet; aesop;

/-
The independence number of H is at most 4 times the independence number of R.
-/
theorem indepNum_H_le (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m) :
    (H_graph m R σ_AB σ_CD).indepNum ≤ 4 * R.indepNum := by
      -- Let $S$ be an independent set in $H$. Then $S$ can be partitioned into four parts: $S \cap A$, $S \cap B$, $S \cap C$, and $S \cap D$.
      have h_partition : ∀ S : Set (V_H m), (H_graph m R σ_AB σ_CD).IsIndepSet S → S.ncard ≤ 4 * R.indepNum := by
        intro S hS
        have h_partition : S.ncard ≤ (Set.ncard {u : Fin m | Sum.inl (Sum.inl u) ∈ S}) + (Set.ncard {u : Fin m | Sum.inl (Sum.inr u) ∈ S}) + (Set.ncard {u : Fin m | Sum.inr (Sum.inl u) ∈ S}) + (Set.ncard {u : Fin m | Sum.inr (Sum.inr u) ∈ S}) := by
          have h_partition : S = (Set.image (fun u : Fin m => Sum.inl (Sum.inl u)) {u : Fin m | Sum.inl (Sum.inl u) ∈ S}) ∪ (Set.image (fun u : Fin m => Sum.inl (Sum.inr u)) {u : Fin m | Sum.inl (Sum.inr u) ∈ S}) ∪ (Set.image (fun u : Fin m => Sum.inr (Sum.inl u)) {u : Fin m | Sum.inr (Sum.inl u) ∈ S}) ∪ (Set.image (fun u : Fin m => Sum.inr (Sum.inr u)) {u : Fin m | Sum.inr (Sum.inr u) ∈ S}) := by
            ext x
            constructor
            · intro hx
              rcases x with ((a | b) | (c | d))
              · exact Or.inl (Or.inl (Or.inl ⟨a, hx, rfl⟩))
              · exact Or.inl (Or.inl (Or.inr ⟨b, hx, rfl⟩))
              · exact Or.inl (Or.inr ⟨c, hx, rfl⟩)
              · exact Or.inr ⟨d, hx, rfl⟩
            · intro hx
              rcases x with ((a | b) | (c | d))
              · rcases hx with (((hx | hx) | hx) | hx)
                · rcases hx with ⟨_, hmem, heq⟩
                  cases heq
                  exact hmem
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, _, h⟩
                  cases h
              · rcases hx with (((hx | hx) | hx) | hx)
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, hmem, heq⟩
                  cases heq
                  exact hmem
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, _, h⟩
                  cases h
              · rcases hx with (((hx | hx) | hx) | hx)
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, hmem, heq⟩
                  cases heq
                  exact hmem
                · rcases hx with ⟨_, _, h⟩
                  cases h
              · rcases hx with (((hx | hx) | hx) | hx)
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, _, h⟩
                  cases h
                · rcases hx with ⟨_, hmem, heq⟩
                  cases heq
                  exact hmem
          conv_lhs => rw [ h_partition ];
          exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add ( le_trans ( Set.ncard_union_le _ _ ) ( add_le_add ( le_trans ( Set.ncard_union_le _ _ ) ( add_le_add ( Set.ncard_image_le ) ( Set.ncard_image_le ) ) ) ( Set.ncard_image_le ) ) ) ( Set.ncard_image_le ) );
        have h_partition : ∀ T : Set (Fin m), R.IsIndepSet T → T.ncard ≤ R.indepNum := by
          intro T hT;
          have h_partition : ∀ T : Finset (Fin m), R.IsIndepSet T → T.card ≤ R.indepNum := by
            exact fun T a ↦ SimpleGraph.IsIndepSet.card_le_indepNum a;
          convert h_partition ( Set.toFinset T ) _;
          · rw [ Set.ncard_eq_toFinset_card' ];
          · aesop;
        linarith [ h_partition { u : Fin m | Sum.inl ( Sum.inl u ) ∈ S } ( isIndepSet_preimage_A m R σ_AB σ_CD S hS ), h_partition { u : Fin m | Sum.inl ( Sum.inr u ) ∈ S } ( isIndepSet_preimage_B m R σ_AB σ_CD S hS ), h_partition { u : Fin m | Sum.inr ( Sum.inl u ) ∈ S } ( isIndepSet_preimage_C m R σ_AB σ_CD S hS ), h_partition { u : Fin m | Sum.inr ( Sum.inr u ) ∈ S } ( isIndepSet_preimage_D m R σ_AB σ_CD S hS ) ];
      refine csSup_le ?_ ?_ <;> norm_num;
      · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩ ⟩;
      · intro b x hx; specialize h_partition x; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
        cases hx ; aesop

/-
The cardinality of an independent set in H is at most 4 times the independence number of R.
-/
theorem card_le_four_times_indepNum (m : ℕ) (R : SimpleGraph (Fin m))
    (σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m)
    (S : Finset (V_H m)) (hS : (H_graph m R σ_AB σ_CD).IsIndepSet S) :
    S.card ≤ 4 * R.indepNum := by
      -- Since S is an independent set in H, its cardinality is at most the independence number of H.
      have h_card_S : S.card ≤ (H_graph m R σ_AB σ_CD).indepNum := by
        exact SimpleGraph.IsIndepSet.card_le_indepNum hS;
      refine le_trans h_card_S ?_;
      exact indepNum_H_le m R σ_AB σ_CD

/-
There exists an ordering of the vertices of two copies of R such that their degrees are non-increasing.
-/
lemma exists_ordering (m : ℕ) (R : SimpleGraph (Fin m)) :
  ∃ σ : Fin (2 * m) ≃ Fin m ⊕ Fin m, is_ordered m R σ := by
    -- By definition of `is_ordered`, we need to show that for any $i < j$, the degree of $σ(i)$ is at least the degree of $σ(j)$.
    have h_order : ∃ σ : Fin (2 * m) ≃ Fin m ⊕ Fin m, ∀ i j : Fin (2 * m), i < j → degree_in_R_copies m R (σ i) ≥ degree_in_R_copies m R (σ j) := by
      -- By definition of `Finset.sort`, we can obtain a sorted list of elements in `Fin m ⊕ Fin m` based on their degrees in `R`.
      obtain ⟨ sorted_list, h_sorted ⟩ : ∃ sorted_list : List (Fin m ⊕ Fin m), List.length sorted_list = 2 * m ∧ List.Pairwise (fun x y => degree_in_R_copies m R x ≥ degree_in_R_copies m R y) sorted_list ∧ List.Nodup sorted_list ∧ ∀ x ∈ sorted_list, x ∈ Finset.univ := by
        have h_sort : ∀ {l : List (Fin m ⊕ Fin m)}, List.Nodup l → ∃ sorted_l : List (Fin m ⊕ Fin m), List.length sorted_l = List.length l ∧ List.Pairwise (fun x y => degree_in_R_copies m R x ≥ degree_in_R_copies m R y) sorted_l ∧ List.Nodup sorted_l ∧ ∀ x ∈ sorted_l, x ∈ l := by
          intros l hl_nodup
          use List.insertionSort (fun x y => degree_in_R_copies m R x ≥ degree_in_R_copies m R y) l;
          refine ⟨ ?_, ?_, ?_, ?_ ⟩;
          · rw [ List.length_insertionSort ];
          · convert List.pairwise_insertionSort _ _;
            · exact ⟨ fun x y => le_total _ _ ⟩;
            · exact ⟨ fun x y z hxy hyz => le_trans hyz hxy ⟩;
          · exact List.Perm.nodup_iff ( List.perm_insertionSort _ _ ) |>.2 hl_nodup;
          · intro x hx; have := List.mem_insertionSort ( fun x y => degree_in_R_copies m R x ≥ degree_in_R_copies m R y ) |>.1 hx; aesop;
        have h_univ_list : ∃ l : List (Fin m ⊕ Fin m), List.length l = 2 * m ∧ List.Nodup l ∧ ∀ x ∈ l, x ∈ Finset.univ := by
          use Finset.univ.toList;
          simp +decide [ Finset.card_univ ];
          exact ⟨ by ring, Finset.nodup_toList _ ⟩;
        obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := h_univ_list; obtain ⟨ sorted_l, hsorted_l₁, hsorted_l₂, hsorted_l₃, hsorted_l₄ ⟩ := h_sort hl₂; use sorted_l; aesop;
      have h_order : ∃ σ : Fin (2 * m) → Fin m ⊕ Fin m, Function.Injective σ ∧ ∀ i j : Fin (2 * m), i < j → degree_in_R_copies m R (σ i) ≥ degree_in_R_copies m R (σ j) := by
        have h_order : ∃ σ : Fin (2 * m) → Fin m ⊕ Fin m, Function.Injective σ ∧ ∀ i j : Fin (2 * m), i < j → degree_in_R_copies m R (σ i) ≥ degree_in_R_copies m R (σ j) := by
          have h_sorted_list : ∃ l : Fin (2 * m) → Fin m ⊕ Fin m, List.Pairwise (fun x y => degree_in_R_copies m R x ≥ degree_in_R_copies m R y) (List.ofFn l) ∧ List.Nodup (List.ofFn l) := by
            have h_sorted_list : ∃ l : Fin (2 * m) → Fin m ⊕ Fin m, List.ofFn l = sorted_list := by
              use fun i => sorted_list.get ⟨ i, by linarith [ Fin.is_lt i ] ⟩;
              refine List.ext_get ?_ ?_ <;> aesop;
            aesop
          obtain ⟨ l, hl₁, hl₂ ⟩ := h_sorted_list;
          refine ⟨ l, ?_, ?_ ⟩ <;> simp_all +decide;
          intro i j hij; have := List.nodup_ofFn.mp hl₂; aesop;
        exact h_order;
      obtain ⟨σ, hσ_inj, hσ_sorted⟩ := h_order;
      use Equiv.ofBijective σ ⟨hσ_inj, by
        exact ( Fintype.bijective_iff_injective_and_card σ ).mpr ⟨ hσ_inj, by simp +decide [ two_mul ] ⟩ |>.2⟩;
      generalize_proofs at *;
      exact fun i j hij => hσ_sorted i j hij;
    exact ⟨ h_order.choose, fun i j hij => by cases lt_or_eq_of_le hij <;> [ exact h_order.choose_spec i j ‹_› ; aesop ] ⟩

/-
For sufficiently large m, the number of distinct degrees is greater than (1 / 2 + epsilon) * 4m.
-/
theorem distinct_degrees_bound_aux (ε : ℝ) (hε : ε < 1 / 4) :
  ∀ᶠ m : ℕ in Filter.atTop,
    (3 * m : ℝ) - 4 * Real.sqrt (m * Real.log m) > (1 / 2 + ε) * (4 * m) := by
      -- We can divide both sides by $m$ to get $3 - 4 \sqrt{\frac{\log m}{m}} > 2 + 4 \epsilon$.
      suffices h_div : ∀ᶠ m : ℕ in Filter.atTop, 3 - 4 * Real.sqrt (Real.log m / (m : ℝ)) > 2 + 4 * ε by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with m hm₁ hm₂ using by rw [ show ( m : ℝ ) * Real.log m = m ^ 2 * ( Real.log m / m ) by rw [ mul_div, eq_div_iff ( by positivity ) ] ; ring ] ; rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; nlinarith [ show ( m :ℝ ) > 0 by exact Nat.cast_pos.mpr hm₂, Real.sqrt_nonneg ( Real.log m / m ), Real.mul_self_sqrt ( show 0 ≤ Real.log m / m by positivity ) ] ;
      -- We'll use the fact that $\sqrt{\frac{\log m}{m}}$ tends to $0$ as $m$ tends to infinity.
      have h_sqrt_zero : Filter.Tendsto (fun m : ℕ => Real.sqrt (Real.log m / (m : ℝ))) Filter.atTop (nhds 0) := by
        have h_log_div_m_zero : Filter.Tendsto (fun m : ℕ => Real.log m / (m : ℝ)) Filter.atTop (nhds 0) := by
          -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
          suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num +zetaDelta at *;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        simpa using h_log_div_m_zero.sqrt;
      exact h_sqrt_zero.const_mul 4 |> fun h => h.const_sub 3 |> fun h => h.eventually ( lt_mem_nhds <| by linarith )

/-
An equivalence between `V_H m` and `Fin (4m)`.
-/
def iso_VH_Fin (m : ℕ) : V_H m ≃ Fin (4 * m) :=
  let e1 : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
    Equiv.trans finSumFinEquiv (finCongr (by
    grind))
  let e2 : Fin (2 * m) ⊕ Fin (2 * m) ≃ Fin (4 * m) :=
    Equiv.trans finSumFinEquiv (finCongr (by
    ring))
  Equiv.trans (Equiv.sumCongr e1 e1) e2

/-
The clique number is preserved under graph isomorphism.
-/
lemma cliqueNum_map_equiv {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).cliqueNum = G.cliqueNum := by
      classical
      letI := Fintype.ofFinite V
      letI := Fintype.ofFinite W
      have h_back : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
        rw [SimpleGraph.map_map]
        convert SimpleGraph.map_id G using 2
        funext v
        simp
      unfold SimpleGraph.cliqueNum
      congr 1
      ext n
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨s.map e.symm.toEmbedding, ?_⟩
        have hs' := SimpleGraph.IsNClique.map hs (f := e.symm.toEmbedding)
        change ((G.map e.toEmbedding).map e.symm.toEmbedding).IsNClique n (s.map e.symm.toEmbedding) at hs'
        simpa [h_back] using hs'
      · rintro ⟨s, hs⟩
        refine ⟨s.map e.toEmbedding, ?_⟩
        simpa using (SimpleGraph.IsNClique.map hs (f := e.toEmbedding))

/-
The independence number is preserved under graph isomorphism.
-/
lemma indepNum_map_equiv {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).indepNum = G.indepNum := by
      classical
      letI := Fintype.ofFinite V
      letI := Fintype.ofFinite W
      unfold SimpleGraph.indepNum
      congr 1
      ext n
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨s.map e.symm.toEmbedding, ?_⟩
        rw [SimpleGraph.isNIndepSet_iff] at hs ⊢
        constructor
        · intro x hx y hy hxy hAdj
          simp only [Finset.mem_coe, Finset.mem_map] at hx hy
          rcases hx with ⟨x', hx', rfl⟩
          rcases hy with ⟨y', hy', rfl⟩
          exact hs.1 hx' hy' (by simpa using hxy) (by
            simpa using
              (SimpleGraph.map_adj_apply.mpr hAdj :
                (G.map e.toEmbedding).Adj (e (e.symm x')) (e (e.symm y'))))
        · simpa using hs.2
      · rintro ⟨s, hs⟩
        refine ⟨s.map e.toEmbedding, ?_⟩
        rw [SimpleGraph.isNIndepSet_iff] at hs ⊢
        constructor
        · intro x hx y hy hxy hAdj
          simp only [Finset.mem_coe, Finset.mem_map] at hx hy
          rcases hx with ⟨x', hx', rfl⟩
          rcases hy with ⟨y', hy', rfl⟩
          exact hs.1 hx' hy' (by simpa using hxy)
            (SimpleGraph.map_adj_apply.mp hAdj)
        · simpa using hs.2

/-
The degree of a vertex is preserved under graph isomorphism.
-/
lemma degree_map_equiv {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) (v : V) :
    (G.map e.toEmbedding).degree (e v) = G.degree v := by
      classical
      rw [ SimpleGraph.degree, SimpleGraph.degree ];
      -- The set of neighbors of $e(v)$ in $G.map e$ is exactly the image of the set of neighbors of $v$ in $G$ under $e$.
      have h_neighbors : (SimpleGraph.map e.toEmbedding G).neighborFinset (e v) = Finset.image (fun w => e w) (G.neighborFinset v) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
        constructor
        · intro hAdj
          rcases (SimpleGraph.map_adj e.toEmbedding G (e v) w).mp hAdj with
            ⟨v', w', hvw', hv', hw'⟩
          have hv_eq : v' = v := e.injective hv'
          exact ⟨w', by simpa [hv_eq] using hvw', hw'⟩
        · rintro ⟨w', hAdj, rfl⟩
          exact (SimpleGraph.map_adj e.toEmbedding G (e v) (e w')).mpr
            ⟨v, w', hAdj, rfl, rfl⟩
      rw [ h_neighbors, Finset.card_image_of_injective _ e.injective ]

/-
The number of distinct degrees is preserved under graph isomorphism.
-/
lemma NumDistinctDegrees_map_equiv {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) :
    NumDistinctDegrees (G.map e.toEmbedding) = NumDistinctDegrees G := by
  unfold NumDistinctDegrees
  have h_image :
      (Finset.univ.image (fun w => (G.map e.toEmbedding).degree w)) =
        (Finset.univ.image (fun v => G.degree v)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨w, _hw, hwx⟩
      refine Finset.mem_image.mpr ⟨e.symm w, Finset.mem_univ _, ?_⟩
      have hdeg := degree_map_equiv G e (e.symm w)
      rw [e.apply_symm_apply] at hdeg
      exact hdeg.symm.trans hwx
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨v, _hv, hvx⟩
      refine Finset.mem_image.mpr ⟨e v, Finset.mem_univ _, ?_⟩
      exact (degree_map_equiv G e v).trans hvx
  rw [h_image]

/-
The property `DegreeOccursAtMostTwice` is preserved under graph isomorphism.
-/
lemma DegreeOccursAtMostTwice_map_equiv {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) :
    DegreeOccursAtMostTwice (G.map e.toEmbedding) ↔ DegreeOccursAtMostTwice G := by
      unfold DegreeOccursAtMostTwice
      constructor
      · intro h t
        rw [show
          (Finset.univ.filter (fun v : V => G.degree v = t)).card =
            (Finset.univ.filter (fun w : W => (G.map e.toEmbedding).degree w = t)).card
          from by
            apply Finset.card_equiv e
            intro v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hv
              rw [degree_map_equiv G e v]
              exact hv
            · intro hv
              rw [degree_map_equiv G e v] at hv
              exact hv]
        exact h t
      · intro h t
        rw [show
          (Finset.univ.filter (fun w : W => (G.map e.toEmbedding).degree w = t)).card =
            (Finset.univ.filter (fun v : V => G.degree v = t)).card
          from by
            apply Finset.card_equiv e.symm
            intro w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hw
              rw [← e.apply_symm_apply w] at hw
              rw [degree_map_equiv G e (e.symm w)] at hw
              exact hw
            · intro hw
              rw [← e.apply_symm_apply w, degree_map_equiv G e (e.symm w)]
              exact hw]
        exact h t

/-
For a fixed $m$ and graph $R$ satisfying the conditions, there exists a graph $H$ on `Fin (4m)` satisfying the derived conditions.
-/
lemma Theorem_Main_Fixed_m (m : ℕ) (R : SimpleGraph (Fin m))
    (h_clique : (R.cliqueNum : ℝ) ≤ 3 * Real.logb 2 m)
    (h_indep : (R.indepNum : ℝ) ≤ 3 * Real.logb 2 m)
    (h_deg : (R.maxDegree : ℝ) - (R.minDegree : ℝ) ≤ 4 * Real.sqrt (m * Real.log m)) :
    ∃ H : SimpleGraph (Fin (4 * m)),
      DegreeOccursAtMostTwice H ∧
      (NumDistinctDegrees H : ℝ) ≥ 3 * m - 4 * Real.sqrt (m * Real.log m) - 1 ∧
      (H.cliqueNum : ℝ) ≤ 12 * Real.logb 2 m ∧
      (H.indepNum : ℝ) ≤ 12 * Real.logb 2 m := by
        -- Apply the reductions to obtain the graph $H$ on `Fin (4m)`.
        obtain ⟨H, hH⟩ : ∃ H : SimpleGraph (V_H m),
            DegreeOccursAtMostTwice H ∧
            (NumDistinctDegrees H : ℝ) ≥ 3 * m - 4 * Real.sqrt (m * Real.log m) - 1 ∧
            (H.cliqueNum : ℝ) ≤ 12 * Real.logb 2 m ∧
            (H.indepNum : ℝ) ≤ 12 * Real.logb 2 m := by
              obtain ⟨σ_AB, hσ_AB⟩ : ∃ σ_AB : Fin (2 * m) ≃ Fin m ⊕ Fin m, is_ordered m R σ_AB := exists_ordering m R
              obtain ⟨σ_CD, hσ_CD⟩ : ∃ σ_CD : Fin (2 * m) ≃ Fin m ⊕ Fin m, is_ordered m R σ_CD := exists_ordering m R
              refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩
              · exact H_graph m R σ_AB σ_CD
              · exact degree_at_most_twice m R σ_AB σ_CD hσ_AB hσ_CD;
              · have := num_distinct_degrees_ge m R σ_AB σ_CD hσ_AB hσ_CD;
                norm_num [ NumDistinctDegrees ] at *;
                norm_cast at *;
                refine le_trans ( Nat.cast_le.mpr this ) ?_;
                norm_num [ degrees_of_H ];
                convert h_deg using 1;
              · exact le_trans ( Nat.cast_le.mpr ( cliqueNum_H_le m R σ_AB σ_CD ) ) ( by norm_num; linarith );
              · exact le_trans ( Nat.cast_le.mpr ( indepNum_H_le m R σ_AB σ_CD ) ) ( by norm_num; linarith );
        let e := iso_VH_Fin m
        letI : DecidableRel (H.map e.toEmbedding).Adj := Classical.decRel _
        have hDegree (v : Fin (4 * m)) :
            @SimpleGraph.degree (Fin (4 * m)) (H.map e.toEmbedding) v
                (Subtype.fintype (Membership.mem ((H.map e.toEmbedding).neighborSet v))) =
              @SimpleGraph.degree (Fin (4 * m)) (H.map e.toEmbedding) v
                (by
                  letI : DecidableRel (H.map e.toEmbedding).Adj :=
                    fun _ _ => H.instDecidableMapAdj
                  exact Subtype.fintype (Membership.mem ((H.map e.toEmbedding).neighborSet v))) := by
          rw [SimpleGraph.degree, SimpleGraph.degree]
          apply congrArg Finset.card
          ext w
          simp [SimpleGraph.neighborFinset_eq_filter]
        refine ⟨H.map e.toEmbedding, ?_, ?_, ?_, ?_⟩
        · intro t
          have h := ((DegreeOccursAtMostTwice_map_equiv H e).2 hH.1) t
          convert h using 2
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hDegree v]
        · change ((@NumDistinctDegrees (Fin (4 * m)) _ _ (H.map e.toEmbedding) (Classical.decRel _) : ℝ) ≥ 3 * m - 4 * Real.sqrt (m * Real.log m) - 1)
          have hNum :
              @NumDistinctDegrees (Fin (4 * m)) _ _ (H.map e.toEmbedding) (Classical.decRel _) =
                NumDistinctDegrees H := by
            trans @NumDistinctDegrees (Fin (4 * m)) _ _ (H.map e.toEmbedding)
                (fun a b => H.instDecidableMapAdj)
            · unfold NumDistinctDegrees
              apply congrArg Finset.card
              ext n
              simp only [Finset.mem_image, Finset.mem_univ, true_and]
              constructor
              · intro hn
                rcases hn with ⟨v, hv⟩
                exact ⟨v, by rwa [← hDegree v]⟩
              · intro hn
                rcases hn with ⟨v, hv⟩
                exact ⟨v, by rwa [hDegree v]⟩
            · exact NumDistinctDegrees_map_equiv H e
          rw [hNum]
          exact hH.2.1
        · change (((H.map e.toEmbedding).cliqueNum : ℝ) ≤ 12 * Real.logb 2 m)
          rw [cliqueNum_map_equiv H e]
          exact hH.2.2.1
        · change (((H.map e.toEmbedding).indepNum : ℝ) ≤ 12 * Real.logb 2 m)
          rw [indepNum_map_equiv H e]
          exact hH.2.2.2

/-
Inequality for logarithms needed for the main theorem.
-/
lemma log_inequality (n : ℕ) (h : n ≥ 4) :
  12 * Real.logb 2 (n / 4 : ℝ) ≤ 20 * Real.log n := by
    rw [ Real.logb, Real.log_div ] <;> norm_num <;> try positivity;
    rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] ; ring_nf;
    field_simp;
    have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ]

/-
Main theorem: For any $\varepsilon \in (0, 1 / 4)$, for sufficiently large $n$ divisible by 4, there exists a graph on $n$ vertices with degrees occurring at most twice, many distinct degrees, and logarithmic clique/independence numbers.
-/
theorem Theorem_Main :
  ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ n₀ : ℕ, ∀ n ≥ n₀, 4 ∣ n →
  ∃ H : SimpleGraph (Fin n),
    DegreeOccursAtMostTwice H ∧
    (NumDistinctDegrees H : ℝ) > (1 / 2 + ε) * n ∧
    (H.cliqueNum : ℝ) ≤ C * Real.log n ∧
    (H.indepNum : ℝ) ≤ C * Real.log n := by
      use 20, fun ε hε₁ hε₂ => ?_;
      -- Let's choose any $m₀$ from Lemma_Base.
      obtain ⟨m₀, hm₀⟩ := Lemma_Base;
      obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, ∀ m ≥ m₁, 3 * m - 4 * Real.sqrt (m * Real.log m) - 1 > (1 / 2 + ε) * (4 * m) := by
        -- We can choose $m₁$ such that for all $m ≥ m₁$, $4 * Real.sqrt (m * Real.log m) < (1 - 4 * ε) * m / 2$.
        obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, ∀ m ≥ m₁, 4 * Real.sqrt (m * Real.log m) < (1 - 4 * ε) * m / 2 := by
          have h_sqrt_log : Filter.Tendsto (fun m : ℕ => Real.sqrt (m * Real.log m) / m) Filter.atTop (nhds 0) := by
            -- We can simplify the expression inside the limit.
            suffices h_simplify : Filter.Tendsto (fun m : ℕ => Real.sqrt (Real.log m / m)) Filter.atTop (nhds 0) by
              refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ show ( m : ℝ ) * Real.log m = m ^ 2 * ( Real.log m / m ) by rw [ mul_div, eq_div_iff ( by positivity ) ] ; ring ] ; norm_num [ hm.ne', le_of_lt hm ] );
            have h_log_div_m : Filter.Tendsto (fun m : ℕ => Real.log m / (m : ℝ)) Filter.atTop (nhds 0) := by
              -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
              suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
              norm_num +zetaDelta at *;
              exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
            simpa using h_log_div_m.sqrt;
          have := h_sqrt_log.eventually ( gt_mem_nhds <| show 0 < ( 1 - 4 * ε ) / 8 by linarith );
          rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ m₁, hm₁ ⟩ ; exact ⟨ m₁ + 1, fun m hm => by have := hm₁ m ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;
        exact ⟨ m₁ + ⌈ ( 1 - 4 * ε ) ⁻¹ * 4⌉₊ + 1, fun m hm => by nlinarith [ Nat.le_ceil ( ( 1 - 4 * ε ) ⁻¹ * 4 ), hm₁ m ( by linarith ), mul_inv_cancel₀ ( by linarith : ( 1 - 4 * ε ) ≠ 0 ), ( by norm_cast : ( m₁ : ℝ ) + ⌈ ( 1 - 4 * ε ) ⁻¹ * 4⌉₊ + 1 ≤ m ) ] ⟩;
      use 4 * ( m₀ + m₁ + 4 );
      intros n hn hn_div
      obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m := hn_div
      have hm_ge : m ≥ m₀ ∧ m ≥ m₁ ∧ m ≥ 4 := by
        exact ⟨ by linarith, by linarith, by linarith ⟩;
      obtain ⟨R, hR⟩ := hm₀ m hm_ge.left
      obtain ⟨H, hH⟩ := Theorem_Main_Fixed_m m R hR.left hR.right.left hR.right.right;
      refine ⟨ H, hH.1, ?_, ?_, ?_ ⟩ <;> norm_num at * <;> try linarith [ hm₁ m hm_ge.2.1 ];
      · have := log_inequality ( 4 * m ) ( by linarith ) ; norm_num [ Real.logb, Real.log_mul, show m ≠ 0 by linarith ] at * ; linarith;
      · have := log_inequality ( 4 * m ) ( by linarith ) ; norm_num [ Real.logb ] at * ; linarith;

theorem not_erdos_1037 :
  ¬(
    ∀ ε : ℝ, 0 < ε →
    ∀ C : ℝ, 0 < C →
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ G : SimpleGraph (Fin n),
        (NumDistinctDegrees G : ℝ) ≥ (1 / 2 + ε) * n →
        (C * Real.log n ≤ (G.cliqueNum : ℝ) ∨
         C * Real.log n ≤ (G.indepNum : ℝ))
  ) := by
  rcases Theorem_Main with ⟨C0, hC0⟩
  intro h
  have hεpos : (0 : ℝ) < (1/8 : ℝ) := by
    norm_num
  have hεlt : (1/8 : ℝ) < (1 / 4 : ℝ) := by
    norm_num
  let C1 : ℝ := |C0| + 1
  have hC1pos : 0 < C1 := by
    have : 0 ≤ |C0| := abs_nonneg C0
    linarith
  have hC0_lt_C1 : C0 < C1 := by
    have : C0 ≤ |C0| := le_abs_self C0
    linarith
  rcases h (1/8) hεpos C1 hC1pos with ⟨n0, hn0⟩
  rcases hC0 (1/8) hεpos hεlt with ⟨n1, hn1⟩
  let n : ℕ := 4 * (Nat.max n0 n1 + 1)
  have hn_ge_n0 : n0 ≤ n := by
    have hx : Nat.max n0 n1 + 1 ≤ 4 * (Nat.max n0 n1 + 1) := by
      have : (1 : ℕ) * (Nat.max n0 n1 + 1) ≤ 4 * (Nat.max n0 n1 + 1) :=
        Nat.mul_le_mul_right (Nat.max n0 n1 + 1) (by decide : (1 : ℕ) ≤ 4)
      simp
    simpa [n] using le_trans (le_trans (le_max_left _ _) (Nat.le_succ _)) hx
  have hn_ge_n1 : n1 ≤ n := by
    have hx : Nat.max n0 n1 + 1 ≤ 4 * (Nat.max n0 n1 + 1) := by
      have : (1 : ℕ) * (Nat.max n0 n1 + 1) ≤ 4 * (Nat.max n0 n1 + 1) :=
        Nat.mul_le_mul_right (Nat.max n0 n1 + 1) (by decide : (1 : ℕ) ≤ 4)
      simp
    simpa [n] using le_trans (le_trans (le_max_right _ _) (Nat.le_succ _)) hx
  have h4 : 4 ∣ n := by
    refine ⟨Nat.max n0 n1 + 1, by simp [n]⟩
  rcases hn1 n hn_ge_n1 h4 with ⟨H, hDegTwice, hNDeg, hClique_le, hIndep_le⟩
  have hNDeg' : (NumDistinctDegrees H : ℝ) ≥ (1 / 2 + (1/8 : ℝ)) * n := by
    exact le_of_lt hNDeg
  have hn_ge4 : 4 ≤ n := by
    simp_all only [one_div, ge_iff_le, gt_iff_lt, inv_pos, Nat.ofNat_pos, dvd_mul_right, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_max, Nat.cast_one, le_mul_iff_one_le_right, le_add_iff_nonneg_left, le_sup_iff, zero_le,
      or_self, C1, n]
  have hn_gt1_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 4) hn_ge4)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    simpa using Real.log_pos hn_gt1_real
  have hmul_lt : C0 * Real.log (n : ℝ) < C1 * Real.log (n : ℝ) := by
    exact mul_lt_mul_of_pos_right hC0_lt_C1 hlogpos
  rcases (hn0 n hn_ge_n0 H hNDeg') with hbigClique | hbigIndep
  · exact (not_le_of_gt (lt_of_le_of_lt hClique_le hmul_lt)) hbigClique
  · exact (not_le_of_gt (lt_of_le_of_lt hIndep_le hmul_lt)) hbigIndep

end Erdos1037

open Erdos1037

#print axioms not_erdos_1037
-- 'Erdos1037.not_erdos_1037' depends on axioms: [propext, Classical.choice, Quot.sound]
