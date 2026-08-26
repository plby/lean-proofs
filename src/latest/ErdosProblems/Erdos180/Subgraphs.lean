/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Geometry

set_option linter.mathlibStandardSet false

namespace Erdos180

section SubdivisionLineExtraction

open SimpleGraph

variable (K : Type*) [Field K]

lemma subdivisionLine_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L C : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L)
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ p : SymplecticPoint K,
      copy (.inr (base, center)) = .inl p ∧
        p.1 ≤ L.1 ∧ p.1 ≤ C.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨p, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K p C).mp hcenteradj.symm⟩

lemma subdivisionLine_center_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ C : SymplecticLine K,
      copy (.inl (.inr center)) = .inr C := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨C, hC, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj.symm
  exact ⟨C, hC⟩

lemma subdivisionLine_base_of_line_center
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {C : SymplecticLine K}
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ L : SymplecticLine K,
      copy (.inl (.inl base)) = .inr L := by
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter] at hcenteradj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hpair] at hbaseadj
  obtain ⟨L, hL, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj.symm
  exact ⟨L, hL⟩

lemma subdivisionLine_base_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ M : SymplecticLine K,
      copy (.inl (.inl otherBase)) = .inr M := by
  obtain ⟨C, hC⟩ := subdivisionLine_center_of_line_base K
    copy (center := center) hbase
  exact subdivisionLine_base_of_line_center K
    copy (base := otherBase) hC

lemma subdivisionLine_centers_injective
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply copy.injective
  change copy (.inl (.inr i)) = copy (.inl (.inr j))
  rw [hcenter i, hcenter j, hij]

lemma subdivisionLine_bases_disjoint
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (L : Fin 3 → SymplecticLine K)
    (C : Fin k → SymplecticLine K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inr (L base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    Disjoint (L i).1 (L j).1 := by
  apply Submodule.disjoint_def.mpr
  intro x hxi hxj
  by_contra hx
  let p : SymplecticPoint K :=
    ⟨K ∙ x, finrank_span_singleton hx⟩
  have hpLi : p.1 ≤ (L i).1 :=
    (Submodule.span_le).mpr (by simpa using hxi)
  have hpLj : p.1 ≤ (L j).1 :=
    (Submodule.span_le).mpr (by simpa using hxj)
  obtain ⟨pi, hpairi, hpiLi, hpiC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase i) (hcenter center)
  obtain ⟨pj, hpairj, hpjLj, hpjC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase j) (hcenter center)
  have hpipj : pi ≠ pj := by
    intro heq
    apply hij
    have hsource :
        (Sum.inr (i, center) : SubdivisionVertex k) =
          .inr (j, center) := by
      apply copy.injective
      change copy (.inr (i, center)) =
        copy (.inr (j, center))
      rw [hpairi, hpairj, heq]
    exact congrArg Prod.fst (Sum.inr.inj hsource)
  have hcenterNeBase (base : Fin 3) : C center ≠ L base := by
    intro heq
    have hsource :
        (Sum.inl (Sum.inr center) : SubdivisionVertex k) =
          .inl (.inl base) := by
      apply copy.injective
      change copy (.inl (.inr center)) =
        copy (.inl (.inl base))
      rw [hcenter center, hbase base, heq]
    cases Sum.inl.inj hsource
  have hpjp : pj ≠ p := by
    intro heq
    have hpjLi : pj.1 ≤ (L i).1 := by
      simpa only [heq] using hpLi
    have hline : C center = L i :=
      symplecticLine_eq_of_points K hpipj
        hpiC hpjC hpiLi hpjLi
    exact hcenterNeBase i hline
  have hline : C center = L j :=
    symplectic_triangle_lines_eq K hpipj hpjp
      hpiC hpjC hpiLi hpLi hpjLj hpLj
  exact hcenterNeBase j hline

end SubdivisionLineExtraction

section Padding

open SimpleGraph

def GraphHasNoIsolated {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ u : V, ∃ v : V, graph.Adj u v

lemma free_map_of_no_isolated
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by
  classical
  rintro ⟨copy⟩
  have hpreimage (u : U) :
      ∃ v : V, embedding v = copy u := by
    obtain ⟨w, huw⟩ := hneighbors u
    have hadj := copy.toHom.map_rel huw
    change (host.map embedding).Adj (copy u) (copy w) at hadj
    obtain ⟨v, _, _, hv, _⟩ :=
      (SimpleGraph.map_adj embedding host _ _).mp hadj
    exact ⟨v, hv⟩
  let lift : U → V := fun u => Classical.choose (hpreimage u)
  have hlift (u : U) : embedding (lift u) = copy u :=
    Classical.choose_spec (hpreimage u)
  apply hfree
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hadj := copy.toHom.map_rel huv
    change (host.map embedding).Adj (copy u) (copy v) at hadj
    rw [← hlift u, ← hlift v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    change lift u = lift v at huv
    apply copy.injective
    change copy u = copy v
    rw [← hlift u, ← hlift v]
    exact congrArg embedding huv

lemma extremalNumber_monotone_of_no_isolated
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.extremalNumber m forbidden ≤
      SimpleGraph.extremalNumber n forbidden := by
  classical
  have hbound :
      SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
        SimpleGraph.extremalNumber n forbidden := by
    apply (SimpleGraph.extremalNumber_le_iff
      (V := Fin m) forbidden
      (SimpleGraph.extremalNumber n forbidden)).mpr
    intro host _ hfree
    let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
    have hpadded : forbidden.Free (host.map embedding) :=
      free_map_of_no_isolated forbidden hneighbors embedding hfree
    calc
      host.edgeFinset.card =
          (host.map embedding).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using
          (SimpleGraph.card_edgeFinset_map embedding host).symm
      _ ≤ SimpleGraph.extremalNumber n forbidden := by
        simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
  simpa using hbound

lemma cycleGraph_no_isolated (k : ℕ) :
    ∀ u : Fin (k + 2),
      ∃ v : Fin (k + 2),
        (SimpleGraph.cycleGraph (k + 2)).Adj u v := by
  intro u
  refine ⟨u + 1, ?_⟩
  change u + 1 ∈
    (SimpleGraph.cycleGraph (k + 2)).neighborSet u
  rw [SimpleGraph.cycleGraph_neighborSet]
  simp

lemma quotientGraph_no_isolated
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v)
    (f : V → V) (hf : ColorRespecting color f) :
    ∀ u : Set.range f,
      ∃ v : Set.range f, (quotientGraph graph f).Adj u v := by
  rintro ⟨_, ⟨u, rfl⟩⟩
  obtain ⟨v, huv⟩ := hneighbors u
  refine ⟨⟨f v, v, rfl⟩, ?_⟩
  exact (colorRespectingQuotientProjectionHom
    graph color hproper f hf).map_rel huv

lemma map_equiv_no_isolated
    {V W : Type*} (graph : SimpleGraph V) (e : V ≃ W)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    ∀ u : W, ∃ v : W, (graph.map e.toEmbedding).Adj u v := by
  intro u
  obtain ⟨v, huv⟩ := hneighbors (e.symm u)
  refine ⟨e v, ?_⟩
  have h :=
    (SimpleGraph.map_adj_apply
      (G := graph) (f := e.toEmbedding)
      (a := e.symm u) (b := v)).mpr huv
  simpa using h

lemma encodeFiniteGraph_no_isolated
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    GraphHasNoIsolated (encodeFiniteGraph graph).graph := by
  classical
  exact map_equiv_no_isolated graph (Fintype.equivFin V) hneighbors

lemma jTemplate_no_isolated :
    GraphHasNoIsolated jTemplate := by
  intro u
  rcases u with (base | ⟨copy, center⟩) |
    (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inl (0, (1, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
    · refine ⟨.inr (.inl (0, (2, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
  · refine ⟨.inr (.inl (copy, (0, center))), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl (jBase copy base)), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl 0), ?_⟩
    cases lastVertex
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]

lemma kTemplate_no_isolated :
    GraphHasNoIsolated kTemplate := by
  intro u
  rcases u with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · refine ⟨(copy, .inr (base, 0)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inr (0, center)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inl (.inl base)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]

lemma encodedJQuotient_no_isolated
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph jTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph jTemplate f)
    (quotientGraph_no_isolated jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h)
      jTemplate_no_isolated f hf.1)

lemma encodedKQuotient_no_isolated
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph kTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph kTemplate f)
    (quotientGraph_no_isolated kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h)
      kTemplate_no_isolated f hf.1)

theorem proposedFamily_member_no_isolated
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    GraphHasNoIsolated forbidden.graph :=
  proposedFamily_induction (P := fun graph => GraphHasNoIsolated graph.graph)
    (cycleGraph_no_isolated 2) (cycleGraph_no_isolated 4)
    (fun _ hf => encodedJQuotient_no_isolated hf)
    (fun _ hf => encodedKQuotient_no_isolated hf)
    forbidden hforbidden

lemma nat_le_pow_of_two_le
    {t : ℕ} (ht : 2 ≤ t) (j : ℕ) : j ≤ t ^ j := by
  exact (Nat.lt_pow_self (show 1 < t by omega)).le

theorem quadrangleVertexCount_parameter_lt (q : ℕ) :
    q < quadrangleVertexCount q := by
  unfold quadrangleVertexCount
  nlinarith [sq_nonneg q]

theorem quadrangle_prime_power_bracketing
    {t n : ℕ} (ht : 2 ≤ t)
    (hn : quadrangleVertexCount t ≤ n) :
    ∃ j : ℕ, 0 < j ∧
      quadrangleVertexCount (t ^ j) ≤ n ∧
      n < t ^ 3 * quadrangleVertexCount (t ^ j) := by
  let P : ℕ → Prop := fun j =>
    quadrangleVertexCount (t ^ j) ≤ n
  let j := Nat.findGreatest P (n + 1)
  have hone : P 1 := by
    simpa [P] using hn
  have hjfit : P j :=
    Nat.findGreatest_spec (P := P)
      (show 1 ≤ n + 1 by omega) hone
  have hjpositive : 0 < j := by
    have hle : 1 ≤ j := Nat.le_findGreatest
      (show 1 ≤ n + 1 by omega) hone
    omega
  have hjn : j ≤ n := by
    have hpow := nat_le_pow_of_two_le ht j
    have hvertex := quadrangleVertexCount_parameter_lt (t ^ j)
    change quadrangleVertexCount (t ^ j) ≤ n at hjfit
    omega
  have hnext : ¬ P (j + 1) :=
    Nat.findGreatest_is_greatest (P := P)
      (show j < j + 1 by omega)
      (show j + 1 ≤ n + 1 by omega)
  have hnnext :
      n < quadrangleVertexCount (t * t ^ j) := by
    have h := Nat.lt_of_not_ge hnext
    change n < quadrangleVertexCount (t ^ (j + 1)) at h
    simpa [pow_succ, Nat.mul_comm] using h
  have hgap := quadrangleVertexCount_mul_le (t ^ j) t
    (show 1 ≤ t by omega)
  exact ⟨j, hjpositive, hjfit, lt_of_lt_of_le hnnext hgap⟩

theorem quadrangle_extremal_lower_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hfree : forbidden.Free (symplecticQuadrangle K)) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber
        (quadrangleVertexCount (Nat.card K)) forbidden := by
  classical
  let : Fintype (QuadrangleVertex K) := Fintype.ofFinite _
  have hvertex : Fintype.card (QuadrangleVertex K) =
      quadrangleVertexCount (Nat.card K) := by
    rw [← Nat.card_eq_fintype_card, symplecticQuadrangle_vertex_card]
    rfl
  calc
    quadrangleEdgeCount (Nat.card K) =
        (symplecticQuadrangle K).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        symplecticQuadrangle_edge_card]
      rfl
    _ ≤ SimpleGraph.extremalNumber
          (Fintype.card (QuadrangleVertex K)) forbidden :=
      SimpleGraph.card_edgeFinset_le_extremalNumber hfree
    _ = SimpleGraph.extremalNumber
          (quadrangleVertexCount (Nat.card K)) forbidden := by
      rw [hvertex]

theorem quadrangle_extremal_lower_padded_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (hfree : forbidden.Free (symplecticQuadrangle K))
    {n : ℕ} (hn : quadrangleVertexCount (Nat.card K) ≤ n) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber n forbidden := by
  exact (quadrangle_extremal_lower_of_free K forbidden hfree).trans
    (extremalNumber_monotone_of_no_isolated forbidden hneighbors hn)

theorem quadrangle_manuscript_scaled_density_of_gap
    (q n : ℕ)
    (hgap : n ≤ 27 * quadrangleVertexCount q) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  have hreal :
      (n : ℝ) ≤ (27 : ℝ) * (quadrangleVertexCount q : ℝ) := by
    exact_mod_cast hgap
  calc
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        (n : ℝ) ^ ((4 : ℝ) / 3) ≤
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        ((27 : ℝ) * (quadrangleVertexCount q : ℝ)) ^
          ((4 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hreal (by positivity))
        (by positivity)
    _ = (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hcancel :
          (27 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ ((4 : ℝ) / 3) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 27)]
        norm_num
      calc
        ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
            ((27 : ℝ) ^ ((4 : ℝ) / 3) *
              (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) =
          (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            ((27 : ℝ) ^ (-((4 : ℝ) / 3)) *
              (27 : ℝ) ^ ((4 : ℝ) / 3)) *
                (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
          ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ (quadrangleEdgeCount q : ℝ) := quadrangle_rpow_density q

theorem quadrangle_uniform_lower_of_prime_power_avoidance
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.Free (symplecticQuadrangle (GaloisField t j)))
    {n : ℕ} (hn : quadrangleVertexCount t ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
  obtain ⟨j, hj, hfit, hgap⟩ :=
    quadrangle_prime_power_bracketing ht hn
  let K := GaloisField t j
  have hcard : Nat.card K = t ^ j :=
    GaloisField.card t j (Nat.ne_of_gt hj)
  have hfitK : quadrangleVertexCount (Nat.card K) ≤ n := by
    simpa [hcard] using hfit
  have havoid : forbidden.Free (symplecticQuadrangle K) :=
    hfree j hj
  have hedge := quadrangle_extremal_lower_padded_of_free K
    forbidden hneighbors havoid hfitK
  have hedge' :
      (quadrangleEdgeCount (t ^ j) : ℝ) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
    exact_mod_cast (show quadrangleEdgeCount (t ^ j) ≤
      SimpleGraph.extremalNumber n forbidden by
        simpa [hcard] using hedge)
  have hfactor :
      t ^ 3 * quadrangleVertexCount (t ^ j) ≤
        27 * quadrangleVertexCount (t ^ j) :=
    Nat.mul_le_mul_right (quadrangleVertexCount (t ^ j)) htgap
  have hgap27 : n ≤ 27 * quadrangleVertexCount (t ^ j) :=
    (Nat.le_of_lt hgap).trans hfactor
  exact (quadrangle_manuscript_scaled_density_of_gap
    (t ^ j) n hgap27).trans hedge'

theorem four_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 4)
    (by simpa using cycleGraph_no_isolated 2)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_four_cycle_free _) hn

theorem six_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 6)
    (by simpa using cycleGraph_no_isolated 4)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_six_cycle_free _) hn

end Padding

section LocalGeometry

open SimpleGraph

theorem common_neighbor_unique_of_four_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  by_contra hxy
  apply hfree
  let f : Fin 4 → V := ![u, x, v, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph]
    all_goals
      first
      | exact hux.symm
      | exact hvx.symm
      | exact huy.symm
      | exact hvy.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hux.ne, hux.symm.ne, hvx.ne, hvx.symm.ne,
        huy.ne, huy.symm.ne, hvy.ne, hvy.symm.ne]

def CommonNeighborRelated {V : Type*} (G : SimpleGraph V)
    (u v : V) : Prop :=
  u ≠ v ∧ ∃ w : V, G.Adj u w ∧ G.Adj v w

lemma commonNeighborRelated_symm
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : CommonNeighborRelated G u v) :
    CommonNeighborRelated G v u := by
  obtain ⟨hne, w, huw, hvw⟩ := h
  exact ⟨hne.symm, w, hvw, huw⟩

lemma bipartite_coloring_eq_of_common_neighbor
    {V : Type*} {G : SimpleGraph V}
    (color : G.Coloring (Fin 2)) {u v w : V}
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    color u = color v := by
  have hu := color.valid huw
  have hv := color.valid hvw
  apply Fin.ext
  omega

theorem common_neighbors_triangle_eq_of_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v w a b c : V}
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hwb : G.Adj w b)
    (hwc : G.Adj w c) (huc : G.Adj u c) :
    a = b ∧ b = c := by
  by_cases hab : a = b
  · subst b
    refine ⟨rfl, ?_⟩
    exact common_neighbor_unique_of_four_cycle_free hfour huw
      hua hwb huc hwc
  by_cases hbc : b = c
  · subst c
    have hac : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour huv
        hua hva huc hvb
    exact (hab hac).elim
  by_cases hac : a = c
  · subst c
    have hab' : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour hvw
        hva hwc hvb hwb
    exact (hab hab').elim
  obtain ⟨color⟩ := hbip
  have hcolor_uv : color u = color v :=
    bipartite_coloring_eq_of_common_neighbor color hua hva
  have hcolor_vw : color v = color w :=
    bipartite_coloring_eq_of_common_neighbor color hvb hwb
  have hub : u ≠ b := by
    intro h
    subst b
    exact color.valid hvb hcolor_uv.symm
  have hvc : v ≠ c := by
    intro h
    subst c
    exact color.valid huc hcolor_uv
  have hwa : w ≠ a := by
    intro h
    subst a
    exact color.valid hva hcolor_vw
  exfalso
  apply hsix
  let f : Fin 6 → V := ![u, a, v, b, w, c]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph]
    all_goals
      first
      | exact hua
      | exact hua.symm
      | exact hva
      | exact hva.symm
      | exact hvb
      | exact hvb.symm
      | exact hwb
      | exact hwb.symm
      | exact hwc
      | exact hwc.symm
      | exact huc
      | exact huc.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, huv, huv.symm, hvw, hvw.symm, huw, huw.symm,
        hab, Ne.symm hab, hbc, Ne.symm hbc, hac, Ne.symm hac,
        hua.ne, hua.symm.ne, hva.ne, hva.symm.ne,
        hvb.ne, hvb.symm.ne, hwb.ne, hwb.symm.ne,
        hwc.ne, hwc.symm.ne, huc.ne, huc.symm.ne,
        hub, hub.symm, hvc, hvc.symm, hwa, hwa.symm] at hij ⊢

theorem common_second_neighbors_pairwise_unrelated
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (hxu : CommonNeighborRelated G x u)
    (hxv : CommonNeighborRelated G x v)
    (hyu : CommonNeighborRelated G y u)
    (hyv : CommonNeighborRelated G y v) :
    ¬ CommonNeighborRelated G x y := by
  rintro ⟨hxy, b, hxb, hyb⟩
  obtain ⟨hxu_ne, a, hxa, hua⟩ := hxu
  obtain ⟨hxv_ne, d, hxd, hvd⟩ := hxv
  obtain ⟨hyu_ne, c, hyc, huc⟩ := hyu
  obtain ⟨hyv_ne, e, hye, hve⟩ := hyv
  have habc : a = c ∧ c = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxu_ne (Ne.symm hyu_ne) hxy
      hxa hua huc hyc hyb hxb
  have hdeb : d = e ∧ e = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxv_ne (Ne.symm hyv_ne) hxy
      hxd hvd hve hye hyb hxb
  apply hunrelated
  refine ⟨huv, b, ?_, ?_⟩
  · rwa [habc.1.trans habc.2] at hua
  · rwa [hdeb.1.trans hdeb.2] at hvd

section FourPathCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NonbacktrackingNeighbor (G : SimpleGraph V)
    (previous current : V) :=
  {next : V // G.Adj current next ∧ next ≠ previous}

lemma card_nonbacktrackingNeighbor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {previous current : V} (hedge : G.Adj current previous) :
    Fintype.card (NonbacktrackingNeighbor G previous current) =
      G.degree current - 1 := by
  classical
  calc
    Fintype.card (NonbacktrackingNeighbor G previous current) =
        ((G.neighborFinset current).erase previous).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext next
      simp [and_comm]
    _ = G.degree current - 1 := by
      rw [Finset.card_erase_of_mem]
      · rfl
      · simpa using hedge

abbrev NonbacktrackingFourPath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
        NonbacktrackingNeighbor G (w : V) (b : V)

lemma fintype_card_sigma_lower
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    {baseLower fiberLower : ℕ}
    (hbase : baseLower ≤ Fintype.card α)
    (hfiber : ∀ a : α, fiberLower ≤ Fintype.card (β a)) :
    baseLower * fiberLower ≤ Fintype.card (Sigma β) := by
  classical
  rw [Fintype.card_sigma]
  calc
    baseLower * fiberLower ≤ Fintype.card α * fiberLower :=
      Nat.mul_le_mul_right fiberLower hbase
    _ = ∑ _a : α, fiberLower := by simp
    _ ≤ ∑ a : α, Fintype.card (β a) :=
      Finset.sum_le_sum fun a _ => hfiber a

lemma card_nonbacktrackingFourPath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (NonbacktrackingFourPath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hthird (a : G.neighborSet u)
      (w : NonbacktrackingNeighbor G u (a : V)) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
            NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep w.property.1.symm
    · intro b
      exact hstep b.property.1.symm
  have hsecond (a : G.neighborSet u) :
      (d - 1) * ((d - 1) * (d - 1)) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
              NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · exact hthird a
  have hfirst : d ≤ Fintype.card (G.neighborSet u) := by
    simpa [G.card_neighborSet_eq_degree] using hdegree u
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
          NonbacktrackingNeighbor G (w : V) (b : V))
    hfirst hsecond
  simpa [pow_succ, mul_assoc] using hcount

def nonbacktrackingFourPathPair
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingFourPath G u) : V × V :=
  (path.2.2.2.1, path.2.1.1)

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_ne
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    u ≠ (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change u ≠ (v : V)
  intro huv
  have hub : G.Adj u (b : V) := by
    simpa only [huv] using v.property.1.symm
  have hab : (a : V) = (b : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm a.property w.property.1.symm
      hub b.property.1
  exact b.property.2 hab.symm

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    ¬ CommonNeighborRelated G u
      (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change ¬ CommonNeighborRelated G u (v : V)
  rintro ⟨_, c, huc, hvc⟩
  have huv : u ≠ (v : V) :=
    nonbacktrackingFourPath_endpoint_ne G hfour
      ⟨a, w, b, v⟩
  have hab := common_neighbors_triangle_eq_of_cycle_free
    hbip hfour hsix w.property.2.symm
    v.property.2.symm huv
    a.property w.property.1.symm
    b.property.1 v.property.1.symm hvc huc
  exact b.property.2 hab.1.symm

abbrev FourPathEndpointWitness (G : SimpleGraph V) (u : V) :=
  {pair : V × V //
    u ≠ pair.1 ∧
      ¬ CommonNeighborRelated G u pair.1 ∧
      CommonNeighborRelated G u pair.2 ∧
      CommonNeighborRelated G pair.1 pair.2}

noncomputable instance fourPathEndpointWitnessFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (FourPathEndpointWitness G u) :=
  Fintype.ofFinite _

def nonbacktrackingFourPathWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    FourPathEndpointWitness G u := by
  refine ⟨nonbacktrackingFourPathPair G path,
    nonbacktrackingFourPath_endpoint_ne G hfour path,
    nonbacktrackingFourPath_endpoint_unrelated G hbip hfour hsix path,
    ?_, ?_⟩
  · refine ⟨path.2.1.property.2.symm, path.1,
      path.1.property, path.2.1.property.1.symm⟩
  · refine ⟨path.2.2.2.property.2, path.2.2.1,
      path.2.2.2.property.1.symm,
      path.2.2.1.property.1⟩

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathPair_injective
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathPair G
        (u := u)) := by
  rintro ⟨a, w, b, v⟩ ⟨a', w', b', v'⟩ hpair
  change ((v : V), (w : V)) =
    ((v' : V), (w' : V)) at hpair
  have hv : (v : V) = (v' : V) :=
    congrArg Prod.fst hpair
  have hw : (w : V) = (w' : V) :=
    congrArg Prod.snd hpair
  have hwa' : G.Adj (w : V) (a' : V) := by
    rw [hw]
    exact w'.property.1.symm
  have haa' : (a : V) = (a' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm
      a.property w.property.1.symm
      a'.property hwa'
  have ha : a = a' := Subtype.ext haa'
  subst a'
  have hw' : w = w' := Subtype.ext hw
  subst w'
  have hvb' : G.Adj (v : V) (b' : V) := by
    rw [hv]
    exact v'.property.1.symm
  have hbb' : (b : V) = (b' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      v.property.2.symm
      b.property.1 v.property.1.symm
      b'.property.1 hvb'
  have hb : b = b' := Subtype.ext hbb'
  subst b'
  have hv' : v = v' := Subtype.ext hv
  subst v'
  rfl

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathWitness G hbip hfour hsix
        (u := u)) := by
  intro p q hpq
  apply nonbacktrackingFourPathPair_injective G hfour
  exact congrArg Subtype.val hpq

lemma four_path_endpoint_witness_count_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (FourPathEndpointWitness G u) := by
  calc
    d * (d - 1) ^ 3 ≤
        Fintype.card (NonbacktrackingFourPath G u) :=
      card_nonbacktrackingFourPath_lower G d hdegree u
    _ ≤ Fintype.card (FourPathEndpointWitness G u) :=
      Fintype.card_le_of_injective
        (nonbacktrackingFourPathWitness G hbip hfour hsix)
        (nonbacktrackingFourPathWitness_injective G hbip hfour hsix)

abbrev UnrelatedFourPathEndpoint (G : SimpleGraph V) (u : V) :=
  {v : V // u ≠ v ∧ ¬ CommonNeighborRelated G u v}

abbrev CommonSecondNeighbor (G : SimpleGraph V) (u v : V) :=
  {w : V //
    CommonNeighborRelated G u w ∧ CommonNeighborRelated G v w}

noncomputable instance unrelatedFourPathEndpointFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (UnrelatedFourPathEndpoint G u) :=
  Fintype.ofFinite _

noncomputable instance commonSecondNeighborFintype
    (G : SimpleGraph V) (u v : V) :
    Fintype (CommonSecondNeighbor G u v) :=
  Fintype.ofFinite _

def fourPathEndpointWitnessEquiv
    (G : SimpleGraph V) (u : V) :
    FourPathEndpointWitness G u ≃
      Σ v : UnrelatedFourPathEndpoint G u,
        CommonSecondNeighbor G u (v : V) where
  toFun pair :=
    ⟨⟨pair.1.1, pair.2.1, pair.2.2.1⟩,
      ⟨pair.1.2, pair.2.2.2.1, pair.2.2.2.2⟩⟩
  invFun pair :=
    ⟨((pair.1 : V), (pair.2 : V)),
      pair.1.2.1, pair.1.2.2,
      pair.2.2.1, pair.2.2.2⟩
  left_inv pair := Subtype.ext rfl
  right_inv pair := by
    rcases pair with ⟨v, w⟩
    rfl

omit [DecidableEq V] in
lemma fourPathEndpointWitness_card_eq_sum
    (G : SimpleGraph V) (u : V) :
    Fintype.card (FourPathEndpointWitness G u) =
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [Fintype.card_congr (fourPathEndpointWitnessEquiv G u),
    Fintype.card_sigma]

theorem four_path_common_second_neighbor_sum_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [← fourPathEndpointWitness_card_eq_sum G u]
  exact four_path_endpoint_witness_count_lower
    G hbip hfour hsix d hdegree u

def CommonNeighborIndependent (G : SimpleGraph V)
    (vertices : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ vertices → y ∈ vertices → x ≠ y →
    ¬ CommonNeighborRelated G x y

omit [Fintype V] in
lemma commonNeighborIndependent_neighborhood_injective
    (G : SimpleGraph V) (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    Function.Injective
      (fun pair :
        (Σ x : {x : V // x ∈ vertices},
          G.neighborSet (x : V)) =>
          (pair.2 : V)) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ hab
  have hxy : (x : V) = (y : V) := by
    by_contra hne
    apply hindependent x.property y.property hne
    refine ⟨hne, (a : V), a.property, ?_⟩
    have hyb : G.Adj (y : V) (b : V) := b.property
    exact Eq.mp
      (congrArg (G.Adj (y : V)) hab.symm) hyb
  have hsub : x = y := Subtype.ext hxy
  subst y
  have hneighbor : a = b := Subtype.ext hab
  subst b
  rfl

lemma commonNeighborIndependent_sum_degree_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    (∑ x : {x : V // x ∈ vertices}, G.degree (x : V)) ≤
      Fintype.card V := by
  have hcard := Fintype.card_le_of_injective
    (fun pair :
      (Σ x : {x : V // x ∈ vertices},
        G.neighborSet (x : V)) =>
        (pair.2 : V))
    (commonNeighborIndependent_neighborhood_injective
      G vertices hindependent)
  simpa only [Fintype.card_sigma,
    SimpleGraph.card_neighborSet_eq_degree] using hcard

lemma commonNeighborIndependent_card_mul_degree_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) :
    vertices.card * d ≤ Fintype.card V := by
  calc
    vertices.card * d = ∑ _x : {x : V // x ∈ vertices}, d := by simp
    _ ≤ ∑ x : {x : V // x ∈ vertices}, G.degree (x : V) :=
      Finset.sum_le_sum fun x _ => hdegree x
    _ ≤ Fintype.card V :=
      commonNeighborIndependent_sum_degree_le_card G vertices hindependent

end FourPathCounting

end LocalGeometry

section BreadthFirstCounting

open SimpleGraph

section BreadthFirstPaths

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NonbacktrackingThreePath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      NonbacktrackingNeighbor G (a : V) (w : V)

def nonbacktrackingThreePathEndpoint
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingThreePath G u) : V :=
  path.2.2.1

lemma card_nonbacktrackingThreePath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    G.degree u * (d - 1) ^ 2 ≤
      Fintype.card (NonbacktrackingThreePath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hsecond (a : G.neighborSet u) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            NonbacktrackingNeighbor G (a : V) (w : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · intro w
      exact hstep w.property.1.symm
  have hroot : G.degree u ≤ Fintype.card (G.neighborSet u) := by
    exact (G.card_neighborSet_eq_degree u).symm.le
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        NonbacktrackingNeighbor G (a : V) (w : V))
    hroot hsecond
  simpa [pow_two] using hcount

omit [Fintype V] in
lemma nonbacktrackingThreePathEndpoint_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingThreePathEndpoint G (u := u)) := by
  rintro ⟨a, w, b⟩ ⟨a', w', b'⟩ hb
  change (b : V) = (b' : V) at hb
  have haa : (a : V) = (a' : V) := by
    by_contra hne
    have hww : (w : V) ≠ (w' : V) := by
      intro heq
      have hwa' : G.Adj (w : V) (a' : V) :=
        Eq.mp
          (congrArg (fun x : V => G.Adj x (a' : V)) heq.symm)
          w'.property.1.symm
      have heqa : (a : V) = (a' : V) :=
        common_neighbor_unique_of_four_cycle_free hfour
          w.property.2.symm
          a.property w.property.1.symm
          a'.property hwa'
      exact hne heqa
    have hwb : G.Adj (w' : V) (b : V) :=
      Eq.mp (congrArg (G.Adj (w' : V)) hb.symm)
        b'.property.1
    have htriangle := common_neighbors_triangle_eq_of_cycle_free
      hbip hfour hsix
      w.property.2.symm hww w'.property.2.symm
      a.property w.property.1.symm
      b.property.1 hwb
      w'.property.1.symm a'.property
    exact b.property.2 htriangle.1.symm
  have ha : a = a' := Subtype.ext haa
  subst a'
  have hwb' : G.Adj (b : V) (w' : V) :=
    Eq.mp (congrArg (fun x : V => G.Adj x (w' : V)) hb.symm)
      b'.property.1.symm
  have hww : (w : V) = (w' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      b.property.2.symm
      w.property.1 b.property.1.symm
      w'.property.1 hwb'
  have hw : w = w' := Subtype.ext hww
  subst w'
  have hb' : b = b' := Subtype.ext hb
  subst b'
  rfl

theorem girthEight_degree_mul_pred_sq_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v)
    (u : V) :
    G.degree u * (d - 1) ^ 2 ≤ Fintype.card V := by
  calc
    G.degree u * (d - 1) ^ 2 ≤
        Fintype.card (NonbacktrackingThreePath G u) :=
      card_nonbacktrackingThreePath_lower G d hdegree u
    _ ≤ Fintype.card V :=
      Fintype.card_le_of_injective
        (nonbacktrackingThreePathEndpoint G)
        (nonbacktrackingThreePathEndpoint_injective
          G hbip hfour hsix)

end BreadthFirstPaths

end BreadthFirstCounting

section SubdivisionCounting

open SimpleGraph

section SubdivisionCopies

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def subdivisionVertexImage
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V) : SubdivisionVertex k → V
  | .inl (.inl i) => base i
  | .inl (.inr j) => center j
  | .inr (i, j) => pair i j

lemma subdivisionPairVertex_injective
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective
      (fun ij : Fin 3 × Fin k => pair ij.1 ij.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hpair
  have hi : i = i' := by
    by_contra hne
    apply hbase_unrelated hne
    refine ⟨fun h => hne (hbase h), pair i j,
      hpair_base i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (base i')) hpair.symm)
      (hpair_base i' j')
  subst i'
  have hj : j = j' := by
    by_contra hne
    apply hcenter_unrelated hne
    refine ⟨fun h => hne (hcenter h), pair i j,
      hpair_center i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (center j')) hpair.symm)
      (hpair_center i j')
  exact Prod.ext rfl hj

lemma subdivisionPairVertex_ne_base
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j : Fin k) (other : Fin 3) :
    pair i j ≠ base other := by
  obtain ⟨color⟩ := hbip
  have hfirst : color (base i) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i j) (hpair_center i j)
  have hother : color (base other) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base other j) (hpair_center other j)
  intro heq
  apply color.valid (hpair_base i j)
  exact hfirst.trans
    (hother.symm.trans (congrArg color heq).symm)

lemma subdivisionPairVertex_ne_center
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j other : Fin k) :
    pair i j ≠ center other := by
  obtain ⟨color⟩ := hbip
  have hother : color (base i) = color (center other) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i other) (hpair_center i other)
  intro heq
  apply color.valid (hpair_base i j)
  exact hother.trans (congrArg color heq).symm

lemma subdivisionVertexImage_injective
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective (subdivisionVertexImage base center pair) := by
  intro u v huv
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩
  · change base i = base i' at huv
    exact congrArg (fun a : Fin 3 =>
      (Sum.inl (Sum.inl a) : SubdivisionVertex k)) (hbase huv)
  · change base i = center j' at huv
    exact False.elim (hbase_center i j' huv)
  · change base i = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i' j' i huv.symm)
  · change center j = base i' at huv
    exact False.elim (hbase_center i' j huv.symm)
  · change center j = center j' at huv
    exact congrArg (fun a : Fin k =>
      (Sum.inl (Sum.inr a) : SubdivisionVertex k)) (hcenter huv)
  · change center j = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i' j' j huv.symm)
  · change pair i j = base i' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i j i' huv)
  · change pair i j = center j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i j j' huv)
  · change pair i j = pair i' j' at huv
    have heq : (i, j) = (i', j') :=
      subdivisionPairVertex_injective base center pair
        hbase hcenter hbase_unrelated hcenter_unrelated
        hpair_base hpair_center huv
    exact congrArg
      (fun ij : Fin 3 × Fin k =>
        (Sum.inr ij : SubdivisionVertex k)) heq

lemma subdivisionVertexImage_map_relation
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    {u v : SubdivisionVertex k}
    (hadj : (SubdivisionGraph k).Adj u v) :
    G.Adj (subdivisionVertexImage base center pair u)
      (subdivisionVertexImage base center pair v) := by
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩ <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation, subdivisionVertexImage]
  all_goals
    first
    | exact (hpair_base _ _).symm
    | exact (hpair_center _ _).symm

def subdivisionCopyOfCommonNeighbors
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  refine ⟨⟨subdivisionVertexImage base center pair, ?_⟩, ?_⟩
  · intro u v huv
    exact subdivisionVertexImage_map_relation base center pair
      hpair_base hpair_center huv
  · exact subdivisionVertexImage_injective hbip base center pair
      hbase hcenter hbase_center hbase_unrelated
      hcenter_unrelated hpair_base hpair_center

noncomputable def subdivisionCopyOfRelatedCenters
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  classical
  let pair : Fin 3 → Fin k → V :=
    fun i j => Classical.choose (hrelated i j).2
  have hpair_base (i : Fin 3) (j : Fin k) :
      G.Adj (base i) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).1
  have hpair_center (i : Fin 3) (j : Fin k) :
      G.Adj (center j) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).2
  exact subdivisionCopyOfCommonNeighbors hbip base center pair
    hbase hcenter (fun i j => (hrelated i j).1)
    hbase_unrelated hcenter_unrelated hpair_base hpair_center

noncomputable def subdivisionCopyOfGirthEightCenters
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  have hbase01 : base 0 ≠ base 1 := by
    intro heq
    exact (by decide : (0 : Fin 3) ≠ 1) (hbase heq)
  have hcenter_unrelated :
      ∀ ⦃i j : Fin k⦄, i ≠ j →
        ¬ CommonNeighborRelated G (center i) (center j) := by
    intro i j hij
    exact common_second_neighbors_pairwise_unrelated
      hbip hfour hsix hbase01
      (hbase_unrelated (by decide : (0 : Fin 3) ≠ 1))
      (commonNeighborRelated_symm (hrelated 0 i))
      (commonNeighborRelated_symm (hrelated 1 i))
      (commonNeighborRelated_symm (hrelated 0 j))
      (commonNeighborRelated_symm (hrelated 1 j))
  exact subdivisionCopyOfRelatedCenters hbip base center
    hbase hcenter hbase_unrelated hcenter_unrelated hrelated

end SubdivisionCopies

end SubdivisionCounting

section QuotientWitnesses

open SimpleGraph

noncomputable def fiberRepresentative
    {α β : Type*} (g : α → β) (b : Set.range g) : α :=
  Classical.choose b.property

lemma fiberRepresentative_spec
    {α β : Type*} (g : α → β) (b : Set.range g) :
    g (fiberRepresentative g b) = b.1 :=
  Classical.choose_spec b.property

noncomputable def kernelNormalForm
    {α β : Type*} (g : α → β) (x : α) : α :=
  fiberRepresentative g ⟨g x, ⟨x, rfl⟩⟩

lemma kernelNormalForm_spec
    {α β : Type*} (g : α → β) (x : α) :
    g (kernelNormalForm g x) = g x :=
  fiberRepresentative_spec g ⟨g x, ⟨x, rfl⟩⟩

lemma kernelNormalForm_eq_iff
    {α β : Type*} (g : α → β) (x y : α) :
    kernelNormalForm g x = kernelNormalForm g y ↔ g x = g y := by
  constructor
  · intro h
    calc
      g x = g (kernelNormalForm g x) :=
        (kernelNormalForm_spec g x).symm
      _ = g (kernelNormalForm g y) := congrArg g h
      _ = g y := kernelNormalForm_spec g y
  · intro h
    unfold kernelNormalForm
    congr 1
    exact Subtype.ext h

lemma kernelNormalForm_idempotent
    {α β : Type*} (g : α → β) (x : α) :
    kernelNormalForm g (kernelNormalForm g x) =
      kernelNormalForm g x := by
  apply (kernelNormalForm_eq_iff g _ _).mpr
  exact kernelNormalForm_spec g x

lemma kernelNormalForm_fixed
    {α β : Type*} (g : α → β)
    (u : Set.range (kernelNormalForm g)) :
    kernelNormalForm g u.1 = u.1 := by
  obtain ⟨x, hx⟩ := u.property
  rw [← hx]
  exact kernelNormalForm_idempotent g x

noncomputable def kernelQuotientCopy
    {α β : Type*} (source : SimpleGraph α)
    (target : SimpleGraph β) (hom : source →g target) :
    SimpleGraph.Copy
      (quotientGraph source (kernelNormalForm hom)) target := by
  refine ⟨⟨fun u => hom u.1, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (quotientRelation source (kernelNormalForm hom))
        u v).mp hadj with ⟨_, hforward | hbackward⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hforward
      have hu : hom u.1 = hom x := by
        calc
          hom u.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hv : hom v.1 = hom y := by
        calc
          hom v.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact hom.map_rel hxy
    · obtain ⟨x, y, hx, hy, hxy⟩ := hbackward
      have hv : hom v.1 = hom x := by
        calc
          hom v.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hu : hom u.1 = hom y := by
        calc
          hom u.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact (hom.map_rel hxy).symm
  · intro u v huv
    apply Subtype.ext
    have h := (kernelNormalForm_eq_iff hom u.1 v.1).mpr huv
    rwa [kernelNormalForm_fixed hom u,
      kernelNormalForm_fixed hom v] at h

noncomputable def encodeFiniteGraphCopy
    {α β : Type*} [Fintype α]
    (source : SimpleGraph α) (target : SimpleGraph β)
    (copy : SimpleGraph.Copy source target) :
    SimpleGraph.Copy (encodeFiniteGraph source).graph target := by
  exact copy.comp
    (SimpleGraph.Iso.map (Fintype.equivFin α) source).symm.toCopy

lemma kernelNormalForm_jAdmissible
    {V : Type*} (g : JVertex → V)
    (hcolor : ∀ u v, g u = g v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => g (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v | InJCopy copy v}) :
    JAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro u v huv
    apply hbase
    exact (kernelNormalForm_eq_iff g _ _).mp huv
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

lemma kernelNormalForm_kAdmissible
    {V : Type*} (g : KVertex → V)
    (hcolor : ∀ u v, g u = g v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v : KVertex | v.1 = copy}) :
    KAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

theorem proposedFamilyFree_no_jTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : jTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) : False := by
  let f := kernelNormalForm hom
  have hf : JAdmissible f :=
    kernelNormalForm_jAdmissible hom hcolor hbase hcopies
  have hmember := jQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph jTemplate f) host
    (kernelQuotientCopy jTemplate host hom)⟩

theorem proposedFamilyFree_no_kTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : kTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) : False := by
  let f := kernelNormalForm hom
  have hf : KAdmissible f :=
    kernelNormalForm_kAdmissible hom hcolor hcopies
  have hmember := kQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph kTemplate f) host
    (kernelQuotientCopy kTemplate host hom)⟩

end QuotientWitnesses

end Erdos180
