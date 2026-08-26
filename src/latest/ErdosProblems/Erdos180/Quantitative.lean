/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Counterexample

set_option linter.mathlibStandardSet false

namespace Erdos180

section Connectedness

open Finset SimpleGraph

lemma jTemplate_connected : jTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable jTemplate).2
  let root : JVertex := .inl (.inl (2 : Fin 4))
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inl (jBase copy base)))
        (.inr (.inl (copy, (base, center)))) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inr (copy, center)))
        (.inr (.inl (copy, (base, center)))) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hrootCenter (copy : Fin 2) (center : Fin 2) :
      jTemplate.Reachable root (.inl (.inr (copy, center))) := by
    have hfirst :
        jTemplate.Adj root
          (.inr (.inl (copy, ((1 : Fin 3), center)))) := by
      simpa [root, jBase] using hbasePair copy 1 center
    exact hfirst.reachable.trans
      (hcenterPair copy 1 center).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Reachable root
        (.inr (.inl (copy, (base, center)))) :=
    (hrootCenter copy center).trans (hcenterPair copy base center).reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      jTemplate.Reachable root (.inl (.inl (jBase copy base))) :=
    (hrootPair copy base 0).trans (hbasePair copy base 0).symm.reachable
  intro vertex
  rcases vertex with (base | ⟨copy, center⟩) |
      (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · simpa [jBase] using hrootBase 0 0
    · simpa [jBase] using hrootBase 1 0
    · simpa [jBase] using hrootBase 0 1
    · simpa [jBase] using hrootBase 0 2
  · exact hrootCenter copy center
  · exact hrootPair copy base center
  · cases lastVertex
    have hjoin :
        jTemplate.Adj (.inl (.inl (0 : Fin 4)))
          (.inr (.inr ())) := by
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    have hzero :
        jTemplate.Reachable root (.inl (.inl (0 : Fin 4))) := by
      simpa [jBase] using hrootBase 0 0
    exact hzero.trans hjoin.reachable

lemma kTemplate_connected : kTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable kTemplate).2
  let root : KVertex := ((0 : Fin 2), kSpecifiedCenter)
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inl base))
        (copy, .inr (base, center)) := by
    simp [kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      subdivisionRelation]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inr center))
        (copy, .inr (base, center)) := by
    simp [kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      subdivisionRelation]
  have hbridge :
      kTemplate.Adj root ((1 : Fin 2), kSpecifiedCenter) := by
    simp [root, kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      kSpecifiedCenter, subdivisionRelation]
  have hhub (copy : Fin 2) :
      kTemplate.Reachable root (copy, kSpecifiedCenter) := by
    fin_cases copy
    · exact SimpleGraph.Reachable.refl root
    · exact hbridge.reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inl base)) := by
    have hfirst :
        kTemplate.Reachable root (copy, .inr (base, (0 : Fin 3))) := by
      exact (hhub copy).trans
        (by
          simpa [kSpecifiedCenter] using
            (hcenterPair copy base 0).reachable)
    exact hfirst.trans (hbasePair copy base 0).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inr (base, center)) :=
    (hrootBase copy base).trans (hbasePair copy base center).reachable
  have hrootCenter (copy : Fin 2) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inr center)) :=
    (hrootPair copy 0 center).trans
      (hcenterPair copy 0 center).symm.reachable
  intro vertex
  rcases vertex with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · exact hrootBase copy base
  · exact hrootCenter copy center
  · exact hrootPair copy base center

lemma quotientGraph_connected_of_colorRespecting
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f)
    (hconnected : graph.Connected) :
    (quotientGraph graph f).Connected := by
  refine SimpleGraph.Connected.map
    (colorRespectingQuotientProjectionHom graph color hproper f hf)
    ?_ hconnected
  rintro ⟨_, ⟨v, rfl⟩⟩
  exact ⟨v, rfl⟩

lemma encodeFiniteGraph_connected
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hconnected : graph.Connected) :
    (encodeFiniteGraph graph).graph.Connected := by
  change (graph.map (Fintype.equivFin V).toEmbedding).Connected
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.Iso.map (Fintype.equivFin V) graph)).mp hconnected

lemma encodedJQuotient_connected {f : JVertex → JVertex}
    (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1 jTemplate_connected)

lemma encodedKQuotient_connected {f : KVertex → KVertex}
    (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1 kTemplate_connected)

theorem finiteCycle_connected {n : ℕ} (hn : 0 < n) :
    (finiteCycle n).graph.Connected := by
  change (SimpleGraph.cycleGraph n).Connected
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨SimpleGraph.cycleGraph_preconnected⟩

theorem proposedFamily_member_connected
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.Connected :=
  proposedFamily_induction (P := fun graph => graph.graph.Connected)
    (finiteCycle_connected (by norm_num : 0 < (4 : ℕ)))
    (finiteCycle_connected (by norm_num : 0 < (6 : ℕ)))
    (fun _ hf => encodedJQuotient_connected hf)
    (fun _ hf => encodedKQuotient_connected hf)
    forbidden hforbidden

end Connectedness

section Bipartiteness

open Finset SimpleGraph

lemma colorRespectingQuotient_isBipartite
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    (quotientGraph graph f).IsBipartite := by
  classical
  let representative : Set.range f → V :=
    fun vertex => Classical.choose vertex.property
  have hrepresentative (vertex : Set.range f) :
      f (representative vertex) = (vertex : V) :=
    Classical.choose_spec vertex.property
  let quotientColor : Set.range f → Bool :=
    fun vertex => color (representative vertex)
  have hdirected {u v : Set.range f}
      (h : quotientRelation graph f u v) :
      quotientColor u ≠ quotientColor v := by
    rcases h with ⟨x, y, hx, hy, hxy⟩
    change color (representative u) ≠ color (representative v)
    intro heq
    apply hproper hxy
    calc
      color x = color (representative u) :=
        (hf (representative u) x
          ((hrepresentative u).trans hx.symm)).symm
      _ = color (representative v) := heq
      _ = color y :=
        hf (representative v) y
          ((hrepresentative v).trans hy.symm)
  have hcoloring : (quotientGraph graph f).Coloring Bool :=
    SimpleGraph.Coloring.mk quotientColor (by
      intro u v hadj
      change (SimpleGraph.fromRel (quotientRelation graph f)).Adj u v at hadj
      rcases
          (SimpleGraph.fromRel_adj (quotientRelation graph f) u v).mp hadj with
        ⟨_, hforward | hbackward⟩
      · exact hdirected hforward
      · exact Ne.symm (hdirected hbackward))
  simpa using hcoloring.colorable

lemma encodeFiniteGraph_isBipartite
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hbipartite : graph.IsBipartite) :
    (encodeFiniteGraph graph).graph.IsBipartite := by
  classical
  exact SimpleGraph.Colorable.map
    (Fintype.equivFin V).toEmbedding hbipartite

lemma encodedJQuotient_isBipartite
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1)

lemma encodedKQuotient_isBipartite
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1)

theorem proposedFamily_member_isBipartite
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.IsBipartite :=
  proposedFamily_induction (P := fun graph => graph.graph.IsBipartite)
    (SimpleGraph.cycleGraph.bicoloring_of_even 4 (by decide)).colorable
    (SimpleGraph.cycleGraph.bicoloring_of_even 6 (by decide)).colorable
    (fun _ hf => encodedJQuotient_isBipartite hf)
    (fun _ hf => encodedKQuotient_isBipartite hf)
    forbidden hforbidden

end Bipartiteness

section FamilyExtremal

open Finset SimpleGraph

theorem finiteNatSup_sixteenth_power_le
    {α : Type*} (s : Finset α) (weight : α → ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hweight : ∀ a ∈ s, (weight a : ℝ) ^ 16 ≤ bound) :
    ((s.sup weight : ℕ) : ℝ) ^ 16 ≤ bound := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst s
    simpa using hbound
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup s hs weight
    simpa [hmax] using hweight a ha

theorem proposedFamily_familyExtremal_sixteenth_power_le (n : ℕ) :
    (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  have hbound :
      0 ≤ compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  unfold familyExtremal
  apply finiteNatSup_sixteenth_power_le
    (Finset.univ.filter (FamilyFree proposedFamily))
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)
    (compactnessHostPowerConstant * (n : ℝ) ^ 21) hbound
  intro host hhost
  exact proposedFamilyFree_sixteenth_power_host_bound n host
    (Finset.mem_filter.mp hhost).2

theorem proposedFamily_familyExtremal_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (familyExtremal proposedFamily n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((21 : ℝ) / 16)) := by
  let C : ℝ := max compactnessHostPowerConstant 1
  have hCone : 1 ≤ C := le_max_right _ _
  have hCnonneg : 0 ≤ C := zero_le_one.trans hCone
  have hconstant : compactnessHostPowerConstant ≤ C ^ (16 : ℕ) :=
    (le_max_left _ _).trans (le_self_pow₀ hCone (by norm_num))
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Filter.Eventually.of_forall fun n => ?_⟩
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hscale :
      ((n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) =
        (n : ℝ) ^ (21 : ℕ) := by
    rw [← Real.rpow_mul_natCast hnnonneg ((21 : ℝ) / 16) 16]
    norm_num
  have hpower :
      (familyExtremal proposedFamily n : ℝ) ^ (16 : ℕ) ≤
        (C * (n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) := by
    calc
      (familyExtremal proposedFamily n : ℝ) ^ (16 : ℕ) ≤
          compactnessHostPowerConstant * (n : ℝ) ^ (21 : ℕ) :=
        proposedFamily_familyExtremal_sixteenth_power_le n
      _ ≤ C ^ (16 : ℕ) * (n : ℝ) ^ (21 : ℕ) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = (C * (n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) := by
        rw [mul_pow, hscale]
  have hbound := le_of_pow_le_pow_left₀
    (by norm_num : (16 : ℕ) ≠ 0)
    (mul_nonneg hCnonneg (Real.rpow_nonneg hnnonneg _)) hpower
  have hextremal_nonneg :
      (0 : ℝ) ≤ (familyExtremal proposedFamily n : ℝ) :=
    Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
    abs_of_nonneg (Real.rpow_nonneg hnnonneg _)] using hbound

end FamilyExtremal

section MainTheorem

open Finset SimpleGraph
open scoped Classical

noncomputable def compactnessSharpHostPowerConstant : ℝ :=
  compactnessHostPowerConstant

theorem compactnessSharpHostPowerConstant_pos :
    0 < compactnessSharpHostPowerConstant := by
  unfold compactnessSharpHostPowerConstant compactnessHostPowerConstant
    compactnessDegreePowerConstant
  positivity

theorem checkedManuscriptCounterexample :
    proposedFamily.Nonempty ∧
      (∀ forbidden ∈ proposedFamily,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      (0 : ℝ) < manuscriptLowerConstant ∧
      UniformMemberLower proposedFamily manuscriptLowerConstant ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree proposedFamily host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤
            compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
          compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily proposedFamily ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily_nonempty, ?_,
    manuscriptLowerConstant_pos, proposedFamily_uniformMemberLower,
    proposedFamilyFree_sixteenth_power_host_bound,
    proposedFamily_familyExtremal_sixteenth_power_le,
    by norm_num, by norm_num,
    proposedFamily_not_compact, not_erdos_180_source⟩
  intro forbidden hforbidden
  exact ⟨proposedFamily_member_connected hforbidden,
    proposedFamily_member_isBipartite hforbidden,
    proposedFamily_isCyclic forbidden hforbidden⟩

theorem quantitativeCompactnessCounterexample :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  obtain ⟨hnonempty, hgeometry, hlower_pos, hlower, hhost, hfamily,
    hgap_pos, hexponents, hnot_compact, hconjecture⟩ :=
    checkedManuscriptCounterexample
  refine ⟨proposedFamily, manuscriptLowerConstant,
    compactnessHostPowerConstant, hnonempty, hgeometry, hlower_pos, ?_,
    hlower, hhost, hfamily, hgap_pos, hexponents, hnot_compact,
    hconjecture⟩
  simpa [compactnessSharpHostPowerConstant] using
    compactnessSharpHostPowerConstant_pos

theorem compactnessCounterexample_bigO :
    ∃ (family : Finset FiniteGraph) (c : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      UniformMemberLower family c ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (familyExtremal family n : ℝ))
        (fun n : ℕ =>
          (n : ℝ) ^ ((4 : ℝ) / 3 - (1 : ℝ) / 48)) ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily, manuscriptLowerConstant,
    proposedFamily_nonempty, ?_, manuscriptLowerConstant_pos,
    proposedFamily_uniformMemberLower, ?_, proposedFamily_not_compact,
    not_erdos_180_source⟩
  · intro forbidden hforbidden
    exact ⟨proposedFamily_member_connected hforbidden,
      proposedFamily_member_isBipartite hforbidden,
      proposedFamily_isCyclic forbidden hforbidden⟩
  · convert proposedFamily_familyExtremal_isBigO using 1
    norm_num

end MainTheorem

end Erdos180
