import ErdosProblems.Erdos79.Core
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Minimal obstructions and the infinitude assembly for Erdős Problem 79

This file contains the finite order-theoretic part of Wigderson's argument.  It is deliberately
separated from the two quantitative inputs (forests are Ramsey size linear, and dense graphs of
arbitrarily large girth exist): those inputs plug into the assembly theorem near the end.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos79

/-- The size used to well-found ordinary containment of finite graphs. -/
def GraphCode.size (G : GraphCode) : ℕ := G.vertexCount + G.edgeCount

/-- Ordinary proper subgraph containment, taken up to graph isomorphism. -/
def ProperSubgraph (F G : GraphCode) : Prop :=
  IsContained F G ∧ ¬ Isomorphic F G

/-- A graph which is not Ramsey size linear although every proper subgraph is. -/
def MinimallyNonRamseySizeLinear (G : GraphCode) : Prop :=
  ¬ RamseySizeLinear G ∧
    ∀ F : GraphCode, ProperSubgraph F G → RamseySizeLinear F

namespace IsContained

/-- A containment between finite graphs with the same numbers of vertices and edges is an
isomorphism.  Surjectivity on vertices follows from the vertex count; equality of the finite
edge sets upgrades the edge-preserving copy to an adjacency-reflecting equivalence. -/
theorem isomorphic_of_vertexCount_eq_of_edgeCount_eq {F G : GraphCode}
    (h : IsContained F G) (hv : F.vertexCount = G.vertexCount)
    (he : F.edgeCount = G.edgeCount) : Isomorphic F G := by
  classical
  rcases h with ⟨f⟩
  have hf_surj : Function.Surjective f.toEmbedding := by
    exact ((Fintype.bijective_iff_injective_and_card f.toEmbedding).mpr
      ⟨f.injective, by simpa using hv⟩).surjective
  let e : Fin F.vertexCount ≃ Fin G.vertexCount :=
    f.toEmbedding.equivOfSurjective hf_surj
  have hedge_card : Fintype.card F.graph.edgeSet = Fintype.card G.graph.edgeSet := by
    simpa only [GraphCode.edgeCount, Nat.card_eq_fintype_card] using he
  have hedge_surj : Function.Surjective f.mapEdgeSet :=
    ((Fintype.bijective_iff_injective_and_card f.mapEdgeSet).mpr
      ⟨f.mapEdgeSet.injective, hedge_card⟩).surjective
  refine ⟨{ e with map_rel_iff' := ?_ }⟩
  intro u v
  change G.graph.Adj (f u) (f v) ↔ F.graph.Adj u v
  constructor
  · intro huv
    let eg : G.graph.edgeSet := ⟨s(f u, f v), huv⟩
    obtain ⟨ef, hef⟩ := hedge_surj eg
    have hedge : (ef : Sym2 (Fin F.vertexCount)) = s(u, v) := by
      apply Sym2.map.injective f.injective
      have hval := congrArg Subtype.val hef
      simpa [eg, SimpleGraph.Copy.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet] using hval
    rw [← SimpleGraph.mem_edgeSet]
    simpa [hedge] using ef.property
  · exact f.toHom.map_adj

/-- Equal total size under containment forces isomorphism. -/
theorem isomorphic_of_size_eq {F G : GraphCode} (h : IsContained F G)
    (hs : F.size = G.size) : Isomorphic F G := by
  have hv := h.vertexCount_le
  have he := h.edgeCount_le
  simp only [GraphCode.size] at hs
  apply h.isomorphic_of_vertexCount_eq_of_edgeCount_eq
  · omega
  · omega

end IsContained

/-- Proper containment strictly decreases `vertexCount + edgeCount`. -/
theorem ProperSubgraph.size_lt {F G : GraphCode} (h : ProperSubgraph F G) :
    F.size < G.size := by
  rcases h with ⟨hFG, hniso⟩
  have hv := hFG.vertexCount_le
  have he := hFG.edgeCount_le
  have hle : F.size ≤ G.size := Nat.add_le_add hv he
  exact hle.lt_of_ne fun hs ↦ hniso (hFG.isomorphic_of_size_eq hs)

namespace MinimallyNonRamseySizeLinear

/-- A minimal obstruction is, in particular, not Ramsey size linear. -/
theorem not_ramseySizeLinear {G : GraphCode} (hG : MinimallyNonRamseySizeLinear G) :
    ¬ RamseySizeLinear G := hG.1

/-- Every proper subgraph of a minimal obstruction is Ramsey size linear. -/
theorem proper_subgraph {G : GraphCode} (hG : MinimallyNonRamseySizeLinear G)
    {F : GraphCode} (hFG : ProperSubgraph F G) : RamseySizeLinear F :=
  hG.2 F hFG

/-- Minimal-obstruction status is invariant under graph isomorphism. -/
theorem congr {F G : GraphCode} (hFG : Isomorphic F G) :
    MinimallyNonRamseySizeLinear F ↔ MinimallyNonRamseySizeLinear G := by
  have forward : ∀ {A B : GraphCode}, Isomorphic A B →
      MinimallyNonRamseySizeLinear A → MinimallyNonRamseySizeLinear B := by
    intro A B hAB
    rintro ⟨hbad, hproper⟩
    refine ⟨?_, ?_⟩
    · exact fun hB ↦ hbad ((RamseySizeLinear.congr hAB).mpr hB)
    · intro H hHB
      apply hproper H
      refine ⟨hHB.1.trans hAB.isContained', ?_⟩
      intro hHA
      exact hHB.2 (hHA.trans hAB)
  exact ⟨forward hFG, forward hFG.symm⟩

end MinimallyNonRamseySizeLinear

/-! ## Finite minimality -/

/-- The natural-number sizes attained by non-Ramsey-size-linear subgraphs of `X`. -/
def badSubgraphSizes (X : GraphCode) : Set ℕ :=
  {n | ∃ F : GraphCode, IsContained F X ∧ ¬ RamseySizeLinear F ∧ F.size = n}

theorem badSubgraphSizes_nonempty {X : GraphCode} (hX : ¬ RamseySizeLinear X) :
    (badSubgraphSizes X).Nonempty := by
  exact ⟨X.size, X, IsContained.rfl, hX, rfl⟩

/-- A finite non-Ramsey-size-linear graph contains a containment-minimal obstruction. -/
theorem exists_minimallyNonRamseySizeLinear_subgraph {X : GraphCode}
    (hX : ¬ RamseySizeLinear X) :
    ∃ G : GraphCode, IsContained G X ∧ MinimallyNonRamseySizeLinear G := by
  let n := sInf (badSubgraphSizes X)
  have hn_mem : n ∈ badSubgraphSizes X :=
    Nat.sInf_mem (badSubgraphSizes_nonempty hX)
  obtain ⟨G, hGX, hbadG, hsizeG⟩ := hn_mem
  refine ⟨G, hGX, hbadG, ?_⟩
  intro F hFG
  by_contra hbadF
  have hFmem : F.size ∈ badSubgraphSizes X :=
    ⟨F, hFG.1.trans hGX, hbadF, rfl⟩
  have hmin : n ≤ F.size := Nat.sInf_le hFmem
  rw [← hsizeG] at hmin
  exact (not_lt_of_ge hmin) hFG.size_lt

/-! ## Cycles and finite-family girth avoidance -/

/-- If all finite forests are Ramsey size linear, every minimal obstruction is cyclic. -/
theorem MinimallyNonRamseySizeLinear.not_isAcyclic
    (forest_ramseySizeLinear : ∀ F : GraphCode,
      F.graph.IsAcyclic → RamseySizeLinear F)
    {G : GraphCode} (hG : MinimallyNonRamseySizeLinear G) :
    ¬ G.graph.IsAcyclic := by
  intro hacyc
  exact hG.1 (forest_ramseySizeLinear G hacyc)

/-- A natural girth threshold strictly exceeding the girth of every graph in `s`.
The extra `max 3` makes it a valid graph-girth request even for the empty family. -/
def familyGirthBound (s : Finset GraphCode) : ℕ :=
  max 3 (s.sup fun G ↦ G.graph.girth + 1)

theorem three_le_familyGirthBound (s : Finset GraphCode) :
    3 ≤ familyGirthBound s := le_max_left _ _

theorem girth_lt_familyGirthBound {s : Finset GraphCode} {G : GraphCode}
    (hGs : G ∈ s) : G.graph.girth < familyGirthBound s := by
  have hsup : G.graph.girth + 1 ≤ s.sup (fun H ↦ H.graph.girth + 1) :=
    Finset.le_sup (f := fun H : GraphCode ↦ H.graph.girth + 1) hGs
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hsup.trans (le_max_right _ _))

/-- A graph whose extended girth reaches `familyGirthBound s` contains no cyclic member of `s`.
Using extended girth here lets the high-girth construction return an acyclic graph as a harmless
degenerate possibility, although the dense graphs used in the final application are cyclic. -/
theorem not_isContained_of_familyGirthBound_le_egirth
    {s : Finset GraphCode} {X : GraphCode}
    (hcyclic : ∀ G ∈ s, ¬ G.graph.IsAcyclic)
    (hgirth : (familyGirthBound s : ℕ∞) ≤ X.graph.egirth) :
    ∀ G ∈ s, ¬ IsContained G X := by
  intro G hGs hGX
  have hle : X.graph.egirth ≤ G.graph.egirth := hGX.egirth_le
  have hfinite : (G.graph.girth : ℕ∞) = G.graph.egirth := by
    exact ENat.natCast_toNat (SimpleGraph.egirth_eq_top.not.mpr (hcyclic G hGs))
  have hbound : (familyGirthBound s : ℕ∞) ≤ (G.graph.girth : ℕ∞) := by
    rw [hfinite]
    exact hgirth.trans hle
  exact (not_le_of_gt (girth_lt_familyGirthBound hGs))
    (ENat.natCast_le_natCast.mp hbound)

/-! ## Assembly from the two quantitative inputs -/

/-- The two mathematical inputs needed by the purely order-theoretic infinitude argument. -/
structure InfinitudeInputs : Prop where
  forest_ramseySizeLinear : ∀ F : GraphCode,
    F.graph.IsAcyclic → RamseySizeLinear F
  nonRamseySizeLinear_largeGirth : ∀ g : ℕ, 3 ≤ g →
    ∃ X : GraphCode, ¬ RamseySizeLinear X ∧ (g : ℕ∞) ≤ X.graph.egirth

/-- Package the exact interfaces supplied by the forest, density-obstruction, and dense
high-girth modules.  The high-girth construction gives the stronger inequality `6v < e`, while
the first-moment obstruction only needs `5v < e`. -/
theorem infinitudeInputs_of_dense_highGirth
    (forest_ramseySizeLinear : ∀ F : GraphCode,
      F.graph.IsAcyclic → RamseySizeLinear F)
    (dense_not_ramseySizeLinear : ∀ F : GraphCode,
      5 * F.vertexCount < F.edgeCount → ¬ RamseySizeLinear F)
    (dense_highGirth : ∀ g : ℕ, ∃ X : GraphCode,
      (g : ℕ∞) ≤ X.graph.egirth ∧ 6 * X.vertexCount < X.edgeCount) :
    InfinitudeInputs := by
  refine ⟨forest_ramseySizeLinear, ?_⟩
  intro g _hg
  obtain ⟨X, hgirth, hdense⟩ := dense_highGirth g
  refine ⟨X, dense_not_ramseySizeLinear X ?_, hgirth⟩
  omega

/-- Given the forest theorem and non-linear graphs of arbitrary girth, every finite family of
minimal obstructions can be avoided up to isomorphism. -/
theorem exists_minimal_avoiding_finset (inputs : InfinitudeInputs)
    (s : Finset GraphCode)
    (hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G) :
    ∃ G : GraphCode, MinimallyNonRamseySizeLinear G ∧
      ∀ H ∈ s, ¬ Isomorphic G H := by
  obtain ⟨X, hbadX, hgirthX⟩ :=
    inputs.nonRamseySizeLinear_largeGirth (familyGirthBound s)
      (three_le_familyGirthBound s)
  have hcyclic : ∀ H ∈ s, ¬ H.graph.IsAcyclic := by
    intro H hHs
    exact (hs H hHs).not_isAcyclic inputs.forest_ramseySizeLinear
  have havoids : ∀ H ∈ s, ¬ IsContained H X :=
    not_isContained_of_familyGirthBound_le_egirth hcyclic hgirthX
  obtain ⟨G, hGX, hminG⟩ := exists_minimallyNonRamseySizeLinear_subgraph hbadX
  refine ⟨G, hminG, ?_⟩
  intro H hHs hGH
  exact havoids H hHs (hGH.isContained'.trans hGX)

/-! ## Turning finite-family avoidance into a sequence -/

/-- The representation-independent finite-family avoidance principle. -/
abbrev FiniteFamilyAvoidance : Prop :=
  ∀ s : Finset GraphCode,
  (∀ G ∈ s, MinimallyNonRamseySizeLinear G) →
    ∃ G : GraphCode, MinimallyNonRamseySizeLinear G ∧
      ∀ H ∈ s, ¬ Isomorphic G H

variable (avoid : FiniteFamilyAvoidance)

/-- A deterministic choice of a new obstruction outside a finite family.  The fallback branch is
never reached in the recursive construction below. -/
noncomputable def freshObstruction (s : Finset GraphCode) : GraphCode :=
  by
    classical
    exact if hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G then
      Classical.choose (avoid s hs)
    else completeCode 0

theorem freshObstruction_minimal {s : Finset GraphCode}
    (hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G) :
    MinimallyNonRamseySizeLinear (freshObstruction avoid s) := by
  classical
  simp only [freshObstruction, dif_pos hs]
  exact (Classical.choose_spec (avoid s hs)).1

theorem freshObstruction_not_isomorphic {s : Finset GraphCode}
    (hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G)
    {H : GraphCode} (hHs : H ∈ s) :
    ¬ Isomorphic (freshObstruction avoid s) H := by
  classical
  simp only [freshObstruction, dif_pos hs]
  exact (Classical.choose_spec (avoid s hs)).2 H hHs

/-- The finite set of obstructions selected during the first `n` stages. -/
noncomputable def obstructionSets : ℕ → Finset GraphCode
  | 0 => ∅
  | n + 1 => by
      classical
      exact insert (freshObstruction avoid (obstructionSets n)) (obstructionSets n)

theorem obstructionSets_mono : Monotone (obstructionSets avoid) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [obstructionSets]
  exact Finset.subset_insert _ _

theorem obstructionSets_all_minimal (n : ℕ) :
    ∀ G ∈ obstructionSets avoid n, MinimallyNonRamseySizeLinear G := by
  classical
  induction n with
  | zero => simp [obstructionSets]
  | succ n ih =>
      intro G hG
      rw [obstructionSets] at hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact freshObstruction_minimal avoid ih
      · exact ih G hG

/-- The recursively selected sequence of minimal obstructions. -/
noncomputable def obstructionSequence (n : ℕ) : GraphCode :=
  freshObstruction avoid (obstructionSets avoid n)

theorem obstructionSequence_minimal (n : ℕ) :
    MinimallyNonRamseySizeLinear (obstructionSequence avoid n) :=
  freshObstruction_minimal avoid (obstructionSets_all_minimal avoid n)

theorem obstructionSequence_mem_obstructionSets_succ (n : ℕ) :
    obstructionSequence avoid n ∈ obstructionSets avoid (n + 1) := by
  classical
  simp [obstructionSequence, obstructionSets]

theorem obstructionSequence_mem_obstructionSets {i j : ℕ} (hij : i < j) :
    obstructionSequence avoid i ∈ obstructionSets avoid j := by
  exact obstructionSets_mono avoid (Nat.succ_le_iff.mpr hij)
    (obstructionSequence_mem_obstructionSets_succ avoid i)

theorem obstructionSequence_not_isomorphic_of_lt {i j : ℕ} (hij : i < j) :
    ¬ Isomorphic (obstructionSequence avoid i) (obstructionSequence avoid j) := by
  intro hijIso
  have hnew := freshObstruction_not_isomorphic avoid
    (obstructionSets_all_minimal avoid j)
    (obstructionSequence_mem_obstructionSets avoid hij)
  exact hnew hijIso.symm

/-- Finite-family avoidance yields a natural-number-indexed pairwise non-isomorphic sequence of
minimal non-Ramsey-size-linear finite graphs. -/
theorem exists_pairwise_nonisomorphic_sequence_of_avoidance
    (avoid : FiniteFamilyAvoidance) :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) := by
  refine ⟨obstructionSequence avoid, obstructionSequence_minimal avoid, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact obstructionSequence_not_isomorphic_of_lt avoid hij
  · intro h
    exact obstructionSequence_not_isomorphic_of_lt avoid hji h.symm

/-- The quantitative inputs imply a pairwise non-isomorphic sequence of minimal obstructions. -/
theorem exists_pairwise_nonisomorphic_sequence (inputs : InfinitudeInputs) :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) := by
  exact exists_pairwise_nonisomorphic_sequence_of_avoidance
    (fun s hs ↦ exists_minimal_avoiding_finset inputs s hs)

end Erdos79
