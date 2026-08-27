/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootTypicality

/-!
# Initial typicality on an arbitrary finite vortex

The ambient loss estimates used for the outer level remain valid after
restricting the candidate vertex set to any vortex level.  Consequently the
initial absorber complement is iteration-typical on every sufficiently large
level of an arbitrary vortex, not only on the two-level diagnostic vortex.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma initial_ambient_degree_loss_restrict_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (U : Finset V) (v : V) :
    U \ neighborsIn (graphDifference (SimpleGraph.completeGraph V) H) U v ⊆
      univ \ neighborsIn
        (graphDifference (SimpleGraph.completeGraph V) H) univ v := by
  intro x hx
  rw [mem_sdiff] at hx ⊢
  refine ⟨mem_univ x, ?_⟩
  intro hxall
  apply hx.2
  rw [mem_neighborsIn_iff] at hxall ⊢
  exact ⟨hx.1, hxall.2⟩

lemma initial_ambient_extension_loss_restrict_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) :
    U \ iterationExtensionVertices A Q U ⊆
      univ \ iterationExtensionVertices A Q univ := by
  intro x hx
  rw [mem_sdiff] at hx ⊢
  refine ⟨mem_univ x, ?_⟩
  intro hxall
  apply hx.2
  rw [mem_iterationExtensionVertices_iff] at hxall ⊢
  exact ⟨hx.1, hxall.2⟩

/-- An inner vortex level is separated from the nonroot support of the
absorber when it contains `X`, while every other vertex of the level is
incident with no absorber edge and lies in no absorber-bank triple. -/
def AbsorberSeparatedLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V)
    (U : Finset V) : Prop :=
  X ⊆ U ∧ ∀ x ∈ U, x ∉ X →
    x ∉ graphSupportFinset H ∧ x ∉ verticesOn B

/-- On a separated inner level, the degree loss is contained in the same
constant-size root-neighbour set as it is on `X` itself. -/
lemma initial_separated_degree_loss_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (X U : Finset V) (B : TripleSystemOn V)
    (hsep : AbsorberSeparatedLevel H X B U) (v : V) :
    U \ neighborsIn
        (graphDifference (SimpleGraph.completeGraph V) H) U v ⊆
      insert v (absorberRootNeighborSet H X v) := by
  intro x hx
  have hxU := (mem_sdiff.mp hx).1
  have hxNotNeighbor := (mem_sdiff.mp hx).2
  by_cases hxv : x = v
  · exact mem_insert.mpr (Or.inl hxv)
  apply mem_insert.mpr
  right
  apply mem_absorberRootNeighborSet_iff.mpr
  have hxH : H.Adj v x := by
    by_contra hxNotH
    apply hxNotNeighbor
    apply mem_neighborsIn_iff.mpr
    refine ⟨hxU, ?_⟩
    refine ⟨?_, Ne.symm hxv, hxNotH⟩
    simpa using Ne.symm hxv
  have hxX : x ∈ X := by
    by_contra hxNotX
    exact (hsep.2 x hxU hxNotX).1
      (mem_graphSupportFinset_iff.mpr ⟨v, hxH.symm⟩)
  exact ⟨hxX, hxH.symm⟩

lemma card_initial_separated_degree_loss_le_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X U : Finset V} {q : ℕ} {B : TripleSystemOn V}
    (hsep : AbsorberSeparatedLevel H X B U)
    (hroot : HasPaddedAbsorberRootBounds q H X B) (v : V) :
    (U \ neighborsIn
      (graphDifference (SimpleGraph.completeGraph V) H) U v).card ≤ 15 := by
  calc
    (U \ neighborsIn
      (graphDifference (SimpleGraph.completeGraph V) H) U v).card
        ≤ (insert v (absorberRootNeighborSet H X v)).card :=
      card_le_card (initial_separated_degree_loss_subset H X U B hsep v)
    _ ≤ (absorberRootNeighborSet H X v).card + 1 := card_insert_le _ _
    _ ≤ 15 := by
      have hv := hroot.1 v
      omega

/-- A free vertex of a separated level is an initially legal extension of
every edge of a supported pattern. -/
lemma separated_free_mem_initial_extensionVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X U : Finset V}
    {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hsep : AbsorberSeparatedLevel H X B U)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H)
    {x : V} (hxU : x ∈ U) (hxX : x ∉ X)
    (hxSupport : x ∉ graphSupportFinset Q) :
    x ∈ iterationExtensionVertices
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available Q U := by
  rw [mem_iterationExtensionVertices_iff]
  refine ⟨hxU, ?_⟩
  intro e he
  have hends := endpoint_mem_graphSupportFinset he
  have hxe₁ : x ≠ e.out.1 := fun h ↦ hxSupport (h ▸ hends.1)
  have hxe₂ : x ≠ e.out.2 := fun h ↦ hxSupport (h ▸ hends.2)
  let w : ThirdVertex e.out.1 e.out.2 := ⟨x, hxe₁, hxe₂⟩
  let T : TripleOn V :=
    thirdVertexTriple (out_fst_ne_snd_of_mem_graphEdges he) w
  have hxNoH : x ∉ graphSupportFinset H := (hsep.2 x hxU hxX).1
  have hxNoB : x ∉ verticesOn B := (hsep.2 x hxU hxX).2
  have heG := hQ (graph_adj_out_of_mem_graphEdges he)
  have hAvoid : TriangleAvoidsGraph H T := by
    apply (triangleAvoidsGraph_thirdVertexTriple_iff H
      (out_fst_ne_snd_of_mem_graphEdges he) w).mpr
    refine ⟨heG.2.2, ?_, ?_⟩
    · intro h
      exact hxNoH (mem_graphSupportFinset_iff.mpr ⟨e.out.1, h.symm⟩)
    · intro h
      exact hxNoH (mem_graphSupportFinset_iff.mpr ⟨e.out.2, h.symm⟩)
  have hTnotB : T ∉ B := by
    intro hTB
    apply hxNoB
    exact mem_biUnion.mpr
      ⟨T, hTB, third_mem_thirdVertexTriple
        (out_fst_ne_snd_of_mem_graphEdges he) w⟩
  have hnotComplete : ¬ CompletesForbidden
      (absorberErdosForbiddenConfigurationsOn q B) ∅ T := by
    intro hcomplete
    apply hxNoB
    exact singleton_absorberForbidden_third_mem_bankSupport
      (out_fst_ne_snd_of_mem_graphEdges he) w hAvoid hcomplete
  have hTA : T ∈ (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available := by
    apply mem_legalAvailable_iff.mpr
    refine ⟨mem_outsideAvailableTriangles_iff.mpr ⟨hTnotB, hAvoid⟩, ?_⟩
    have hpacking : IsPackingOn (∅ : TripleSystemOn V) := by
      intro _ _ _ R hR
      simp at hR
    have havoid : AvoidsForbidden (∅ : TripleSystemOn V)
        (absorberErdosForbiddenConfigurationsOn q B) := by
      intro S hSF hSempty
      obtain ⟨R, hRS⟩ := absorberErdosForbidden_nonempty hSF
      simpa using hSempty hRS
    rw [isLegalExtension_iff hpacking havoid]
    refine ⟨by simp, ?_, hnotComplete⟩
    simp [TriangleAvoidsGraph, coveredGraph]
  refine ⟨T, hTA, ?_, ?_⟩
  · exact third_mem_thirdVertexTriple _ _
  · have hs : s(e.out.1, e.out.2) ∈ tripleEdgeFinset T :=
      mk_mem_tripleEdgeFinset_iff.mpr
        ⟨left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
          out_fst_ne_snd_of_mem_graphEdges he⟩
    simpa only [T, e.out_eq] using hs

/-- The extension loss on a separated level is contained in the same
constant-size root obstruction set as the loss on `X`. -/
lemma initial_separated_extension_loss_subset_pattern_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X U : Finset V}
    {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hsep : AbsorberSeparatedLevel H X B U)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H) :
    U \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q U ⊆
      initialRootBadForPattern q H X B Q := by
  intro x hx
  have hxU := (mem_sdiff.mp hx).1
  have hxNotExtension := (mem_sdiff.mp hx).2
  by_cases hxSupport : x ∈ graphSupportFinset Q
  · exact mem_union_left _ hxSupport
  by_cases hxX : x ∈ X
  · have hxLossX : x ∈ X \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q X := by
      apply mem_sdiff.mpr
      refine ⟨hxX, ?_⟩
      intro hxExtX
      apply hxNotExtension
      rw [mem_iterationExtensionVertices_iff] at hxExtX ⊢
      exact ⟨hxU, hxExtX.2⟩
    exact initial_root_extension_loss_subset_pattern_bad hQ hxLossX
  · exact (hxNotExtension
      (separated_free_mem_initial_extensionVertices hsep hQ hxU hxX
        hxSupport)).elim

theorem card_initial_separated_extension_loss_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q h : ℕ} {H : SimpleGraph V} {X U : Finset V}
    {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hsep : AbsorberSeparatedLevel H X B U)
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H)
    (hQsupport : (graphSupportFinset Q).card ≤ h) :
    (U \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q U).card ≤
      h + h ^ 2 * 36 := by
  exact (card_le_card
      (initial_separated_extension_loss_subset_pattern_bad hsep hQ)).trans
    ((card_initialRootBadForPattern_le hroot Q).trans (by
      have hedge := card_graphEdges_le_graphSupportFinset_sq Q
      have hsq : (graphSupportFinset Q).card ^ 2 ≤ h ^ 2 := by
        gcongr
      omega))

/-- The padded absorber complement is initially typical on every level of an
arbitrary vortex once its smallest relevant level dominates the two uniform
ambient loss bounds. -/
theorem initial_vortex_isIterationTypical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {q h C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {B : TripleSystemOn V} {xi : ℝ≥0}
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    (hxi : xi ≤ 1)
    (hDegreeLevels : ∀ j : Fin (ell + 1), k.val ≤ j.val →
      (C + 1 : ℝ≥0) ≤ xi * (W.U j).card)
    (hExtensionLevels : ∀ j : Fin (ell + 1), k.val ≤ j.val →
      (h + h ^ 2 * (3 * C) : ℝ≥0) ≤ xi * (W.U j).card) :
    IsIterationTypical W k
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 1 xi h := by
  apply initialIterationTypical_of_loss_bounds W k
    (graphDifference (SimpleGraph.completeGraph V) H)
    ((absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available) xi hxi h
  · intro i hki v _hv
    have hsubset := initial_ambient_degree_loss_restrict_subset
      H (W.U i.castSucc) v
    have hcard := card_le_card hsubset
    have hambient := card_initial_ambient_degree_loss_le hdegree v
    have hcast :
        (((W.U i.castSucc \ neighborsIn
          (graphDifference (SimpleGraph.completeGraph V) H)
          (W.U i.castSucc) v).card : ℕ) : ℝ≥0) ≤ (C + 1 : ℝ≥0) := by
      exact_mod_cast hcard.trans hambient
    exact hcast.trans (hDegreeLevels i.castSucc hki)
  · intro i hki v _hv
    have hsubset := initial_ambient_degree_loss_restrict_subset
      H (W.U i.succ) v
    have hcard := card_le_card hsubset
    have hambient := card_initial_ambient_degree_loss_le hdegree v
    have hcast :
        (((W.U i.succ \ neighborsIn
          (graphDifference (SimpleGraph.completeGraph V) H)
          (W.U i.succ) v).card : ℕ) : ℝ≥0) ≤ (C + 1 : ℝ≥0) := by
      exact_mod_cast hcard.trans hambient
    exact hcast.trans (hDegreeLevels i.succ (by
      change k.val ≤ i.val + 1
      omega))
  · intro i hki iStar hiStar Q hQ _hQsupported hQcard
    have hsubset := initial_ambient_extension_loss_restrict_subset
      ((absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available) Q (W.U iStar)
    have hcardSubset := card_le_card hsubset
    have hambient := card_initial_ambient_extension_loss_le
      (q := q) hdegree hbankSupport hQ hQcard
    have hcast :
        (((W.U iStar \ iterationExtensionVertices
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)).available Q
          (W.U iStar)).card : ℕ) : ℝ≥0) ≤
            (h + h ^ 2 * (3 * C) : ℝ≥0) := by
      exact_mod_cast hcardSubset.trans hambient
    have hkStar : k.val ≤ iStar.val := by
      rcases hiStar with rfl | rfl
      · exact hki
      · change k.val ≤ i.val + 1
        omega
    exact hcast.trans (hExtensionLevels iStar hkStar)

/-- Initial typicality for a vortex whose positive levels avoid the
nonroot absorber support.  Only level zero pays the coarse global absorber
bound; every positive level enjoys the sharp padded-root constants. -/
theorem initial_separated_vortex_isIterationTypical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {q h C : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V} {xi : ℝ≥0}
    (hseparated : ∀ j : Fin (ell + 1), j ≠ 0 →
      AbsorberSeparatedLevel H X B (W.U j))
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    (hxi : xi ≤ 1)
    (hDegreeAmbient : (C + 1 : ℝ≥0) ≤
      xi * (Fintype.card V : ℝ≥0))
    (hDegreeInner : ∀ j : Fin (ell + 1), j ≠ 0 →
      (15 : ℝ≥0) ≤ xi * (W.U j).card)
    (hExtensionAmbient : (h + h ^ 2 * (3 * C) : ℝ≥0) ≤
      xi * (Fintype.card V : ℝ≥0))
    (hExtensionInner : ∀ j : Fin (ell + 1), j ≠ 0 →
      (h + h ^ 2 * 36 : ℝ≥0) ≤ xi * (W.U j).card) :
    IsIterationTypical W 0
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 1 xi h := by
  apply initialIterationTypical_of_loss_bounds W 0
    (graphDifference (SimpleGraph.completeGraph V) H)
    ((absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available) xi hxi h
  · intro i _hki v _hv
    by_cases hi0 : i.castSucc = 0
    · have hnat := card_initial_ambient_degree_loss_le hdegree v
      have hcast :
          ((univ \ neighborsIn
            (graphDifference (SimpleGraph.completeGraph V) H) univ v).card :
              ℝ≥0) ≤ (C + 1 : ℝ≥0) := by
        exact_mod_cast hnat
      rw [hi0, W.root]
      simpa only [card_univ] using hcast.trans hDegreeAmbient
    · have hnat := card_initial_separated_degree_loss_le_fifteen
        (hseparated i.castSucc hi0) hroot v
      have hcast :
          (((W.U i.castSucc \ neighborsIn
            (graphDifference (SimpleGraph.completeGraph V) H)
            (W.U i.castSucc) v).card : ℕ) : ℝ≥0) ≤ (15 : ℝ≥0) := by
        exact_mod_cast hnat
      exact hcast.trans (hDegreeInner i.castSucc hi0)
  · intro i _hki v _hv
    have hi0 : i.succ ≠ (0 : Fin (ell + 1)) := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_succ, Fin.val_zero] at hval
      omega
    have hnat := card_initial_separated_degree_loss_le_fifteen
      (hseparated i.succ hi0) hroot v
    have hcast :
        (((W.U i.succ \ neighborsIn
          (graphDifference (SimpleGraph.completeGraph V) H)
          (W.U i.succ) v).card : ℕ) : ℝ≥0) ≤ (15 : ℝ≥0) := by
      exact_mod_cast hnat
    exact hcast.trans (hDegreeInner i.succ hi0)
  · intro i _hki iStar _hiStar Q hQ _hQsupported hQcard
    by_cases hi0 : iStar = 0
    · have hnat := card_initial_ambient_extension_loss_le
        (q := q) hdegree hbankSupport hQ hQcard
      have hcast :
          ((univ \ iterationExtensionVertices
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available Q univ).card :
              ℝ≥0) ≤ (h + h ^ 2 * (3 * C) : ℝ≥0) := by
        exact_mod_cast hnat
      rw [hi0, W.root]
      simpa only [card_univ] using hcast.trans hExtensionAmbient
    · have hnat := card_initial_separated_extension_loss_le
        (hseparated iStar hi0) hroot hQ hQcard
      have hcast :
          (((W.U iStar \ iterationExtensionVertices
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available Q
            (W.U iStar)).card : ℕ) : ℝ≥0) ≤
              (h + h ^ 2 * 36 : ℝ≥0) := by
        exact_mod_cast hnat
      exact hcast.trans (hExtensionInner iStar hi0)

/-- Initial typicality on a gradual vortex ending at the padded absorber
root.  The coarse global absorber bounds are used only away from the last
level; on the last level the sharp padded-root bounds give the constant
losses `15` and `h + h^2 * 36`. -/
theorem initial_gradual_vortex_isIterationTypical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {q h C : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V} {xi : ℝ≥0}
    (hell : 0 < ell)
    (hterminal : W.U (Fin.last ell) = X)
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    (hxi : xi ≤ 1)
    (hDegreeOuter : ∀ j : Fin (ell + 1), j ≠ Fin.last ell →
      (C + 1 : ℝ≥0) ≤ xi * (W.U j).card)
    (hDegreeRoot : (15 : ℝ≥0) ≤ xi * (X.card : ℝ≥0))
    (hExtensionOuter : ∀ j : Fin (ell + 1), j ≠ Fin.last ell →
      (h + h ^ 2 * (3 * C) : ℝ≥0) ≤ xi * (W.U j).card)
    (hExtensionRoot : (h + h ^ 2 * 36 : ℝ≥0) ≤
      xi * (X.card : ℝ≥0)) :
    IsIterationTypical W 0
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 1 xi h := by
  apply initialIterationTypical_of_loss_bounds W 0
    (graphDifference (SimpleGraph.completeGraph V) H)
    ((absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available) xi hxi h
  · intro i _hki v _hv
    have hnotLast : i.castSucc ≠ Fin.last ell := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_castSucc, Fin.val_last] at hval
      omega
    have hsubset := initial_ambient_degree_loss_restrict_subset
      H (W.U i.castSucc) v
    have hcard := card_le_card hsubset
    have hambient := card_initial_ambient_degree_loss_le hdegree v
    have hcast :
        (((W.U i.castSucc \ neighborsIn
          (graphDifference (SimpleGraph.completeGraph V) H)
          (W.U i.castSucc) v).card : ℕ) : ℝ≥0) ≤ (C + 1 : ℝ≥0) := by
      exact_mod_cast hcard.trans hambient
    exact hcast.trans (hDegreeOuter i.castSucc hnotLast)
  · intro i _hki v _hv
    by_cases hiLast : i.succ = Fin.last ell
    · have hnat := card_initial_root_degree_loss_le_fifteen hroot v
      have hcast :
          ((X \ neighborsIn
            (graphDifference (SimpleGraph.completeGraph V) H) X v).card :
              ℝ≥0) ≤ (15 : ℝ≥0) := by
        exact_mod_cast hnat
      rw [hiLast, hterminal]
      exact hcast.trans hDegreeRoot
    · have hsubset := initial_ambient_degree_loss_restrict_subset
        H (W.U i.succ) v
      have hcard := card_le_card hsubset
      have hambient := card_initial_ambient_degree_loss_le hdegree v
      have hcast :
          (((W.U i.succ \ neighborsIn
            (graphDifference (SimpleGraph.completeGraph V) H)
            (W.U i.succ) v).card : ℕ) : ℝ≥0) ≤ (C + 1 : ℝ≥0) := by
        exact_mod_cast hcard.trans hambient
      exact hcast.trans (hDegreeOuter i.succ hiLast)
  · intro i _hki iStar _hiStar Q hQ _hQsupported hQcard
    by_cases hiLast : iStar = Fin.last ell
    · have hnat := card_initial_root_extension_loss_le hroot hQ hQcard
      have hcast :
          ((X \ iterationExtensionVertices
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available Q X).card :
              ℝ≥0) ≤ (h + h ^ 2 * 36 : ℝ≥0) := by
        exact_mod_cast hnat
      rw [hiLast, hterminal]
      exact hcast.trans hExtensionRoot
    · have hsubset := initial_ambient_extension_loss_restrict_subset
        ((absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available) Q (W.U iStar)
      have hcardSubset := card_le_card hsubset
      have hambient := card_initial_ambient_extension_loss_le
        (q := q) hdegree hbankSupport hQ hQcard
      have hcast :
          (((W.U iStar \ iterationExtensionVertices
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available Q
            (W.U iStar)).card : ℕ) : ℝ≥0) ≤
              (h + h ^ 2 * (3 * C) : ℝ≥0) := by
        exact_mod_cast hcardSubset.trans hambient
      exact hcast.trans (hExtensionOuter iStar hiLast)

end

end Erdos207
