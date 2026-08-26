import ErdosProblems.Erdos547.SeededSkewSetup
import ErdosProblems.Erdos547.ReducedSeedEmbedding
import ErdosProblems.Erdos547.StructuralRealScaling

/-!
# Embedding from strict reduced degrees and explicit scalar margins
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)
  {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}

noncomputable def partRatio (c : Fin 2) : ℝ :=
  ((P.farVertices c).card : ℝ) / (P.nearVertices c).card

theorem isContained_of_reduced_degrees (hT : T.IsTree) (R : EquitableRegularPartition G ε)
    (δ d η s L θ err scale : ℝ) (A : Fin 2 → ℝ) (M q : ℕ)
    (hε : 0 < ε) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2) (hεone : ε ≤ 1) (hclean : ε + 2 * δ < 1)
    (hη : 0 ≤ η) (hs : 0 < s) (hsone : s ≤ 1) (hL : 0 < L) (hθ : 0 < θ)
    (herr : 0 ≤ err) (hA : ∀ c, 0 < A c) (hscale : 0 < scale) (hM : 0 < M)
    (hnear : ∀ c, 0 < (P.nearVertices c).card) (hfar : ∀ c, 0 < (P.farVertices c).card)
    (v₀ : ↥R.clusters) (hlarge : scale * Fintype.card U < (R.reducedWeights d).degree v₀)
    (hminimum : ∀ i, scale * Fintype.card U / 2 < (R.reducedWeights d).degree i)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η) (hprivate : ε ≤ s * θ)
    (hεm : 1 ≤ ε * R.clusterSize) (hseed : (P.seeds.card : ℝ) ≤ ε * R.clusterSize)
    (hseedq : 2 * P.seeds.card ≤ q) (hbuffer : η * R.clusterSize ≤ (q : ℝ) / 2)
    (hvolume : M + 2 * q = R.clusterSize)
    (hsmall : (ℓ : ℝ) ≤ ε * R.clusterSize) (hℓtarget : (ℓ : ℝ) ≤ s / 4 * L)
    (hmass : ∀ c, A c ≤ scale * (P.nearVertices c).card - θ * R.clusters.card - 2 -
      4 * (δ * R.clusters.card))
    (hvariance : ∀ c, (ℓ : ℝ) * ((P.nearVertices c).card + (P.farVertices c).card) < err ^ 2)
    (hmeanNear : ∀ c, ((P.nearVertices c).card : ℝ) / A c + s * M ≤ (1 - s) * M)
    (hmeanFar : ∀ c, ((P.farVertices c).card : ℝ) / A c + s * M * P.partRatio c ≤
      (1 - s) * M * P.partRatio c)
    (herrorNear : err ≤ θ * (s * M)) (herrorFar : ∀ c, err ≤ θ * (s * M * P.partRatio c))
    (htarget : ∀ c, L * R.clusters.card ≤ s / 4 * (P.partRatio c * M * θ))
    (hBtypical : (R.clusterSize : ℝ) * ε ≤ M) (hQtypical : (R.clusterSize : ℝ) * ε ≤ q)
    (hseedForest : (P.seeds.card : ℝ) ≤ (d - 2 * ε - 2 * δ) * R.clusterSize)
    (hrootMargin : 12 * ε * R.clusterSize ≤ (θ - ε) * q) : T ⊑ G := by
  classical
  have hcount := P.four_part_count
  have hparts : ((P.nearVertices 0).card : ℝ) + (P.farVertices 0).card +
      (P.nearVertices 1).card + (P.farVertices 1).card ≤ Fintype.card U := by
    exact_mod_cast (show (P.nearVertices 0).card + (P.farVertices 0).card +
      (P.nearVertices 1).card + (P.farVertices 1).card ≤ Fintype.card U by omega)
  have hscaled := mul_le_mul_of_nonneg_left hparts hscale.le
  obtain ⟨a, b, σ₀, σ₁, hp, hσ₀, hσ₁⟩ := DPRS.exists_anchored_totals_scaled_of_strict_degree
    (R.reducedWeights d) v₀ (P.nearVertices 0).card (P.farVertices 0).card
    (P.nearVertices 1).card (P.farVertices 1).card (hnear 0) (hfar 0) (hnear 1) (hfar 1)
    scale hscale (hscaled.trans_lt hlarge) (fun i ↦ by linarith only [hscaled, hminimum i])
  let σ : ∀ c, DPRS.SkewMatching (R.reducedGraph d) (P.partRatio c) := DPRS.twoSkewFamily σ₀ σ₁
  let anchor : Fin 2 → ↥R.clusters := ![a, b]
  have hanchor (c c' : Fin 2) (hcc : c ≠ c') :
      (R.reducedGraph d).Adj (anchor c) (anchor c') := by
    fin_cases c <;> fin_cases c'
    · exact (hcc rfl).elim
    · exact hp.adjacent
    · exact hp.adjacent.symm
    · exact (hcc rfl).elim
  have hγ (c : Fin 2) : 0 < P.partRatio c :=
    div_pos (by exact_mod_cast hfar c) (by exact_mod_cast hnear c)
  have htotal (c : Fin 2) : (σ c).total = scale * ((P.nearVertices c).card + (P.farVertices c).card) := by
    fin_cases c
    · exact hσ₀
    · exact hσ₁
  have hout (c : Fin 2) : (∑ i, (σ c).outLoad i) = scale * (P.nearVertices c).card :=
    (σ c).sum_outLoad_of_part_total (by exact_mod_cast hnear c) scale (htotal c)
  have hfitW (c : Fin 2) : (σ c).Fits (R.reducedWeights d) (anchor c) :=
    hp.two_family_fits c
  have hfit (c : Fin 2) (i : ↥R.clusters) : (σ c).outLoad i ≤
      (G.edgeDensity (anchor c).val i.val : ℝ) :=
    (hfitW c i).trans (R.reduced_weight_le_density d (anchor c) i)
  have hjoint (i : ↥R.clusters) : (σ 0).outLoad i + (σ 1).outLoad i ≤
      max (G.edgeDensity (anchor 0).val i.val : ℝ) (G.edgeDensity (anchor 1).val i.val : ℝ) :=
    (hp.joint i).trans (max_le_max (R.reduced_weight_le_density d a i) (R.reduced_weight_le_density d b i))
  obtain ⟨Q, buffer, hQB⟩ := R.exists_cluster_reservoirs q (by omega)
  let B := fun i : ↥R.clusters ↦ i.val \ (Q i ∪ buffer i)
  have hB (i : ↥R.clusters) : B i ⊆ i.val := Finset.sdiff_subset
  have hQ (i : ↥R.clusters) : Q i ⊆ i.val := (hQB i).1
  have hBsize (i : ↥R.clusters) : (B i).card = M := by
    have hh := (hQB i).2.2.2.2.2
    change (B i).card = R.clusterSize - 2 * q at hh
    omega
  have hQsize (i : ↥R.clusters) : (Q i).card = q := (hQB i).2.2.1
  have hBQ (i : ↥R.clusters) : Disjoint (B i) (Q i) := by
    apply Finset.disjoint_left.mpr
    intro v hv hqv
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hqv)
  obtain ⟨seed, hseedData⟩ := P.exists_reduced_seed_copy hT R δ d hδ hεδ hεone hclean
    anchor hanchor B Q hB hQ (fun i ↦ by simpa only [hBsize] using hBtypical)
    (fun i ↦ by simpa only [hQsize] using hQtypical)
    (fun c ↦ Finset.card_pos.mp (hnear c)) hseedForest
  let D := fun S : ↥P.shrubs ↦ Classical.choice (P.nonempty_shrub_root_data hT S.val S.property)
  let J := fun c ↦ (R.reducedGraph d).neighborFinset (anchor c)
  have hsupport (c : Fin 2) (i : ↥R.clusters) (hi : θ ≤ (σ c).outLoad i) : i ∈ J c :=
    ((R.reducedGraph d).mem_neighborFinset _ _).mpr
      ((hfitW c).adj_of_outLoad_pos i (hθ.trans_le hi))
  obtain ⟨H⟩ := P.exists_setup_from_typical_seed G (R.reducedGraph d) Subtype.val B Q anchor J seed D
    P.partRatio σ ε δ d η s L θ err A R.clusterSize M q
    hε hδ.le hη hs hsone hL hθ herr hA hM hγ hde hmargin hprivate hεm hseed hseedq hbuffer
    hvolume (fun i ↦ R.equal_size i.val i.property) R.index_disjoint hsmall hℓtarget
    (fun i j h ↦ R.reduced_pair d i j h) (fun i ↦ hp.two_family_capacity i) hfit hjoint hsupport
    (fun c ↦ by simpa only [hout c, Fintype.card_coe] using hmass c)
    hvariance hmeanNear hmeanFar herrorNear herrorFar
    (fun c ↦ by simpa only [Fintype.card_coe] using htarget c)
    hB hQ hBQ hBsize hQsize (fun z ↦ (hseedData z).1)
    (fun z ↦ by simpa only [Fintype.card_coe] using (hseedData z).2.1)
    (fun z ↦ by simpa only [Fintype.card_coe] using (hseedData z).2.2) hrootMargin
  exact H.isContained hT

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.isContained_of_reduced_degrees
