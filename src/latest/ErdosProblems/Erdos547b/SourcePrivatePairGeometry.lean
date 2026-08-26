/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePrivateCrossingPairs
import ErdosProblems.Erdos547b.SourceMarkedGroupStep

/-!
# Genuine cluster geometry of the simultaneous private-pair allocation

All intermediate clusters and both sides of every allocated matching edge
are actual partition indices. The disjointness is derived from the original
matching and partition, including disjointness across different groups.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePrivatePairGeometry

open Finset SimpleGraph
open Erdos547b.ZhaoSourcePrivateCrossingPairs Erdos547b.ZhaoSourceCleanCrossingAccess
open Erdos547b.ZhaoSourceCrossingClusters Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceMarkedAvailableSets Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoStability Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim616

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

theorem real_of_adj {x y : EvenPadding (Index W)}
    (h : (padGraph (reduced W)).Adj x y) : ∃ c : Index W, x = Sum.inl c := by
  cases x with
  | inl c => exact ⟨c, rfl⟩
  | inr d => exact (padGraph_not_adj_inr_left (reduced W) d y h).elim

theorem density_of_mem_V1 (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {x : EvenPadding (Index W)} (hx : x ∈ O.D.V1) :
    1 - 2 * (eta α : ℝ) < rootDensity W S (Sum.inl Q.A) x := by
  obtain ⟨e, he, h0 | h1⟩ := (mem_matchingSupport O.D.Min x).mp hx
  · subst x
    exact (O.min_density W Q S hα hα1 he).1
  · subst x
    exact (O.min_density W Q S hα hα1 he).2

theorem adjA_of_mem_V1 (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {x : EvenPadding (Index W)} (hx : x ∈ O.D.V1) :
    (padGraph (reduced W)).Adj x (Sum.inl Q.A) := by
  have hd := density_of_mem_V1 W Q S O hα hα1 hx
  have he := (parameter_bounds hα hα1).2.1
  exact ((S.source_rows W).supportA x (by linarith only [hd, he])).symm

abbrev pairWhole (e : MatchingEdge Q.claim67.M) := edgeWhole W Q e 0 ∪ edgeWhole W Q e 1

theorem pairWhole_disjoint (e f : MatchingEdge Q.claim67.M) (hef : e ≠ f) :
    Disjoint (pairWhole W Q e) (pairWhole W Q f) := by
  apply Finset.disjoint_union_left.mpr
  constructor <;> apply Finset.disjoint_union_right.mpr
  · exact ⟨edgeWhole_cross_disjoint W Q e f hef 0 0,
      edgeWhole_cross_disjoint W Q e f hef 0 1⟩
  · exact ⟨edgeWhole_cross_disjoint W Q e f hef 1 0,
      edgeWhole_cross_disjoint W Q e f hef 1 1⟩

theorem center_disjoint_available (c : Index W) (hc : Sum.inl c ∈ O.D.V1)
    (e : MatchingEdge Q.claim67.M) (he : e ∈ availableEdges W Q S O) :
    Disjoint (whole W c) (pairWhole W Q e) := by
  have heNot : e ∉ O.D.minEdges :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).1).1).2
  have hside : ∀ d, Disjoint (whole W c) (edgeWhole W Q e d) := by
    intro d
    have hne : Sum.inl c ≠ edgeVertex W Q e d := by
      intro h
      have hh : edgeVertex W Q e d ∈ O.D.V1 := by rw [← h]; exact hc
      exact heNot ((O.D.endpoint_mem_V1_iff e d).mp hh)
    have h := clusterVertices_disjoint (padAssignment (assignment W)) hne
    simpa only [whole, edgeWhole, clusterVertices_padAssignment, padCluster] using h
  exact Finset.disjoint_union_right.mpr ⟨hside 0, hside 1⟩

theorem orient_access_pair (c : Index W) (e : MatchingEdge Q.claim67.M)
    (he : e ∈ matchingAccessEdges (padGraph (reduced W)) (availableEdges W Q S O)
      (edgeVertex W Q) (Sum.inl c) (availableVertices W Q S O)) :
    ∃ X Y : Index W, (reduced W).Adj c X ∧ (reduced W).Adj Y X ∧
      whole W X ∪ whole W Y = pairWhole W Q e := by
  obtain ⟨v, hv⟩ := real_of_adj W (edge_pair_adj W Q e)
  obtain ⟨w, hw⟩ := real_of_adj W (edge_pair_adj W Q e).symm
  have hpair : (reduced W).Adj v w := by
    simpa only [hv, hw, padGraph_adj_inl] using edge_pair_adj W Q e
  have hwhole : pairWhole W Q e = whole W v ∪ whole W w := by
    change padCluster (clusterVertices (assignment W)) (edgeVertex W Q e 0) ∪
      padCluster (clusterVertices (assignment W)) (edgeVertex W Q e 1) = _
    rw [hv, hw]
    rfl
  simp only [matchingAccessEdges, Finset.mem_filter] at he
  rcases he.2 with h0 | h1
  · refine ⟨v, w, ?_, hpair.symm, hwhole.symm⟩
    simpa only [hv, padGraph_adj_inl] using h0.2
  · refine ⟨w, v, ?_, hpair, ?_⟩
    · simpa only [hw, padGraph_adj_inl] using h1.2
    · rw [hwhole, Finset.union_comm]

structure Geometry (C : Finset (EvenPadding (Index W))) where
  center : {x // x ∈ C} → Index W
  center_eq : ∀ x, x.1 = Sum.inl (center x)
  center_adj : ∀ x, (reduced W).Adj (center x) Q.A
  center_density : ∀ x, 1 - 2 * (eta α : ℝ) <
    rootDensity W S (Sum.inl Q.A) (Sum.inl (center x))
  edge : {x // x ∈ C} × Fin 4 → MatchingEdge Q.claim67.M
  edge_injective : Function.Injective edge
  edge_available : ∀ p, edge p ∈ availableEdges W Q S O
  X : {x // x ∈ C} × Fin 4 → Index W
  Y : {x // x ∈ C} × Fin 4 → Index W
  center_X : ∀ p, (reduced W).Adj (center p.1) (X p)
  Y_X : ∀ p, (reduced W).Adj (Y p) (X p)
  pair_eq : ∀ p, whole W (X p) ∪ whole W (Y p) = pairWhole W Q (edge p)
  center_pair_disjoint : ∀ x p, Disjoint (whole W (center x)) (whole W (X p) ∪ whole W (Y p))
  pairs_disjoint : ∀ p r, p ≠ r →
    Disjoint (whole W (X p) ∪ whole W (Y p)) (whole W (X r) ∪ whole W (Y r))

theorem geometry_of_representatives (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (C : Finset (EvenPadding (Index W))) (hCV1 : C ⊆ O.D.V1)
    (center : {x // x ∈ C} → Index W) (hcenter : ∀ x, x.1 = Sum.inl (center x))
    (f : {x // x ∈ C} × Fin 4 → MatchingEdge Q.claim67.M) (hf : Function.Injective f)
    (hallowed : ∀ p, f p ∈ matchingAccessEdges (padGraph (reduced W)) (availableEdges W Q S O)
      (edgeVertex W Q) p.1.1 (availableVertices W Q S O)) :
    Nonempty (Geometry W Q S O C) := by
  have haccess : ∀ p : {x // x ∈ C} × Fin 4,
      f p ∈ matchingAccessEdges (padGraph (reduced W)) (availableEdges W Q S O)
        (edgeVertex W Q) (Sum.inl (center p.1)) (availableVertices W Q S O) := by
    intro p
    rw [← hcenter p.1]
    exact hallowed p
  have horient : ∀ p : {x // x ∈ C} × Fin 4, ∃ X Y : Index W,
      (reduced W).Adj (center p.1) X ∧ (reduced W).Adj Y X ∧
        whole W X ∪ whole W Y = pairWhole W Q (f p) := by
    intro p
    exact orient_access_pair W Q S O (center p.1) (f p) (haccess p)
  choose X Y hCX hYX hpair using horient
  have hfavailable : ∀ p, f p ∈ availableEdges W Q S O := by
    intro p
    have h := hallowed p
    simp only [matchingAccessEdges, Finset.mem_filter] at h
    exact h.1
  refine ⟨{
    center := center
    center_eq := hcenter
    center_adj := ?_
    center_density := ?_
    edge := f
    edge_injective := hf
    edge_available := hfavailable
    X := X
    Y := Y
    center_X := hCX
    Y_X := hYX
    pair_eq := hpair
    center_pair_disjoint := ?_
    pairs_disjoint := ?_ }⟩
  · intro x
    simpa only [hcenter x, padGraph_adj_inl] using
      adjA_of_mem_V1 W Q S O hα hα1 (hCV1 x.2)
  · intro x
    rw [← hcenter x]
    exact density_of_mem_V1 W Q S O hα hα1 (hCV1 x.2)
  · intro x p
    rw [hpair p]
    exact center_disjoint_available W Q S O (center x)
      (hcenter x ▸ hCV1 x.2) (f p) (hfavailable p)
  · intro p r hpr
    rw [hpair p, hpair r]
    exact pairWhole_disjoint W Q (f p) (f r) (fun he => hpr (hf he))

theorem exists_geometry (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    ∃ C : Finset (EvenPadding (Index W)), C ⊆ O.D.V1 ∧ C ⊆ Q.claim67.O ∧
      C.card = crossingScale W ∧ Nonempty (Geometry W Q S O C) := by
  obtain ⟨C, hCV1, hCO, hcard, f, hf, hallowed⟩ :=
    exists_private_pairs W Q S O hα hα1 hhost horder hcross
  have hreal : ∀ x : {x // x ∈ C}, ∃ c : Index W, x.1 = Sum.inl c := by
    intro x
    exact real_of_adj W (adjA_of_mem_V1 W Q S O hα hα1 (hCV1 x.2))
  choose center hcenter using hreal
  exact ⟨C, hCV1, hCO, hcard,
    geometry_of_representatives W Q S O hα hα1 C hCV1 center hcenter f hf hallowed⟩

theorem Geometry.center_injective {C : Finset (EvenPadding (Index W))}
    (P : Geometry W Q S O C) : Function.Injective P.center := by
  intro x y h
  apply Subtype.ext
  rw [P.center_eq x, P.center_eq y, h]

theorem Geometry.centers_disjoint {C : Finset (EvenPadding (Index W))}
    (P : Geometry W Q S O C) (x y : {x // x ∈ C}) (hxy : x ≠ y) :
    Disjoint (whole W (P.center x)) (whole W (P.center y)) :=
  clusterVertices_disjoint (assignment W) (fun h => hxy (P.center_injective W Q S O h))

end Erdos547b.ZhaoSourcePrivatePairGeometry

#print axioms Erdos547b.ZhaoSourcePrivatePairGeometry.exists_geometry
#print axioms Erdos547b.ZhaoSourcePrivatePairGeometry.Geometry.centers_disjoint
