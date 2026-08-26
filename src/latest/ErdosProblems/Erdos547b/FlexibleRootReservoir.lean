/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59Part2Full
import ErdosProblems.Erdos547b.LargeClusterReservoir
import ErdosProblems.Erdos547b.FlexibleBadRoots

/-!
# Realizing a flexible forest arrow inside a quantitative root reservoir

The online conclusion of Lemma 5.9 records at most `rootSlack` forbidden
images for each source root.  Zhao's Lemma 6.5 then chooses all source roots
inside the actual high-degree reservoir `A₀` of a large cluster.  The Hall
argument below performs that choice and immediately realizes the graph copy;
the root map is not a caller-supplied premise.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoFlexibleRootReservoir

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoQuantitativeLargeClusters

universe u v

/-- Public `FlexibleEmbedding` realization lemma.  Hall chooses distinct
allowed images for the literal root finset, then the online certificate
constructs the actual rooted-target copy. -/
theorem _root_.Erdos547b.ZhaoProp57.FlexibleEmbedding.exists_realization_in_reservoir
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots : Finset A)
    (rootCluster target reservoir : Finset B) (slack : ℕ)
    (E : Erdos547b.ZhaoProp57.FlexibleEmbedding F G roots rootCluster
      target slack)
    (hreservoir : reservoir ⊆ rootCluster)
    (hcard : roots.card + slack ≤ reservoir.card) :
    ∃ rootImage : A → B,
      (∀ r ∈ roots, rootImage r ∈ reservoir) ∧
      Nonempty (Erdos547b.ZhaoProp57.RootedTargetEmbedding
        F G roots target rootImage) := by
  classical
  let choices : {r // r ∈ roots} → Finset B := fun r ↦
    reservoir \ E.bad r.1
  have hchoices (r : {r // r ∈ roots}) :
      roots.card ≤ (choices r).card := by
    have hinter : (reservoir ∩ E.bad r.1).card ≤ slack :=
      (Finset.card_le_card Finset.inter_subset_right).trans
        (E.card_bad r.2)
    have hpartition := Finset.card_sdiff_add_card_inter reservoir (E.bad r.1)
    change (reservoir \ E.bad r.1).card +
      (reservoir ∩ E.bad r.1).card = reservoir.card at hpartition
    dsimp only [choices]
    omega
  have hHall : ∀ S : Finset {r // r ∈ roots},
      S.card ≤ (S.biUnion choices).card := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      calc
        S.card ≤ Fintype.card {r // r ∈ roots} := Finset.card_le_univ S
        _ = roots.card := Fintype.card_coe roots
        _ ≤ (choices r).card := hchoices r
        _ ≤ (S.biUnion choices).card :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem choices hr)
  obtain ⟨selected, hselectedInjective, hselectedMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp hHall
  let rootImage : A → B := fun x ↦
    if hx : x ∈ roots then selected ⟨x, hx⟩ else default
  have hrootInjective : ∀ ⦃r q⦄, r ∈ roots → q ∈ roots →
      rootImage r = rootImage q → r = q := by
    intro r q hr hq heq
    have hselectedEq : selected ⟨r, hr⟩ = selected ⟨q, hq⟩ := by
      simpa [rootImage, hr, hq] using heq
    exact congrArg Subtype.val (hselectedInjective hselectedEq)
  have hrootReservoir : ∀ r ∈ roots, rootImage r ∈ reservoir := by
    intro r hr
    have hm := (Finset.mem_sdiff.mp (hselectedMem ⟨r, hr⟩)).1
    simpa [rootImage, hr] using hm
  have hrootGood : ∀ r ∈ roots, rootImage r ∉ E.bad r := by
    intro r hr
    have hm := (Finset.mem_sdiff.mp (hselectedMem ⟨r, hr⟩)).2
    simpa [rootImage, hr] using hm
  refine ⟨rootImage, hrootReservoir, ?_⟩
  exact E.realize rootImage hrootInjective
    (fun hr ↦ hreservoir (hrootReservoir _ hr)) hrootGood

/-- Quantitative-large-cluster specialization of the public flexible-arrow
realizer.  It returns an actual graph copy and records the literal degree of
every chosen root image. -/
theorem _root_.Erdos547b.ZhaoProp57.FlexibleEmbedding.exists_highDegree_realization
    {A : Type u} {B : Type v} {I : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype I] [DecidableEq I]
    (F : SimpleGraph A) (Gpair Gdegree : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gdegree.Adj]
    (roots : Finset A) (P : ClusterAssignment B I) (C : I)
    (threshold quota : ℕ)
    (hC : C ∈ largeClustersAtLeast P Gdegree threshold quota)
    (target : Finset B) (slack : ℕ)
    (E : Erdos547b.ZhaoProp57.FlexibleEmbedding F Gpair roots
      (clusterVertices P C) target slack)
    (hfit : roots.card + slack ≤ quota) :
    ∃ rootImage : A → B,
      (∀ r ∈ roots,
        rootImage r ∈ largeVertexReservoir P Gdegree threshold C) ∧
      (∀ r ∈ roots, threshold ≤ Gdegree.degree (rootImage r)) ∧
      Nonempty (Erdos547b.ZhaoProp57.RootedTargetEmbedding
        F Gpair roots target rootImage) := by
  have hcard : roots.card + slack ≤
      (largeVertexReservoir P Gdegree threshold C).card :=
    hfit.trans (largeVertexReservoir_card P Gdegree threshold quota hC)
  obtain ⟨rootImage, hmem, hcopy⟩ :=
    E.exists_realization_in_reservoir F Gpair roots (clusterVertices P C)
      target (largeVertexReservoir P Gdegree threshold C) slack
      (largeVertexReservoir_subset_cluster P Gdegree threshold C) hcard
  exact ⟨rootImage, hmem,
    fun r hr ↦ degree_of_mem_largeVertexReservoir P Gdegree threshold C
      (hmem r hr), hcopy⟩

/-- A flexible three-layer embedding can be realized with all roots in any
subreservoir that has room for the roots and the per-root exceptional loss.
The injective root map and the resulting copy are both constructed here. -/
theorem FlexibleThreeLayerEmbedding.exists_realization_in_reservoir
    {r b : ℕ} {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster clusterTarget matchingTarget reservoir : Finset B)
    (rootSlack specialSlack : ℕ)
    (E : FlexibleThreeLayerEmbedding F G rootCluster clusterTarget
      matchingTarget rootSlack specialSlack)
    (hreservoir : reservoir ⊆ rootCluster)
    (hcard : r + rootSlack ≤ reservoir.card)
    (special : Finset F.Vertex)
    (hspecial : special ⊆ F.oddVertices)
    (hspecialCard : special.card ≤ specialSlack) :
    ∃ rootImage : Fin r → B,
      Function.Injective rootImage ∧
      (∀ i, rootImage i ∈ reservoir) ∧
      Nonempty (ThreeLayerCopy F G rootImage special
        clusterTarget matchingTarget) := by
  classical
  let choices : Fin r → Finset B := fun i ↦ reservoir \ E.bad i
  have hchoices (i : Fin r) : r ≤ (choices i).card := by
    have hinter : (reservoir ∩ E.bad i).card ≤ rootSlack :=
      (Finset.card_le_card Finset.inter_subset_right).trans (E.card_bad i)
    have hpartition := Finset.card_sdiff_add_card_inter reservoir (E.bad i)
    change (reservoir \ E.bad i).card + (reservoir ∩ E.bad i).card =
      reservoir.card at hpartition
    dsimp only [choices]
    omega
  have hHall : ∀ S : Finset (Fin r), S.card ≤ (S.biUnion choices).card := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      calc
        S.card ≤ Fintype.card (Fin r) := Finset.card_le_univ S
        _ = r := Fintype.card_fin r
        _ ≤ (choices i).card := hchoices i
        _ ≤ (S.biUnion choices).card :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem choices hi)
  obtain ⟨rootImage, hrootInjective, hrootMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp hHall
  have hrootReservoir (i : Fin r) : rootImage i ∈ reservoir :=
    (Finset.mem_sdiff.mp (hrootMem i)).1
  have hrootGood (i : Fin r) : rootImage i ∉ E.bad i :=
    (Finset.mem_sdiff.mp (hrootMem i)).2
  refine ⟨rootImage, hrootInjective, hrootReservoir, ?_⟩
  exact E.realize special hspecial hspecialCard rootImage hrootInjective
    (fun i ↦ hreservoir (hrootReservoir i)) hrootGood

/-- Quantitative-large-cluster specialization.  Every selected root image
has literal host degree at least `threshold`, and the three-layer copy is an
actual output rather than a continuation hypothesis. -/
theorem FlexibleThreeLayerEmbedding.exists_highDegree_realization
    {r b : ℕ} {V : Type u} {I : Type v}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (F : OrderedBranchForest r b)
    (Gpair Gdegree : SimpleGraph V)
    [DecidableRel Gpair.Adj] [DecidableRel Gdegree.Adj]
    (P : ClusterAssignment V I) (A : I)
    (threshold quota : ℕ)
    (hA : A ∈ largeClustersAtLeast P Gdegree threshold quota)
    (clusterTarget matchingTarget : Finset V)
    (rootSlack specialSlack : ℕ)
    (E : FlexibleThreeLayerEmbedding F Gpair (clusterVertices P A)
      clusterTarget matchingTarget rootSlack specialSlack)
    (hfit : r + rootSlack ≤ quota)
    (special : Finset F.Vertex)
    (hspecial : special ⊆ F.oddVertices)
    (hspecialCard : special.card ≤ specialSlack) :
    ∃ rootImage : Fin r → V,
      Function.Injective rootImage ∧
      (∀ i, rootImage i ∈ largeVertexReservoir P Gdegree threshold A) ∧
      (∀ i, threshold ≤ Gdegree.degree (rootImage i)) ∧
      Nonempty (ThreeLayerCopy F Gpair rootImage special
        clusterTarget matchingTarget) := by
  have hcard : r + rootSlack ≤
      (largeVertexReservoir P Gdegree threshold A).card :=
    hfit.trans (largeVertexReservoir_card P Gdegree threshold quota hA)
  obtain ⟨rootImage, hinj, hmem, hcopy⟩ :=
    E.exists_realization_in_reservoir F Gpair (clusterVertices P A)
      clusterTarget matchingTarget
      (largeVertexReservoir P Gdegree threshold A) rootSlack specialSlack
      (largeVertexReservoir_subset_cluster P Gdegree threshold A) hcard
      special hspecial hspecialCard
  exact ⟨rootImage, hinj, hmem,
    fun i ↦ degree_of_mem_largeVertexReservoir P Gdegree threshold A (hmem i),
    hcopy⟩

/-- Concrete regular-pair forest embedding with all prescribed component
roots selected in a quantitative high-degree reservoir.  This composes the
honest bad-root construction with the Hall realizer above; neither a root
map nor a flexible-arrow/copy hypothesis remains in the interface. -/
theorem exists_orderedForestCopy_with_highDegreeRoots
    {m : ℕ} {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype I] [DecidableEq I]
    (F : Erdos547b.RegularPair.OrderedRootedForest m)
    (Gpair Gdegree : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gdegree.Adj]
    (P : ClusterAssignment B I) (A : I)
    (threshold quota : ℕ)
    (hA : A ∈ largeClustersAtLeast P Gdegree threshold quota)
    {rho : ℝ} (X Y : Fin m → Finset B) (slack : ℕ)
    (hunif : ∀ i, Gpair.IsUniform rho (X i) (Y i))
    (hrootUnif : ∀ i,
      Gpair.IsUniform rho (clusterVertices P A) (Y i))
    (hrho : rho ≤ 1)
    (hcapX : ∀ i, (F.size i : ℝ) + rho * #(X i) ≤
      (Gpair.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (Gpair.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootCap : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (Gpair.edgeDensity (clusterVertices P A) (Y i) - rho) * #(Y i))
    (hslack : rho * (#(clusterVertices P A) : ℝ) ≤ slack)
    (hrootOutside : ∀ z ∈ clusterVertices P A, ∀ i,
      z ∉ Erdos547b.RegularPair.cleanedSide Gpair rho (X i) (Y i) ∧
      z ∉ Erdos547b.RegularPair.cleanedSide Gpair rho (Y i) (X i))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (Erdos547b.RegularPair.cleanedSide Gpair rho (X i) (Y i) ∪
          Erdos547b.RegularPair.cleanedSide Gpair rho (Y i) (X i))
        (Erdos547b.RegularPair.cleanedSide Gpair rho (X k) (Y k) ∪
          Erdos547b.RegularPair.cleanedSide Gpair rho (Y k) (X k)))
    (hfit : m + slack ≤ quota) :
    ∃ C : F.graph.Copy Gpair,
      ∀ i : Fin m, threshold ≤ Gdegree.degree (C ⟨i, F.root i⟩) := by
  obtain ⟨E⟩ :=
    Erdos547b.ZhaoLemma614Full.exists_flexibleEmbedding_of_rootUniformPairs
      F Gpair (clusterVertices P A) X Y slack hunif hrootUnif hrho
      hcapX hcapY hrootCap hslack hrootOutside hdisjoint
  have hrootCard : (Erdos547b.ZhaoLemma614Full.ORF.roots F).card = m := by
    simp [Erdos547b.ZhaoLemma614Full.ORF.roots]
  have hfit' :
      (Erdos547b.ZhaoLemma614Full.ORF.roots F).card + slack ≤ quota := by
    simpa [hrootCard] using hfit
  obtain ⟨rootImage, _hmem, hdegree, R⟩ :=
    E.exists_highDegree_realization F.graph Gpair Gdegree
      (Erdos547b.ZhaoLemma614Full.ORF.roots F) P A threshold quota hA
      (Erdos547b.ZhaoLemma614Full.ORF.target F (fun i c ↦
        if c = 0 then Erdos547b.RegularPair.cleanedSide Gpair rho (X i) (Y i)
        else Erdos547b.RegularPair.cleanedSide Gpair rho (Y i) (X i)))
      slack hfit'
  obtain ⟨R⟩ := R
  refine ⟨R.copy, ?_⟩
  intro i
  have hi : (⟨i, F.root i⟩ : Σ i, Fin (F.size i)) ∈
      Erdos547b.ZhaoLemma614Full.ORF.roots F := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [R.map_root hi]
  exact hdegree _ hi

end Erdos547b.ZhaoFlexibleRootReservoir

#print axioms Erdos547b.ZhaoFlexibleRootReservoir.FlexibleThreeLayerEmbedding.exists_realization_in_reservoir
#print axioms Erdos547b.ZhaoFlexibleRootReservoir.FlexibleThreeLayerEmbedding.exists_highDegree_realization
#print axioms Erdos547b.ZhaoProp57.FlexibleEmbedding.exists_realization_in_reservoir
#print axioms Erdos547b.ZhaoProp57.FlexibleEmbedding.exists_highDegree_realization
#print axioms Erdos547b.ZhaoFlexibleRootReservoir.exists_orderedForestCopy_with_highDegreeRoots
