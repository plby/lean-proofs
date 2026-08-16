import Wikipedia.SzemeredisTheorem.Finite.CauchySchwarz
import Wikipedia.SzemeredisTheorem.Finite.ProductMean

/-!
# Hypergraph bundles and the counting-lemma decomposition

Tao's hypergraph counting lemma is proved after passing from one copy of
each vertex class to a *hypergraph bundle*.  A bundle has a finite set of
occurrence vertices, a finite family of occurrence edges, and a projection
to the base vertex classes which is injective on every occurrence edge.
The extra occurrence vertices record the copies created by repeated
Cauchy--Schwarz.

This file supplies the finite bundle object and the exact analytic
identities at one step of the double induction.  For a selected edge `g₀`,
the bundle count is split according to

```
edgeWeight = main + defect + uniform.
```

The uniform contribution is rewritten by freezing all variables outside
`g₀`.  The defect contribution is bounded by Cauchy--Schwarz; the second
factor is written exactly as an average with two independent copies of the
outside variables.  This is the doubled lower-rank bundle appearing in
Tao's proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A finite hypergraph bundle over a fixed finite base hypergraph `H`.
The projection is required to be injective on every bundle edge, and every
bundle edge projects to an edge of `H`. -/
structure HypergraphBundle
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  projection_injective_on_edge :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  projection_mem_base :
    ∀ g ∈ edges, g.image projection ∈ H

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- A bundle is closed under inclusion when every subedge of every bundle
edge is again a bundle edge. -/
def IsClosedUnderInclusion
    (B : HypergraphBundle J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges

/-- The order of a bundle is the largest cardinality of one of its edges.
The empty bundle has order zero. -/
def order (B : HypergraphBundle J K H) : ℕ :=
  B.edges.sup Finset.card

/-- Number of occurrence edges at one specified rank. -/
def edgeCountAtRank
    (B : HypergraphBundle J K H) (r : ℕ) : ℕ :=
  (B.edges.filter fun g => g.card = r).card

/-- Every edge cardinality is bounded by the order of the bundle. -/
theorem edge_card_le_order
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    g.card ≤ B.order := by
  exact Finset.le_sup hg

/-- Erase one occurrence edge while retaining the same projection. -/
def eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg)
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl

/-- Erasing an edge cannot increase bundle order. -/
theorem eraseEdge_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).order ≤ B.order := by
  unfold order eraseEdge
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order (Finset.mem_of_mem_erase hg)

/-- Erasing a rank-`r` edge removes exactly one edge from the rank-`r`
count. -/
theorem edgeCountAtRank_eraseEdge
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    {r : ℕ} (hr : g₀.card = r) :
    (B.eraseEdge g₀).edgeCountAtRank r =
      B.edgeCountAtRank r - 1 := by
  unfold edgeCountAtRank eraseEdge
  have hmem :
      g₀ ∈ B.edges.filter fun g => g.card = r :=
    Finset.mem_filter.mpr ⟨hg₀, hr⟩
  have hfilter :
      (B.edges.erase g₀).filter
          (fun g => g.card = r) =
        (B.edges.filter fun g => g.card = r).erase g₀ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    aesop
  rw [hfilter, Finset.card_erase_of_mem hmem]

/-- Erasing a maximum-cardinality edge from a downward-closed bundle
preserves downward closure. -/
theorem eraseEdge_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (_hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.eraseEdge g₀).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hfB : f ∈ B.edges :=
    hclosed hgB hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfB⟩
  intro hfg₀
  subst f
  have hcard₂ : g.card ≤ g₀.card :=
    hmax g hgB
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hfg hcard₂
  exact (Finset.mem_erase.mp hg).1 heq.symm

/-! ## Local tuples and pulled-back base weights -/

/-- Restriction of a full bundle assignment to one occurrence edge. -/
def edgeTuple
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1

/-- Projection gives a bijection from an occurrence edge to its image in
the base vertex set. -/
noncomputable def projectionEquiv
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w hvw
    apply Subtype.ext
    apply B.projection_injective_on_edge g hg v.2 w.2
    exact congrArg Subtype.val hvw
  · intro j
    obtain ⟨v, hv, hvj⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hvj

/-- Transport an occurrence-edge tuple to its projected base edge. -/
noncomputable def projectedEdgeTuple
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.projectionEquiv hg).symm j)

/-- A family of local weights indexed by all finite base edges. -/
abbrev BaseEdgeWeight
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ

/-- Pointwise unit-interval bounds on the edges of a base hypergraph. -/
def BaseWeightsInUnitInterval
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1

/-- Pull a base edge-weight family back along a bundle projection.  Values
away from the bundle edge family are set to one and are never used in the
bundle product. -/
noncomputable def pullbackBaseEdgeWeight
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.projectedEdgeTuple hg y)
  · exact 1

@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]

/-- Pullback preserves unit-interval bounds on every bundle edge. -/
theorem pullbackBaseEdgeWeight_unitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.pullbackBaseEdgeWeight A g y ∧
      B.pullbackBaseEdgeWeight A g y ≤ 1 := by
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

/-! ## Bundle products and normalized counts -/

/-- Unit-interval bounds on an ambient occurrence-edge weight family, on
the edges used by a bundle. -/
def WeightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1

/-- Pulling back a bounded base family gives a bounded bundle family. -/
theorem pullbackBaseEdgeWeight_weightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A) :
    B.WeightsInUnitInterval
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  exact B.pullbackBaseEdgeWeight_unitInterval A hA hg y

/-- Product of all local edge weights on one full bundle assignment. -/
noncomputable def bundleProduct
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (edgeTuple g x)

/-- Normalized count of a weighted hypergraph bundle. -/
noncomputable def bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.bundleProduct A)

theorem bundleProduct_nonneg
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    0 ≤ B.bundleProduct A x := by
  unfold bundleProduct
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (edgeTuple g x)).1

theorem bundleProduct_le_one
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    B.bundleProduct A x ≤ 1 := by
  unfold bundleProduct
  apply Finset.prod_le_one
  · intro g hg
    exact (hA g hg (edgeTuple g x)).1
  · intro g hg
    exact (hA g hg (edgeTuple g x)).2

theorem bundleCount_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    0 ≤ B.bundleCount A :=
  mean_nonneg (B.bundleProduct_nonneg hA)

theorem bundleCount_le_one
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    B.bundleCount A ≤ 1 :=
  mean_le_of_le_const (B.bundleProduct_le_one hA)

/-- Unit-interval bounds survive erasing an occurrence edge. -/
theorem WeightsInUnitInterval.eraseEdge
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    (B.eraseEdge g₀).WeightsInUnitInterval A := by
  intro g hg y
  exact hA g (Finset.mem_of_mem_erase hg) y

/-- The product left after removing one selected occurrence edge. -/
noncomputable def edgeRemainder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.eraseEdge g₀).bundleProduct A x

/-- Contribution obtained by placing a local function at one selected edge
and retaining all other bundle factors. -/
noncomputable def edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (edgeTuple g₀ x) * B.edgeRemainder g₀ A x)

/-- Factoring a selected edge out of the bundle product. -/
theorem bundleCount_eq_edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.bundleCount A =
      B.edgeContribution g₀ (A g₀) A := by
  unfold bundleCount edgeContribution edgeRemainder
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (edgeTuple g x)) hg₀).symm

/-- Exact main/defect/uniform decomposition at one selected edge. -/
theorem bundleCount_decompose_edge
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (hdecomp : ∀ y, A g₀ y = p + b y + c y) :
    B.bundleCount A =
      p * (B.eraseEdge g₀).bundleCount A +
        B.edgeContribution g₀ b A +
        B.edgeContribution g₀ c A := by
  rw [B.bundleCount_eq_edgeContribution A hg₀]
  unfold edgeContribution bundleCount
  calc
    mean (fun x : K → G =>
        A g₀ (edgeTuple g₀ x) *
          B.edgeRemainder g₀ A x) =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x +
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x +
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      apply congrArg mean
      funext x
      rw [hdecomp]
      ring
    _ =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      rw [mean_add, mean_add]
    _ =
        p * (B.eraseEdge g₀).bundleCount A +
          B.edgeContribution g₀ b A +
          B.edgeContribution g₀ c A := by
      rw [mean_smul]
      rfl

/-- A constant local term contributes that constant times the bundle count
with the selected edge erased. -/
theorem edgeContribution_const
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (p : ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ (fun _ => p) A =
      p * (B.eraseEdge g₀).bundleCount A := by
  unfold edgeContribution bundleCount
  rw [← mean_smul]
  rfl

/-! ## Freezing the outside variables -/

/-- Coordinates outside a selected occurrence edge. -/
abbrev EdgeComplement (g : Finset K) :=
  {v : K // v ∉ g}

/-- Split the occurrence-vertex set into a selected edge and its
complement. -/
noncomputable def edgeSumEquiv (g : Finset K) :
    {v : K // v ∈ g} ⊕ EdgeComplement g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g

/-- Split a full bundle assignment into its selected-edge and outside
coordinates. -/
noncomputable def splitEdgeEquiv
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (EdgeComplement g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (edgeSumEquiv g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        EdgeComplement g => G))

@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

/-- Recombining a selected-edge tuple and an outside tuple recovers the
selected-edge tuple on restriction. -/
@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp

/-- Fubini decomposition into selected-edge and outside assignments. -/
theorem mean_splitEdge
    [Fintype K] [Fintype G]
    (g : Finset K) (f : (K → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g} → G =>
        fun z : EdgeComplement g → G =>
          f ((splitEdgeEquiv g).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g} → G) ×
            (EdgeComplement g → G) =>
              f ((splitEdgeEquiv g).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv (splitEdgeEquiv g)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : {v : K // v ∈ g} → G =>
            fun z : EdgeComplement g → G =>
              f ((splitEdgeEquiv g).symm (y, z))))

/-- The remaining bundle product after fixing the selected edge tuple and
the outside tuple. -/
noncomputable def edgeRemainderFiber
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G) : ℝ :=
  B.edgeRemainder g₀ A
    ((splitEdgeEquiv g₀).symm (y, z))

/-- Conditional average of the remaining bundle product after the selected
edge tuple is fixed. -/
noncomputable def edgeRemainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.edgeRemainderFiber g₀ A y)

/-- A selected-edge contribution is the pairing of its local function with
the conditional average of all remaining factors. -/
theorem edgeContribution_eq_mean_mul_remainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (fun y =>
        q y * B.edgeRemainderAverage g₀ A y) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀]
  unfold mean₂ edgeRemainderAverage edgeRemainderFiber
  apply congrArg mean
  funext y
  simp only [edgeTuple_splitEdgeEquiv_symm]
  rw [mean_smul]

/-- Inner selected-edge correlation after all outside variables have been
frozen. -/
noncomputable def frozenEdgeCorrelation
    [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : EdgeComplement g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.edgeRemainderFiber g₀ A y z)

/-- The selected-edge contribution is the outside average of the
correlations obtained by freezing the outside variables. -/
theorem edgeContribution_eq_mean_frozenEdgeCorrelation
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (B.frozenEdgeCorrelation g₀ q A) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀, mean₂_comm]
  unfold frozenEdgeCorrelation edgeRemainderFiber mean₂
  apply congrArg mean
  funext z
  apply congrArg mean
  funext y
  change
    q (edgeTuple g₀
        ((splitEdgeEquiv g₀).symm (y, z))) *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z)) =
      q y *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z))
  rw [edgeTuple_splitEdgeEquiv_symm]

/-- Uniform control after freezing the outside variables controls the full
uniform contribution. -/
theorem abs_edgeContribution_le_of_frozen
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {ε : ℝ}
    (hfrozen :
      ∀ z, |B.frozenEdgeCorrelation g₀ q A z| ≤ ε) :
    |B.edgeContribution g₀ q A| ≤ ε := by
  rw [B.edgeContribution_eq_mean_frozenEdgeCorrelation]
  calc
    |mean (B.frozenEdgeCorrelation g₀ q A)| ≤
        mean (fun z =>
          |B.frozenEdgeCorrelation g₀ q A z|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _z : EdgeComplement g₀ → G => ε) :=
      mean_mono hfrozen
    _ = ε := mean_const _

/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

/-- The exact doubled moment created by Cauchy--Schwarz at a selected
edge. -/
noncomputable def doubledRemainderMoment
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.edgeRemainderAverage g₀ A y ^ 2)

theorem doubledRemainderMoment_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    0 ≤ B.doubledRemainderMoment g₀ A :=
  mean_nonneg fun _ => sq_nonneg _

/-- For unit-interval bundle factors, the conditional remainder average is
itself in the unit interval. -/
theorem edgeRemainderAverage_unitInterval
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G) :
    0 ≤ B.edgeRemainderAverage g₀ A y ∧
      B.edgeRemainderAverage g₀ A y ≤ 1 := by
  constructor
  · apply mean_nonneg
    intro z
    exact
      (B.eraseEdge g₀).bundleProduct_nonneg
        (hA.eraseEdge B g₀) _
  · apply mean_le_of_le_const
    intro z
    exact
      (B.eraseEdge g₀).bundleProduct_le_one
        (hA.eraseEdge B g₀) _

/-- For unit-interval factors, the doubled remainder moment is at most one.
This gives an ambient-size-independent absolute defect estimate. -/
theorem doubledRemainderMoment_le_one
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    B.doubledRemainderMoment g₀ A ≤ 1 := by
  unfold doubledRemainderMoment
  apply mean_le_of_le_const
  intro y
  have hy :=
    B.edgeRemainderAverage_unitInterval hA g₀ y
  nlinarith

/-- The doubled moment is exactly the average obtained by taking two
independent copies of every outside variable. -/
theorem doubledRemainderMoment_eq_mean₂_pair
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean₂ (fun y :
          {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          B.edgeRemainderFiber g₀ A y z.1 *
            B.edgeRemainderFiber g₀ A y z.2) := by
  unfold doubledRemainderMoment edgeRemainderAverage
  exact mean_inner_sq_eq_mean₂_pair
    (B.edgeRemainderFiber g₀ A)

/-- Cauchy--Schwarz bounds a selected-edge contribution by the local square
mass of its edge term times the doubled lower-rank remainder moment. -/
theorem edgeContribution_sq_le_localSquare_mul_doubled
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A ^ 2 ≤
      mean (fun y => q y ^ 2) *
        B.doubledRemainderMoment g₀ A := by
  rw [B.edgeContribution_eq_mean_mul_remainderAverage]
  exact mean_mul_sq_le_product q
    (B.edgeRemainderAverage g₀ A)

/-- Localized defect estimate.  Once the square mass of the defect on its
boundary base is at most `β` times the base mass, the only remaining factor
is the doubled lower-rank bundle moment. -/
theorem edgeContribution_sq_le_of_localized_defect
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (b base : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (β : ℝ)
    (hlocalized :
      mean (fun y => b y ^ 2) ≤
        β * mean base) :
    B.edgeContribution g₀ b A ^ 2 ≤
      (β * mean base) *
        B.doubledRemainderMoment g₀ A := by
  calc
    B.edgeContribution g₀ b A ^ 2 ≤
        mean (fun y => b y ^ 2) *
          B.doubledRemainderMoment g₀ A :=
      B.edgeContribution_sq_le_localSquare_mul_doubled
        g₀ b A
    _ ≤
        (β * mean base) *
          B.doubledRemainderMoment g₀ A :=
      mul_le_mul_of_nonneg_right hlocalized
        (B.doubledRemainderMoment_nonneg g₀ A)

/-- Absolute localized defect bound for unit-interval remaining factors.
The stronger doubled-moment form above is retained for the relative
double-induction estimate. -/
theorem edgeContribution_sq_le_of_localized_defect_unitInterval
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (b base : ({v : K // v ∈ g₀} → G) → ℝ)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    {β : ℝ} (hβ : 0 ≤ β)
    (hbase : ∀ y, 0 ≤ base y)
    (hlocalized :
      mean (fun y => b y ^ 2) ≤
        β * mean base) :
    B.edgeContribution g₀ b A ^ 2 ≤
      β * mean base := by
  calc
    B.edgeContribution g₀ b A ^ 2 ≤
        (β * mean base) *
          B.doubledRemainderMoment g₀ A :=
      B.edgeContribution_sq_le_of_localized_defect
        g₀ b base A β hlocalized
    _ ≤ β * mean base := by
      apply mul_le_of_le_one_right
      · exact mul_nonneg hβ (mean_nonneg hbase)
      · exact B.doubledRemainderMoment_le_one hA g₀

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
