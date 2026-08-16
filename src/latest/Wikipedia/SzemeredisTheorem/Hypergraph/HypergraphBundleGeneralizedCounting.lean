import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleIndicatorDuplication
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleFiltration

/-!
# Generalized counting for closed hypergraph bundles

This file packages the part of Tao's generalized counting argument which
is specific to hypergraph bundles.

There are two points which are easy to lose in a scalar recurrence.

* The defect at a selected maximal edge is localized to the product of
  the strict-boundary indicators.  Since those indicators already occur
  among the remaining bundle factors, idempotence lets us insert that
  boundary product without changing the contribution.
* After Cauchy--Schwarz, all remaining maximal-rank indicator factors may
  be discarded.  The resulting moment is the count of the duplicated
  lower-order bundle.  Its main-density product contains one copy of the
  strict boundary and two copies of every other lower-order edge.

The last section records a flexible numerical envelope for the ensuing
double induction.  It deliberately separates the same-rank density floor
`α` from the all-rank density floor `μ`: the defect term only loses powers
of `α`, while the common frozen-uniformity error may lose powers of `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Local strict-boundary products -/

/-- Restrict a tuple on `g` to a subedge `f`. -/
def restrictEdgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, hfg v.2⟩

omit [DecidableEq K] in
@[simp]
theorem restrictEdgeTuple_edgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (x : K → G) :
    restrictEdgeTuple hfg (edgeTuple g x) =
      edgeTuple f x := by
  rfl

/-- Product of all strict-boundary occurrence-edge weights, viewed as a
function of a tuple on the selected edge.  The subtype index retains the
proof that every factor really is a strict subedge of `g₀`. -/
noncomputable def strictBoundaryLocalProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.strictBoundary g₀).edges},
    A g.1
      (restrictEdgeTuple
        (((B.mem_strictBoundary_edges g₀ g.1).1
          g.2).2.1)
        y)

/-- The local strict-boundary product is exactly the ordinary bundle
product of the strict-boundary subbundle. -/
theorem strictBoundaryLocalProduct_edgeTuple
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
        (edgeTuple g₀ x) =
      (B.strictBoundary g₀).bundleProduct A x := by
  classical
  unfold strictBoundaryLocalProduct
  calc
    (∏ g :
        {g : Finset K //
          g ∈ (B.strictBoundary g₀).edges},
      A g.1
        (restrictEdgeTuple
          (((B.mem_strictBoundary_edges g₀ g.1).1
            g.2).2.1)
          (edgeTuple g₀ x))) =
        ∏ g :
          {g : Finset K //
            g ∈ (B.strictBoundary g₀).edges},
          A g.1 (edgeTuple g.1 x) := by
      apply Finset.prod_congr rfl
      intro g _hg
      apply congrArg (A g.1)
      exact restrictEdgeTuple_edgeTuple _ x
    _ =
        ∏ g ∈ (B.strictBoundary g₀).edges,
          A g (edgeTuple g x) :=
      Finset.prod_coe_sort
        (B.strictBoundary g₀).edges
        (fun g => A g (edgeTuple g x))
    _ = (B.strictBoundary g₀).bundleProduct A x := by
      rfl

/-- Every strict-boundary edge occurs in the erased remainder. -/
theorem strictBoundary_edges_subset_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges ⊆
      B.edges.erase g₀ := by
  intro g hg
  have hg' :=
    (B.mem_strictBoundary_edges g₀ g).1 hg
  exact Finset.mem_erase.mpr
    ⟨hg'.2.ne, hg'.1⟩

/-- Pointwise idempotence of an occurrence-edge weight family. -/
def WeightsIdempotent
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y

/-- Pullback preserves pointwise idempotence. -/
theorem pullbackBaseEdgeWeight_weightsIdempotent
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.WeightsIdempotent
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

/-- If `s ⊆ t` and all factors on `s` are idempotent, multiplying the
`t`-product by the `s`-product does not change it. -/
theorem prod_mul_prod_eq_right_of_subset_of_idempotent
    {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hat : a ∈ t :=
        hst (Finset.mem_insert_self a s)
      have hst' : s ⊆ t.erase a := by
        intro i hi
        exact Finset.mem_erase.mpr
          ⟨fun hia => ha (hia ▸ hi),
            hst (Finset.mem_insert_of_mem hi)⟩
      have hf' :
          ∀ i ∈ s, f i * f i = f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha]
      rw [← Finset.mul_prod_erase t f hat]
      calc
        (f a * ∏ i ∈ s, f i) *
              (f a * ∏ i ∈ t.erase a, f i) =
            (f a * f a) *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          ring
        _ =
            f a *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          rw [hf a (Finset.mem_insert_self a s)]
        _ = f a * ∏ i ∈ t.erase a, f i := by
          rw [ih (t.erase a) hst' hf']

/-- The strict-boundary product is already present in the selected-edge
remainder.  Thus an idempotent boundary product may be inserted for free. -/
theorem strictBoundaryLocalProduct_mul_edgeRemainder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
          (edgeTuple g₀ x) *
        B.edgeRemainder g₀ A x =
      B.edgeRemainder g₀ A x := by
  rw [B.strictBoundaryLocalProduct_edgeTuple]
  unfold edgeRemainder bundleProduct
  apply prod_mul_prod_eq_right_of_subset_of_idempotent
    (B.strictBoundary g₀).edges
    (B.edges.erase g₀)
    (fun g => A g (edgeTuple g x))
    (B.strictBoundary_edges_subset_erase g₀)
  intro g hg
  exact hA g
    (Finset.mem_of_mem_erase
      (B.strictBoundary_edges_subset_erase g₀ hg))
    (edgeTuple g x)

/-- Localizing a selected-edge function to the strict boundary does not
change its contribution.  This is the exact insertion used before the
localized defect estimate. -/
theorem edgeContribution_mul_strictBoundaryLocalProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A) :
    B.edgeContribution g₀ q A =
      B.edgeContribution g₀
        (fun y =>
          q y *
            B.strictBoundaryLocalProduct g₀ A y)
        A := by
  unfold edgeContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    B.strictBoundaryLocalProduct_mul_edgeRemainder
      g₀ A hA x]

/-! ## Main-product cancellation at a selected edge -/

/-- Product of the lower-order main densities which do not lie in the
selected edge. -/
noncomputable def lowerExteriorMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)

/-- Product of the main densities on the erased edges which are not
strictly lower than the selected edge.  Under maximality these are exactly
the other edges of the selected rank. -/
noncomputable def maximalRemainderMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)

/-- Projection preserves the cardinality of every occurrence edge. -/
theorem card_image_projection
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have hcard :=
    Fintype.card_congr (B.projectionEquiv hg)
  simpa using hcard.symm

/-- A uniform lower bound on the base densities gives the corresponding
power lower bound for every bundle main product. -/
theorem pow_card_edges_le_bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp : ∀ e ∈ H, a ≤ p e) :
    a ^ B.edges.card ≤ B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  calc
    a ^ B.edges.card =
        ∏ _g ∈ B.edges, a := by
      simp
    _ ≤
        ∏ g ∈ B.edges,
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        exact hp _ (B.projection_mem_base g hg)

/-- Nonnegative base densities give a nonnegative bundle main product. -/
theorem bundleMainProduct_nonneg
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e) :
    0 ≤ B.bundleMainProduct p := by
  unfold bundleMainProduct
  exact Finset.prod_nonneg fun g hg =>
    hp _ (B.projection_mem_base g hg)

/-- The lower-order main product splits into the strict boundary and the
lower-order exterior. -/
theorem bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
        B.lowerExteriorMainProduct g₀ p := by
  classical
  let s :=
    B.edges.filter
      (fun g => g.card < g₀.card)
  have hboundary :
      s.filter (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB, Finset.card_lt_card hgstrict⟩,
        hgstrict.1⟩
  have hexterior :
      s.filter (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g =>
            g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    tauto
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  unfold bundleMainProduct lowerExteriorMainProduct
  simp only [lowerOrder_edges, strictBoundary_edges]
  rw [← hboundary, ← hexterior]
  exact hsplit.symm

/-- The strict-boundary factor in the localized defect and the main
product of the duplicated lower-order bundle form the square of the full
lower-order main product.  This is the cancellation which prevents the
defect estimate from paying every lower-rank density a second time. -/
theorem boundary_mul_duplicateLower_main_eq_lowerOrder_sq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p *
        ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      ((B.lowerOrder g₀.card).bundleMainProduct p) ^ 2 := by
  rw [B.bundleMainProduct_duplicateOutside_lowerOrder
    g₀ p]
  rw [Finset.prod_pow]
  rw [B.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    g₀ p]
  unfold lowerExteriorMainProduct
  ring

/-- Erasing the selected edge leaves the lower-order product times the
product of the other edges at least as large as the selected edge. -/
theorem lowerOrder_mul_maximalRemainder_eq_erase_main
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p *
        B.maximalRemainderMainProduct g₀ p =
      (B.eraseEdge g₀).bundleMainProduct p := by
  classical
  have hlower :
      (B.edges.erase g₀).filter
          (fun g => g.card < g₀.card) =
        B.edges.filter
          (fun g => g.card < g₀.card) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_hne, hgB⟩, hgcard⟩
      exact ⟨hgB, hgcard⟩
    · rintro ⟨hgB, hgcard⟩
      exact ⟨⟨fun hgg₀ => by
        subst g
        exact Nat.lt_irrefl _ hgcard, hgB⟩,
        hgcard⟩
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      (B.edges.erase g₀)
      (fun g => g.card < g₀.card)
      (fun g => p (g.image B.projection))
  unfold bundleMainProduct maximalRemainderMainProduct
  simp only [lowerOrder_edges, eraseEdge_edges]
  rw [← hlower]
  exact hsplit

/-- Under maximality, every factor in `maximalRemainderMainProduct` is
another factor of exactly the selected rank. -/
theorem card_eq_selected_of_mem_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hg :
      g ∈ (B.edges.erase g₀).filter
        (fun f => ¬ f.card < g₀.card)) :
    g.card = g₀.card := by
  have hg' := Finset.mem_filter.mp hg
  exact Nat.le_antisymm
    (hmax g (Finset.mem_of_mem_erase hg'.1))
    (Nat.le_of_not_gt hg'.2)

/-- The number of other selected-rank edges is at most the number of
edges left after erasing the selected one. -/
theorem card_maximalRemainder_le_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    ((B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)).card ≤
        (B.edges.erase g₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- A same-rank density floor controls the entire maximal-rank remainder
product. -/
theorem pow_card_maximalRemainder_le
    (B : HypergraphBundle J K H)
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.maximalRemainderMainProduct g₀ p := by
  classical
  unfold maximalRemainderMainProduct
  calc
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card =
        ∏ _g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          a := by
      simp
    _ ≤
        ∏ g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        apply hp _ (B.projection_mem_base g
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1))
        rw [B.card_image_projection
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1)]
        exact B.card_eq_selected_of_mem_maximalRemainder
          hmax hg

/-! ## Discarding the other maximal-rank factors -/

/-- Pullbacks through two bundles with the same occurrence projection
agree on every edge common to the two bundles. -/
theorem pullbackBaseEdgeWeight_eq_of_projection_eq
    (B C : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hprojection : B.projection = C.projection)
    {g : Finset K}
    (hgB : g ∈ B.edges) (hgC : g ∈ C.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      C.pullbackBaseEdgeWeight A g y := by
  classical
  rw [B.pullbackBaseEdgeWeight_of_mem A hgB y,
    C.pullbackBaseEdgeWeight_of_mem A hgC y]
  have himage :
      g.image B.projection = g.image C.projection :=
    congrArg (fun q : K → J => g.image q) hprojection
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB y⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image C.projection,
      C.projectedEdgeTuple hgC y⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jB :
      {j : J // j ∈ g.image B.projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let vB := (B.projectionEquiv hgB).symm jB
  let vC := (C.projectionEquiv hgC).symm j
  have hjB : jB.1 = j.1 :=
    finsetMembershipEquivOfEq_symm_val himage j
  have hvB :
      B.projection vB.1 = jB.1 := by
    exact congrArg Subtype.val
      ((B.projectionEquiv hgB).apply_symm_apply jB)
  have hvC' :
      C.projection vC.1 = j.1 := by
    exact congrArg Subtype.val
      ((C.projectionEquiv hgC).apply_symm_apply j)
  have hvC :
      B.projection vC.1 = j.1 := by
    rw [hprojection]
    exact hvC'
  have hval : vB.1 = vC.1 :=
    B.projection_injective_on_edge g hgB
      vB.2 vC.2
      ((hvB.trans hjB).trans hvC.symm)
  unfold lhsInput rhsInput projectedEdgeTuple
  change y vB = y vC
  exact congrArg y (Subtype.ext hval)

/-- The doubled lower-order edge family is a subfamily of the full
doubled remainder edge family. -/
theorem doubledEdges_lowerOrder_subset
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.lowerOrder g₀.card).doubledEdges g₀ ⊆
      B.doubledEdges g₀ := by
  intro d hd
  obtain ⟨copy, g, hg, hgd⟩ :=
    ((B.lowerOrder g₀.card).mem_doubledEdges_iff
      g₀ d).1 hd
  apply (B.mem_doubledEdges_iff g₀ d).2
  refine ⟨copy, g, ?_, hgd⟩
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hg).1,
      ((B.mem_lowerOrder_edges g₀.card g).1
        hgLower).1⟩

/-- For pulled-back `[0,1]` weights, deleting every other maximal-rank
factor can only increase the doubled bundle product. -/
theorem duplicateOutside_bundleProduct_le_lowerOrder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleProduct
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  let C := B.duplicateOutside g₀
  let D := (B.lowerOrder g₀.card).duplicateOutside g₀
  have hDC : D.edges ⊆ C.edges := by
    simpa [C, D] using
      B.doubledEdges_lowerOrder_subset g₀
  have hprojection : C.projection = D.projection := by
    rfl
  unfold bundleProduct
  calc
    (∏ d ∈ C.edges,
        C.pullbackBaseEdgeWeight A
          d (edgeTuple d x)) ≤
        ∏ d ∈ D.edges,
          C.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
        hDC
      · intro d hd
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).1
      · intro d hd _hdD
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).2
    _ =
        ∏ d ∈ D.edges,
          D.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact C.pullbackBaseEdgeWeight_eq_of_projection_eq
        D A hprojection (hDC hd) hd (edgeTuple d x)

/-- **Maximal-factor discard.**  For indicator base weights, the exact
doubled remainder moment is bounded by the count of the duplicated
lower-order bundle. -/
theorem doubledRemainderMoment_pullback_le_lowerOrder
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  rw [B.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    hclosed hg₀ hmax A hAidempotent]
  unfold bundleCount
  apply mean_mono
  intro x
  exact B.duplicateOutside_bundleProduct_le_lowerOrder
    g₀ A hA01 x

/-- A localized defect square bound and the maximal-factor discard give
the source-faithful square-root defect estimate.  The two lower-order
counts in this statement are precisely the two outer-induction calls. -/
theorem abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlocalized :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) :
    |B.edgeContribution g₀ q
        (B.pullbackBaseEdgeWeight A)| ≤
      Real.sqrt
        ((β *
            (B.strictBoundary g₀).bundleCount
              ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) *
          ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
              (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)) := by
  let boundaryCount :=
    (B.strictBoundary g₀).bundleCount
      ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)
  let lowerDoubledCount :=
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
        (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)
  have hboundary0 : 0 ≤ boundaryCount := by
    apply (B.strictBoundary g₀).bundleCount_nonneg
    exact
      (B.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hlower0 : 0 ≤ lowerDoubledCount := by
    apply
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
    exact
      ((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hmoment0 :
      0 ≤ B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) :=
    B.doubledRemainderMoment_nonneg g₀
      (B.pullbackBaseEdgeWeight A)
  have hmoment :
      B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
        lowerDoubledCount :=
    B.doubledRemainderMoment_pullback_le_lowerOrder
      hclosed hg₀ hmax A hA01 hAidempotent
  have hsq :
      B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A) ^ 2 ≤
        (β * boundaryCount) * lowerDoubledCount := by
    calc
      B.edgeContribution g₀ q
            (B.pullbackBaseEdgeWeight A) ^ 2 ≤
          mean (fun y => q y ^ 2) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        B.edgeContribution_sq_le_localSquare_mul_doubled
          g₀ q (B.pullbackBaseEdgeWeight A)
      _ ≤
          (β * boundaryCount) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        mul_le_mul_of_nonneg_right hlocalized hmoment0
      _ ≤ (β * boundaryCount) * lowerDoubledCount :=
        mul_le_mul_of_nonneg_left hmoment
          (mul_nonneg hβ hboundary0)
  have hradicand :
      0 ≤ (β * boundaryCount) * lowerDoubledCount :=
    mul_nonneg (mul_nonneg hβ hboundary0) hlower0
  apply
    (sq_le_sq₀
      (abs_nonneg
        (B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hradicand]
  exact hsq

end HypergraphBundle

/-! ## Numerical envelope for the double induction -/

/-- A quantitative envelope for Tao's double induction on bundle order
and bundle size.

The recurrence has three pieces:

* the error already accumulated after erasing the selected edge;
* the localized defect error, controlled by two lower-order bundle calls;
* the common frozen-uniformity error.

The field `rankFloor` says that `μ d` is a common lower bound for every
density at rank at most `d`. -/
structure IsBundleCountingEnvelope
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  density_pos : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  defect_nonneg : ∀ d, 0 ≤ β d
  uniform_nonneg : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  rankFloor :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  error_nonneg :
    ∀ d n, 0 ≤ E d n
  error_mono_order :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  error_mono_card :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)

/-- The one-step increment appearing in a bundle-counting envelope. -/
noncomputable def bundleCountingStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

/-- Restatement of the envelope recurrence using the named increment. -/
theorem IsBundleCountingEnvelope.add_stepIncrement_le
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    E (d + 1) n +
        bundleCountingStepIncrement α β μ τ E d n ≤
      E (d + 1) (n + 1) := by
  simpa [bundleCountingStepIncrement, add_assoc] using hE.step d n

/-- Both lower-order correction factors in the envelope are nonnegative. -/
theorem IsBundleCountingEnvelope.lower_correction_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    0 ≤
      (1 + E d (n + 1)) *
        (1 + E d (2 * (n + 1))) := by
  exact mul_nonneg
    (by linarith [hE.error_nonneg d (n + 1)])
    (by linarith [hE.error_nonneg d (2 * (n + 1))])

end Wikipedia.SzemeredisTheorem
