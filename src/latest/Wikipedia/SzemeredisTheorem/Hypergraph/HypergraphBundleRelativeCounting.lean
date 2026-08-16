import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleGeneralizedCounting

/-!
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Canonical pullbacks on subbundles -/

/-- On a subbundle with the same occurrence projection, pulling a base
weight back before or after passing to the subbundle gives the same
bundle product. -/
theorem bundleProduct_pullback_eq_of_subset_of_projection_eq
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G)
    (x : K → G) :
    C.bundleProduct (B.pullbackBaseEdgeWeight A) x =
      C.bundleProduct (C.pullbackBaseEdgeWeight A) x := by
  unfold bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  exact B.pullbackBaseEdgeWeight_eq_of_projection_eq
    C A hprojection (hCB hg) hg (edgeTuple g x)

/-- Count-level version of canonical pullback invariance. -/
theorem bundleCount_pullback_eq_of_subset_of_projection_eq
    [Fintype K] [Fintype G]
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G) :
    C.bundleCount (B.pullbackBaseEdgeWeight A) =
      C.bundleCount (C.pullbackBaseEdgeWeight A) := by
  unfold bundleCount
  apply congrArg mean
  funext x
  exact B.bundleProduct_pullback_eq_of_subset_of_projection_eq
    C hCB hprojection A x

/-- In particular, the erased count may always be written using the
canonical pullback of the erased bundle. -/
theorem eraseEdge_bundleCount_pullback
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (A : BaseEdgeWeight J G) :
    (B.eraseEdge g₀).bundleCount
        (B.pullbackBaseEdgeWeight A) =
      (B.eraseEdge g₀).bundleCount
        ((B.eraseEdge g₀).pullbackBaseEdgeWeight A) := by
  apply B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.eraseEdge g₀)
  · exact Finset.erase_subset _ _
  · rfl

/-! ## Structural bounds for the two outer-induction bundles -/

/-- The duplicated lower-order bundle remains downward closed. -/
theorem duplicateOutside_lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).IsClosedUnderInclusion := by
  apply (B.lowerOrder g₀.card).duplicateOutside_closed
    g₀
  intro g hg f hfg
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  have hfLower :
      f ∈ (B.lowerOrder g₀.card).edges :=
    B.lowerOrder_closed hclosed g₀.card
      hgLower hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfLower⟩
  intro hfg₀
  subst f
  have hgcard :
      g.card < g₀.card :=
    ((B.mem_lowerOrder_edges g₀.card g).1
      hgLower).2
  have hcardle : g₀.card ≤ g.card :=
    Finset.card_le_card hfg
  exact (Nat.not_le_of_gt hgcard) hcardle

/-- Duplicating the lower-order subbundle still has order strictly below
the selected edge. -/
theorem duplicateOutside_lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).order <
      g₀.card := by
  exact
    ((B.lowerOrder g₀.card).duplicateOutside_order_le
      g₀).trans_lt
      (B.lowerOrder_order_lt
        (Finset.card_pos.mpr hg₀))

/-- The duplicated lower-order bundle has at most twice as many edges as
the original bundle. -/
theorem card_duplicateOutside_lowerOrder_le
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card ≤
      2 * B.edges.card := by
  calc
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card =
        ((B.lowerOrder g₀.card).doubledEdges g₀).card := by
      rfl
    _ ≤
        2 *
          ((B.lowerOrder g₀.card).edges.erase g₀).card :=
      (B.lowerOrder g₀.card).card_doubledEdges_le g₀
    _ ≤ 2 * (B.lowerOrder g₀.card).edges.card :=
      Nat.mul_le_mul_left 2
        Finset.card_erase_le
    _ ≤ 2 * B.edges.card :=
      Nat.mul_le_mul_left 2
        (B.card_lowerOrder_edges_le g₀.card)

/-! ## Elementary main-product and induction helpers -/

/-- A bundle of positive order has a maximal occurrence edge which
realizes its order. -/
theorem exists_edge_card_eq_order
    (B : HypergraphBundle J K H)
    (horder : 0 < B.order) :
    ∃ g₀ ∈ B.edges,
      g₀.card = B.order ∧
        ∀ g ∈ B.edges, g.card ≤ g₀.card := by
  have hedges : B.edges.Nonempty := by
    by_contra hempty
    have hbe : B.edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [order, hbe] at horder
  obtain ⟨g₀, hg₀, hsup⟩ :=
    Finset.exists_mem_eq_sup B.edges hedges Finset.card
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · simpa [order] using hsup.symm
  · intro g hg
    rw [← hsup]
    exact Finset.le_sup hg

/-- A relative absolute-error estimate gives the corresponding upper
bound for the count. -/
theorem count_le_one_add_error_mul_main
    {count main error : ℝ}
    (herror : |count - main| ≤ error * main) :
    count ≤ (1 + error) * main := by
  have hleft : count - main ≤ |count - main| :=
    le_abs_self _
  calc
    count ≤ main + |count - main| := by
      linarith
    _ ≤ main + error * main :=
      add_le_add_right herror main
    _ = (1 + error) * main := by
      ring

/-- It is enough to check a density floor on the actual occurrence edges
of a bundle. -/
theorem pow_card_edges_le_bundleMainProduct_of_edges
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ g ∈ B.edges,
        a ≤ p (g.image B.projection)) :
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
        exact hp g hg

/-- The selected density together with all other selected-rank densities
is bounded below by one floor factor per edge of the original bundle. -/
theorem pow_card_edges_le_selected_mul_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^ B.edges.card ≤
      p (g₀.image B.projection) *
        B.maximalRemainderMainProduct g₀ p := by
  let s :=
    (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)
  have hscard :
      s.card ≤ (B.edges.erase g₀).card :=
    B.card_maximalRemainder_le_erase g₀
  have hpmax :
      a ^ s.card ≤
        B.maximalRemainderMainProduct g₀ p :=
    B.pow_card_maximalRemainder_le
      hmax p ha0 hp
  have hpow :
      a ^ (B.edges.erase g₀).card ≤
        a ^ s.card :=
    pow_le_pow_of_le_one ha0 ha1 hscard
  have hremain :
      a ^ (B.edges.erase g₀).card ≤
        B.maximalRemainderMainProduct g₀ p :=
    hpow.trans hpmax
  have hselected :
      a ≤ p (g₀.image B.projection) := by
    apply hp _ (B.projection_mem_base g₀ hg₀)
    exact B.card_image_projection hg₀
  have hselected0 :
      0 ≤ p (g₀.image B.projection) :=
    ha0.trans hselected
  calc
    a ^ B.edges.card =
        a * a ^ (B.edges.erase g₀).card := by
      rw [← Finset.card_erase_add_one hg₀,
        pow_succ, mul_comm]
    _ ≤
        p (g₀.image B.projection) *
          a ^ (B.edges.erase g₀).card :=
      mul_le_mul_of_nonneg_right hselected
        (pow_nonneg ha0 _)
    _ ≤
        p (g₀.image B.projection) *
          B.maximalRemainderMainProduct g₀ p :=
      mul_le_mul_of_nonneg_left hremain hselected0

/-- Neutral empty-edge weights make every order-zero bundle count exact. -/
theorem bundleCount_eq_bundleMainProduct_of_order_zero
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (horder : B.order = 0) :
    B.bundleCount (B.pullbackBaseEdgeWeight A) =
      B.bundleMainProduct p := by
  have hedgeEmpty :
      ∀ g ∈ B.edges, g = ∅ := by
    intro g hg
    apply Finset.card_eq_zero.mp
    exact Nat.le_zero.mp
      (horder ▸ B.edge_card_le_order hg)
  have hproduct :
      ∀ x : K → G,
        B.bundleProduct
            (B.pullbackBaseEdgeWeight A) x = 1 := by
    intro x
    unfold bundleProduct
    apply Finset.prod_eq_one
    intro g hg
    have hge : g = ∅ :=
      hedgeEmpty g hg
    subst g
    rw [B.pullbackBaseEdgeWeight_of_mem A hg]
    exact hAempty _
  have hmain :
      B.bundleMainProduct p = 1 := by
    unfold bundleMainProduct
    apply Finset.prod_eq_one
    intro g hg
    rw [hedgeEmpty g hg]
    simp [hpempty]
  rw [hmain]
  unfold bundleCount
  calc
    mean
        (B.bundleProduct
          (B.pullbackBaseEdgeWeight A)) =
        mean (fun _x : K → G => 1) := by
      apply congrArg mean
      funext x
      exact hproduct x
    _ = 1 := mean_const 1

end HypergraphBundle

/-! ## The analytic one-edge interface -/

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}

/-- The exact analytic output of one maximal-edge step in Tao's bundle
counting proof.  No induction estimate or density normalization is hidden
in this hypothesis. -/
def HasTaoBundleCountingStep
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (β : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, g₀ ∈ B.edges →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      |B.bundleCount (B.pullbackBaseEdgeWeight A) -
          p (g₀.image B.projection) *
            (B.eraseEdge g₀).bundleCount
              ((B.eraseEdge g₀).pullbackBaseEdgeWeight A)| ≤
        Real.sqrt
            (β g₀.card *
              (B.strictBoundary g₀).bundleCount
                ((B.strictBoundary g₀).pullbackBaseEdgeWeight A) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                  A)) +
          τ

/-! ## Full double induction -/

omit [DecidableEq G] in
/-- **Relative generalized bundle counting.**  A source-faithful
maximal-edge analytic step and a numerical envelope control every closed
bundle, uniformly in its occurrence-vertex type. -/
theorem abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
    [Nonempty G]
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hA01 :
      HypergraphBundle.BaseWeightsInUnitInterval H A)
    (_hAidempotent :
      HypergraphBundle.BaseWeightsIdempotent H A)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (hpLower :
      ∀ e ∈ H, α e.card ≤ p e)
    (hstep :
      HasTaoBundleCountingStep
        (H := H) A p β τ)
    (hE :
      IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount (B.pullbackBaseEdgeWeight A) -
        B.bundleMainProduct p| ≤
      E B.order B.edges.card *
        B.bundleMainProduct p := by
  let P : ℕ → ℕ → Prop :=
    fun d n =>
      ∀ (K' : Type) [Fintype K'] [DecidableEq K']
        (C : HypergraphBundle J K' H),
        C.order ≤ d →
        C.edges.card ≤ n →
        C.IsClosedUnderInclusion →
        |C.bundleCount (C.pullbackBaseEdgeWeight A) -
            C.bundleMainProduct p| ≤
          E d n * C.bundleMainProduct p
  have hp0 :
      ∀ e ∈ H, 0 ≤ p e := by
    intro e he
    exact (hE.density_pos e.card).le.trans
      (hpLower e he)
  unfold HasTaoBundleCountingStep at hstep
  have hP : ∀ d n, P d n := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihOrder =>
        intro n
        induction n using Nat.strong_induction_on with
        | h n ihCard =>
            dsimp [P]
            intro K' _instK' _decK' C hCd hCn hclosedC
            by_cases horderEq : C.order = d
            · by_cases hcardEq : C.edges.card = n
              · by_cases hd0 : d = 0
                · have hzero : C.order = 0 :=
                    horderEq.trans hd0
                  have hexact :=
                    C.bundleCount_eq_bundleMainProduct_of_order_zero
                      A p hAempty hpempty hzero
                  rw [hexact, sub_self, abs_zero]
                  exact mul_nonneg
                    (hE.error_nonneg d n)
                    (C.bundleMainProduct_nonneg p hp0)
                · have hdpos : 0 < d :=
                    Nat.pos_of_ne_zero hd0
                  obtain ⟨g₀, hg₀, hgcard, hmax⟩ :=
                    C.exists_edge_card_eq_order
                      (horderEq.symm ▸ hdpos)
                  have hgcardD : g₀.card = d :=
                    hgcard.trans horderEq
                  have hg₀ne : g₀.Nonempty := by
                    apply Finset.card_pos.mp
                    rw [hgcardD]
                    exact hdpos
                  obtain ⟨d₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hd0
                  have hn0 : n ≠ 0 := by
                    intro hn
                    have hcardzero : C.edges.card = 0 :=
                      hcardEq.trans hn
                    exact
                      (Finset.card_ne_zero.mpr
                        ⟨g₀, hg₀⟩) hcardzero
                  obtain ⟨n₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hn0
                  let Cerase := C.eraseEdge g₀
                  let Cboundary := C.strictBoundary g₀
                  let Clower :=
                    (C.lowerOrder g₀.card).duplicateOutside g₀
                  have hCeraseClosed :
                      Cerase.IsClosedUnderInclusion :=
                    C.eraseEdge_closed_of_maximal
                      hclosedC hg₀ hmax
                  have hCeraseOrder :
                      Cerase.order ≤ d₀ + 1 := by
                    exact
                      (C.eraseEdge_order_le g₀).trans_eq
                        horderEq
                  have hCeraseCard :
                      Cerase.edges.card ≤ n₀ := by
                    have hcard :
                        Cerase.edges.card = n₀ := by
                      simp [Cerase,
                        Finset.card_erase_of_mem hg₀,
                        hcardEq]
                    exact hcard.le
                  have hEraseIH :=
                    (ihCard n₀ (Nat.lt_succ_self n₀))
                      K' Cerase hCeraseOrder
                        hCeraseCard hCeraseClosed
                  have hCboundaryClosed :
                      Cboundary.IsClosedUnderInclusion :=
                    C.strictBoundary_closed hclosedC g₀
                  have hCboundaryOrder :
                      Cboundary.order ≤ d₀ := by
                    have hlt :
                        Cboundary.order < d₀ + 1 := by
                      simpa [Cboundary, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.strictBoundary_order_lt hg₀ne
                    omega
                  have hCboundaryCard :
                      Cboundary.edges.card ≤ n₀ + 1 := by
                    exact
                      (C.card_strictBoundary_edges_le g₀).trans_eq
                        hcardEq
                  have hBoundaryIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (n₀ + 1))
                      K' Cboundary hCboundaryOrder
                        hCboundaryCard hCboundaryClosed
                  have hClowerClosed :
                      Clower.IsClosedUnderInclusion := by
                    dsimp [Clower]
                    exact C.duplicateOutside_lowerOrder_closed
                      hclosedC g₀
                  have hClowerOrder :
                      Clower.order ≤ d₀ := by
                    have hlt :
                        Clower.order < d₀ + 1 := by
                      simpa [Clower, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.duplicateOutside_lowerOrder_order_lt
                          hg₀ne
                    omega
                  have hClowerCard :
                      Clower.edges.card ≤
                        2 * (n₀ + 1) := by
                    dsimp [Clower]
                    exact
                      (C.card_duplicateOutside_lowerOrder_le
                        g₀).trans_eq
                        (congrArg (fun m => 2 * m)
                          hcardEq)
                  have hLowerIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (2 * (n₀ + 1)))
                      (HypergraphBundle.DoubledOccurrenceVertex g₀)
                      Clower hClowerOrder
                        hClowerCard hClowerClosed
                  let mainErase :=
                    Cerase.bundleMainProduct p
                  let mainBoundary :=
                    Cboundary.bundleMainProduct p
                  let mainLower :=
                    Clower.bundleMainProduct p
                  let mainLowerOrder :=
                    (C.lowerOrder g₀.card).bundleMainProduct p
                  let mainMax :=
                    C.maximalRemainderMainProduct g₀ p
                  let mainC := C.bundleMainProduct p
                  let countErase :=
                    Cerase.bundleCount
                      (Cerase.pullbackBaseEdgeWeight A)
                  let countBoundary :=
                    Cboundary.bundleCount
                      (Cboundary.pullbackBaseEdgeWeight A)
                  let countLower :=
                    Clower.bundleCount
                      (Clower.pullbackBaseEdgeWeight A)
                  let p₀ :=
                    p (g₀.image C.projection)
                  have hmainErase0 : 0 ≤ mainErase := by
                    dsimp [mainErase, Cerase]
                    exact
                      (C.eraseEdge g₀).bundleMainProduct_nonneg p hp0
                  have hmainBoundary0 :
                      0 ≤ mainBoundary := by
                    dsimp [mainBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleMainProduct_nonneg p hp0
                  have hmainLower0 :
                      0 ≤ mainLower := by
                    dsimp [mainLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct_nonneg
                        p hp0
                  have hmainLowerOrder0 :
                      0 ≤ mainLowerOrder := by
                    dsimp [mainLowerOrder]
                    exact
                      (C.lowerOrder g₀.card).bundleMainProduct_nonneg p hp0
                  have hmainC0 : 0 ≤ mainC := by
                    dsimp [mainC]
                    exact C.bundleMainProduct_nonneg p hp0
                  have hcountBoundary0 :
                      0 ≤ countBoundary := by
                    dsimp [countBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleCount_nonneg
                        ((C.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
                            A hA01)
                  have hcountLower0 :
                      0 ≤ countLower := by
                    dsimp [countLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
                          (((C.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
                              A hA01)
                  have hcountBoundary :
                      countBoundary ≤
                        (1 + E d₀ (n₀ + 1)) *
                          mainBoundary :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hBoundaryIH
                  have hcountLower :
                      countLower ≤
                        (1 + E d₀
                            (2 * (n₀ + 1))) *
                          mainLower :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hLowerIH
                  have hcorrection0 :
                      0 ≤
                        (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) :=
                    hE.lower_correction_nonneg d₀ n₀
                  have hfirstCorrection0 :
                      0 ≤ 1 + E d₀ (n₀ + 1) := by
                    linarith
                      [hE.error_nonneg d₀ (n₀ + 1)]
                  have hβ0 :
                      0 ≤ β (d₀ + 1) :=
                    hE.defect_nonneg _
                  have hradicand :
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                        β (d₀ + 1) *
                            ((1 + E d₀ (n₀ + 1)) *
                              mainBoundary) *
                          ((1 + E d₀
                              (2 * (n₀ + 1))) *
                            mainLower) := by
                    calc
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            countLower :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            hcountBoundary hβ0)
                          hcountLower0
                      _ ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            ((1 + E d₀
                                (2 * (n₀ + 1))) *
                              mainLower) :=
                        mul_le_mul_of_nonneg_left
                          hcountLower
                          (mul_nonneg hβ0
                            (mul_nonneg
                              hfirstCorrection0
                              hmainBoundary0))
                  let rootCorrection :=
                    Real.sqrt
                      (β (d₀ + 1) *
                        (1 + E d₀ (n₀ + 1)) *
                        (1 + E d₀
                          (2 * (n₀ + 1))))
                  have hrootCorrection0 :
                      0 ≤ rootCorrection :=
                    Real.sqrt_nonneg _
                  have hmainBoundaryLower :
                      mainBoundary * mainLower =
                        mainLowerOrder ^ 2 := by
                    dsimp [mainBoundary, mainLower,
                      mainLowerOrder, Cboundary, Clower]
                    exact
                      C.boundary_mul_duplicateLower_main_eq_lowerOrder_sq
                        g₀ p
                  have hcoefficient0 :
                      0 ≤
                        β (d₀ + 1) *
                          (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) := by
                    rw [mul_assoc]
                    exact mul_nonneg hβ0 hcorrection0
                  have hsqrt :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        rootCorrection * mainLowerOrder := by
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          Real.sqrt
                            (β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                              ((1 + E d₀
                                  (2 * (n₀ + 1))) *
                                mainLower)) :=
                        Real.sqrt_le_sqrt hradicand
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                (mainBoundary * mainLower)) := by
                        congr 1
                        ring
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                mainLowerOrder ^ 2) := by
                        congr 1
                        rw [hmainBoundaryLower]
                      _ = rootCorrection * mainLowerOrder := by
                        dsimp [rootCorrection]
                        rw [Real.sqrt_mul hcoefficient0]
                        rw [Real.sqrt_sq hmainLowerOrder0]
                  have hαp :
                      α (d₀ + 1) ^ (n₀ + 1) ≤
                        p₀ * mainMax := by
                    dsimp [p₀, mainMax]
                    have hpow :=
                      C.pow_card_edges_le_selected_mul_maximalRemainder
                        hg₀ hmax p
                        (hE.density_pos g₀.card).le
                        (hE.density_le_one g₀.card)
                        (fun e he hcard =>
                          hpLower e he |>
                            fun h => by
                              simpa [hcard] using h)
                    simpa [hgcardD, hcardEq,
                      Nat.succ_eq_add_one] using hpow
                  have hαpowpos :
                      0 < α (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.density_pos _) _
                  have hmainFactor :
                      mainLowerOrder * (p₀ * mainMax) =
                        mainC := by
                    dsimp [mainLowerOrder, p₀, mainMax,
                      mainC, Cerase]
                    calc
                      (C.lowerOrder g₀.card).bundleMainProduct p *
                          (p (g₀.image C.projection) *
                            C.maximalRemainderMainProduct
                              g₀ p) =
                          ((C.lowerOrder g₀.card).bundleMainProduct p *
                            C.maximalRemainderMainProduct
                              g₀ p) *
                            p (g₀.image C.projection) := by
                        ring
                      _ =
                          (C.eraseEdge g₀).bundleMainProduct p *
                            p (g₀.image C.projection) := by
                        rw [
                          C.lowerOrder_mul_maximalRemainder_eq_erase_main
                            g₀ p]
                      _ = C.bundleMainProduct p :=
                        C.bundleMainProduct_eraseEdge_mul
                          p hg₀
                  have hsqrtNormalized :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        (rootCorrection /
                            α (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    have hscaled :
                        rootCorrection ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax) := by
                      calc
                        rootCorrection =
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              α (d₀ + 1) ^ (n₀ + 1) := by
                          field_simp
                        _ ≤
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              (p₀ * mainMax) :=
                          mul_le_mul_of_nonneg_left hαp
                            (div_nonneg hrootCorrection0
                              hαpowpos.le)
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          rootCorrection * mainLowerOrder :=
                        hsqrt
                      _ ≤
                          ((rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax)) *
                              mainLowerOrder :=
                        mul_le_mul_of_nonneg_right
                          hscaled hmainLowerOrder0
                      _ =
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        rw [← hmainFactor]
                        ring
                  have hμmain :
                      μ (d₀ + 1) ^ (n₀ + 1) ≤
                        mainC := by
                    dsimp [mainC]
                    have hpow :=
                      C.pow_card_edges_le_bundleMainProduct_of_edges
                        p (hE.floor_pos (d₀ + 1)).le
                        (fun g hg => by
                          have hcard :
                              g.card ≤ d₀ + 1 := by
                            exact
                              (C.edge_card_le_order hg).trans_eq
                                (by
                                  simpa [Nat.succ_eq_add_one] using
                                    horderEq)
                          exact
                            (hE.rankFloor hcard).trans
                              (hpLower _
                                (C.projection_mem_base g hg) |>
                                  fun h => by
                                    simpa [C.card_image_projection hg]
                                      using h))
                    simpa [hcardEq] using hpow
                  have hμpowpos :
                      0 < μ (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.floor_pos _) _
                  have huniformNormalized :
                      τ ≤
                        (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      τ =
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                              μ (d₀ + 1) ^ (n₀ + 1) := by
                        field_simp
                      _ ≤
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC :=
                        mul_le_mul_of_nonneg_left hμmain
                          (div_nonneg hE.uniform_nonneg
                            hμpowpos.le)
                  have hstepRaw :=
                    hstep K' C hclosedC hg₀ hmax
                  have hstepNormalized :
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                          Real.sqrt
                              (β (d₀ + 1) *
                                countBoundary * countLower) +
                            τ := by
                        simpa [p₀, countErase,
                          countBoundary, countLower,
                          Cerase, Cboundary, Clower,
                          hgcardD] using hstepRaw
                      _ ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              mainC +
                            (τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                              mainC :=
                        add_le_add hsqrtNormalized
                          huniformNormalized
                      _ =
                          (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        ring
                  have hp₀0 : 0 ≤ p₀ := by
                    dsimp [p₀]
                    exact hp0 _
                      (C.projection_mem_base g₀ hg₀)
                  have hmainEraseFactor :
                      p₀ * mainErase = mainC := by
                    dsimp [p₀, mainErase, mainC,
                      Cerase]
                    rw [mul_comm]
                    exact
                      C.bundleMainProduct_eraseEdge_mul
                        p hg₀
                  have hEraseNormalized :
                      p₀ *
                          |countErase - mainErase| ≤
                        E (d₀ + 1) n₀ * mainC := by
                    calc
                      p₀ *
                            |countErase - mainErase| ≤
                          p₀ *
                            (E (d₀ + 1) n₀ *
                              mainErase) :=
                        mul_le_mul_of_nonneg_left
                          hEraseIH hp₀0
                      _ =
                          E (d₀ + 1) n₀ * mainC := by
                        rw [← hmainEraseFactor]
                        ring
                  have hdecompose :
                      C.bundleCount
                            (C.pullbackBaseEdgeWeight A) -
                          mainC =
                        (C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase) := by
                    rw [← hmainEraseFactor]
                    ring
                  rw [hdecompose]
                  calc
                    |(C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase)| ≤
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          |p₀ * (countErase - mainErase)| :=
                      abs_add_le _ _
                    _ =
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          p₀ * |countErase - mainErase| := by
                      rw [abs_mul, abs_of_nonneg hp₀0]
                    _ ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC +
                          E (d₀ + 1) n₀ * mainC :=
                      add_le_add hstepNormalized
                        hEraseNormalized
                    _ =
                        (E (d₀ + 1) n₀ +
                            (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1))) *
                          mainC := by
                      ring
                    _ ≤
                        E (d₀ + 1) (n₀ + 1) *
                          mainC := by
                      apply mul_le_mul_of_nonneg_right
                      · simpa [rootCorrection,
                          bundleCountingStepIncrement,
                          add_assoc] using
                          hE.add_stepIncrement_le d₀ n₀
                      · exact hmainC0
              · have hcardLt : C.edges.card < n :=
                  lt_of_le_of_ne hCn
                    hcardEq
                have hsmall :=
                  (ihCard C.edges.card hcardLt)
                    K' C hCd le_rfl hclosedC
                have hmain0 :
                    0 ≤ C.bundleMainProduct p :=
                  C.bundleMainProduct_nonneg p hp0
                exact hsmall.trans
                  (mul_le_mul_of_nonneg_right
                    (hE.error_mono_card hCn) hmain0)
            · have horderLt : C.order < d :=
                lt_of_le_of_ne hCd
                  horderEq
              have hsmall :=
                (ihOrder C.order horderLt n)
                  K' C le_rfl hCn hclosedC
              have hmain0 :
                  0 ≤ C.bundleMainProduct p :=
                C.bundleMainProduct_nonneg p hp0
              exact hsmall.trans
                (mul_le_mul_of_nonneg_right
                  (hE.error_mono_order hCd) hmain0)
  exact
    (hP B.order B.edges.card)
      K B le_rfl le_rfl hclosed

end Wikipedia.SzemeredisTheorem
