import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleDuplication

/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- Pointwise idempotence of a base-edge weight family on the base
hypergraph.  Real-valued indicator families satisfy this condition. -/
def BaseWeightsIdempotent
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y

/-- Equality of finite sets transports their membership subtypes. -/
def finsetMembershipEquivOfEq
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)

@[simp]
theorem finsetMembershipEquivOfEq_symm_val
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((finsetMembershipEquivOfEq h).symm a).1 = a.1 := by
  subst t
  rfl

/-- Transporting a function on a finite-set membership subtype amounts to
precomposing with the inverse membership transport. -/
theorem cast_finsetPi_apply
    {α G' : Type*} {s t : Finset α} (h : s = t)
    (f : {a : α // a ∈ s} → G')
    (a : {a : α // a ∈ t}) :
    cast
        (congrArg
          (fun u : Finset α =>
            ({a : α // a ∈ u} → G'))
          h)
        f a =
      f ((finsetMembershipEquivOfEq h).symm a) := by
  subst t
  rfl

/-- The forward map of `projectionEquiv` is the bundle projection. -/
@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

/-- A product is unchanged when its indexing map identifies factors whose
common value is idempotent. -/
theorem prod_comp_eq_prod_image_of_idempotent
    {α β M : Type*} [DecidableEq α] [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hw' :
          ∀ b ∈ s.image f, w b * w b = w b := by
        intro b hb
        exact hw b (by
          rw [Finset.image_insert]
          exact Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, ih hw',
        Finset.image_insert]
      by_cases hfa : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hfa]
        calc
          w (f a) * ∏ b ∈ s.image f, w b =
              w (f a) *
                (w (f a) *
                  ∏ b ∈ (s.image f).erase (f a), w b) := by
            rw [Finset.mul_prod_erase (s.image f) w hfa]
          _ =
              w (f a) *
                ∏ b ∈ (s.image f).erase (f a), w b := by
            rw [← mul_assoc,
              hw (f a) (by
                rw [Finset.image_insert]
                exact Finset.mem_insert_self _ _)]
          _ = ∏ b ∈ s.image f, w b :=
            Finset.mul_prod_erase (s.image f) w hfa
      · rw [Finset.prod_insert hfa]

/-- Two labelled sources produce the same doubled edge exactly when they
come from the same old edge and either have the same copy label or that old
edge is wholly contained in the shared edge.  Thus the latter two-copy
collision is the only multiplicity removed by `doubledEdges`. -/
theorem doubledEdgeOfSource_eq_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s t : B.DoubledEdgeSource g₀) :
    B.doubledEdgeOfSource g₀ s =
        B.doubledEdgeOfSource g₀ t ↔
      s.2.1 = t.2.1 ∧
        (s.1 = t.1 ∨ s.2.1 ⊆ g₀) := by
  classical
  constructor
  · intro hst
    have hgg : s.2.1 = t.2.1 := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀))
          hst
      simpa [doubledEdgeOfSource] using himage
    refine ⟨hgg, ?_⟩
    by_cases hcopy : s.1 = t.1
    · exact Or.inl hcopy
    · right
      have hedges :
          doubledEdge g₀ s.1 s.2.1 =
            doubledEdge g₀ t.1 s.2.1 := by
        simpa [doubledEdgeOfSource, hgg] using hst
      cases hs : s.1 <;> cases ht : t.1
      · exact False.elim (hcopy (by simp [hs, ht]))
      · exact
          (doubledEdge_false_eq_true_iff_subset
            g₀ s.2.1).1 (by
              simpa [hs, ht] using hedges)
      · exact
          (doubledEdge_false_eq_true_iff_subset
            g₀ s.2.1).1 (by
              simpa [hs, ht] using hedges.symm)
      · exact False.elim (hcopy (by simp [hs, ht]))
  · rintro ⟨hgg, hcopy⟩
    rcases hcopy with hcopy | hsubset
    · simp [doubledEdgeOfSource, hgg, hcopy]
    · simpa [doubledEdgeOfSource, hgg] using
        doubledEdge_copy_independent_of_subset
          g₀ hsubset s.1 t.1

/-- Evaluating a pulled-back base weight on a lifted occurrence edge agrees
with evaluating the original pulled-back weight on its labelled source. -/
theorem pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).pullbackBaseEdgeWeight A
        (doubledEdge g₀ copy g)
        (edgeTuple (doubledEdge g₀ copy g) x) =
      B.pullbackBaseEdgeWeight A g
        (fun v => x (doubledVertexLift g₀ copy v.1)) := by
  classical
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hd :
      doubledEdge g₀ copy g ∈
        (B.duplicateOutside g₀).edges := by
    exact
      (B.mem_doubledEdges_iff g₀
        (doubledEdge g₀ copy g)).2
        ⟨copy, g, hg, rfl⟩
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd,
    B.pullbackBaseEdgeWeight_of_mem A hgB]
  have himage :
      (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection =
        g.image B.projection := by
    exact B.image_doubledProjection_doubledEdge g₀ copy g
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨(doubledEdge g₀ copy g).image
        (B.duplicateOutside g₀).projection,
      (B.duplicateOutside g₀).projectedEdgeTuple hd
        (edgeTuple (doubledEdge g₀ copy g) x)⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB
        (fun v =>
          x (doubledVertexLift g₀ copy v.1))⟩
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
  let jleft :
      {j : J //
        j ∈ (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let v : {v : K // v ∈ g} :=
    (B.projectionEquiv hgB).symm j
  have hjv :
      (⟨B.projection v.1,
          Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}) = j := by
    exact
      (B.projectionEquiv hgB).apply_symm_apply j
  have hvlift :
      doubledVertexLift g₀ copy v.1 ∈
        doubledEdge g₀ copy g :=
    mem_doubledEdge g₀ copy g v.1 v.2
  have hpreimage :
      ((B.duplicateOutside g₀).projectionEquiv hd).symm jleft =
        ⟨doubledVertexLift g₀ copy v.1, hvlift⟩ := by
    apply ((B.duplicateOutside g₀).projectionEquiv hd).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    calc
      jleft.1 = j.1 := by
        exact
          finsetMembershipEquivOfEq_symm_val
            himage j
      _ = B.projection v.1 :=
        congrArg Subtype.val hjv.symm
      _ =
          (((B.duplicateOutside g₀).projectionEquiv hd)
            ⟨doubledVertexLift g₀ copy v.1,
              hvlift⟩).1 := by
        rw [projectionEquiv_apply_val,
          duplicateOutside_projection,
          doubledProjection_lift]
  unfold lhsInput rhsInput projectedEdgeTuple edgeTuple
  change
    x (((B.duplicateOutside g₀).projectionEquiv hd).symm
        jleft).1 =
      x (doubledVertexLift g₀ copy v.1)
  rw [hpreimage]

/-- The weight of an actual doubled occurrence edge at a fixed doubled
assignment. -/
noncomputable def doubledBundleEdgeFactor
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀)) : ℝ :=
  (B.duplicateOutside g₀).pullbackBaseEdgeWeight A d
    (edgeTuple d x)

/-- A source factor is the factor attached to its actual doubled edge. -/
theorem doubledBundleEdgeFactor_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledBundleEdgeFactor g₀ A x
        (B.doubledEdgeOfSource g₀ s) =
      B.pullbackBaseEdgeWeight A s.2.1
        (fun v =>
          x (doubledVertexLift g₀ s.1 v.1)) := by
  exact
    B.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
      g₀ A s.1 s.2.2 x

/-- Every actual doubled-edge factor is idempotent when the base weights
are idempotent. -/
theorem doubledBundleEdgeFactor_idempotent
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀))
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledBundleEdgeFactor g₀ A x d *
        B.doubledBundleEdgeFactor g₀ A x d =
      B.doubledBundleEdgeFactor g₀ A x d := by
  classical
  unfold doubledBundleEdgeFactor
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd]
  exact hA _ ((B.duplicateOutside g₀).projection_mem_base d hd) _

/-- For indicator base weights, the source-indexed doubled product is
exactly the ordinary bundle product of the duplicated bundle. -/
theorem doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    B.doubledSourceProduct g₀
        (B.pullbackBaseEdgeWeight A) x =
      (B.duplicateOutside g₀).bundleProduct
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  unfold doubledSourceProduct
  calc
    (∏ s : B.DoubledEdgeSource g₀,
        B.pullbackBaseEdgeWeight A s.2.1
          (fun v =>
            x (doubledVertexLift g₀ s.1 v.1))) =
        ∏ s : B.DoubledEdgeSource g₀,
          B.doubledBundleEdgeFactor g₀ A x
            (B.doubledEdgeOfSource g₀ s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact
        (B.doubledBundleEdgeFactor_doubledEdgeOfSource
          g₀ A x s).symm
    _ =
        ∏ d ∈
            (Finset.univ :
              Finset (B.DoubledEdgeSource g₀)).image
                (B.doubledEdgeOfSource g₀),
          B.doubledBundleEdgeFactor g₀ A x d := by
      apply prod_comp_eq_prod_image_of_idempotent
      intro d hd
      apply B.doubledBundleEdgeFactor_idempotent
        g₀ A hA x d
      simpa [doubledEdges] using hd
    _ =
        (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
      rfl

/-- Consequently the doubled Cauchy--Schwarz remainder moment is the
ordinary count of the duplicated bundle for pulled-back indicator
weights.  Downward closure and maximality ensure that this duplicated
bundle remains a downward-closed bundle of no larger order. -/
theorem doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) =
      (B.duplicateOutside g₀).bundleCount
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  have _hduplicateClosed :
      (B.duplicateOutside g₀).IsClosedUnderInclusion :=
    B.duplicateOutside_closed_of_maximal
      hclosed hg₀ hmax
  rw [B.doubledRemainderMoment_eq_mean_doubledSourceProduct]
  unfold bundleCount
  apply congrArg mean
  funext x
  exact
    B.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
      g₀ A hA x

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
