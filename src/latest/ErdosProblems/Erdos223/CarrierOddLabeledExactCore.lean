import ErdosProblems.Erdos223.CarrierOddStableShape
import ErdosProblems.Erdos223.CosphericalTransfer

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223.CarrierOdd

noncomputable section

/-- The labeled coordinate certificate underlying the exact-cross weak
carrier theorem.  Unlike the existential `IsWeakCarrierSet` wrapper, this
retains the original part labels. -/
theorem exists_labeled_coordinate_certificate_of_axisPlane_cross_unit_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (seed : Fin p → Point (2 * p + 1))
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - baseCenter)))
    (hseedSupport : ∀ j,
      InAxisPlane j (coord.symm (seed j - baseCenter)))
    (hseedCross : ∀ {i j : Fin p}, i ≠ j → dist (seed i) (seed j) = 1)
    (hdist : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}) j,
      j ≠ part x → dist x.1 (seed j) = 1) :
    ∃ center : Point (2 * p + 1),
      (∀ x : {x : Point (2 * p + 1) // x ∈ A},
        InAxisPlane (part x) (coord.symm (x.1 - center))) ∧
      ∀ x : {x : Point (2 * p + 1) // x ∈ A},
        ‖coord.symm (x.1 - center)‖ ^ 2 = (1 : ℝ) / 2 := by
  let z : Fin p → ℝ := fun j ↦
    coord.symm (seed j - baseCenter) (axisIndex p)
  let radiusSq : Fin p → ℝ := fun j ↦
    ‖coord.symm (seed j - baseCenter)‖ ^ 2 - (z j) ^ 2
  have hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1 := by
    intro i j hij
    have h := axisPlane_energy_eq_of_dist_seed baseCenter coord hij
      (seed i) (seed j) (z j) (radiusSq j)
      (hseedSupport i) (hseedSupport j) rfl (by
        dsimp [radiusSq]
        ring) (hseedCross hij)
    simpa [z, radiusSq] using h
  obtain ⟨s, _hs, hcomplete⟩ :=
    exists_axis_weak_center_of_four_le_with_completion z radiusSq hp hcross
  let center := baseCenter + coord (axisVector p s)
  refine ⟨center, ?_, ?_⟩
  · intro x q hqf hqs hqa
    have hu := hsupport x q hqf hqs hqa
    have he : axisVector p s q = 0 := by simp [axisVector_apply, hqa]
    change (coord.symm (x.1 - center)) q = 0
    have hcoord : coord.symm (x.1 - center) =
        coord.symm (x.1 - baseCenter) - axisVector p s := by
      dsimp [center]
      rw [show x.1 - (baseCenter + coord (axisVector p s)) =
          (x.1 - baseCenter) - coord (axisVector p s) by abel]
      rw [map_sub, coord.symm_apply_apply]
    rw [hcoord, PiLp.sub_apply, hu, he, sub_zero]
  · intro x
    let u := coord.symm (x.1 - baseCenter)
    let e := axisVector p s
    let q := u (axisIndex p)
    let R := ‖u‖ ^ 2 - q ^ 2
    have henergy : ∀ j, j ≠ part x →
        R + radiusSq j + (q - z j) ^ 2 = 1 := by
      intro j hj
      exact axisPlane_energy_eq_of_dist_seed baseCenter coord hj.symm x.1 (seed j)
        (z j) (radiusSq j) (hsupport x) (hseedSupport j)
        rfl (by dsimp [radiusSq]; ring) (hdist x j hj)
    have hscalar : R + (q - s) ^ 2 = (1 : ℝ) / 2 :=
      hcomplete (part x) q R henergy
    have hcoord : coord.symm (x.1 - center) = u - e := by
      dsimp [center, u, e]
      rw [show x.1 - (baseCenter + coord (axisVector p s)) =
          (x.1 - baseCenter) - coord (axisVector p s) by abel]
      rw [map_sub, coord.symm_apply_apply]
    rw [hcoord, norm_sub_sq_real]
    have hinner : inner ℝ u e = s * q := by
      dsimp [e, axisVector, q]
      rw [EuclideanSpace.inner_single_right]
      simp
    have hnorme : ‖e‖ ^ 2 = s ^ 2 := by
      dsimp [e, axisVector]
      rw [EuclideanSpace.norm_single, Real.norm_eq_abs, sq_abs]
    rw [hinner, hnorme]
    dsimp [R, q] at hscalar
    nlinarith

/-- An exact cross-unit partition with triples admits a coordinate
certificate whose sphere index is exactly the supplied part function. -/
theorem exists_labeled_coordinate_certificate_of_exact_cross_unit_triples_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (part : {q : Point (2 * p + 1) // q ∈ A} → Fin p)
    (x : Fin p → Fin 3 → Point (2 * p + 1))
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      dist (x i a) (x j b) = 1)
    (hcomplete : ∀ (q : {q : Point (2 * p + 1) // q ∈ A}) j,
      j ≠ part q → ∀ a, dist q.1 (x j a) = 1) :
    ∃ (center : Point (2 * p + 1))
        (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1)),
      (∀ q : {q : Point (2 * p + 1) // q ∈ A},
        InAxisPlane (part q) (coord.symm (q.1 - center))) ∧
      ∀ q : {q : Point (2 * p + 1) // q ∈ A},
        ‖coord.symm (q.1 - center)‖ ^ 2 = (1 : ℝ) / 2 := by
  obtain ⟨baseCenter, coord, hcoord⟩ :=
    exists_axisPlane_coordinates_of_cross_unit_triples (by omega : 2 ≤ p)
      x hinj hcross
  let seed : Fin p → Point (2 * p + 1) := fun j ↦ x j 0
  obtain ⟨center, hsupport, hradius⟩ :=
    exists_labeled_coordinate_certificate_of_axisPlane_cross_unit_four hp
      baseCenter coord part seed
      (fun q ↦ hcoord (part q) q.1 (hcomplete q))
      (fun j ↦ hcoord j (seed j) (fun k hkj a ↦ hcross hkj.symm 0 a))
      (fun hij ↦ hcross hij 0 0)
      (fun q j hj ↦ hcomplete q j hj 0)
  exact ⟨center, coord, hsupport, hradius⟩

/-- The aligned stable exact core carries an explicit coordinate certificate
whose labels are the stable-partition colors. -/
theorem exists_labeled_coordinate_certificate_stableExactCore
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (hp : 4 ≤ p)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      (diameterGraph A).Adj (x i a) (x j b)) :
    ∃ (center : Point (2 * p + 1))
        (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1)),
      (∀ q : {q : Point (2 * p + 1) // q ∈ stableExactCore P x},
        InAxisPlane (stableExactCorePart P x q)
          (coord.symm (q.1 - center))) ∧
      ∀ q : {q : Point (2 * p + 1) // q ∈ stableExactCore P x},
        ‖coord.symm (q.1 - center)‖ ^ 2 = (1 : ℝ) / 2 := by
  let y : Fin p → Fin 3 → Point (2 * p + 1) := fun i a ↦ (x i a).1
  apply exists_labeled_coordinate_certificate_of_exact_cross_unit_triples_four
    hp (stableExactCorePart P x) y
  · intro i a b hab
    apply hinj i
    exact Subtype.ext hab
  · intro i j hij a b
    exact (diameterGraph_adj A (x i a) (x j b)).1 (hcross hij a b)
  · intro q j hj a
    let qA : {q : Point (2 * p + 1) // q ∈ A} :=
      ⟨q.1, stableExactCore_subset P x q.2⟩
    have hqmem := mem_stableExactCoreVertices_of_mem_core P x q
    have hqprop := (Finset.mem_filter.mp hqmem).2
    have hj' : j ≠ P.color qA := by
      simpa [stableExactCorePart, qA] using hj
    exact (diameterGraph_adj A qA (x j a)).1 (hqprop.2 j hj' a)

/-- Off-span version of cospherical transfer.  The prescribed center need
not lie in the anchor span: both its projection and the projection of a
cosphere center are the simplex circumcenter, and two Pythagoras identities
remove the normal offsets. -/
theorem dist_eq_of_cospherical_of_affineSpan_le_offspan
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} {F : Set E}
    (a : Fin (n + 1) → E) (ha : AffineIndependent ℝ a)
    (haF : ∀ i, a i ∈ F)
    (hFspan : F ⊆ affineSpan ℝ (Set.range a))
    (hcos : EuclideanGeometry.Cospherical F)
    (c : E) (r : ℝ)
    (har : ∀ i, dist (a i) c = r) :
    ∀ x ∈ F, dist x c = r := by
  let S : Affine.Simplex ℝ E n := ⟨a, ha⟩
  obtain ⟨d, s, hds⟩ := hcos
  have hdproj : ↑(S.orthogonalProjectionSpan d) = S.circumcenter := by
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S] using hds (a i) (haF i)
  have hcproj : ↑(S.orthogonalProjectionSpan c) = S.circumcenter := by
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S] using har i
  intro x hx
  have hxspan : x ∈ affineSpan ℝ (Set.range a) := hFspan hx
  have ha0span : a 0 ∈ affineSpan ℝ (Set.range a) :=
    mem_affineSpan ℝ ⟨0, rfl⟩
  have hxD := S.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    d (by simpa [S] using hxspan)
  have h0D := S.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    d (by simpa [S] using ha0span)
  rw [hdproj, hds x hx] at hxD
  rw [hdproj, hds (a 0) (haF 0),
    S.dist_circumcenter_eq_circumradius] at h0D
  have hxcirc : dist x S.circumcenter = S.circumradius := by
    have hcr : 0 ≤ S.circumradius := S.circumradius_nonneg
    nlinarith [dist_nonneg (x := x) (y := S.circumcenter)]
  have hxC := S.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    c (by simpa [S] using hxspan)
  have h0C := S.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    c (by simpa [S] using ha0span)
  rw [hcproj, hxcirc] at hxC
  rw [hcproj, S.dist_circumcenter_eq_circumradius, har 0] at h0C
  have hr0 : 0 ≤ r := by rw [← har 0]; positivity
  nlinarith [dist_nonneg (x := x) (y := c)]

/-- A labeled weak-carrier certificate on four affinely independent anchor
points in every part extends to cospherical full fibers contained in the
corresponding anchor spans. -/
theorem isWeakCarrierSet_of_fullRank_labeled_core
    {p : ℕ} {B C : Finset (Point (2 * p + 1))}
    (partB : {q : Point (2 * p + 1) // q ∈ B} → Fin p)
    (partC : {q : Point (2 * p + 1) // q ∈ C} → Fin p)
    (center : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (hcoreSupport : ∀ q : {q : Point (2 * p + 1) // q ∈ C},
      InAxisPlane (partC q) (coord.symm (q.1 - center)))
    (hcoreRadius : ∀ q : {q : Point (2 * p + 1) // q ∈ C},
      ‖coord.symm (q.1 - center)‖ ^ 2 = (1 : ℝ) / 2)
    (fiber : Fin p → Set (Point (2 * p + 1)))
    (hBfiber : ∀ q : {q : Point (2 * p + 1) // q ∈ B},
      q.1 ∈ fiber (partB q))
    (a : Fin p → Fin 4 → Point (2 * p + 1))
    (haC : ∀ i k, a i k ∈ C)
    (haPart : ∀ i k, partC ⟨a i k, haC i k⟩ = i)
    (haAI : ∀ i, AffineIndependent ℝ (a i))
    (haFiber : ∀ i k, a i k ∈ fiber i)
    (hfiberSpan : ∀ i, fiber i ⊆ affineSpan ℝ (Set.range (a i)))
    (hfiberCospherical : ∀ i, EuclideanGeometry.Cospherical (fiber i)) :
    IsWeakCarrierSet (p := p) B := by
  apply isWeakCarrierSet_of_coordinate_certificate_sq center coord partB
  · intro q k hkf hks hka
    let i := partB q
    have hqspan : q.1 ∈ affineSpan ℝ (Set.range (a i)) :=
      hfiberSpan i (hBfiber q)
    refine affineSpan_induction
      (p := fun z ↦ (coord.symm (z - center)) k = 0) hqspan ?_ ?_
    · intro z hz
      obtain ⟨j, rfl⟩ := hz
      have hs := hcoreSupport ⟨a i j, haC i j⟩
      rw [haPart i j] at hs
      exact hs k hkf hks hka
    · intro c u v w hu hv hw
      change (coord.symm ((c • (u - v) + w) - center)) k = 0
      rw [show (c • (u - v) + w) - center =
          c • ((u - center) - (v - center)) + (w - center) by module]
      rw [map_add, map_smul, map_sub, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, hu, hv, hw]
      simp
  · intro q
    let i := partB q
    have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
    have hrpos : 0 < (1 : ℝ) / Real.sqrt 2 := by positivity
    have hanchorDist : ∀ k, dist (a i k) center = 1 / Real.sqrt 2 := by
      intro k
      have hsq := hcoreRadius ⟨a i k, haC i k⟩
      have hn : 0 ≤ ‖coord.symm (a i k - center)‖ := norm_nonneg _
      have hnorm : ‖coord.symm (a i k - center)‖ = 1 / Real.sqrt 2 := by
        have htarget : (1 / Real.sqrt (2 : ℝ)) ^ 2 = (1 : ℝ) / 2 := by
          rw [div_pow, one_pow, hsqrt]
        nlinarith
      rw [dist_eq_norm, ← coord.symm.norm_map]
      exact hnorm
    have hdist : dist q.1 center = 1 / Real.sqrt 2 :=
      dist_eq_of_cospherical_of_affineSpan_le_offspan (a i) (haAI i)
        (haFiber i) (hfiberSpan i) (hfiberCospherical i)
        center (1 / Real.sqrt 2) hanchorDist q.1 (hBfiber q)
    rw [dist_eq_norm, ← coord.symm.norm_map] at hdist
    rw [hdist, div_pow, one_pow, hsqrt]

def stableRetainedVertices
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon) :
    Finset {q : Point (2 * p + 1) // q ∈ A} :=
  Finset.univ \ P.exceptional

def stableRetainedSet
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon) :
    Finset (Point (2 * p + 1)) :=
  (stableRetainedVertices P).map ⟨Subtype.val, Subtype.val_injective⟩

lemma stableRetainedSet_subset
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon) :
    stableRetainedSet P ⊆ A := by
  intro q hq
  obtain ⟨v, _hv, rfl⟩ := Finset.mem_map.mp hq
  exact v.2

def stableRetainedSetPart
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (q : {q : Point (2 * p + 1) // q ∈ stableRetainedSet P}) : Fin p :=
  P.color ⟨q.1, stableRetainedSet_subset P q.2⟩

def stableRetainedFiberPoints
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (i : Fin p) : Set (Point (2 * p + 1)) :=
  ↑((Stability.retainedFiber P.color P.exceptional i).map
    ⟨Subtype.val, Subtype.val_injective⟩)

lemma stableRetainedSet_mem_fiber
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (q : {q : Point (2 * p + 1) // q ∈ stableRetainedSet P}) :
    q.1 ∈ stableRetainedFiberPoints P (stableRetainedSetPart P q) := by
  obtain ⟨v, hv, heq⟩ := Finset.mem_map.mp q.2
  have hvne : v ∉ P.exceptional := (Finset.mem_sdiff.mp hv).2
  have hveq : v = ⟨q.1, stableRetainedSet_subset P q.2⟩ := by
    apply Subtype.ext
    exact heq
  change q.1 ∈ (Stability.retainedFiber P.color P.exceptional
    (stableRetainedSetPart P q)).map ⟨Subtype.val, Subtype.val_injective⟩
  apply Finset.mem_map.mpr
  refine ⟨v, ?_, heq⟩
  rw [Stability.mem_retainedFiber]
  refine ⟨?_, hvne⟩
  simpa [stableRetainedSetPart, hveq]

lemma stableExactCore_mem_retainedFiberPoints
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (q : {q : Point (2 * p + 1) // q ∈ stableExactCore P x}) :
    q.1 ∈ stableRetainedFiberPoints P (stableExactCorePart P x q) := by
  let qA : {q : Point (2 * p + 1) // q ∈ A} :=
    ⟨q.1, stableExactCore_subset P x q.2⟩
  have hqmem := mem_stableExactCoreVertices_of_mem_core P x q
  have hqprop := (Finset.mem_filter.mp hqmem).2
  change q.1 ∈ (Stability.retainedFiber P.color P.exceptional
    (stableExactCorePart P x q)).map ⟨Subtype.val, Subtype.val_injective⟩
  apply Finset.mem_map.mpr
  refine ⟨qA, ?_, rfl⟩
  rw [Stability.mem_retainedFiber]
  exact ⟨by simp [stableExactCorePart, qA], hqprop.1⟩

/-- If every retained fiber is cospherical and is spanned by four affinely
independent, correctly labeled points of the stable exact core, then the
entire retained set lies on the same labeled weak carrier. -/
theorem isWeakCarrierSet_stableRetainedSet_of_fullRankCore
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (hp : 4 ≤ p)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      (diameterGraph A).Adj (x i a) (x j b))
    (a : Fin p → Fin 4 → Point (2 * p + 1))
    (haCore : ∀ i k, a i k ∈ stableExactCore P x)
    (haPart : ∀ i k,
      stableExactCorePart P x ⟨a i k, haCore i k⟩ = i)
    (haAI : ∀ i, AffineIndependent ℝ (a i))
    (hspan : ∀ i, stableRetainedFiberPoints P i ⊆
      affineSpan ℝ (Set.range (a i)))
    (hcos : ∀ i, EuclideanGeometry.Cospherical
      (stableRetainedFiberPoints P i)) :
    IsWeakCarrierSet (p := p) (stableRetainedSet P) := by
  obtain ⟨center, coord, hsupport, hradius⟩ :=
    exists_labeled_coordinate_certificate_stableExactCore hp P x hinj hcross
  apply isWeakCarrierSet_of_fullRank_labeled_core
    (stableRetainedSetPart P) (stableExactCorePart P x)
    center coord hsupport hradius (stableRetainedFiberPoints P)
    (stableRetainedSet_mem_fiber P) a haCore haPart haAI
  · intro i k
    simpa [haPart i k] using
      stableExactCore_mem_retainedFiberPoints P x
        ⟨a i k, haCore i k⟩
  · exact hspan
  · exact hcos

/-- Stable-shape specialization of
`isWeakCarrierSet_stableRetainedSet_of_fullRankCore`: the explicit size
bound supplies cosphericity, so only the robust full-rank core anchors remain
as a geometric hypothesis. -/
theorem isWeakCarrierSet_stableRetainedSet_of_spanningCore
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (hp : 4 ≤ p)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      (diameterGraph A).Adj (x i a) (x j b))
    (a : Fin p → Fin 4 → Point (2 * p + 1))
    (haCore : ∀ i k, a i k ∈ stableExactCore P x)
    (haPart : ∀ i k,
      stableExactCorePart P x ⟨a i k, haCore i k⟩ = i)
    (haAI : ∀ i, AffineIndependent ℝ (a i))
    (hspan : ∀ i, stableRetainedFiberPoints P i ⊆
      affineSpan ℝ (Set.range (a i))) :
    IsWeakCarrierSet (p := p) (stableRetainedSet P) := by
  apply isWeakCarrierSet_stableRetainedSet_of_fullRankCore hp P x hinj hcross
    a haCore haPart haAI hspan
  intro i
  simpa [stableRetainedFiberPoints] using
    retainedFiber_cospherical_highOdd hp P hepsilon hlarge i

/-- A local robust-rank certificate: fiber `i` has a correctly labeled
affine basis already inside the stable exact core. -/
def HasSpanningCoreBasis
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (i : Fin p) : Prop :=
  ∃ a : Fin 4 → Point (2 * p + 1),
    (∀ k, a k ∈ stableExactCore P x) ∧
    (∀ k (h : a k ∈ stableExactCore P x),
      stableExactCorePart P x ⟨a k, h⟩ = i) ∧
    AffineIndependent ℝ a ∧
    stableRetainedFiberPoints P i ⊆ affineSpan ℝ (Set.range a)

lemma exists_spanningCoreFamily_iff
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A}) :
    (∃ a : Fin p → Fin 4 → Point (2 * p + 1),
      (∀ i k, a i k ∈ stableExactCore P x) ∧
      (∀ i k (h : a i k ∈ stableExactCore P x),
        stableExactCorePart P x ⟨a i k, h⟩ = i) ∧
      (∀ i, AffineIndependent ℝ (a i)) ∧
      ∀ i, stableRetainedFiberPoints P i ⊆
        affineSpan ℝ (Set.range (a i))) ↔
      ∀ i, HasSpanningCoreBasis P x i := by
  classical
  constructor
  · rintro ⟨a, haCore, haPart, haAI, hspan⟩ i
    exact ⟨a i, haCore i, haPart i, haAI i, hspan i⟩
  · intro h
    let a : Fin p → Fin 4 → Point (2 * p + 1) := fun i ↦
      Classical.choose (h i)
    have ha (i : Fin p) := Classical.choose_spec (h i)
    exact ⟨a, (fun i ↦ (ha i).1), (fun i ↦ (ha i).2.1),
      (fun i ↦ (ha i).2.2.1), fun i ↦ (ha i).2.2.2⟩

/-- Unconditional retained-core classifier under the explicit stable size
bound.  It produces aligned seed triples and either upgrades the full
retained set to a weak carrier or identifies the precise remaining defect:
there is no correctly labeled affine basis of every retained fiber inside
the exact core. -/
theorem exists_aligned_core_carrier_or_nonspanning
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (hp : 4 ≤ p)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card) :
    ∃ x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A},
      (∀ i a, x i a ∈
        Stability.retainedFiber P.color P.exceptional i) ∧
      (∀ i, Function.Injective (x i)) ∧
      (∀ {i j : Fin p}, i ≠ j → ∀ a b,
        (diameterGraph A).Adj (x i a) (x j b)) ∧
      (IsWeakCarrierSet (p := p) (stableRetainedSet P) ∨
        ¬ ∃ a : Fin p → Fin 4 → Point (2 * p + 1),
          (∀ i k, a i k ∈ stableExactCore P x) ∧
          (∀ i k (h : a i k ∈ stableExactCore P x),
            stableExactCorePart P x ⟨a i k, h⟩ = i) ∧
          (∀ i, AffineIndependent ℝ (a i)) ∧
          ∀ i, stableRetainedFiberPoints P i ⊆
            affineSpan ℝ (Set.range (a i))) := by
  have hseedLarge : ∀ j : Fin p,
      (3 * p) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card := by
    intro j
    have hcoeff : 3 * p ≤ 5 + (p - 1) * 3 := by omega
    exact (Nat.add_le_add_right
      (Nat.mul_le_mul_right ⌈epsilon * (A.card : ℝ)⌉₊ hcoeff) 3).trans
      (hlarge j)
  obtain ⟨x, hxmem, hxinj, hxcross⟩ :=
    exists_aligned_retained_cross_triples (diameterGraph A) P hepsilon
      (fun j ↦ by simpa using hseedLarge j)
  refine ⟨x, hxmem, hxinj, hxcross, ?_⟩
  by_cases H : ∃ a : Fin p → Fin 4 → Point (2 * p + 1),
      (∀ i k, a i k ∈ stableExactCore P x) ∧
      (∀ i k (h : a i k ∈ stableExactCore P x),
        stableExactCorePart P x ⟨a i k, h⟩ = i) ∧
      (∀ i, AffineIndependent ℝ (a i)) ∧
      ∀ i, stableRetainedFiberPoints P i ⊆
        affineSpan ℝ (Set.range (a i))
  · left
    obtain ⟨a, haCore, haPart, haAI, hspan⟩ := H
    exact isWeakCarrierSet_stableRetainedSet_of_spanningCore hp P hepsilon
      hlarge x hxinj hxcross a haCore
      (fun i k ↦ haPart i k (haCore i k)) haAI hspan
  · exact Or.inr H

/-- Localized form of `exists_aligned_core_carrier_or_nonspanning`: in the
defect branch one specific stable color lacks a spanning core basis. -/
theorem exists_aligned_core_carrier_or_fiber_nonspanning
    {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}
    (hp : 4 ≤ p)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card) :
    ∃ x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A},
      (∀ i a, x i a ∈
        Stability.retainedFiber P.color P.exceptional i) ∧
      (∀ i, Function.Injective (x i)) ∧
      (∀ {i j : Fin p}, i ≠ j → ∀ a b,
        (diameterGraph A).Adj (x i a) (x j b)) ∧
      (IsWeakCarrierSet (p := p) (stableRetainedSet P) ∨
        ∃ i, ¬ HasSpanningCoreBasis P x i) := by
  obtain ⟨x, hxmem, hxinj, hxcross, hcase⟩ :=
    exists_aligned_core_carrier_or_nonspanning hp P hepsilon hlarge
  refine ⟨x, hxmem, hxinj, hxcross, ?_⟩
  rcases hcase with hcarrier | hfamily
  · exact Or.inl hcarrier
  · right
    by_contra hnone
    push_neg at hnone
    exact hfamily ((exists_spanningCoreFamily_iff P x).2 hnone)

end

end Erdos223.CarrierOdd
