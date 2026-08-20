/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.HullChains

/-!
# Exposed edges from the first crossing of finite support functions

This file isolates the finite part of the usual support-line sweep.  If `p`
is the unique maximizer of a linear functional `l`, and another functional
`m` is increased from coefficient zero, then the first point whose support
value catches that of `p` exists.  At the first crossing, `p` and that point
lie on a common supporting line.  When the crossing times are distinct, they
are the only hull vertices on that line, hence form a strict supporting edge.

The remaining planar input needed for a cyclic hull order is therefore a
generic choice of sweep direction for which the crossing times are distinct,
followed by iteration around the circle.
-/

open Set

namespace Erdos957

noncomputable section

/-- The positive time at which `x` catches `p` when the functional changes
from `l` to `l + t m`.  It is used only when `m p < m x`. -/
def supportCrossingTime (l m : Point →L[ℝ] ℝ) (p x : Point) : ℝ :=
  (l p - l x) / (m x - m p)

/-- Points whose `m`-value is larger than that of `p`, i.e. the points which
can catch `p` at a positive time. -/
def forwardSupportPoints (A : Finset Point) (m : Point →L[ℝ] ℝ)
    (p : Point) : Finset Point :=
  A.filter fun x ↦ m p < m x

@[simp]
theorem mem_forwardSupportPoints {A : Finset Point} {m : Point →L[ℝ] ℝ}
    {p x : Point} :
    x ∈ forwardSupportPoints A m p ↔ x ∈ A ∧ m p < m x := by
  simp [forwardSupportPoints]

/-- A point strictly exposed by `l` has positive crossing time with every
point lying forward in the `m` direction. -/
theorem supportCrossingTime_pos {A : Finset Point} {p x : Point}
    {l m : Point →L[ℝ] ℝ} (hstrict : ∀ y ∈ A, y ≠ p → l y < l p)
    (hx : x ∈ forwardSupportPoints A m p) :
    0 < supportCrossingTime l m p x := by
  rw [supportCrossingTime]
  exact div_pos (sub_pos.mpr (hstrict x (mem_forwardSupportPoints.mp hx).1
    (fun hxp ↦ by
      subst x
      exact (lt_irrefl (m p)) (mem_forwardSupportPoints.mp hx).2)))
    (sub_pos.mpr (mem_forwardSupportPoints.mp hx).2)

/-- At its crossing time, `x` has the same perturbed support value as `p`. -/
theorem supportCrossingTime_tie {p x : Point} {l m : Point →L[ℝ] ℝ}
    (hforward : m p < m x) :
    (l + supportCrossingTime l m p x • m) x =
      (l + supportCrossingTime l m p x • m) p := by
  have hden : m x - m p ≠ 0 := ne_of_gt (sub_pos.mpr hforward)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, supportCrossingTime]
  field_simp [hden]
  ring

/-- The first crossing of a finite family produces a supporting functional.

This is the core finite support-adjacency lemma.  It does not use planarity:
planarity enters only in choosing and ordering the successive sweep
directions. -/
theorem exists_first_support_tie (A : Finset Point) {p : Point}
    (hp : p ∈ A) (l m : Point →L[ℝ] ℝ)
    (hstrict : ∀ x ∈ A, x ≠ p → l x < l p)
    (hforward : ∃ x ∈ A, m p < m x) :
    ∃ t : ℝ, 0 < t ∧ ∃ q ∈ A, q ≠ p ∧
      (l + t • m) q = (l + t • m) p ∧
      ∀ x ∈ A, (l + t • m) x ≤ (l + t • m) p := by
  let B := forwardSupportPoints A m p
  have hB : B.Nonempty := by
    obtain ⟨x, hxA, hx⟩ := hforward
    exact ⟨x, mem_forwardSupportPoints.mpr ⟨hxA, hx⟩⟩
  obtain ⟨q, hqB, hqmin⟩ :=
    B.exists_min_image (supportCrossingTime l m p) hB
  let t := supportCrossingTime l m p q
  have hqdata := mem_forwardSupportPoints.mp hqB
  have ht : 0 < t := supportCrossingTime_pos hstrict hqB
  have hqp : q ≠ p := fun hqp ↦ by
    subst q
    exact (lt_irrefl (m p)) hqdata.2
  refine ⟨t, ht, q, hqdata.1, hqp, ?_, ?_⟩
  · exact supportCrossingTime_tie hqdata.2
  · intro x hxA
    by_cases hxforward : m p < m x
    · have hxB : x ∈ B := mem_forwardSupportPoints.mpr ⟨hxA, hxforward⟩
      have hmin : t ≤ supportCrossingTime l m p x := hqmin x hxB
      have hden : 0 < m x - m p := sub_pos.mpr hxforward
      rw [supportCrossingTime] at hmin
      have hmul := (le_div_iff₀ hden).mp hmin
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      linarith
    · have hmx : m x ≤ m p := le_of_not_gt hxforward
      have hlx : l x ≤ l p := by
        by_cases hxp : x = p
        · exact (congrArg l hxp).le
        · exact (hstrict x hxA hxp).le
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hmx ht.le]

/-- If all forward crossing times are distinct, the first crossing leaves
every point other than its two endpoints strictly below the supporting line. -/
theorem exists_first_support_tie_strict (A : Finset Point) {p : Point}
    (hp : p ∈ A) (l m : Point →L[ℝ] ℝ)
    (hstrict : ∀ x ∈ A, x ≠ p → l x < l p)
    (hforward : ∃ x ∈ A, m p < m x)
    (hinj : Set.InjOn (supportCrossingTime l m p)
      (forwardSupportPoints A m p : Set Point)) :
    ∃ t : ℝ, 0 < t ∧ ∃ q ∈ A, q ≠ p ∧
      (l + t • m) q = (l + t • m) p ∧
      (∀ x ∈ A, (l + t • m) x ≤ (l + t • m) p) ∧
      (∀ x ∈ A, x ≠ p → x ≠ q →
        (l + t • m) x < (l + t • m) p) := by
  let B := forwardSupportPoints A m p
  have hB : B.Nonempty := by
    obtain ⟨x, hxA, hx⟩ := hforward
    exact ⟨x, mem_forwardSupportPoints.mpr ⟨hxA, hx⟩⟩
  obtain ⟨q, hqB, hqmin⟩ :=
    B.exists_min_image (supportCrossingTime l m p) hB
  let t := supportCrossingTime l m p q
  have hqdata := mem_forwardSupportPoints.mp hqB
  have ht : 0 < t := supportCrossingTime_pos hstrict hqB
  have hqp : q ≠ p := fun hqp ↦ by
    subst q
    exact (lt_irrefl (m p)) hqdata.2
  refine ⟨t, ht, q, hqdata.1, hqp,
    supportCrossingTime_tie hqdata.2, ?_, ?_⟩
  · intro x hxA
    by_cases hxforward : m p < m x
    · have hxB : x ∈ B := mem_forwardSupportPoints.mpr ⟨hxA, hxforward⟩
      have hmin : t ≤ supportCrossingTime l m p x := hqmin x hxB
      have hden : 0 < m x - m p := sub_pos.mpr hxforward
      rw [supportCrossingTime] at hmin
      have hmul := (le_div_iff₀ hden).mp hmin
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      linarith
    · have hmx : m x ≤ m p := le_of_not_gt hxforward
      have hlx : l x ≤ l p := by
        by_cases hxp : x = p
        · exact (congrArg l hxp).le
        · exact (hstrict x hxA hxp).le
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hmx ht.le]
  · intro x hxA hxp hxq
    by_cases hxforward : m p < m x
    · have hxB : x ∈ B := mem_forwardSupportPoints.mpr ⟨hxA, hxforward⟩
      have hmin : t ≤ supportCrossingTime l m p x := hqmin x hxB
      have hne : supportCrossingTime l m p q ≠
          supportCrossingTime l m p x := by
        intro heq
        exact hxq (hinj hqB hxB heq).symm
      have hmin' : t < supportCrossingTime l m p x :=
        lt_of_le_of_ne hmin (by simpa [t] using hne)
      have hden : 0 < m x - m p := sub_pos.mpr hxforward
      rw [supportCrossingTime] at hmin'
      have hmul := (lt_div_iff₀ hden).mp hmin'
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      linarith
    · have hmx : m x ≤ m p := le_of_not_gt hxforward
      have hlx : l x < l p := hstrict x hxA hxp
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hmx ht.le]

/-- With at least one third point, the strict first crossing gives a nonzero
functional and hence a strict supporting edge of the convex hull. -/
theorem exists_strictSupportingEdge_of_first_crossing
    (A : Finset Point) {p : Point} (hp : p ∈ A)
    (l m : Point →L[ℝ] ℝ)
    (hstrict : ∀ x ∈ A, x ≠ p → l x < l p)
    (hforward : ∃ x ∈ A, m p < m x)
    (hinj : Set.InjOn (supportCrossingTime l m p)
      (forwardSupportPoints A m p : Set Point))
    (hthree : 3 ≤ A.card) :
    ∃ q ∈ A, IsStrictSupportingEdge A p q := by
  obtain ⟨t, ht, q, hqA, hqp, htie, hmax, hstrict'⟩ :=
    exists_first_support_tie_strict A hp l m hstrict hforward hinj
  have hex : ∃ x ∈ A, x ≠ p ∧ x ≠ q := by
    by_contra h
    push_neg at h
    have hsub : A ⊆ {p, q} := by
      intro x hx
      by_cases hxp : x = p
      · simp [hxp]
      · simp [h x hx hxp]
    have hcard : A.card ≤ 2 := by
      calc
        A.card ≤ ({p, q} : Finset Point).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨x, hxA, hxp, hxq⟩ := hex
  let f : Point →L[ℝ] ℝ := l + t • m
  have hf : f ≠ 0 := by
    intro hf0
    have hxzero : f x = 0 := by rw [hf0]; rfl
    have hpzero : f p = 0 := by rw [hf0]; rfl
    exact (ne_of_lt (hstrict' x hxA hxp hxq)) (hxzero.trans hpzero.symm)
  refine ⟨q, hqA, hqp.symm, f, hf, htie.symm, hmax, ?_⟩
  intro y hyHull hyp hyq
  exact hstrict' y (hullVertices_subset A hyHull) hyp hyq

/-! ## The finite successor permutation -/

/-- Subtype-valued form of the checked counterclockwise outgoing-edge
theorem from `Erdos957HullOrder`. -/
theorem exists_orientedSupportingSuccessor (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    ∃ q : {x // x ∈ hullVertices A},
      IsStrictSupportingEdge A p q ∧
      ∀ r : {x // x ∈ hullVertices A}, r ≠ p → r ≠ q →
        0 < crossVec (q.1 - p.1) (r.1 - p.1) := by
  obtain ⟨q, hq, hedge, hleft⟩ :=
    hullVertex_exists_ccw_strictSupportingEdge A hthree p.property
  refine ⟨⟨q, hq⟩, hedge, ?_⟩
  intro r hrp hrq
  rw [← orientedTurn_eq_crossVec]
  exact hleft r r.property
    (fun h ↦ hrp (Subtype.ext h)) (fun h ↦ hrq (Subtype.ext h))


/-- The counterclockwise exposed-edge successor selected above. -/
noncomputable def orientedHullSuccessor (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) : {x // x ∈ hullVertices A} :=
  Classical.choose (exists_orientedSupportingSuccessor A hthree p)

theorem orientedHullSuccessor_spec (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    IsStrictSupportingEdge A p (orientedHullSuccessor A hthree p) ∧
      ∀ r : {x // x ∈ hullVertices A}, r ≠ p →
        r ≠ orientedHullSuccessor A hthree p →
        0 < crossVec ((orientedHullSuccessor A hthree p).1 - p.1)
          (r.1 - p.1) :=
  Classical.choose_spec (exists_orientedSupportingSuccessor A hthree p)

/-- Two distinct vertices cannot have the same counterclockwise outgoing
edge target. -/
theorem orientedHullSuccessor_injective (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) :
    Function.Injective (orientedHullSuccessor A hthree) := by
  intro p p' hnext
  by_contra hpp'
  let s := orientedHullSuccessor A hthree
  have hpnext : p ≠ s p := by
    intro h
    exact (orientedHullSuccessor_spec A hthree p).1.1
      (congrArg Subtype.val h)
  have hp'next' : p' ≠ s p' := by
    intro h
    exact (orientedHullSuccessor_spec A hthree p').1.1
      (congrArg Subtype.val h)
  have hp'next : p' ≠ s p := by
    change p' ≠ orientedHullSuccessor A hthree p
    rw [hnext]
    exact hp'next'
  have hpnext' : p ≠ s p' := by
    change p ≠ orientedHullSuccessor A hthree p'
    rw [← hnext]
    exact hpnext
  have hleft :
      0 < crossVec ((s p).1 - p.1) (p'.1 - p.1) :=
    (orientedHullSuccessor_spec A hthree p).2 p' (Ne.symm hpp') hp'next
  have hleft' :
      0 < crossVec ((s p').1 - p'.1) (p.1 - p'.1) :=
    (orientedHullSuccessor_spec A hthree p').2 p hpp' hpnext'
  have hneg : crossVec ((s p').1 - p'.1) (p.1 - p'.1) =
      -crossVec ((s p).1 - p.1) (p'.1 - p.1) := by
    change crossVec ((orientedHullSuccessor A hthree p').1 - p'.1)
      (p.1 - p'.1) =
      -crossVec ((orientedHullSuccessor A hthree p).1 - p.1)
        (p'.1 - p.1)
    rw [← hnext]
    simp only [crossVec, PiLp.sub_apply]
    ring
  rw [hneg] at hleft'
  linarith

/-- The outgoing-edge map is a permutation because the hull vertex type is
finite and the map is injective. -/
noncomputable def orientedHullPerm (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) :
    Equiv.Perm {x // x ∈ hullVertices A} :=
  Equiv.ofBijective (orientedHullSuccessor A hthree)
    ⟨orientedHullSuccessor_injective A hthree,
      Finite.surjective_of_injective (orientedHullSuccessor_injective A hthree)⟩

@[simp]
theorem orientedHullPerm_apply (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    orientedHullPerm A hthree p = orientedHullSuccessor A hthree p :=
  rfl

theorem orientedHullPerm_edge_support (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    IsStrictSupportingEdge A p (orientedHullPerm A hthree p) :=
  (orientedHullSuccessor_spec A hthree p).1

theorem orientedHullPerm_left (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p r : {x // x ∈ hullVertices A}) (hrp : r ≠ p)
    (hrq : r ≠ orientedHullPerm A hthree p) :
    0 < crossVec ((orientedHullPerm A hthree p).1 - p.1)
      (r.1 - p.1) :=
  (orientedHullSuccessor_spec A hthree p).2 r hrp hrq

theorem orientedHullPerm_apply_ne (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    orientedHullPerm A hthree p ≠ p := by
  intro h
  exact (orientedHullPerm_edge_support A hthree p).1
    (congrArg Subtype.val h).symm

/-- The oriented successor has no two-cycle.  A third hull vertex would have
to lie strictly to the left of both orientations of the same edge. -/
theorem orientedHullPerm_sq_apply_ne (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    orientedHullPerm A hthree (orientedHullPerm A hthree p) ≠ p := by
  let σ := orientedHullPerm A hthree
  let q := σ p
  obtain ⟨r, hrp, hrq⟩ : ∃ r : {x // x ∈ hullVertices A}, r ≠ p ∧ r ≠ q := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset {x // x ∈ hullVertices A}) ⊆ {p, q} := by
      intro x _
      by_cases hxp : x = p
      · simp [hxp]
      · simp [h x hxp]
    have hc := Finset.card_le_card hsub
    have hpq : p ≠ q := (orientedHullPerm_apply_ne A hthree p).symm
    simp [hpq] at hc
    have : (hullVertices A).card ≤ 2 := by simpa using hc
    omega
  intro hsq
  have hsq' : σ q = p := by simpa [σ, q] using hsq
  have hleft : 0 < crossVec (q.1 - p.1) (r.1 - p.1) := by
    simpa [σ, q] using orientedHullPerm_left A hthree p r hrp hrq
  have hrq' : r ≠ σ p := by simpa [q] using hrq
  have hrp' : r ≠ σ q := by rw [hsq']; exact hrp
  have hleft' : 0 < crossVec ((σ q).1 - q.1) (r.1 - q.1) :=
    by simpa [σ] using orientedHullPerm_left A hthree q r hrq' hrp'
  have hneg : crossVec ((σ q).1 - q.1) (r.1 - q.1) =
      -crossVec (q.1 - p.1) (r.1 - p.1) := by
    rw [hsq']
    simp only [crossVec, PiLp.sub_apply]
    ring
  rw [hneg] at hleft'
  linarith

theorem orientedHullPerm_strict_turn (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card)
    (p : {x // x ∈ hullVertices A}) :
    0 < orientedTurn p.1 (orientedHullPerm A hthree p).1
      (orientedHullPerm A hthree (orientedHullPerm A hthree p)).1 := by
  rw [orientedTurn_eq_crossVec]
  apply orientedHullPerm_left A hthree p
  · exact orientedHullPerm_sq_apply_ne A hthree p
  · exact (orientedHullPerm A hthree).injective.ne
      (orientedHullPerm_apply_ne A hthree p)

/-- The oriented successor permutation is one cycle.  The proof is finite
gift-wrapping: if one orbit omitted a hull vertex, strictly separate that
vertex from the orbit's convex hull.  At an orbit vertex maximizing the
separating functional, the omitted vertex lies in the positive cone spanned
by the two inward edge rays, contradicting strict separation. -/
theorem orientedHullPerm_isCycleOn (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) :
    (orientedHullPerm A hthree).IsCycleOn
      (Finset.univ : Finset {x // x ∈ hullVertices A}) := by
  classical
  let σ := orientedHullPerm A hthree
  refine ⟨by
    simpa only [Finset.coe_univ, Set.bijOn_univ] using σ.bijective, ?_⟩
  intro p _ q _
  by_contra hpqCycle
  let S : Finset {x // x ∈ hullVertices A} :=
    Finset.univ.filter fun x ↦ σ.SameCycle p x
  have hpS : p ∈ S := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl σ p⟩
  have hS : S.Nonempty := ⟨p, hpS⟩
  have hqS : q ∉ S := by
    intro hqS
    exact hpqCycle (Finset.mem_filter.mp hqS).2
  let T : Finset Point := S.image Subtype.val
  have hqHull : q.1 ∉ convexHull ℝ (T : Set Point) := by
    intro hqHull
    have hqHull' : q.1 ∈ convexHull ℝ
        ((Subtype.val : {x // x ∈ hullVertices A} → Point) '' (S : Set _)) := by
      simpa [T] using hqHull
    have hqmem :=
      (hullVertices_convexIndependent A).mem_convexHull_iff (S : Set _) q
    have : q ∈ (S : Set _) := hqmem.mp hqHull'
    exact hqS this
  have hclosed : IsClosed (convexHull ℝ (T : Set Point)) :=
    (Set.Finite.isCompact_convexHull ℝ T.finite_toSet).isClosed
  obtain ⟨l, u, hlt, hulq⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (T : Set Point)) hclosed hqHull
  obtain ⟨r, hrS, hrmax⟩ := S.exists_max_image (fun x ↦ l x.1) hS
  let rprev := σ⁻¹ r
  let rnext := σ r
  have hrCycle : σ.SameCycle p r := (Finset.mem_filter.mp hrS).2
  have hprevS : rprev ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [rprev] using hrCycle
  have hnextS : rnext ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [rnext] using hrCycle
  have hprevNext : σ rprev = r := by simp [rprev]
  have hrnext : rnext = σ r := rfl
  have hprevNeR : rprev ≠ r := by
    intro h
    have hfix : σ rprev = rprev := by rw [hprevNext, h]
    exact orientedHullPerm_apply_ne A hthree rprev (by simpa [σ] using hfix)
  have hnextNeR : rnext ≠ r := by
    simpa [σ, rnext] using orientedHullPerm_apply_ne A hthree r
  have hnextNePrev : rnext ≠ rprev := by
    intro h
    have htwo : σ (σ rprev) = rprev := by
      rw [hprevNext, ← hrnext, h]
    exact orientedHullPerm_sq_apply_ne A hthree rprev (by simpa [σ] using htwo)
  have hqNePrev : q ≠ rprev := fun h ↦ hqS (h.symm ▸ hprevS)
  have hqNeR : q ≠ r := fun h ↦ hqS (h.symm ▸ hrS)
  have hqNeNext : q ≠ rnext := fun h ↦ hqS (h.symm ▸ hnextS)
  let a : Point := r.1 - rprev.1
  let b : Point := rnext.1 - r.1
  let v : Point := q.1 - r.1
  have hab : 0 < crossVec a b := by
    have hrnextNotSuccPrev : rnext ≠ σ rprev := by
      rw [hprevNext]
      exact hnextNeR
    have h := orientedHullPerm_left A hthree rprev rnext hnextNePrev
      (by simpa [σ] using hrnextNotSuccPrev)
    have hsigmaPrev : orientedHullPerm A hthree rprev = r := by
      simpa [σ] using hprevNext
    rw [hsigmaPrev] at h
    change 0 < crossVec (r.1 - rprev.1) (rnext.1 - rprev.1) at h
    have heq : crossVec (r.1 - rprev.1) (rnext.1 - rprev.1) =
        crossVec (r.1 - rprev.1) (rnext.1 - r.1) := by
      simp only [crossVec, PiLp.sub_apply]
      ring
    rw [heq] at h
    simpa [a, b] using h
  have hav : 0 < crossVec a v := by
    have hqNotSuccPrev : q ≠ σ rprev := by
      rw [hprevNext]
      exact hqNeR
    have h := orientedHullPerm_left A hthree rprev q hqNePrev
      (by simpa [σ] using hqNotSuccPrev)
    have hsigmaPrev : orientedHullPerm A hthree rprev = r := by
      simpa [σ] using hprevNext
    rw [hsigmaPrev] at h
    change 0 < crossVec (r.1 - rprev.1) (q.1 - rprev.1) at h
    have heq : crossVec (r.1 - rprev.1) (q.1 - rprev.1) =
        crossVec (r.1 - rprev.1) (q.1 - r.1) := by
      simp only [crossVec, PiLp.sub_apply]
      ring
    rw [heq] at h
    exact h
  have hbv : 0 < crossVec b v := by
    have h := orientedHullPerm_left A hthree r q hqNeR
      (by simpa [σ, rnext] using hqNeNext)
    simpa [b, v, σ, rnext] using h
  let α : ℝ := crossVec a v / crossVec a b
  let β : ℝ := crossVec b v / crossVec a b
  have hα : 0 < α := div_pos hav hab
  have hβ : 0 < β := div_pos hbv hab
  have hvdecomp : v = α • b + β • (-a) := by
    have hd : crossVec a b ≠ 0 := ne_of_gt hab
    ext i
    fin_cases i
    · change v 0 = α * b 0 + β * (-a 0)
      dsimp only [α, β]
      field_simp [hd]
      simp only [crossVec]
      ring
    · change v 1 = α * b 1 + β * (-a 1)
      dsimp only [α, β]
      field_simp [hd]
      simp only [crossVec]
      ring
  have hlprev : l rprev.1 ≤ l r.1 := hrmax rprev hprevS
  have hlnext : l rnext.1 ≤ l r.1 := hrmax rnext hnextS
  have hlv : l v ≤ 0 := by
    rw [hvdecomp, map_add, map_smul, map_smul, map_neg]
    simp only [smul_eq_mul]
    have hlb : l b ≤ 0 := by
      simp only [b, map_sub]
      linarith
    have hlnega : -l a ≤ 0 := by
      simp only [a, map_sub]
      linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hα.le hlb,
      mul_nonpos_of_nonneg_of_nonpos hβ.le hlnega]
  have hrT : r.1 ∈ T := by
    exact Finset.mem_image.mpr ⟨r, hrS, rfl⟩
  have hrHull : r.1 ∈ convexHull ℝ (T : Set Point) :=
    subset_convexHull ℝ (T : Set Point) hrT
  have hlrq : l r.1 < l q.1 := (hlt r.1 hrHull).trans hulq
  have : l q.1 - l r.1 ≤ 0 := by simpa [v, map_sub] using hlv
  linarith

/-- The actual gift-wrapping certificate obtained from the finite planar
convex hull, with no geometric fields left as assumptions. -/
noncomputable def finiteHullGiftWrapCycle (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) : GiftWrapCycle A := by
  have hH : (hullVertices A).Nonempty := by
    rw [← Finset.card_pos]
    omega
  let start : {x // x ∈ hullVertices A} :=
    ⟨Classical.choose hH, Classical.choose_spec hH⟩
  exact
    { next := orientedHullPerm A hthree
      start := start
      isCycle := orientedHullPerm_isCycleOn A hthree
      edge_support := fun p ↦
        (isStrictChainEdge_iff_isStrictSupportingEdge A _ _).mpr
          (orientedHullPerm_edge_support A hthree p)
      strict_turn := fun p ↦ by
        simpa [chainOrientedTurn_eq_orientedTurn] using
          orientedHullPerm_strict_turn A hthree p }

/-- Every finite planar convex hull with at least three vertices admits the
exact `Fin h` cyclic enumeration consumed by the Erdős 957 development. -/
noncomputable def cyclicHullOrderOfThree (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) : CyclicHullOrder A :=
  (finiteHullGiftWrapCycle A hthree).toCyclicHullOrder

theorem nonempty_cyclicHullOrder_of_three_le (A : Finset Point)
    (hthree : 3 ≤ hullVertexCount A) : Nonempty (CyclicHullOrder A) :=
  ⟨cyclicHullOrderOfThree A hthree⟩

end

end Erdos957
