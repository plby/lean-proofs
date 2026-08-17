import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# One-subdivisions of finite complete graphs

This file supplies the elementary finite graph used in the proof of Erdős
Problem 63.  The type `SubdivisionEdge t` consists of the strictly ordered
pairs of elements of `Fin t`.  Thus it is canonically in bijection with the
unordered two-element subsets of `Fin t`: there is exactly one subdivision
vertex for each edge of `K_t`.
-/

open Function
open scoped SimpleGraph

namespace Erdos63

/-- The subdivision vertices of the one-subdivision of `K_t`.  The condition
`p.1 < p.2` chooses the unique increasing ordering of an unordered pair. -/
abbrev SubdivisionEdge (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}

/-- Vertices of the one-subdivision of `K_t`: original (core) vertices on the
left and one vertex for each unordered pair of core vertices on the right. -/
abbrev SubdivisionVertex (t : ℕ) := Fin t ⊕ SubdivisionEdge t

/-- Incidence between a core vertex and a subdivision vertex. -/
def subdivisionAdj {t : ℕ} : SubdivisionVertex t → SubdivisionVertex t → Prop
  | .inl i, .inr e => i = e.1.1 ∨ i = e.1.2
  | .inr e, .inl i => i = e.1.1 ∨ i = e.1.2
  | .inl _, .inl _ => False
  | .inr _, .inr _ => False

/-- The graph obtained by subdividing every edge of `K_t` exactly once. -/
def oneSubdivisionClique (t : ℕ) : SimpleGraph (SubdivisionVertex t) where
  Adj := subdivisionAdj
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simp_all [subdivisionAdj]
  loopless := by
    constructor
    intro x
    cases x <;> simp [subdivisionAdj]

@[simp] lemma oneSubdivisionClique_adj_core_edge {t : ℕ} (i : Fin t)
    (e : SubdivisionEdge t) :
    (oneSubdivisionClique t).Adj (.inl i) (.inr e) ↔
      i = e.1.1 ∨ i = e.1.2 :=
  Iff.rfl

@[simp] lemma oneSubdivisionClique_adj_edge_core {t : ℕ} (i : Fin t)
    (e : SubdivisionEdge t) :
    (oneSubdivisionClique t).Adj (.inr e) (.inl i) ↔
      i = e.1.1 ∨ i = e.1.2 :=
  Iff.rfl

@[simp] lemma oneSubdivisionClique_not_adj_core_core {t : ℕ} (i j : Fin t) :
    ¬(oneSubdivisionClique t).Adj (.inl i) (.inl j) :=
  id

@[simp] lemma oneSubdivisionClique_not_adj_edge_edge {t : ℕ}
    (e f : SubdivisionEdge t) :
    ¬(oneSubdivisionClique t).Adj (.inr e) (.inr f) :=
  id


section CycleCopy

variable {r t : ℕ}

/-- The order-preserving inclusion of the first `r` core vertices into the
first `t` core vertices. -/
private def coreInclusion (hrt : r ≤ t) : Fin r ↪ Fin t where
  toFun i := ⟨i, lt_of_lt_of_le i.isLt hrt⟩
  inj' x y h := by
    have hv := congrArg (fun z : Fin t => z.val) h
    apply Fin.ext
    exact hv

@[simp] private lemma coreInclusion_apply_val (hrt : r ≤ t) (i : Fin r) :
    (coreInclusion hrt i).val = i.val :=
  rfl

/-- The subdivision vertex used at an odd position of the standard `2*r`
cycle.  All but the last join consecutive cores; the final one joins `0` to
`r - 1`. -/
private def oddCycleEdge (h3 : 3 ≤ r) (hrt : r ≤ t) (x : Fin (2 * r))
    (hx : x.val % 2 = 1) : SubdivisionEdge t :=
  if hlast : x.val + 1 = 2 * r then
    ⟨(coreInclusion hrt ⟨0, by omega⟩,
        coreInclusion hrt ⟨r - 1, by omega⟩), by
      change 0 < r - 1
      omega⟩
  else
    ⟨(coreInclusion hrt ⟨x.val / 2, by omega⟩,
        coreInclusion hrt ⟨x.val / 2 + 1, by omega⟩), by
      change x.val / 2 < x.val / 2 + 1
      omega⟩

/-- The alternating vertex map from the `2*r`-cycle to the one-subdivision
of `K_t`. -/
private def cycleVertex (h3 : 3 ≤ r) (hrt : r ≤ t) :
    Fin (2 * r) → SubdivisionVertex t := fun x =>
  if hx : x.val % 2 = 0 then
    .inl (coreInclusion hrt ⟨x.val / 2, by omega⟩)
  else
    .inr (oddCycleEdge h3 hrt x (by omega))

/-- Cyclic successor on `Fin (2*r)`, written without a `NeZero` typeclass
argument so that positivity follows directly from `h3`. -/
private def cycleSucc (h3 : 3 ≤ r) (x : Fin (2 * r)) : Fin (2 * r) :=
  if h : x.val + 1 < 2 * r then ⟨x.val + 1, h⟩ else ⟨0, by omega⟩

/-- The element one in `Fin (2*r)`, again with its bound recorded explicitly. -/
private def cycleOne (h3 : 3 ≤ r) : Fin (2 * r) := ⟨1, by omega⟩

private lemma add_cycleOne_eq_cycleSucc (h3 : 3 ≤ r) [NeZero (2 * r)]
    (x : Fin (2 * r)) :
    x + cycleOne h3 = cycleSucc h3 x := by
  by_cases h : x.val + 1 < 2 * r
  · apply Fin.ext
    simp [cycleOne, cycleSucc, h, Fin.add_def, Nat.mod_eq_of_lt h]
  · have heq : x.val + 1 = 2 * r := by omega
    apply Fin.ext
    simp [cycleOne, cycleSucc, Fin.add_def, heq]

private lemma cycleVertex_succ_adj (h3 : 3 ≤ r) (hrt : r ≤ t)
    (x : Fin (2 * r)) :
    (oneSubdivisionClique t).Adj (cycleVertex h3 hrt x)
      (cycleVertex h3 hrt (cycleSucc h3 x)) := by
  have hpos : 0 < 2 * r := by omega
  by_cases hlast : x.val + 1 = 2 * r
  · have hxval : x.val = 2 * r - 1 := by omega
    have hsval : (cycleSucc h3 x).val = 0 := by
      simp [cycleSucc, hlast]
    have hxodd : x.val % 2 = 1 := by omega
    simp [cycleVertex, hxodd, oddCycleEdge, hlast, Fin.ext_iff, hsval]
  · have hlt : x.val + 1 < 2 * r := by omega
    have hsval : (cycleSucc h3 x).val = x.val + 1 := by
      simp [cycleSucc, hlt]
    by_cases hx : x.val % 2 = 0
    · have hsodd : (cycleSucc h3 x).val % 2 = 1 := by omega
      by_cases hsnextlast : (cycleSucc h3 x).val + 1 = 2 * r
      · simp [cycleVertex, hx, hsodd, oddCycleEdge, hsnextlast, Fin.ext_iff]
        omega
      · simp [cycleVertex, hx, hsodd, oddCycleEdge, hsnextlast, Fin.ext_iff]
        omega
    · have hxodd : x.val % 2 = 1 := by omega
      have hseven : (cycleSucc h3 x).val % 2 = 0 := by omega
      simp [cycleVertex, hx, hseven, oddCycleEdge, hlast, Fin.ext_iff]
      omega

private lemma cycleVertex_injective (h3 : 3 ≤ r) (hrt : r ≤ t) :
    Injective (cycleVertex h3 hrt) := by
  intro x y hxy
  by_cases hx : x.val % 2 = 0 <;> by_cases hy : y.val % 2 = 0
  · have hcore :
        coreInclusion hrt ⟨x.val / 2, by omega⟩ =
          coreInclusion hrt ⟨y.val / 2, by omega⟩ := by
      simpa [cycleVertex, hx, hy] using hxy
    have hdiv : x.val / 2 = y.val / 2 := by
      have hv := congrArg (fun z : Fin t => z.val) hcore
      simpa using hv
    apply Fin.ext
    have hxlt : x.val % 2 < 2 := Nat.mod_lt _ (by omega)
    have hylt : y.val % 2 < 2 := Nat.mod_lt _ (by omega)
    omega
  · simp [cycleVertex, hx, hy] at hxy
  · simp [cycleVertex, hx, hy] at hxy
  · have hxodd : x.val % 2 = 1 := by omega
    have hyodd : y.val % 2 = 1 := by omega
    have hedge : oddCycleEdge h3 hrt x hxodd = oddCycleEdge h3 hrt y hyodd := by
      simpa [cycleVertex, hx, hy] using hxy
    by_cases hxl : x.val + 1 = 2 * r <;>
      by_cases hyl : y.val + 1 = 2 * r
    · apply Fin.ext
      omega
    · have hfst := congrArg (fun e : SubdivisionEdge t => e.1.1.val) hedge
      have hsnd := congrArg (fun e : SubdivisionEdge t => e.1.2.val) hedge
      simp [oddCycleEdge, hxl, hyl] at hfst hsnd
      omega
    · have hfst := congrArg (fun e : SubdivisionEdge t => e.1.1.val) hedge
      have hsnd := congrArg (fun e : SubdivisionEdge t => e.1.2.val) hedge
      simp [oddCycleEdge, hxl, hyl] at hfst hsnd
      omega
    · have hfst := congrArg (fun e : SubdivisionEdge t => e.1.1.val) hedge
      simp [oddCycleEdge, hxl, hyl] at hfst
      apply Fin.ext
      omega

/-- If `3 ≤ r ≤ t`, the one-subdivision of `K_t` contains the standard cycle
of length `2*r`. -/
theorem cycleGraph_isContained_oneSubdivisionClique (h3 : 3 ≤ r) (hrt : r ≤ t) :
    SimpleGraph.cycleGraph (2 * r) ⊑ oneSubdivisionClique t := by
  haveI : NeZero (2 * r) := ⟨by omega⟩
  let f : SimpleGraph.cycleGraph (2 * r) →g oneSubdivisionClique t :=
    ⟨cycleVertex h3 hrt, by
      intro x y hxy
      rw [SimpleGraph.cycleGraph_adj'] at hxy
      rcases hxy with hxy | hxy
      · have hsub : x - y = cycleOne h3 := by
          apply Fin.ext
          simpa [cycleOne] using hxy
        have heq : x = y + cycleOne h3 := sub_eq_iff_eq_add'.mp hsub
        rw [add_cycleOne_eq_cycleSucc] at heq
        subst x
        exact (cycleVertex_succ_adj h3 hrt y).symm
      · have hsub : y - x = cycleOne h3 := by
          apply Fin.ext
          simpa [cycleOne] using hxy
        have heq : y = x + cycleOne h3 := sub_eq_iff_eq_add'.mp hsub
        rw [add_cycleOne_eq_cycleSucc] at heq
        subst y
        exact cycleVertex_succ_adj h3 hrt x⟩
  exact ⟨⟨f, cycleVertex_injective h3 hrt⟩⟩

/-- Containment is transitive: an ambient graph containing the one-subdivision
also contains all the even cycles supplied by it. -/
theorem cycleGraph_isContained_of_oneSubdivisionClique_isContained
    {V : Type*} {G : SimpleGraph V} (h3 : 3 ≤ r) (hrt : r ≤ t)
    (hsub : oneSubdivisionClique t ⊑ G) :
    SimpleGraph.cycleGraph (2 * r) ⊑ G :=
  (cycleGraph_isContained_oneSubdivisionClique h3 hrt).trans hsub

/-- Consequently an ambient graph containing the one-subdivision of `K_t`
contains every even cycle whose length lies between `6` and `2*t`. -/
theorem every_even_cycle_isContained_of_oneSubdivisionClique
    {V : Type*} {G : SimpleGraph V} (hsub : oneSubdivisionClique t ⊑ G)
    {n : ℕ} (heven : Even n) (h6 : 6 ≤ n) (hnt : n ≤ 2 * t) :
    SimpleGraph.cycleGraph n ⊑ G := by
  obtain ⟨r, rfl⟩ := heven
  rw [← two_mul r]
  exact cycleGraph_isContained_of_oneSubdivisionClique_isContained
    (r := r) (t := t) (by omega) (by omega) hsub

end CycleCopy

end Erdos63
