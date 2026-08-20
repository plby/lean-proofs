/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.TripleFree

/-!
# The blue-triple path

This file formalizes the constructive ingredient in Chen--Chen's high-degree case.  If three
vertices outside a path have complement-colour neighbours at ordered positions
`alpha <= beta < gamma <= delta`, then the two corresponding subpaths can be spliced through
the three outside vertices.  The resulting complement-colour path contains all three vertices,
and uses no vertex outside those three and the original path.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- The part of a walk running from position `i` to position `j` (inclusive on vertices).
The endpoint is copied from `i + (j - i)` to `j` using `i <= j`. -/
private def walkSegment {H : SimpleGraph V} {a b : V} (w : H.Walk a b)
    (i j : ℕ) (hij : i ≤ j) : H.Walk (w.getVert i) (w.getVert j) :=
  ((w.drop i).take (j - i)).copy rfl (by
    rw [SimpleGraph.Walk.drop_getVert]
    congr
    omega)

private lemma support_walkSegment_subset {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    (walkSegment w i j hij).support ⊆ w.support := by
  simpa [walkSegment] using (((w.drop i).isSubwalk_take (j - i)).trans
    (w.isSubwalk_drop i)).support_subset

@[simp] private lemma length_walkSegment {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ w.length) :
    (walkSegment w i j hij).length = j - i := by
  simp only [walkSegment, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length]
  exact Nat.min_eq_left (Nat.sub_le_sub_right hj i)

private lemma getVert_walkSegment {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) (i j t : ℕ) (hij : i ≤ j) (ht : t ≤ j - i) :
    (walkSegment w i j hij).getVert t = w.getVert (i + t) := by
  simp [walkSegment, Nat.min_eq_right ht]

private lemma mem_support_walkSegment_iff {H : SimpleGraph V} {a b z : V}
    (w : H.Walk a b) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ w.length) :
    z ∈ (walkSegment w i j hij).support ↔
      ∃ k, i ≤ k ∧ k ≤ j ∧ z = w.getVert k := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨t, htz, ht⟩
    rw [length_walkSegment w i j hij hj] at ht
    have ht' : t ≤ j - i := ht
    refine ⟨i + t, by omega, by omega, ?_⟩
    simpa [getVert_walkSegment w i j t hij ht'] using htz.symm
  · rintro ⟨k, hik, hkj, rfl⟩
    refine ⟨k - i, ?_, ?_⟩
    · rw [getVert_walkSegment w i j (k - i) hij (by omega)]
      congr
      omega
    · simp only [length_walkSegment w i j hij hj]
      omega

/-- Splice three new vertices through two ordered segments of a walk. -/
private def tripleWalk {H : SimpleGraph V} {a b u m v : V} (w : H.Walk a b)
    (alpha beta gamma delta : ℕ) (hab : alpha ≤ beta) (hgd : gamma ≤ delta)
    (hua : H.Adj u (w.getVert alpha)) (hmb : H.Adj m (w.getVert beta))
    (hmg : H.Adj m (w.getVert gamma)) (hvd : H.Adj v (w.getVert delta)) :
    H.Walk u v :=
  (((((walkSegment w alpha beta hab).cons hua).concat hmb.symm).concat hmg).append
    (walkSegment w gamma delta hgd)).concat hvd.symm

private lemma support_tripleWalk {H : SimpleGraph V} {a b u m v : V} (w : H.Walk a b)
    (alpha beta gamma delta : ℕ) (hab : alpha ≤ beta) (hgd : gamma ≤ delta)
    (hua : H.Adj u (w.getVert alpha)) (hmb : H.Adj m (w.getVert beta))
    (hmg : H.Adj m (w.getVert gamma)) (hvd : H.Adj v (w.getVert delta)) :
    (tripleWalk w alpha beta gamma delta hab hgd hua hmb hmg hvd).support =
      u :: (walkSegment w alpha beta hab).support ++
        m :: (walkSegment w gamma delta hgd).support ++ [v] := by
  simp [tripleWalk, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_concat,
    SimpleGraph.Walk.support_cons]

private lemma tripleWalk_isPath {H : SimpleGraph V} {a b u m v : V} (w : H.Walk a b)
    (hw : w.IsPath) (alpha beta gamma delta : ℕ)
    (hab : alpha ≤ beta) (hbg : beta < gamma) (hgd : gamma ≤ delta)
    (hd : delta ≤ w.length) (hu : u ∉ w.support) (hm : m ∉ w.support)
    (hv : v ∉ w.support) (hum : u ≠ m) (huv : u ≠ v) (hmv : m ≠ v)
    (hua : H.Adj u (w.getVert alpha)) (hmb : H.Adj m (w.getVert beta))
    (hmg : H.Adj m (w.getVert gamma)) (hvd : H.Adj v (w.getVert delta)) :
    (tripleWalk w alpha beta gamma delta hab hgd hua hmb hmg hvd).IsPath := by
  have hb : beta ≤ w.length := by omega
  have hg : gamma ≤ w.length := by omega
  let s₁ := walkSegment w alpha beta hab
  let s₂ := walkSegment w gamma delta hgd
  have hs₁ : s₁.support.Nodup := by
    simpa [s₁, walkSegment] using ((hw.drop alpha).take (beta - alpha)).support_nodup
  have hs₂ : s₂.support.Nodup := by
    simpa [s₂, walkSegment] using ((hw.drop gamma).take (delta - gamma)).support_nodup
  have hs₁sub : s₁.support ⊆ w.support :=
    support_walkSegment_subset w alpha beta hab
  have hs₂sub : s₂.support ⊆ w.support :=
    support_walkSegment_subset w gamma delta hgd
  have hu₁ : u ∉ s₁.support := fun h ↦ hu (hs₁sub h)
  have hu₂ : u ∉ s₂.support := fun h ↦ hu (hs₂sub h)
  have hm₁ : m ∉ s₁.support := fun h ↦ hm (hs₁sub h)
  have hm₂ : m ∉ s₂.support := fun h ↦ hm (hs₂sub h)
  have hv₁ : v ∉ s₁.support := fun h ↦ hv (hs₁sub h)
  have hv₂ : v ∉ s₂.support := fun h ↦ hv (hs₂sub h)
  have hdis : s₁.support.Disjoint s₂.support := by
    rw [List.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨i, hai, hib, hiz⟩ :=
      (mem_support_walkSegment_iff w alpha beta hab hb).mp hz₁
    obtain ⟨j, hgj, hjd, hjz⟩ :=
      (mem_support_walkSegment_iff w gamma delta hgd hd).mp hz₂
    have hij : i = j := hw.getVert_injOn (by simpa using hib.trans hb)
      (by simpa using hjd.trans hd) (by simpa [hiz] using hjz)
    omega
  apply SimpleGraph.Walk.IsPath.mk'
  rw [support_tripleWalk]
  change ((u :: s₁.support) ++ (m :: s₂.support) ++ [v]).Nodup
  have hus₁ : (u :: s₁.support).Nodup :=
    List.nodup_cons.mpr ⟨hu₁, hs₁⟩
  have hms₂ : (m :: s₂.support).Nodup :=
    List.nodup_cons.mpr ⟨hm₂, hs₂⟩
  have hdis' : (u :: s₁.support).Disjoint (m :: s₂.support) := by
    rw [List.disjoint_left]
    intro z hz₁ hz₂
    simp only [List.mem_cons] at hz₁ hz₂
    rcases hz₁ with rfl | hz₁ <;> rcases hz₂ with rfl | hz₂
    · exact hum rfl
    · exact hu₂ hz₂
    · exact hm₁ hz₁
    · exact hdis hz₁ hz₂
  have habNodup : ((u :: s₁.support) ++ (m :: s₂.support)).Nodup :=
    hus₁.append hms₂ hdis'
  apply habNodup.append (by simp)
  rw [List.disjoint_left]
  intro z hz hzv
  simp only [List.mem_singleton] at hzv
  subst z
  simp only [List.mem_append, List.mem_cons] at hz
  rcases hz with (h | h) | h | h
  · exact huv h.symm
  · exact hv₁ h
  · exact hmv h.symm
  · exact hv₂ h

/-- Three distinct vertices outside a simple path can be spliced through two ordered pairs of
neighbours.  Every vertex of the resulting path is either one of the three new vertices or was
already on the original walk. -/
theorem exists_path_of_ordered_neighbors {H : SimpleGraph V} {a b u m v : V}
    (w : H.Walk a b) (hw : w.IsPath) (alpha beta gamma delta : ℕ)
    (hab : alpha ≤ beta) (hbg : beta < gamma) (hgd : gamma ≤ delta)
    (hd : delta ≤ w.length) (hu : u ∉ w.support) (hm : m ∉ w.support)
    (hv : v ∉ w.support) (hum : u ≠ m) (huv : u ≠ v) (hmv : m ≠ v)
    (hua : H.Adj u (w.getVert alpha)) (hmb : H.Adj m (w.getVert beta))
    (hmg : H.Adj m (w.getVert gamma)) (hvd : H.Adj v (w.getVert delta)) :
    ∃ p : List V, IsPath H p ∧ u ∈ p ∧ m ∈ p ∧ v ∈ p ∧
      ∀ z ∈ p, z = u ∨ z = m ∨ z = v ∨ z ∈ w.support := by
  let q := tripleWalk w alpha beta gamma delta hab hgd hua hmb hmg hvd
  have hq : q.IsPath :=
    tripleWalk_isPath w hw alpha beta gamma delta hab hbg hgd hd hu hm hv
      hum huv hmv hua hmb hmg hvd
  refine ⟨q.support, ⟨q.support_ne_nil, hq.support_nodup, q.isChain_adj_support⟩,
    ?_, ?_, ?_, ?_⟩
  · simp [q, support_tripleWalk]
  · simp [q, support_tripleWalk]
  · simp [q, support_tripleWalk]
  · intro z hz
    rw [show q.support =
      (u :: (walkSegment w alpha beta hab).support) ++
        (m :: (walkSegment w gamma delta hgd).support) ++ [v] by
          simpa [q] using support_tripleWalk w alpha beta gamma delta hab hgd hua hmb hmg hvd]
      at hz
    rcases List.mem_append.mp hz with hzab | hzv
    · rcases List.mem_append.mp hzab with hzu | hzm
      · rcases List.mem_cons.mp hzu with hzu | hz₁
        · exact Or.inl hzu
        · exact Or.inr (Or.inr (Or.inr
            (support_walkSegment_subset w alpha beta hab hz₁)))
      · rcases List.mem_cons.mp hzm with hzm | hz₂
        · exact Or.inr (Or.inl hzm)
        · exact Or.inr (Or.inr (Or.inr
            (support_walkSegment_subset w gamma delta hgd hz₂)))
    · have hzv' : z = v := by simpa using hzv
      exact Or.inr (Or.inr (Or.inl hzv'))

namespace Configuration

variable [Fintype V] (C : Configuration V)

/-- The path supplied by an ordered blue triple.  The final clause records the useful support
bound: away from `Q`, the path uses only the three vertices of the triple. -/
theorem exists_path_of_orderedBlueTriple_with_support {u m v : V}
    (htriple : C.OrderedBlueTriple u m v)
    (hu : u ∈ C.Y1) (hm : m ∈ C.Y1) (hv : v ∈ C.Y1)
    (hum : u ≠ m) (huv : u ≠ v) (hmv : m ≠ v) :
    ∃ p : List V, IsPath C.Gᶜ p ∧ u ∈ p ∧ m ∈ p ∧ v ∈ p ∧
      ∀ z ∈ p, z ∉ C.Q → z = u ∨ z = m ∨ z = v := by
  classical
  obtain ⟨alpha, halpha, beta, hbeta, gamma, hgamma, delta, hdelta,
      hab, hbg, hgd⟩ := htriple
  obtain ⟨xa, hxaX, hua, hxa⟩ := C.mem_blueIndices.mp halpha
  obtain ⟨xb, hxbX, hmb, hxb⟩ := C.mem_blueIndices.mp hbeta
  obtain ⟨xg, hxgX, hmg, hxg⟩ := C.mem_blueIndices.mp hgamma
  obtain ⟨xd, hxdX, hvd, hxd⟩ := C.mem_blueIndices.mp hdelta
  let w := pathWalk C.q_isPath
  have hw : w.IsPath := isPath_pathWalk C.q_isPath
  have hwsupport : w.support = C.Q := by simp [w]
  have hwa : w.getVert (C.Q.idxOf xa) = xa := by
    have hmem : xa ∈ w.support := by
      rw [hwsupport]
      exact C.mem_X.mp hxaX
    simpa [hwsupport] using w.getVert_support_idxOf hmem
  have hwb : w.getVert (C.Q.idxOf xb) = xb := by
    have hmem : xb ∈ w.support := by
      rw [hwsupport]
      exact C.mem_X.mp hxbX
    simpa [hwsupport] using w.getVert_support_idxOf hmem
  have hwg : w.getVert (C.Q.idxOf xg) = xg := by
    have hmem : xg ∈ w.support := by
      rw [hwsupport]
      exact C.mem_X.mp hxgX
    simpa [hwsupport] using w.getVert_support_idxOf hmem
  have hwd : w.getVert (C.Q.idxOf xd) = xd := by
    have hmem : xd ∈ w.support := by
      rw [hwsupport]
      exact C.mem_X.mp hxdX
    simpa [hwsupport] using w.getVert_support_idxOf hmem
  have hab' : C.Q.idxOf xa ≤ C.Q.idxOf xb := by omega
  have hbg' : C.Q.idxOf xb < C.Q.idxOf xg := by omega
  have hgd' : C.Q.idxOf xg ≤ C.Q.idxOf xd := by omega
  have hxdlt : C.Q.idxOf xd < C.Q.length :=
    List.idxOf_lt_length_iff.mpr (C.mem_X.mp hxdX)
  have hlen : C.Q.length = w.length + 1 := by
    calc
      C.Q.length = w.support.length := congrArg List.length hwsupport.symm
      _ = w.length + 1 := w.length_support
  have hxdle : C.Q.idxOf xd ≤ w.length := by omega
  have huQ : u ∉ C.Q := fun h ↦
    (C.mem_Y.mp (C.mem_Y1.mp hu).1) (C.mem_X.mpr h)
  have hmQ : m ∉ C.Q := fun h ↦
    (C.mem_Y.mp (C.mem_Y1.mp hm).1) (C.mem_X.mpr h)
  have hvQ : v ∉ C.Q := fun h ↦
    (C.mem_Y.mp (C.mem_Y1.mp hv).1) (C.mem_X.mpr h)
  obtain ⟨p, hp, hup, hmp, hvp, hsupport⟩ :=
    exists_path_of_ordered_neighbors w hw
      (C.Q.idxOf xa) (C.Q.idxOf xb) (C.Q.idxOf xg) (C.Q.idxOf xd)
      hab' hbg' hgd' hxdle
      (by simpa [hwsupport] using huQ) (by simpa [hwsupport] using hmQ)
      (by simpa [hwsupport] using hvQ) hum huv hmv
      (by simpa [hwa] using hua) (by simpa [hwb] using hmb)
      (by simpa [hwg] using hmg) (by simpa [hwd] using hvd)
  refine ⟨p, hp, hup, hmp, hvp, ?_⟩
  intro z hzp hzQ
  rcases hsupport z hzp with rfl | rfl | rfl | hz
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact (hzQ (hwsupport ▸ hz)).elim

/-- Compatibility form of `exists_path_of_orderedBlueTriple_with_support` when only coverage
of the three triple vertices is needed. -/
theorem exists_path_of_orderedBlueTriple {u m v : V}
    (htriple : C.OrderedBlueTriple u m v)
    (hu : u ∈ C.Y1) (hm : m ∈ C.Y1) (hv : v ∈ C.Y1)
    (hum : u ≠ m) (huv : u ≠ v) (hmv : m ≠ v) :
    ∃ p : List V, IsPath C.Gᶜ p ∧ u ∈ p ∧ m ∈ p ∧ v ∈ p := by
  obtain ⟨p, hp, hu, hm, hv, -⟩ :=
    C.exists_path_of_orderedBlueTriple_with_support htriple hu hm hv hum huv hmv
  exact ⟨p, hp, hu, hm, hv⟩

end Configuration

end Erdos518
