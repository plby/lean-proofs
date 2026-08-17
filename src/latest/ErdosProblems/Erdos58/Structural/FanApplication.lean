/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos58.Fan

/-!
# Applying the fan lemma at an endpoint of a longest path

Let `P` be a simple path starting at `x`, and suppose that `x` has at least
`2*j+1` neighbours on `P`.  Choose that many neighbours and record their
positive positions on `P`.  Among the positions, at least `j+1` have the same
parity.

* even positions close initial segments of `P` to odd cycles, with distinct
  lengths;
* odd positions give shortcuts from `x` to the other endpoint of `P`, with
  distinct lengths of one parity.  The path edges, together with only these
  odd-position spokes, form a bipartite fan (colour a path vertex by the
  parity of its position).

The theorems below carry this argument out with actual Mathlib walks.  The
mixed-parity theorem uses a torsion-free Cauchy--Davenport count of signed
even--odd gaps.  The endpoint-only parity-majority theorem is also retained
because it is convenient when the two prescribed attachment vertices are
the endpoints of the original path.
-/

namespace Erdos58

open SimpleGraph
open scoped Pointwise

universe u

/-- `2*j+1` different positive positions of neighbours of the initial
endpoint on a simple path. -/
structure EndpointFanData {V : Type u} (G : SimpleGraph V) (x y : V) (j : ℕ) where
  path : G.Walk x y
  isPath : path.IsPath
  position : Fin (2 * j + 1) → ℕ
  position_pos : ∀ i, 0 < position i
  position_le : ∀ i, position i ≤ path.length
  position_injective : Function.Injective position
  spoke : ∀ i, G.Adj x (path.getVert (position i))

namespace EndpointFanData

variable {V : Type u} {G : SimpleGraph V} {x y : V} {j : ℕ}

/-- A path family whose every vertex lies on the endpoint fan's spine.
This is the support control needed when gluing the family to external
connectors with interiors disjoint from the fan carrier. -/
structure SpineSupportedPathFamily (D : EndpointFanData G x y j)
    (a b r : ℕ) where
  family : PathFamily G (D.path.getVert a) (D.path.getVert b) (Fin r)
  support_subset : ∀ i v, v ∈ (family.path i).support → v ∈ D.path.support

/-- Endpoint-explicit variant, convenient when one endpoint is the hub. -/
structure FanSupportedPathFamily (D : EndpointFanData G x y j)
    (u v : V) (r : ℕ) where
  family : PathFamily G u v (Fin r)
  support_subset : ∀ i z, z ∈ (family.path i).support → z ∈ D.path.support

def SpineSupportedPathFamily.toFanSupported
    {D : EndpointFanData G x y j} {a b r : ℕ}
    (F : SpineSupportedPathFamily D a b r) :
    FanSupportedPathFamily D (D.path.getVert a) (D.path.getVert b) r where
  family := F.family
  support_subset := F.support_subset

/-- The cycle obtained by closing the initial path segment at a spoke. -/
def prefixCycle (D : EndpointFanData G x y j) (i : Fin (2 * j + 1)) :
    G.Walk x x :=
  Walk.cons (D.spoke i) (D.path.take (D.position i)).reverse

/-- The path obtained by taking a spoke and then the terminal path segment. -/
def shortcut (D : EndpointFanData G x y j) (i : Fin (2 * j + 1)) :
    G.Walk x y :=
  Walk.cons (D.spoke i) (D.path.drop (D.position i))

/-- The subpath between two ordered spoke endpoints. -/
def segment (D : EndpointFanData G x y j) (i i' : Fin (2 * j + 1))
    (hii' : D.position i < D.position i') :
    G.Walk (D.path.getVert (D.position i))
      (D.path.getVert (D.position i')) :=
  ((D.path.drop (D.position i)).take (D.position i' - D.position i)).copy rfl (by
    rw [Walk.drop_getVert]
    congr 1
    omega)

/-- The two-spoke cycle cut out by two ordered endpoint neighbours. -/
def betweenCycle (D : EndpointFanData G x y j) (i i' : Fin (2 * j + 1))
    (hii' : D.position i < D.position i') : G.Walk x x :=
  Walk.cons (D.spoke i)
    ((D.segment i i' hii').concat (D.spoke i').symm)

/-- A path segment addressed directly by natural positions. -/
def spineSegment (D : EndpointFanData G x y j) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ D.path.length) :
    G.Walk (D.path.getVert a) (D.path.getVert b) :=
  ((D.path.drop a).take (b - a)).copy rfl (by
    rw [Walk.drop_getVert]
    congr 1
    omega)

@[simp] lemma length_prefixCycle (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) :
    (D.prefixCycle i).length = D.position i + 1 := by
  simp [prefixCycle, D.position_le i]

@[simp] lemma length_shortcut (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) :
    (D.shortcut i).length = D.path.length - D.position i + 1 := by
  simp [shortcut]

@[simp] lemma length_segment (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    (D.segment i i' hii').length = D.position i' - D.position i := by
  simp [segment, D.position_le i, D.position_le i']

@[simp] lemma length_betweenCycle (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    (D.betweenCycle i i' hii').length =
      D.position i' - D.position i + 2 := by
  simp [betweenCycle]

@[simp] lemma length_spineSegment (D : EndpointFanData G x y j)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ D.path.length) :
    (D.spineSegment a b hab hb).length = b - a := by
  have hle : b - a ≤ D.path.length - a := by omega
  simp [spineSegment, hle]

lemma spineSegment_isPath (D : EndpointFanData G x y j)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ D.path.length) :
    (D.spineSegment a b hab hb).IsPath := by
  simp only [spineSegment, Walk.isPath_copy]
  exact (D.isPath.drop _).take _

lemma getVert_mem_path_support (D : EndpointFanData G x y j)
    {n : ℕ} (hn : n ≤ D.path.length) :
    D.path.getVert n ∈ D.path.support := by
  exact Walk.mem_support_iff_exists_getVert.mpr ⟨n, rfl, hn⟩

lemma mem_spineSegment_support_iff (D : EndpointFanData G x y j)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ D.path.length) (v : V) :
    v ∈ (D.spineSegment a b hab hb).support ↔
      ∃ n : ℕ, a ≤ n ∧ n ≤ b ∧ D.path.getVert n = v := by
  constructor
  · intro hv
    obtain ⟨r, hget, hr⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    have hr' : r ≤ b - a := by simpa using hr
    refine ⟨a + r, by omega, by omega, ?_⟩
    simpa [spineSegment, Walk.drop_getVert, min_eq_right hr'] using hget
  · rintro ⟨n, han, hnb, rfl⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨n - a, ?_, ?_⟩
    · simp [spineSegment, Walk.drop_getVert]
      congr 1
      omega
    · rw [D.length_spineSegment]
      omega

lemma spineSegment_support_subset (D : EndpointFanData G x y j)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ D.path.length) :
    ∀ ⦃v⦄, v ∈ (D.spineSegment a b hab hb).support → v ∈ D.path.support := by
  intro v hv
  obtain ⟨n, han, hnb, hget⟩ :=
    (D.mem_spineSegment_support_iff a b hab hb v).mp hv
  exact hget ▸ D.getVert_mem_path_support (hnb.trans hb)

lemma hub_notMem_spineSegment (D : EndpointFanData G x y j)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ D.path.length) :
    x ∉ (D.spineSegment a b hab hb).support := by
  intro hx
  obtain ⟨n, han, hnb, hget⟩ :=
    (D.mem_spineSegment_support_iff a b hab hb x).mp hx
  have hnle : n ≤ D.path.length := hnb.trans hb
  have hn0 := (D.isPath.getVert_eq_start_iff hnle).mp hget
  omega

lemma spineSegments_disjoint_of_lt (D : EndpointFanData G x y j)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) (hbc : b < c)
    (hd : d ≤ D.path.length) :
    (D.spineSegment a b hab (by omega)).support.Disjoint
      (D.spineSegment c d hcd hd).support := by
  rw [List.disjoint_left]
  intro v hv₁ hv₂
  obtain ⟨n, han, hnb, hn⟩ :=
    (D.mem_spineSegment_support_iff a b hab (by omega) v).mp hv₁
  obtain ⟨m, hcm, hmd, hm⟩ :=
    (D.mem_spineSegment_support_iff c d hcd hd v).mp hv₂
  have heq : n = m := D.isPath.getVert_injOn (hnb.trans (by omega))
    (hmd.trans hd) (hn.trans hm.symm)
  omega

private lemma isPath_append_of_disjoint_tail
    {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.Disjoint q.support.tail) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  exact ⟨hp.support_nodup, hq.support_nodup.tail, hd⟩

private lemma getVert_ne_hub (D : EndpointFanData G x y j)
    {n : ℕ} (hn : 0 < n) (hnle : n ≤ D.path.length) :
    D.path.getVert n ≠ x := by
  exact fun h ↦ hn.ne' ((D.isPath.getVert_eq_start_iff hnle).mp h)

/-- The cross path using a portal before `a` and a portal after `b`. -/
def outerPath (D : EndpointFanData G x y j) (ip iq : Fin (2 * j + 1))
    (a b : ℕ) (hpa : D.position ip ≤ a) (hab : a < b)
    (hbq : b ≤ D.position iq) :
    G.Walk (D.path.getVert a) (D.path.getVert b) :=
  ((((D.spineSegment (D.position ip) a hpa
      (hab.le.trans (hbq.trans (D.position_le iq)))).reverse.concat
      (D.spoke ip).symm).concat
      (D.spoke iq)).append
    (D.spineSegment b (D.position iq) hbq (D.position_le iq)).reverse)

/-- The cross path using a portal before `a` and one strictly between
`a` and `b`. -/
def middleLeftPath (D : EndpointFanData G x y j) (ip iq : Fin (2 * j + 1))
    (a b : ℕ) (hpa : D.position ip ≤ a) (haq : a < D.position iq)
    (hqb : D.position iq < b) (hb : b ≤ D.path.length) :
    G.Walk (D.path.getVert a) (D.path.getVert b) :=
  ((((D.spineSegment (D.position ip) a hpa
      (haq.le.trans (hqb.le.trans hb))).reverse.concat
      (D.spoke ip).symm).concat
      (D.spoke iq)).append
    (D.spineSegment (D.position iq) b hqb.le hb))

/-- The cross path using a portal strictly between `a` and `b` and one
after `b`. -/
def middleRightPath (D : EndpointFanData G x y j) (ip iq : Fin (2 * j + 1))
    (a b : ℕ) (hap : a < D.position ip) (hpb : D.position ip < b)
    (hbq : b ≤ D.position iq) :
    G.Walk (D.path.getVert a) (D.path.getVert b) :=
  (((D.spineSegment a (D.position ip) hap.le (D.position_le ip)).concat
      (D.spoke ip).symm).concat (D.spoke iq)).append
    (D.spineSegment b (D.position iq) hbq (D.position_le iq)).reverse

@[simp] lemma length_outerPath (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hpa : D.position ip ≤ a) (hab : a < b) (hbq : b ≤ D.position iq) :
    (D.outerPath ip iq a b hpa hab hbq).length =
      (a - D.position ip) + (D.position iq - b) + 2 := by
  simp [outerPath]
  omega

@[simp] lemma length_middleLeftPath (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hpa : D.position ip ≤ a) (haq : a < D.position iq)
    (hqb : D.position iq < b) (hb : b ≤ D.path.length) :
    (D.middleLeftPath ip iq a b hpa haq hqb hb).length =
      (a - D.position ip) + (b - D.position iq) + 2 := by
  simp [middleLeftPath]
  omega

@[simp] lemma length_middleRightPath (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hap : a < D.position ip) (hpb : D.position ip < b)
    (hbq : b ≤ D.position iq) :
    (D.middleRightPath ip iq a b hap hpb hbq).length =
      (D.position ip - a) + (D.position iq - b) + 2 := by
  simp [middleRightPath]
  omega

lemma outerPath_isPath (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hpa : D.position ip ≤ a) (hab : a < b)
    (hbq : b ≤ D.position iq) :
    (D.outerPath ip iq a b hpa hab hbq).IsPath := by
  let L := D.spineSegment (D.position ip) a hpa
    (hab.le.trans (hbq.trans (D.position_le iq)))
  let R := D.spineSegment b (D.position iq) hbq (D.position_le iq)
  have hL : L.IsPath := D.spineSegment_isPath _ _ _ _
  have hR : R.IsPath := D.spineSegment_isPath _ _ _ _
  have hxL : x ∉ L.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    exact D.hub_notMem_spineSegment _ _ (D.position_pos ip) _ _
  have hfirst : (L.reverse.concat (D.spoke ip).symm).IsPath :=
    hL.reverse.concat hxL (D.spoke ip).symm
  have hqL : D.path.getVert (D.position iq) ∉ L.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    intro hmem
    obtain ⟨n, hnlo, hnhi, hnget⟩ :=
      (D.mem_spineSegment_support_iff _ _ _ _ _).mp hmem
    have heq : n = D.position iq := D.isPath.getVert_injOn
      (hnhi.trans (hab.le.trans (hbq.trans (D.position_le iq))))
      (D.position_le iq) hnget
    omega
  have hqx : D.path.getVert (D.position iq) ≠ x :=
    D.getVert_ne_hub (D.position_pos iq) (D.position_le iq)
  have hqfirst : D.path.getVert (D.position iq) ∉
      (L.reverse.concat (D.spoke ip).symm).support := by
    rw [Walk.support_concat]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hqL, hqx⟩
  have hprefix :
      ((L.reverse.concat (D.spoke ip).symm).concat (D.spoke iq)).IsPath :=
    hfirst.concat hqfirst (D.spoke iq)
  have hdis :
      ((L.reverse.concat (D.spoke ip).symm).concat (D.spoke iq)).support.Disjoint
        R.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvprefix hvRtail
    rw [Walk.support_concat, Walk.support_concat] at hvprefix
    simp only [List.mem_append, List.mem_singleton] at hvprefix
    rcases hvprefix with (hvL | hvx) | hvq
    · rw [Walk.support_reverse, List.mem_reverse] at hvL
      have hvR : v ∈ R.support := by
        rw [← List.mem_reverse, ← Walk.support_reverse]
        exact List.mem_of_mem_tail hvRtail
      obtain ⟨n, hnlo, hnhi, hnget⟩ :=
        (D.mem_spineSegment_support_iff _ _ _ _ _).mp hvL
      obtain ⟨m, hmlo, hmhi, hmget⟩ :=
        (D.mem_spineSegment_support_iff _ _ _ _ _).mp hvR
      have heq : n = m := D.isPath.getVert_injOn
        (hnhi.trans (hab.le.trans (hbq.trans (D.position_le iq))))
        (hmhi.trans (D.position_le iq)) (hnget.trans hmget.symm)
      omega
    · subst v
      have hxR : x ∉ R.reverse.support := by
        rw [Walk.support_reverse, List.mem_reverse]
        exact D.hub_notMem_spineSegment _ _ (by omega) _ _
      exact hxR (List.mem_of_mem_tail hvRtail)
    · subst v
      have hnod := hR.reverse.support_nodup
      rw [← R.reverse.cons_tail_support, List.nodup_cons] at hnod
      exact hnod.1 hvRtail
  simpa [outerPath, L, R] using
    isPath_append_of_disjoint_tail hprefix hR.reverse hdis

lemma middleLeftPath_isPath (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hpa : D.position ip ≤ a) (haq : a < D.position iq)
    (hqb : D.position iq < b) (hb : b ≤ D.path.length) :
    (D.middleLeftPath ip iq a b hpa haq hqb hb).IsPath := by
  let L := D.spineSegment (D.position ip) a hpa
    (haq.le.trans (hqb.le.trans hb))
  let R := D.spineSegment (D.position iq) b hqb.le hb
  have hL : L.IsPath := D.spineSegment_isPath _ _ _ _
  have hR : R.IsPath := D.spineSegment_isPath _ _ _ _
  have hxL : x ∉ L.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    exact D.hub_notMem_spineSegment _ _ (D.position_pos ip) _ _
  have hfirst : (L.reverse.concat (D.spoke ip).symm).IsPath :=
    hL.reverse.concat hxL (D.spoke ip).symm
  have hqL : D.path.getVert (D.position iq) ∉ L.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    intro hmem
    obtain ⟨n, hnlo, hnhi, hnget⟩ :=
      (D.mem_spineSegment_support_iff _ _ _ _ _).mp hmem
    have heq : n = D.position iq := D.isPath.getVert_injOn
      (hnhi.trans (haq.le.trans (hqb.le.trans hb)))
      ((hqb.le).trans hb) hnget
    omega
  have hqx : D.path.getVert (D.position iq) ≠ x :=
    D.getVert_ne_hub (D.position_pos iq) ((hqb.le).trans hb)
  have hqfirst : D.path.getVert (D.position iq) ∉
      (L.reverse.concat (D.spoke ip).symm).support := by
    rw [Walk.support_concat]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hqL, hqx⟩
  have hprefix :
      ((L.reverse.concat (D.spoke ip).symm).concat (D.spoke iq)).IsPath :=
    hfirst.concat hqfirst (D.spoke iq)
  have hdis :
      ((L.reverse.concat (D.spoke ip).symm).concat (D.spoke iq)).support.Disjoint
        R.support.tail := by
    rw [List.disjoint_left]
    intro v hvprefix hvRtail
    rw [Walk.support_concat, Walk.support_concat] at hvprefix
    simp only [List.mem_append, List.mem_singleton] at hvprefix
    rcases hvprefix with (hvL | hvx) | hvq
    · rw [Walk.support_reverse, List.mem_reverse] at hvL
      have hvR : v ∈ R.support := List.mem_of_mem_tail hvRtail
      obtain ⟨n, hnlo, hnhi, hnget⟩ :=
        (D.mem_spineSegment_support_iff _ _ _ _ _).mp hvL
      obtain ⟨m, hmlo, hmhi, hmget⟩ :=
        (D.mem_spineSegment_support_iff _ _ _ _ _).mp hvR
      have heq : n = m := D.isPath.getVert_injOn
        (hnhi.trans (haq.le.trans (hqb.le.trans hb)))
        (hmhi.trans hb) (hnget.trans hmget.symm)
      omega
    · subst v
      have hxR : x ∉ R.support :=
        D.hub_notMem_spineSegment _ _ (D.position_pos iq) _ _
      exact hxR (List.mem_of_mem_tail hvRtail)
    · subst v
      have hnod := hR.support_nodup
      rw [← R.cons_tail_support, List.nodup_cons] at hnod
      exact hnod.1 hvRtail
  simpa [middleLeftPath, L, R] using
    isPath_append_of_disjoint_tail hprefix hR hdis

lemma middleRightPath_isPath (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ) (ha : 0 < a)
    (hap : a < D.position ip) (hpb : D.position ip < b)
    (hbq : b ≤ D.position iq) :
    (D.middleRightPath ip iq a b hap hpb hbq).IsPath := by
  let L := D.spineSegment a (D.position ip) hap.le (D.position_le ip)
  let R := D.spineSegment b (D.position iq) hbq (D.position_le iq)
  have hL : L.IsPath := D.spineSegment_isPath _ _ _ _
  have hR : R.IsPath := D.spineSegment_isPath _ _ _ _
  have hxL : x ∉ L.support :=
    D.hub_notMem_spineSegment _ _ ha _ _
  have hfirst : (L.concat (D.spoke ip).symm).IsPath :=
    hL.concat hxL (D.spoke ip).symm
  have hqL : D.path.getVert (D.position iq) ∉ L.support := by
    intro hmem
    obtain ⟨n, hnlo, hnhi, hnget⟩ :=
      (D.mem_spineSegment_support_iff _ _ _ _ _).mp hmem
    have heq : n = D.position iq := D.isPath.getVert_injOn
      (hnhi.trans (D.position_le ip)) (D.position_le iq) hnget
    omega
  have hqx : D.path.getVert (D.position iq) ≠ x :=
    D.getVert_ne_hub (D.position_pos iq) (D.position_le iq)
  have hqfirst : D.path.getVert (D.position iq) ∉
      (L.concat (D.spoke ip).symm).support := by
    rw [Walk.support_concat]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hqL, hqx⟩
  have hprefix :
      ((L.concat (D.spoke ip).symm).concat (D.spoke iq)).IsPath :=
    hfirst.concat hqfirst (D.spoke iq)
  have hdis :
      ((L.concat (D.spoke ip).symm).concat (D.spoke iq)).support.Disjoint
        R.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvprefix hvRtail
    rw [Walk.support_concat, Walk.support_concat] at hvprefix
    simp only [List.mem_append, List.mem_singleton] at hvprefix
    rcases hvprefix with (hvL | hvx) | hvq
    · have hvR : v ∈ R.support := by
        rw [← List.mem_reverse, ← Walk.support_reverse]
        exact List.mem_of_mem_tail hvRtail
      obtain ⟨n, hnlo, hnhi, hnget⟩ :=
        (D.mem_spineSegment_support_iff _ _ _ _ _).mp hvL
      obtain ⟨m, hmlo, hmhi, hmget⟩ :=
        (D.mem_spineSegment_support_iff _ _ _ _ _).mp hvR
      have heq : n = m := D.isPath.getVert_injOn
        (hnhi.trans (D.position_le ip))
        (hmhi.trans (D.position_le iq)) (hnget.trans hmget.symm)
      omega
    · subst v
      have hxR : x ∉ R.reverse.support := by
        rw [Walk.support_reverse, List.mem_reverse]
        exact D.hub_notMem_spineSegment _ _ (by omega) _ _
      exact hxR (List.mem_of_mem_tail hvRtail)
    · subst v
      have hnod := hR.reverse.support_nodup
      rw [← R.reverse.cons_tail_support, List.nodup_cons] at hnod
      exact hnod.1 hvRtail
  simpa [middleRightPath, L, R] using
    isPath_append_of_disjoint_tail hprefix hR.reverse hdis

lemma outerPath_support_subset (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hpa : D.position ip ≤ a) (hab : a < b)
    (hbq : b ≤ D.position iq) :
    ∀ ⦃v⦄, v ∈ (D.outerPath ip iq a b hpa hab hbq).support →
      v ∈ D.path.support := by
  intro v hv
  rw [outerPath, Walk.support_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rw [Walk.support_concat, Walk.support_concat] at hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with (hv | hvx) | hvq
    · rw [Walk.support_reverse, List.mem_reverse] at hv
      exact D.spineSegment_support_subset _ _ _ _ hv
    · rw [hvx]
      exact D.path.start_mem_support
    · rw [hvq]
      exact D.getVert_mem_path_support (D.position_le iq)
  · have hv' := List.mem_of_mem_tail hv
    rw [Walk.support_reverse, List.mem_reverse] at hv'
    exact D.spineSegment_support_subset _ _ _ _ hv'

lemma middleLeftPath_support_subset (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hpa : D.position ip ≤ a) (haq : a < D.position iq)
    (hqb : D.position iq < b) (hb : b ≤ D.path.length) :
    ∀ ⦃v⦄, v ∈ (D.middleLeftPath ip iq a b hpa haq hqb hb).support →
      v ∈ D.path.support := by
  intro v hv
  rw [middleLeftPath, Walk.support_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rw [Walk.support_concat, Walk.support_concat] at hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with (hv | hvx) | hvq
    · rw [Walk.support_reverse, List.mem_reverse] at hv
      exact D.spineSegment_support_subset _ _ _ _ hv
    · rw [hvx]
      exact D.path.start_mem_support
    · rw [hvq]
      exact D.getVert_mem_path_support (by omega)
  · exact D.spineSegment_support_subset _ _ _ _ (List.mem_of_mem_tail hv)

lemma middleRightPath_support_subset (D : EndpointFanData G x y j)
    (ip iq : Fin (2 * j + 1)) (a b : ℕ)
    (hap : a < D.position ip) (hpb : D.position ip < b)
    (hbq : b ≤ D.position iq) :
    ∀ ⦃v⦄, v ∈ (D.middleRightPath ip iq a b hap hpb hbq).support →
      v ∈ D.path.support := by
  intro v hv
  rw [middleRightPath, Walk.support_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rw [Walk.support_concat, Walk.support_concat] at hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with (hv | hvx) | hvq
    · exact D.spineSegment_support_subset _ _ _ _ hv
    · rw [hvx]
      exact D.path.start_mem_support
    · rw [hvq]
      exact D.getVert_mem_path_support (D.position_le iq)
  · have hv' := List.mem_of_mem_tail hv
    rw [Walk.support_reverse, List.mem_reverse] at hv'
    exact D.spineSegment_support_subset _ _ _ _ hv'

/-- Portals on the hub side of a prescribed spine vertex. -/
def leftPortalIndices (D : EndpointFanData G x y j) (a : ℕ) :
    Finset (Fin (2 * j + 1)) :=
  Finset.univ.filter fun i ↦ D.position i ≤ a

/-- Portals strictly between two prescribed spine vertices. -/
def middlePortalIndices (D : EndpointFanData G x y j) (a b : ℕ) :
    Finset (Fin (2 * j + 1)) :=
  Finset.univ.filter fun i ↦ a < D.position i ∧ D.position i < b

/-- Portals on the far side of a prescribed spine vertex. -/
def rightPortalIndices (D : EndpointFanData G x y j) (b : ℕ) :
    Finset (Fin (2 * j + 1)) :=
  Finset.univ.filter fun i ↦ b ≤ D.position i

def outerLeftOffsets (D : EndpointFanData G x y j) (a : ℕ) : Finset ℕ :=
  (D.leftPortalIndices a).image fun i ↦ a - D.position i

def middleLeftOffsets (D : EndpointFanData G x y j) (b : ℕ) : Finset ℕ :=
  (D.middlePortalIndices 0 b).image fun i ↦ b - D.position i

def middleRightOffsets (D : EndpointFanData G x y j) (a b : ℕ) : Finset ℕ :=
  (D.middlePortalIndices a b).image fun i ↦ D.position i - a

def outerRightOffsets (D : EndpointFanData G x y j) (b : ℕ) : Finset ℕ :=
  (D.rightPortalIndices b).image fun i ↦ D.position i - b

/-- The length parameters of the outer cross-path system. -/
def outerLengthSums (D : EndpointFanData G x y j) (a b : ℕ) : Finset ℕ :=
  D.outerLeftOffsets a + D.outerRightOffsets b

/-- The length parameters of the left-middle cross-path system. -/
def middleLeftLengthSums (D : EndpointFanData G x y j) (a b : ℕ) : Finset ℕ :=
  D.outerLeftOffsets a +
    (D.middlePortalIndices a b).image (fun i ↦ b - D.position i)

/-- The length parameters of the right-middle cross-path system. -/
def middleRightLengthSums (D : EndpointFanData G x y j) (a b : ℕ) : Finset ℕ :=
  (D.middlePortalIndices a b).image (fun i ↦ D.position i - a) +
    D.outerRightOffsets b

lemma card_left_middle_right (D : EndpointFanData G x y j)
    {a b : ℕ} (hab : a < b) :
    (D.leftPortalIndices a).card + (D.middlePortalIndices a b).card +
        (D.rightPortalIndices b).card = 2 * j + 1 := by
  classical
  let A := D.leftPortalIndices a
  let B := D.middlePortalIndices a b
  let C := D.rightPortalIndices b
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have ha := (Finset.mem_filter.mp hiA).2
    have hb := (Finset.mem_filter.mp hiB).2
    omega
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro i hiAB hiC
    have hc := (Finset.mem_filter.mp hiC).2
    rcases Finset.mem_union.mp hiAB with hiA | hiB
    · have ha := (Finset.mem_filter.mp hiA).2
      omega
    · have hb := (Finset.mem_filter.mp hiB).2
      omega
  have hunion : (A ∪ B) ∪ C = Finset.univ := by
    ext i
    simp only [A, B, C, leftPortalIndices, middlePortalIndices,
      rightPortalIndices, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    omega
  calc
    A.card + B.card + C.card = (A ∪ B).card + C.card := by
      rw [Finset.card_union_of_disjoint hAB]
    _ = ((A ∪ B) ∪ C).card := by
      rw [Finset.card_union_of_disjoint hABC]
    _ = (Finset.univ : Finset (Fin (2 * j + 1))).card := by rw [hunion]
    _ = 2 * j + 1 := by simp

private lemma outerLengthSums_exists (D : EndpointFanData G x y j)
    {a b n : ℕ} (hn : n ∈ D.outerLengthSums a b) :
    ∃ z : Fin (2 * j + 1) × Fin (2 * j + 1),
      z.1 ∈ D.leftPortalIndices a ∧ z.2 ∈ D.rightPortalIndices b ∧
      (a - D.position z.1) + (D.position z.2 - b) = n := by
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.mem_add.mp hn
  obtain ⟨ip, hip, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨iq, hiq, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨(ip, iq), hip, hiq, hrs⟩

private lemma middleLeftLengthSums_exists (D : EndpointFanData G x y j)
    {a b n : ℕ} (hn : n ∈ D.middleLeftLengthSums a b) :
    ∃ z : Fin (2 * j + 1) × Fin (2 * j + 1),
      z.1 ∈ D.leftPortalIndices a ∧ z.2 ∈ D.middlePortalIndices a b ∧
      (a - D.position z.1) + (b - D.position z.2) = n := by
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.mem_add.mp hn
  obtain ⟨ip, hip, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨iq, hiq, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨(ip, iq), hip, hiq, hrs⟩

private lemma middleRightLengthSums_exists (D : EndpointFanData G x y j)
    {a b n : ℕ} (hn : n ∈ D.middleRightLengthSums a b) :
    ∃ z : Fin (2 * j + 1) × Fin (2 * j + 1),
      z.1 ∈ D.middlePortalIndices a b ∧ z.2 ∈ D.rightPortalIndices b ∧
      (D.position z.1 - a) + (D.position z.2 - b) = n := by
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.mem_add.mp hn
  obtain ⟨ip, hip, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨iq, hiq, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨(ip, iq), hip, hiq, hrs⟩

private noncomputable def outerWitness (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.outerLengthSums a b)) :
    Fin (2 * j + 1) × Fin (2 * j + 1) :=
  Classical.choose (D.outerLengthSums_exists n.2)

private noncomputable def middleLeftWitness (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleLeftLengthSums a b)) :
    Fin (2 * j + 1) × Fin (2 * j + 1) :=
  Classical.choose (D.middleLeftLengthSums_exists n.2)

private noncomputable def middleRightWitness (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleRightLengthSums a b)) :
    Fin (2 * j + 1) × Fin (2 * j + 1) :=
  Classical.choose (D.middleRightLengthSums_exists n.2)

private lemma outerWitness_spec (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.outerLengthSums a b)) :
    (D.outerWitness a b n).1 ∈ D.leftPortalIndices a ∧
      (D.outerWitness a b n).2 ∈ D.rightPortalIndices b ∧
      (a - D.position (D.outerWitness a b n).1) +
        (D.position (D.outerWitness a b n).2 - b) = n :=
  Classical.choose_spec (D.outerLengthSums_exists n.2)

private lemma outerWitness_left_le (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.outerLengthSums a b)) :
    D.position (D.outerWitness a b n).1 ≤ a := by
  exact (Finset.mem_filter.mp (D.outerWitness_spec a b n).1).2

private lemma outerWitness_right_le (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.outerLengthSums a b)) :
    b ≤ D.position (D.outerWitness a b n).2 := by
  exact (Finset.mem_filter.mp (D.outerWitness_spec a b n).2.1).2

private lemma middleLeftWitness_spec (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleLeftLengthSums a b)) :
    (D.middleLeftWitness a b n).1 ∈ D.leftPortalIndices a ∧
      (D.middleLeftWitness a b n).2 ∈ D.middlePortalIndices a b ∧
      (a - D.position (D.middleLeftWitness a b n).1) +
        (b - D.position (D.middleLeftWitness a b n).2) = n :=
  Classical.choose_spec (D.middleLeftLengthSums_exists n.2)

private lemma middleRightWitness_spec (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleRightLengthSums a b)) :
    (D.middleRightWitness a b n).1 ∈ D.middlePortalIndices a b ∧
      (D.middleRightWitness a b n).2 ∈ D.rightPortalIndices b ∧
      (D.position (D.middleRightWitness a b n).1 - a) +
        (D.position (D.middleRightWitness a b n).2 - b) = n :=
  Classical.choose_spec (D.middleRightLengthSums_exists n.2)

private lemma middleLeftWitness_left_le (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleLeftLengthSums a b)) :
    D.position (D.middleLeftWitness a b n).1 ≤ a := by
  exact (Finset.mem_filter.mp (D.middleLeftWitness_spec a b n).1).2

private lemma middleLeftWitness_middle (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleLeftLengthSums a b)) :
    a < D.position (D.middleLeftWitness a b n).2 ∧
      D.position (D.middleLeftWitness a b n).2 < b := by
  exact (Finset.mem_filter.mp (D.middleLeftWitness_spec a b n).2.1).2

private lemma middleRightWitness_middle (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleRightLengthSums a b)) :
    a < D.position (D.middleRightWitness a b n).1 ∧
      D.position (D.middleRightWitness a b n).1 < b := by
  exact (Finset.mem_filter.mp (D.middleRightWitness_spec a b n).1).2

private lemma middleRightWitness_right_le (D : EndpointFanData G x y j)
    (a b : ℕ) (n : ↥(D.middleRightLengthSums a b)) :
    b ≤ D.position (D.middleRightWitness a b n).2 := by
  exact (Finset.mem_filter.mp (D.middleRightWitness_spec a b n).2.1).2

private noncomputable def reindexDistinctSystem {u v : V} (s : Finset ℕ)
    (F : DistinctPathSystem G u v ↥s) :
    DistinctPathSystem G u v (Fin s.card) where
  path i := F.path ((Finset.equivFin s).symm i)
  isPath i := F.isPath ((Finset.equivFin s).symm i)
  length_injective := F.length_injective.comp (Finset.equivFin s).symm.injective

/-- The outer Cauchy--Davenport system, indexed by its exact set of length
parameters. -/
noncomputable def outerDistinctSystem (D : EndpointFanData G x y j)
    {a b : ℕ} (hab : a < b) :
    DistinctPathSystem G (D.path.getVert a) (D.path.getVert b)
      (Fin (D.outerLengthSums a b).card) := by
  let raw : DistinctPathSystem G (D.path.getVert a) (D.path.getVert b)
      ↥(D.outerLengthSums a b) :=
    { path := fun n ↦
        D.outerPath (D.outerWitness a b n).1 (D.outerWitness a b n).2 a b
          (D.outerWitness_left_le a b n) hab (D.outerWitness_right_le a b n)
      isPath := fun n ↦ D.outerPath_isPath _ _ _ _
        (D.outerWitness_left_le a b n) hab (D.outerWitness_right_le a b n)
      length_injective := by
        intro n m hlen
        apply Subtype.ext
        simp only at hlen
        rw [D.length_outerPath, D.length_outerPath] at hlen
        have hn := (D.outerWitness_spec a b n).2.2
        have hm := (D.outerWitness_spec a b m).2.2
        omega }
  exact reindexDistinctSystem _ raw

/-- The left-middle Cauchy--Davenport system. -/
noncomputable def middleLeftDistinctSystem (D : EndpointFanData G x y j)
    {a b : ℕ} (hab : a < b) (hb : b ≤ D.path.length) :
    DistinctPathSystem G (D.path.getVert a) (D.path.getVert b)
      (Fin (D.middleLeftLengthSums a b).card) := by
  let raw : DistinctPathSystem G (D.path.getVert a) (D.path.getVert b)
      ↥(D.middleLeftLengthSums a b) :=
    { path := fun n ↦
        D.middleLeftPath (D.middleLeftWitness a b n).1
          (D.middleLeftWitness a b n).2 a b
          (D.middleLeftWitness_left_le a b n)
          (D.middleLeftWitness_middle a b n).1
          (D.middleLeftWitness_middle a b n).2 hb
      isPath := fun n ↦ D.middleLeftPath_isPath _ _ _ _
        (D.middleLeftWitness_left_le a b n)
        (D.middleLeftWitness_middle a b n).1
        (D.middleLeftWitness_middle a b n).2 hb
      length_injective := by
        intro n m hlen
        apply Subtype.ext
        simp only at hlen
        rw [D.length_middleLeftPath, D.length_middleLeftPath] at hlen
        have hn := (D.middleLeftWitness_spec a b n).2.2
        have hm := (D.middleLeftWitness_spec a b m).2.2
        omega }
  exact reindexDistinctSystem _ raw

/-- The right-middle Cauchy--Davenport system. -/
noncomputable def middleRightDistinctSystem (D : EndpointFanData G x y j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    DistinctPathSystem G (D.path.getVert a) (D.path.getVert b)
      (Fin (D.middleRightLengthSums a b).card) := by
  let raw : DistinctPathSystem G (D.path.getVert a) (D.path.getVert b)
      ↥(D.middleRightLengthSums a b) :=
    { path := fun n ↦
        D.middleRightPath (D.middleRightWitness a b n).1
          (D.middleRightWitness a b n).2 a b
          (D.middleRightWitness_middle a b n).1
          (D.middleRightWitness_middle a b n).2
          (D.middleRightWitness_right_le a b n)
      isPath := fun n ↦ D.middleRightPath_isPath _ _ _ _ ha
        (D.middleRightWitness_middle a b n).1
        (D.middleRightWitness_middle a b n).2
        (D.middleRightWitness_right_le a b n)
      length_injective := by
        intro n m hlen
        apply Subtype.ext
        simp only at hlen
        rw [D.length_middleRightPath, D.length_middleRightPath] at hlen
        have hn := (D.middleRightWitness_spec a b n).2.2
        have hm := (D.middleRightWitness_spec a b m).2.2
        omega }
  exact reindexDistinctSystem _ raw

lemma card_outerLeftOffsets (D : EndpointFanData G x y j) (a : ℕ) :
    (D.outerLeftOffsets a).card = (D.leftPortalIndices a).card := by
  classical
  apply Finset.card_image_of_injOn
  intro i hi i' hi' heq
  apply D.position_injective
  change a - D.position i = a - D.position i' at heq
  have hi := (Finset.mem_filter.mp hi).2
  have hi' := (Finset.mem_filter.mp hi').2
  omega

lemma card_outerRightOffsets (D : EndpointFanData G x y j) (b : ℕ) :
    (D.outerRightOffsets b).card = (D.rightPortalIndices b).card := by
  classical
  apply Finset.card_image_of_injOn
  intro i hi i' hi' heq
  apply D.position_injective
  change D.position i - b = D.position i' - b at heq
  have hi := (Finset.mem_filter.mp hi).2
  have hi' := (Finset.mem_filter.mp hi').2
  omega

lemma card_middleLeftOffsets (D : EndpointFanData G x y j) (a b : ℕ) :
    ((D.middlePortalIndices a b).image
      (fun i ↦ b - D.position i)).card =
      (D.middlePortalIndices a b).card := by
  classical
  apply Finset.card_image_of_injOn
  intro i hi i' hi' heq
  apply D.position_injective
  change b - D.position i = b - D.position i' at heq
  have hi := (Finset.mem_filter.mp hi).2
  have hi' := (Finset.mem_filter.mp hi').2
  omega

lemma card_middleRightOffsets (D : EndpointFanData G x y j) (a b : ℕ) :
    ((D.middlePortalIndices a b).image
      (fun i ↦ D.position i - a)).card =
      (D.middlePortalIndices a b).card := by
  classical
  apply Finset.card_image_of_injOn
  intro i hi i' hi' heq
  apply D.position_injective
  change D.position i - a = D.position i' - a at heq
  have hi := (Finset.mem_filter.mp hi).2
  have hi' := (Finset.mem_filter.mp hi').2
  omega

lemma card_outerLengthSums_lower (D : EndpointFanData G x y j)
    {a b : ℕ} (hleft : (D.leftPortalIndices a).Nonempty)
    (hright : (D.rightPortalIndices b).Nonempty) :
    (D.leftPortalIndices a).card + (D.rightPortalIndices b).card - 1 ≤
      (D.outerLengthSums a b).card := by
  have hL : (D.outerLeftOffsets a).Nonempty := by
    simpa [outerLeftOffsets] using hleft.image (fun i ↦ a - D.position i)
  have hR : (D.outerRightOffsets b).Nonempty := by
    simpa [outerRightOffsets] using hright.image (fun i ↦ D.position i - b)
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hL hR
  rw [D.card_outerLeftOffsets, D.card_outerRightOffsets] at hcd
  exact hcd

lemma card_middleLeftLengthSums_lower (D : EndpointFanData G x y j)
    {a b : ℕ} (hleft : (D.leftPortalIndices a).Nonempty)
    (hmiddle : (D.middlePortalIndices a b).Nonempty) :
    (D.leftPortalIndices a).card + (D.middlePortalIndices a b).card - 1 ≤
      (D.middleLeftLengthSums a b).card := by
  have hL : (D.outerLeftOffsets a).Nonempty := by
    simpa [outerLeftOffsets] using hleft.image (fun i ↦ a - D.position i)
  have hM : ((D.middlePortalIndices a b).image
      (fun i ↦ b - D.position i)).Nonempty := by
    exact hmiddle.image (fun i ↦ b - D.position i)
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hL hM
  rw [D.card_outerLeftOffsets, D.card_middleLeftOffsets] at hcd
  exact hcd

lemma card_middleRightLengthSums_lower (D : EndpointFanData G x y j)
    {a b : ℕ} (hmiddle : (D.middlePortalIndices a b).Nonempty)
    (hright : (D.rightPortalIndices b).Nonempty) :
    (D.middlePortalIndices a b).card + (D.rightPortalIndices b).card - 1 ≤
      (D.middleRightLengthSums a b).card := by
  have hM : ((D.middlePortalIndices a b).image
      (fun i ↦ D.position i - a)).Nonempty := by
    exact hmiddle.image (fun i ↦ D.position i - a)
  have hR : (D.outerRightOffsets b).Nonempty := by
    simpa [outerRightOffsets] using hright.image (fun i ↦ D.position i - b)
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hM hR
  rw [D.card_middleRightOffsets, D.card_outerRightOffsets] at hcd
  exact hcd

lemma outerPath_sameParity_of_all_odd (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i))
    {ip iq ip' iq' : Fin (2 * j + 1)} {a b : ℕ}
    (hpa : D.position ip ≤ a) (hab : a < b) (hbq : b ≤ D.position iq)
    (hpa' : D.position ip' ≤ a) (hbq' : b ≤ D.position iq') :
    (D.outerPath ip iq a b hpa hab hbq).length % 2 =
      (D.outerPath ip' iq' a b hpa' hab hbq').length % 2 := by
  rw [D.length_outerPath, D.length_outerPath]
  have hip := hall ip
  have hiq := hall iq
  have hip' := hall ip'
  have hiq' := hall iq'
  rw [Nat.odd_iff] at hip hiq hip' hiq'
  omega

lemma middleLeftPath_sameParity_of_all_odd (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i))
    {ip iq ip' iq' : Fin (2 * j + 1)} {a b : ℕ}
    (hpa : D.position ip ≤ a) (haq : a < D.position iq)
    (hqb : D.position iq < b) (hb : b ≤ D.path.length)
    (hpa' : D.position ip' ≤ a) (haq' : a < D.position iq')
    (hqb' : D.position iq' < b) :
    (D.middleLeftPath ip iq a b hpa haq hqb hb).length % 2 =
      (D.middleLeftPath ip' iq' a b hpa' haq' hqb' hb).length % 2 := by
  rw [D.length_middleLeftPath, D.length_middleLeftPath]
  have hip := hall ip
  have hiq := hall iq
  have hip' := hall ip'
  have hiq' := hall iq'
  rw [Nat.odd_iff] at hip hiq hip' hiq'
  omega

lemma middleRightPath_sameParity_of_all_odd (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i))
    {ip iq ip' iq' : Fin (2 * j + 1)} {a b : ℕ}
    (hap : a < D.position ip) (hpb : D.position ip < b)
    (hbq : b ≤ D.position iq)
    (hap' : a < D.position ip') (hpb' : D.position ip' < b)
    (hbq' : b ≤ D.position iq') :
    (D.middleRightPath ip iq a b hap hpb hbq).length % 2 =
      (D.middleRightPath ip' iq' a b hap' hpb' hbq').length % 2 := by
  rw [D.length_middleRightPath, D.length_middleRightPath]
  have hip := hall ip
  have hiq := hall iq
  have hip' := hall ip'
  have hiq' := hall iq'
  rw [Nat.odd_iff] at hip hiq hip' hiq'
  omega

private def distinctSystemToPathFamily {u v : V} {r : ℕ}
    (F : DistinctPathSystem G u v (Fin r))
    (hparity : ∀ i i', (F.path i).length % 2 = (F.path i').length % 2) :
    PathFamily G u v (Fin r) where
  path := F.path
  isPath := F.isPath
  length_injective := F.length_injective
  sameParity := hparity

private def takePathFamily {u v : V} {r q : ℕ}
    (F : PathFamily G u v (Fin r)) (hqr : q ≤ r) :
    PathFamily G u v (Fin q) where
  path i := F.path ⟨i, lt_of_lt_of_le i.isLt hqr⟩
  isPath i := F.isPath ⟨i, lt_of_lt_of_le i.isLt hqr⟩
  length_injective := by
    intro i i' hii'
    have hbig : (⟨i, lt_of_lt_of_le i.isLt hqr⟩ : Fin r) =
        ⟨i', lt_of_lt_of_le i'.isLt hqr⟩ := F.length_injective hii'
    apply Fin.ext
    exact congrArg (fun z : Fin r ↦ z.val) hbig
  sameParity i i' := F.sameParity _ _

private def takeSupportedPathFamily (D : EndpointFanData G x y j)
    {a b r q : ℕ} (F : SpineSupportedPathFamily D a b r) (hqr : q ≤ r) :
    SpineSupportedPathFamily D a b q where
  family := takePathFamily F.family hqr
  support_subset i v hv :=
    F.support_subset ⟨i, lt_of_lt_of_le i.isLt hqr⟩ v hv

private def takeFanSupportedPathFamily (D : EndpointFanData G x y j)
    {u v : V} {r q : ℕ} (F : FanSupportedPathFamily D u v r) (hqr : q ≤ r) :
    FanSupportedPathFamily D u v q where
  family := takePathFamily F.family hqr
  support_subset i z hz :=
    F.support_subset ⟨i, lt_of_lt_of_le i.isLt hqr⟩ z hz

private def castFanSupportedPathFamily (D : EndpointFanData G x y j)
    {u u' v v' : V} {r : ℕ} (F : FanSupportedPathFamily D u v r)
    (hu : u = u') (hv : v = v') : FanSupportedPathFamily D u' v' r := by
  subst u'
  subst v'
  exact F

lemma outerDistinctSystem_sameParity (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b) :
    ∀ i i', ((D.outerDistinctSystem hab).path i).length % 2 =
      ((D.outerDistinctSystem hab).path i').length % 2 := by
  intro i i'
  simp only [outerDistinctSystem, reindexDistinctSystem]
  apply D.outerPath_sameParity_of_all_odd hall

lemma middleLeftDistinctSystem_sameParity (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b)
    (hb : b ≤ D.path.length) :
    ∀ i i', ((D.middleLeftDistinctSystem hab hb).path i).length % 2 =
      ((D.middleLeftDistinctSystem hab hb).path i').length % 2 := by
  intro i i'
  simp only [middleLeftDistinctSystem, reindexDistinctSystem]
  apply D.middleLeftPath_sameParity_of_all_odd hall

lemma middleRightDistinctSystem_sameParity (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i i', ((D.middleRightDistinctSystem ha hab).path i).length % 2 =
      ((D.middleRightDistinctSystem ha hab).path i').length % 2 := by
  intro i i'
  simp only [middleRightDistinctSystem, reindexDistinctSystem]
  apply D.middleRightPath_sameParity_of_all_odd hall

noncomputable def outerPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b) :
    PathFamily G (D.path.getVert a) (D.path.getVert b)
      (Fin (D.outerLengthSums a b).card) :=
  distinctSystemToPathFamily (D.outerDistinctSystem hab)
    (D.outerDistinctSystem_sameParity hall hab)

noncomputable def middleLeftPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b)
    (hb : b ≤ D.path.length) :
    PathFamily G (D.path.getVert a) (D.path.getVert b)
      (Fin (D.middleLeftLengthSums a b).card) :=
  distinctSystemToPathFamily (D.middleLeftDistinctSystem hab hb)
    (D.middleLeftDistinctSystem_sameParity hall hab hb)

noncomputable def middleRightPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (ha : 0 < a)
    (hab : a < b) :
    PathFamily G (D.path.getVert a) (D.path.getVert b)
      (Fin (D.middleRightLengthSums a b).card) :=
  distinctSystemToPathFamily (D.middleRightDistinctSystem ha hab)
    (D.middleRightDistinctSystem_sameParity hall ha hab)

lemma outerPathFamily_support_subset (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b) :
    ∀ i v, v ∈ ((D.outerPathFamily hall hab).path i).support →
      v ∈ D.path.support := by
  intro i v hv
  simp only [outerPathFamily, distinctSystemToPathFamily, outerDistinctSystem,
    reindexDistinctSystem] at hv
  exact D.outerPath_support_subset _ _ _ _ _ _ _ hv

lemma middleLeftPathFamily_support_subset (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b)
    (hb : b ≤ D.path.length) :
    ∀ i v, v ∈ ((D.middleLeftPathFamily hall hab hb).path i).support →
      v ∈ D.path.support := by
  intro i v hv
  simp only [middleLeftPathFamily, distinctSystemToPathFamily,
    middleLeftDistinctSystem, reindexDistinctSystem] at hv
  exact D.middleLeftPath_support_subset _ _ _ _ _ _ _ _ hv

lemma middleRightPathFamily_support_subset (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i v, v ∈ ((D.middleRightPathFamily hall ha hab).path i).support →
      v ∈ D.path.support := by
  intro i v hv
  simp only [middleRightPathFamily, distinctSystemToPathFamily,
    middleRightDistinctSystem, reindexDistinctSystem] at hv
  exact D.middleRightPath_support_subset _ _ _ _ _ _ _ hv

noncomputable def outerSupportedPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b) :
    SpineSupportedPathFamily D a b (D.outerLengthSums a b).card where
  family := D.outerPathFamily hall hab
  support_subset := D.outerPathFamily_support_subset hall hab

noncomputable def middleLeftSupportedPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (hab : a < b)
    (hb : b ≤ D.path.length) :
    SpineSupportedPathFamily D a b (D.middleLeftLengthSums a b).card where
  family := D.middleLeftPathFamily hall hab hb
  support_subset := D.middleLeftPathFamily_support_subset hall hab hb

noncomputable def middleRightSupportedPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {a b : ℕ} (ha : 0 < a)
    (hab : a < b) :
    SpineSupportedPathFamily D a b (D.middleRightLengthSums a b).card where
  family := D.middleRightPathFamily hall ha hab
  support_subset := D.middleRightPathFamily_support_subset hall ha hab

/-- Portals strictly beyond a prescribed spine position. -/
def strictRightPortalIndices (D : EndpointFanData G x y j) (b : ℕ) :
    Finset (Fin (2 * j + 1)) :=
  Finset.univ.filter fun i ↦ b < D.position i

/-- Hub-to-spine path through a portal at or before the target. -/
def hubLeftPath (D : EndpointFanData G x y j) (i : Fin (2 * j + 1))
    (b : ℕ) (hib : D.position i ≤ b) (hb : b ≤ D.path.length) :
    G.Walk x (D.path.getVert b) :=
  Walk.cons (D.spoke i) (D.spineSegment (D.position i) b hib hb)

/-- Hub-to-spine path through a portal strictly beyond the target. -/
def hubRightPath (D : EndpointFanData G x y j) (i : Fin (2 * j + 1))
    (b : ℕ) (hbi : b < D.position i) :
    G.Walk x (D.path.getVert b) :=
  Walk.cons (D.spoke i)
    (D.spineSegment b (D.position i) hbi.le (D.position_le i)).reverse

@[simp] lemma length_hubLeftPath (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (b : ℕ)
    (hib : D.position i ≤ b) (hb : b ≤ D.path.length) :
    (D.hubLeftPath i b hib hb).length = b - D.position i + 1 := by
  simp [hubLeftPath]

@[simp] lemma length_hubRightPath (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (b : ℕ) (hbi : b < D.position i) :
    (D.hubRightPath i b hbi).length = D.position i - b + 1 := by
  simp [hubRightPath]

lemma hubLeftPath_isPath (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (b : ℕ)
    (hib : D.position i ≤ b) (hb : b ≤ D.path.length) :
    (D.hubLeftPath i b hib hb).IsPath := by
  apply (D.spineSegment_isPath _ _ _ _).cons
  exact D.hub_notMem_spineSegment _ _ (D.position_pos i) _ _

lemma hubRightPath_isPath (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (b : ℕ) (hb0 : 0 < b)
    (hbi : b < D.position i) :
    (D.hubRightPath i b hbi).IsPath := by
  apply (D.spineSegment_isPath _ _ _ _).reverse.cons
  rw [Walk.support_reverse, List.mem_reverse]
  exact D.hub_notMem_spineSegment _ _ hb0 _ _

lemma hubLeftPath_support_subset (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (b : ℕ)
    (hib : D.position i ≤ b) (hb : b ≤ D.path.length) :
    ∀ ⦃v⦄, v ∈ (D.hubLeftPath i b hib hb).support → v ∈ D.path.support := by
  intro v hv
  rw [hubLeftPath, Walk.support_cons] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact D.path.start_mem_support
  · exact D.spineSegment_support_subset _ _ _ _ hv

lemma hubRightPath_support_subset (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (b : ℕ) (hbi : b < D.position i) :
    ∀ ⦃v⦄, v ∈ (D.hubRightPath i b hbi).support → v ∈ D.path.support := by
  intro v hv
  rw [hubRightPath, Walk.support_cons] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact D.path.start_mem_support
  · rw [Walk.support_reverse, List.mem_reverse] at hv
    exact D.spineSegment_support_subset _ _ _ _ hv

noncomputable def hubLeftPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {b : ℕ} (hb : b ≤ D.path.length) :
    PathFamily G x (D.path.getVert b) (Fin (D.leftPortalIndices b).card) := by
  let e := (Finset.equivFin (D.leftPortalIndices b)).symm
  let pick : Fin (D.leftPortalIndices b).card → Fin (2 * j + 1) :=
    fun r ↦ (e r).1
  have hpick : ∀ r, D.position (pick r) ≤ b := by
    intro r
    exact (Finset.mem_filter.mp (e r).2).2
  refine
    { path := fun r ↦ D.hubLeftPath (pick r) b (hpick r) hb
      isPath := fun r ↦ D.hubLeftPath_isPath (pick r) b (hpick r) hb
      length_injective := ?_
      sameParity := ?_ }
  · intro r s hrs
    simp only at hrs
    rw [D.length_hubLeftPath, D.length_hubLeftPath] at hrs
    have hpr := hpick r
    have hps := hpick s
    have hpos : D.position (pick r) = D.position (pick s) := by omega
    have hpickeq := D.position_injective hpos
    apply (Finset.equivFin (D.leftPortalIndices b)).symm.injective
    exact Subtype.ext hpickeq
  · intro r s
    rw [D.length_hubLeftPath, D.length_hubLeftPath]
    have hr := hall (pick r)
    have hs := hall (pick s)
    rw [Nat.odd_iff] at hr hs
    have hpr := hpick r
    have hps := hpick s
    omega

noncomputable def hubRightPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {b : ℕ} (hb0 : 0 < b) :
    PathFamily G x (D.path.getVert b) (Fin (D.strictRightPortalIndices b).card) := by
  let e := (Finset.equivFin (D.strictRightPortalIndices b)).symm
  let pick : Fin (D.strictRightPortalIndices b).card → Fin (2 * j + 1) :=
    fun r ↦ (e r).1
  have hpick : ∀ r, b < D.position (pick r) := by
    intro r
    exact (Finset.mem_filter.mp (e r).2).2
  refine
    { path := fun r ↦ D.hubRightPath (pick r) b (hpick r)
      isPath := fun r ↦ D.hubRightPath_isPath (pick r) b hb0 (hpick r)
      length_injective := ?_
      sameParity := ?_ }
  · intro r s hrs
    simp only at hrs
    rw [D.length_hubRightPath, D.length_hubRightPath] at hrs
    have hpr := hpick r
    have hps := hpick s
    have hpos : D.position (pick r) = D.position (pick s) := by omega
    have hpickeq := D.position_injective hpos
    apply (Finset.equivFin (D.strictRightPortalIndices b)).symm.injective
    exact Subtype.ext hpickeq
  · intro r s
    rw [D.length_hubRightPath, D.length_hubRightPath]
    have hr := hall (pick r)
    have hs := hall (pick s)
    rw [Nat.odd_iff] at hr hs
    have hpr := hpick r
    have hps := hpick s
    omega

lemma hubLeftPathFamily_support_subset (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {b : ℕ} (hb : b ≤ D.path.length) :
    ∀ i v, v ∈ ((D.hubLeftPathFamily hall hb).path i).support →
      v ∈ D.path.support := by
  intro i v hv
  simp only [hubLeftPathFamily] at hv
  exact D.hubLeftPath_support_subset _ _ _ _ hv

lemma hubRightPathFamily_support_subset (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {b : ℕ} (hb0 : 0 < b) :
    ∀ i v, v ∈ ((D.hubRightPathFamily hall hb0).path i).support →
      v ∈ D.path.support := by
  intro i v hv
  simp only [hubRightPathFamily] at hv
  exact D.hubRightPath_support_subset _ _ _ hv

noncomputable def hubLeftFanSupportedPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {b : ℕ} (hb : b ≤ D.path.length) :
    FanSupportedPathFamily D x (D.path.getVert b)
      (D.leftPortalIndices b).card where
  family := D.hubLeftPathFamily hall hb
  support_subset := D.hubLeftPathFamily_support_subset hall hb

noncomputable def hubRightFanSupportedPathFamily (D : EndpointFanData G x y j)
    (hall : ∀ i, Odd (D.position i)) {b : ℕ} (hb0 : 0 < b) :
    FanSupportedPathFamily D x (D.path.getVert b)
      (D.strictRightPortalIndices b).card where
  family := D.hubRightPathFamily hall hb0
  support_subset := D.hubRightPathFamily_support_subset hall hb0

lemma card_left_add_strictRight (D : EndpointFanData G x y j) (b : ℕ) :
    (D.leftPortalIndices b).card + (D.strictRightPortalIndices b).card =
      2 * j + 1 := by
  classical
  have hdis : Disjoint (D.leftPortalIndices b) (D.strictRightPortalIndices b) := by
    rw [Finset.disjoint_left]
    intro i hi hri
    have hi := (Finset.mem_filter.mp hi).2
    have hri := (Finset.mem_filter.mp hri).2
    omega
  have hunion : D.leftPortalIndices b ∪ D.strictRightPortalIndices b = Finset.univ := by
    ext i
    simp [leftPortalIndices, strictRightPortalIndices]
    omega
  rw [← Finset.card_union_of_disjoint hdis, hunion]
  simp

theorem allOdd_pathFamily_from_hub (D : EndpointFanData G x y j)
    (hj : 1 ≤ j) (hall : ∀ i, Odd (D.position i))
    {b : ℕ} (hb0 : 0 < b) (hb : b ≤ D.path.length) :
    Nonempty (PathFamily G x (D.path.getVert b) (Fin (j + 1))) := by
  have hcard := D.card_left_add_strictRight b
  by_cases hleft : j + 1 ≤ (D.leftPortalIndices b).card
  · exact ⟨takePathFamily (D.hubLeftPathFamily hall hb) hleft⟩
  · have hright : j + 1 ≤ (D.strictRightPortalIndices b).card := by omega
    exact ⟨takePathFamily (D.hubRightPathFamily hall hb0) hright⟩

theorem allOdd_supportedPathFamily_from_hub (D : EndpointFanData G x y j)
    (hj : 1 ≤ j) (hall : ∀ i, Odd (D.position i))
    {b : ℕ} (hb0 : 0 < b) (hb : b ≤ D.path.length) :
    Nonempty (FanSupportedPathFamily D x (D.path.getVert b) (j + 1)) := by
  have hcard := D.card_left_add_strictRight b
  by_cases hleft : j + 1 ≤ (D.leftPortalIndices b).card
  · exact ⟨takeFanSupportedPathFamily D
      (D.hubLeftFanSupportedPathFamily hall hb) hleft⟩
  · have hright : j + 1 ≤ (D.strictRightPortalIndices b).card := by omega
    exact ⟨takeFanSupportedPathFamily D
      (D.hubRightFanSupportedPathFamily hall hb0) hright⟩

lemma leftPortalIndices_nonempty_of_position_one
    (D : EndpointFanData G x y j) {i : Fin (2 * j + 1)}
    (hi : D.position i = 1) {a : ℕ} (ha : 0 < a) :
    (D.leftPortalIndices a).Nonempty := by
  refine ⟨i, ?_⟩
  simp [leftPortalIndices, hi]
  omega

lemma rightPortalIndices_nonempty_of_position_length
    (D : EndpointFanData G x y j) {i : Fin (2 * j + 1)}
    (hi : D.position i = D.path.length) {b : ℕ}
    (hb : b ≤ D.path.length) :
    (D.rightPortalIndices b).Nonempty := by
  refine ⟨i, ?_⟩
  simp [rightPortalIndices, hi, hb]

/-- The nonexceptional part of the arbitrary-spine-vertex fan lemma.
The only omitted configuration has `j = 1` and exactly one portal in each
of the three intervals; it is handled by the four-path argument below. -/
theorem allOdd_pathFamily_between_ordered_nonexceptional
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b ≤ D.path.length)
    (hnexceptional : ¬(j = 1 ∧
      (D.leftPortalIndices a).card = 1 ∧
      (D.middlePortalIndices a b).card = 1 ∧
      (D.rightPortalIndices b).card = 1)) :
    Nonempty (PathFamily G (D.path.getVert a) (D.path.getVert b) (Fin (j + 1))) := by
  have hA : (D.leftPortalIndices a).Nonempty :=
    D.leftPortalIndices_nonempty_of_position_one hfirst ha
  have hC : (D.rightPortalIndices b).Nonempty :=
    D.rightPortalIndices_nonempty_of_position_length hlast hb
  have hpart := D.card_left_middle_right hab
  by_cases hB : (D.middlePortalIndices a b).Nonempty
  · have houter := D.card_outerLengthSums_lower hA hC
    by_cases hA2 : 2 ≤ (D.leftPortalIndices a).card
    · have hmiddle := D.card_middleLeftLengthSums_lower hA hB
      have hsum : 2 * j + 1 ≤
          (D.outerLengthSums a b).card +
            (D.middleLeftLengthSums a b).card := by omega
      by_cases hout : j + 1 ≤ (D.outerLengthSums a b).card
      · exact ⟨takePathFamily (D.outerPathFamily hall hab) hout⟩
      · have hmid : j + 1 ≤ (D.middleLeftLengthSums a b).card := by omega
        exact ⟨takePathFamily (D.middleLeftPathFamily hall hab hb) hmid⟩
    · have hAcard : (D.leftPortalIndices a).card = 1 := by
        have hApos := Finset.card_pos.mpr hA
        omega
      by_cases hC2 : 2 ≤ (D.rightPortalIndices b).card
      · have hmiddle := D.card_middleRightLengthSums_lower hB hC
        have hsum : 2 * j + 1 ≤
            (D.outerLengthSums a b).card +
              (D.middleRightLengthSums a b).card := by omega
        by_cases hout : j + 1 ≤ (D.outerLengthSums a b).card
        · exact ⟨takePathFamily (D.outerPathFamily hall hab) hout⟩
        · have hmid : j + 1 ≤ (D.middleRightLengthSums a b).card := by omega
          exact ⟨takePathFamily (D.middleRightPathFamily hall ha hab) hmid⟩
      · have hCcard : (D.rightPortalIndices b).card = 1 := by
          have hCpos := Finset.card_pos.mpr hC
          omega
        by_cases hj2 : 2 ≤ j
        · have hmiddle := D.card_middleLeftLengthSums_lower hA hB
          have hlarge : j + 1 ≤ (D.middleLeftLengthSums a b).card := by
            omega
          exact ⟨takePathFamily (D.middleLeftPathFamily hall hab hb) hlarge⟩
        · have hjone : j = 1 := by omega
          have hBcard : (D.middlePortalIndices a b).card = 1 := by omega
          exact (hnexceptional ⟨hjone, hAcard, hBcard, hCcard⟩).elim
  · have hBcard : (D.middlePortalIndices a b).card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hB ▸ rfl
    have houter := D.card_outerLengthSums_lower hA hC
    have hlarge : j + 1 ≤ (D.outerLengthSums a b).card := by omega
    exact ⟨takePathFamily (D.outerPathFamily hall hab) hlarge⟩

theorem allOdd_supportedPathFamily_between_ordered_nonexceptional
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b ≤ D.path.length)
    (hnexceptional : ¬(j = 1 ∧
      (D.leftPortalIndices a).card = 1 ∧
      (D.middlePortalIndices a b).card = 1 ∧
      (D.rightPortalIndices b).card = 1)) :
    Nonempty (SpineSupportedPathFamily D a b (j + 1)) := by
  have hA : (D.leftPortalIndices a).Nonempty :=
    D.leftPortalIndices_nonempty_of_position_one hfirst ha
  have hC : (D.rightPortalIndices b).Nonempty :=
    D.rightPortalIndices_nonempty_of_position_length hlast hb
  have hpart := D.card_left_middle_right hab
  by_cases hB : (D.middlePortalIndices a b).Nonempty
  · have houter := D.card_outerLengthSums_lower hA hC
    by_cases hA2 : 2 ≤ (D.leftPortalIndices a).card
    · have hmiddle := D.card_middleLeftLengthSums_lower hA hB
      have hsum : 2 * j + 1 ≤
          (D.outerLengthSums a b).card +
            (D.middleLeftLengthSums a b).card := by omega
      by_cases hout : j + 1 ≤ (D.outerLengthSums a b).card
      · exact ⟨takeSupportedPathFamily D (D.outerSupportedPathFamily hall hab) hout⟩
      · have hmid : j + 1 ≤ (D.middleLeftLengthSums a b).card := by omega
        exact ⟨takeSupportedPathFamily D
          (D.middleLeftSupportedPathFamily hall hab hb) hmid⟩
    · have hAcard : (D.leftPortalIndices a).card = 1 := by
        have hApos := Finset.card_pos.mpr hA
        omega
      by_cases hC2 : 2 ≤ (D.rightPortalIndices b).card
      · have hmiddle := D.card_middleRightLengthSums_lower hB hC
        have hsum : 2 * j + 1 ≤
            (D.outerLengthSums a b).card +
              (D.middleRightLengthSums a b).card := by omega
        by_cases hout : j + 1 ≤ (D.outerLengthSums a b).card
        · exact ⟨takeSupportedPathFamily D (D.outerSupportedPathFamily hall hab) hout⟩
        · have hmid : j + 1 ≤ (D.middleRightLengthSums a b).card := by omega
          exact ⟨takeSupportedPathFamily D
            (D.middleRightSupportedPathFamily hall ha hab) hmid⟩
      · have hCcard : (D.rightPortalIndices b).card = 1 := by
          have hCpos := Finset.card_pos.mpr hC
          omega
        by_cases hj2 : 2 ≤ j
        · have hmiddle := D.card_middleLeftLengthSums_lower hA hB
          have hlarge : j + 1 ≤ (D.middleLeftLengthSums a b).card := by omega
          exact ⟨takeSupportedPathFamily D
            (D.middleLeftSupportedPathFamily hall hab hb) hlarge⟩
        · have hjone : j = 1 := by omega
          have hBcard : (D.middlePortalIndices a b).card = 1 := by omega
          exact (hnexceptional ⟨hjone, hAcard, hBcard, hCcard⟩).elim
  · have hBcard : (D.middlePortalIndices a b).card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hB ▸ rfl
    have houter := D.card_outerLengthSums_lower hA hC
    have hlarge : j + 1 ≤ (D.outerLengthSums a b).card := by omega
    exact ⟨takeSupportedPathFamily D (D.outerSupportedPathFamily hall hab) hlarge⟩

private def pairPathFamily {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (hlength : p.length ≠ q.length)
    (hparity : p.length % 2 = q.length % 2) :
    PathFamily G u v (Fin 2) where
  path i := if i.val = 0 then p else q
  isPath i := by
    fin_cases i <;> simp [hp, hq]
  length_injective := by
    intro i i' hii'
    fin_cases i <;> fin_cases i' <;> simp_all
  sameParity i i' := by
    fin_cases i <;> fin_cases i' <;> simp_all [hparity]

private def pairSpineSupportedPathFamily (D : EndpointFanData G x y j)
    {a b : ℕ} (p q : G.Walk (D.path.getVert a) (D.path.getVert b))
    (hp : p.IsPath) (hq : q.IsPath) (hlength : p.length ≠ q.length)
    (hparity : p.length % 2 = q.length % 2)
    (hps : ∀ ⦃v⦄, v ∈ p.support → v ∈ D.path.support)
    (hqs : ∀ ⦃v⦄, v ∈ q.support → v ∈ D.path.support) :
    SpineSupportedPathFamily D a b 2 where
  family := pairPathFamily p q hp hq hlength hparity
  support_subset i v hv := by
    fin_cases i <;> simp_all [pairPathFamily]

/-- The sole small exceptional placement in the cross-system count.
Four explicit paths have length sums differing by two, so two of them have
different lengths. -/
theorem allOdd_pathFamily_between_ordered_exceptional
    (D : EndpointFanData G x y j) (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b ≤ D.path.length)
    (hjone : j = 1)
    (hBcard : (D.middlePortalIndices a b).card = 1) :
    Nonempty (PathFamily G (D.path.getVert a) (D.path.getVert b) (Fin (j + 1))) := by
  have hB : (D.middlePortalIndices a b).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨iMid, hiMid⟩ := hB
  have hmid : a < D.position iMid ∧ D.position iMid < b :=
    (Finset.mem_filter.mp hiMid).2
  have hfirstA : D.position iFirst ≤ a := by omega
  have hlastC : b ≤ D.position iLast := by omega
  let direct := D.spineSegment a b hab.le hb
  let outside := D.outerPath iFirst iLast a b hfirstA hab hlastC
  let leftMiddle := D.middleLeftPath iFirst iMid a b hfirstA hmid.1 hmid.2 hb
  let rightMiddle := D.middleRightPath iMid iLast a b hmid.1 hmid.2 hlastC
  have hdirect : direct.IsPath := D.spineSegment_isPath _ _ _ _
  have houtside : outside.IsPath := D.outerPath_isPath _ _ _ _ _ _ _
  have hleftMiddle : leftMiddle.IsPath :=
    D.middleLeftPath_isPath _ _ _ _ _ _ _ _
  have hrightMiddle : rightMiddle.IsPath :=
    D.middleRightPath_isPath _ _ _ _ ha _ _ _
  have hDO : direct.length + outside.length = D.path.length + 1 := by
    simp only [direct, outside, D.length_spineSegment, D.length_outerPath]
    rw [hfirst, hlast]
    omega
  have hLR : leftMiddle.length + rightMiddle.length = D.path.length + 3 := by
    simp only [leftMiddle, rightMiddle, D.length_middleLeftPath,
      D.length_middleRightPath]
    rw [hfirst, hlast]
    omega
  have hparDO : direct.length % 2 = outside.length % 2 := by
    simp only [direct, outside, D.length_spineSegment, D.length_outerPath]
    have hlastOdd := hall iLast
    rw [hfirst, hlast]
    rw [Nat.odd_iff] at hlastOdd
    omega
  have hparDL : direct.length % 2 = leftMiddle.length % 2 := by
    simp only [direct, leftMiddle, D.length_spineSegment,
      D.length_middleLeftPath]
    have hmidOdd := hall iMid
    rw [hfirst]
    rw [Nat.odd_iff] at hmidOdd
    omega
  have hparDR : direct.length % 2 = rightMiddle.length % 2 := by
    simp only [direct, rightMiddle, D.length_spineSegment,
      D.length_middleRightPath]
    have hmidOdd := hall iMid
    have hlastOdd := hall iLast
    rw [hlast]
    rw [Nat.odd_iff] at hmidOdd hlastOdd
    omega
  subst j
  by_cases hdo : direct.length = outside.length
  · by_cases hdl : direct.length = leftMiddle.length
    · have hdr : direct.length ≠ rightMiddle.length := by
        intro hdr
        omega
      exact ⟨pairPathFamily direct rightMiddle hdirect hrightMiddle hdr hparDR⟩
    · exact ⟨pairPathFamily direct leftMiddle hdirect hleftMiddle hdl hparDL⟩
  · exact ⟨pairPathFamily direct outside hdirect houtside hdo hparDO⟩

theorem allOdd_supportedPathFamily_between_ordered_exceptional
    (D : EndpointFanData G x y j) (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b ≤ D.path.length)
    (hjone : j = 1)
    (hBcard : (D.middlePortalIndices a b).card = 1) :
    Nonempty (SpineSupportedPathFamily D a b (j + 1)) := by
  have hB : (D.middlePortalIndices a b).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨iMid, hiMid⟩ := hB
  have hmid : a < D.position iMid ∧ D.position iMid < b :=
    (Finset.mem_filter.mp hiMid).2
  have hfirstA : D.position iFirst ≤ a := by omega
  have hlastC : b ≤ D.position iLast := by omega
  let direct := D.spineSegment a b hab.le hb
  let outside := D.outerPath iFirst iLast a b hfirstA hab hlastC
  let leftMiddle := D.middleLeftPath iFirst iMid a b hfirstA hmid.1 hmid.2 hb
  let rightMiddle := D.middleRightPath iMid iLast a b hmid.1 hmid.2 hlastC
  have hdirect : direct.IsPath := D.spineSegment_isPath _ _ _ _
  have houtside : outside.IsPath := D.outerPath_isPath _ _ _ _ _ _ _
  have hleftMiddle : leftMiddle.IsPath := D.middleLeftPath_isPath _ _ _ _ _ _ _ _
  have hrightMiddle : rightMiddle.IsPath :=
    D.middleRightPath_isPath _ _ _ _ ha _ _ _
  have hsdirect : ∀ ⦃v⦄, v ∈ direct.support → v ∈ D.path.support :=
    D.spineSegment_support_subset _ _ _ _
  have hsoutside : ∀ ⦃v⦄, v ∈ outside.support → v ∈ D.path.support :=
    D.outerPath_support_subset _ _ _ _ _ _ _
  have hsleft : ∀ ⦃v⦄, v ∈ leftMiddle.support → v ∈ D.path.support :=
    D.middleLeftPath_support_subset _ _ _ _ _ _ _ _
  have hsright : ∀ ⦃v⦄, v ∈ rightMiddle.support → v ∈ D.path.support :=
    D.middleRightPath_support_subset _ _ _ _ _ _ _
  have hDO : direct.length + outside.length = D.path.length + 1 := by
    simp only [direct, outside, D.length_spineSegment, D.length_outerPath]
    rw [hfirst, hlast]
    omega
  have hLR : leftMiddle.length + rightMiddle.length = D.path.length + 3 := by
    simp only [leftMiddle, rightMiddle, D.length_middleLeftPath,
      D.length_middleRightPath]
    rw [hfirst, hlast]
    omega
  have hparDO : direct.length % 2 = outside.length % 2 := by
    simp only [direct, outside, D.length_spineSegment, D.length_outerPath]
    have hlastOdd := hall iLast
    rw [hfirst, hlast]
    rw [Nat.odd_iff] at hlastOdd
    omega
  have hparDL : direct.length % 2 = leftMiddle.length % 2 := by
    simp only [direct, leftMiddle, D.length_spineSegment, D.length_middleLeftPath]
    have hmidOdd := hall iMid
    rw [hfirst]
    rw [Nat.odd_iff] at hmidOdd
    omega
  have hparDR : direct.length % 2 = rightMiddle.length % 2 := by
    simp only [direct, rightMiddle, D.length_spineSegment,
      D.length_middleRightPath]
    have hmidOdd := hall iMid
    have hlastOdd := hall iLast
    rw [hlast]
    rw [Nat.odd_iff] at hmidOdd hlastOdd
    omega
  subst j
  by_cases hdo : direct.length = outside.length
  · by_cases hdl : direct.length = leftMiddle.length
    · have hdr : direct.length ≠ rightMiddle.length := by
        intro hdr
        omega
      exact ⟨pairSpineSupportedPathFamily D direct rightMiddle hdirect hrightMiddle
        hdr hparDR hsdirect hsright⟩
    · exact ⟨pairSpineSupportedPathFamily D direct leftMiddle hdirect hleftMiddle
        hdl hparDL hsdirect hsleft⟩
  · exact ⟨pairSpineSupportedPathFamily D direct outside hdirect houtside
      hdo hparDO hsdirect hsoutside⟩

theorem allOdd_pathFamily_between_ordered
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b ≤ D.path.length) :
    Nonempty (PathFamily G (D.path.getVert a) (D.path.getVert b) (Fin (j + 1))) := by
  by_cases hexceptional : j = 1 ∧
      (D.leftPortalIndices a).card = 1 ∧
      (D.middlePortalIndices a b).card = 1 ∧
      (D.rightPortalIndices b).card = 1
  · exact D.allOdd_pathFamily_between_ordered_exceptional hall hfirst hlast
      ha hab hb hexceptional.1 hexceptional.2.2.1
  · exact D.allOdd_pathFamily_between_ordered_nonexceptional hj hall hfirst hlast
      ha hab hb hexceptional

theorem allOdd_supportedPathFamily_between_ordered
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b ≤ D.path.length) :
    Nonempty (SpineSupportedPathFamily D a b (j + 1)) := by
  by_cases hexceptional : j = 1 ∧
      (D.leftPortalIndices a).card = 1 ∧
      (D.middlePortalIndices a b).card = 1 ∧
      (D.rightPortalIndices b).card = 1
  · exact D.allOdd_supportedPathFamily_between_ordered_exceptional hall hfirst hlast
      ha hab hb hexceptional.1 hexceptional.2.2.1
  · exact D.allOdd_supportedPathFamily_between_ordered_nonexceptional
      hj hall hfirst hlast ha hab hb hexceptional

private def reversePathFamily {u v : V} {r : ℕ}
    (F : PathFamily G u v (Fin r)) : PathFamily G v u (Fin r) where
  path i := (F.path i).reverse
  isPath i := (F.isPath i).reverse
  length_injective := by
    simpa only [Walk.length_reverse] using F.length_injective
  sameParity i i' := by
    simpa only [Walk.length_reverse] using F.sameParity i i'

private def reverseFanSupportedPathFamily (D : EndpointFanData G x y j)
    {u v : V} {r : ℕ} (F : FanSupportedPathFamily D u v r) :
    FanSupportedPathFamily D v u r where
  family := reversePathFamily F.family
  support_subset i z hz := by
    apply F.support_subset i z
    simpa only [reversePathFamily, Walk.support_reverse, List.mem_reverse] using hz

/-- Arbitrary-pair version of the all-odd endpoint-fan lemma.

Every two distinct vertices of the selected spine prefix (including the hub
at coordinate `0`) are joined by `j+1` actual simple paths whose lengths are
pairwise different and all have one parity.  This is the form needed after
truncating two external connectors at their first fan vertices. -/
theorem allOdd_pathFamily_between_positions
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : a ≤ D.path.length) (hb : b ≤ D.path.length)
    (habne : a ≠ b) :
    Nonempty (PathFamily G (D.path.getVert a) (D.path.getVert b) (Fin (j + 1))) := by
  rcases lt_or_gt_of_ne habne with hab | hba
  · by_cases ha0 : a = 0
    · subst a
      obtain ⟨P⟩ := D.allOdd_pathFamily_from_hub hj hall (by omega) hb
      exact ⟨by simpa using P⟩
    · exact D.allOdd_pathFamily_between_ordered hj hall hfirst hlast
        (Nat.pos_of_ne_zero ha0) hab hb
  · by_cases hb0 : b = 0
    · subst b
      obtain ⟨P⟩ := D.allOdd_pathFamily_from_hub hj hall (by omega) ha
      exact ⟨by simpa using reversePathFamily P⟩
    · obtain ⟨P⟩ := D.allOdd_pathFamily_between_ordered hj hall hfirst hlast
        (Nat.pos_of_ne_zero hb0) hba ha
      exact ⟨reversePathFamily P⟩

theorem allOdd_supportedPathFamily_between_positions
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (hall : ∀ i, Odd (D.position i))
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {a b : ℕ} (ha : a ≤ D.path.length) (hb : b ≤ D.path.length)
    (habne : a ≠ b) :
    Nonempty (FanSupportedPathFamily D (D.path.getVert a)
      (D.path.getVert b) (j + 1)) := by
  rcases lt_or_gt_of_ne habne with hab | hba
  · by_cases ha0 : a = 0
    · subst a
      obtain ⟨P⟩ := D.allOdd_supportedPathFamily_from_hub hj hall (by omega) hb
      exact ⟨castFanSupportedPathFamily D P (by simp) rfl⟩
    · obtain ⟨P⟩ := D.allOdd_supportedPathFamily_between_ordered
        hj hall hfirst hlast (Nat.pos_of_ne_zero ha0) hab hb
      exact ⟨P.toFanSupported⟩
  · by_cases hb0 : b = 0
    · subst b
      obtain ⟨P⟩ := D.allOdd_supportedPathFamily_from_hub hj hall (by omega) ha
      exact ⟨castFanSupportedPathFamily D (reverseFanSupportedPathFamily D P)
        rfl (by simp)⟩
    · obtain ⟨P⟩ := D.allOdd_supportedPathFamily_between_ordered
        hj hall hfirst hlast (Nat.pos_of_ne_zero hb0) hba ha
      exact ⟨reverseFanSupportedPathFamily D P.toFanSupported⟩

private lemma two_le_position_of_even (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (hi : Even (D.position i)) :
    2 ≤ D.position i := by
  obtain ⟨n, hn⟩ := hi
  have hpos : 0 < n + n := by simpa [hn] using D.position_pos i
  rw [hn]
  omega

lemma prefixCycle_isCycle_of_even (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (hi : Even (D.position i)) :
    (D.prefixCycle i).IsCycle := by
  rw [prefixCycle, Walk.cons_isCycle_iff]
  refine ⟨(D.isPath.take _).reverse, ?_⟩
  intro hedge
  have hedge' : s(x, D.path.getVert (D.position i)) ∈
      (D.path.take (D.position i)).edges := by
    simpa using hedge
  have hone := (D.isPath.take (D.position i)).length_eq_one_of_mem_edges hedge'
  simp only [Walk.take_length, min_eq_left (D.position_le i)] at hone
  have htwo := D.two_le_position_of_even i hi
  omega

lemma prefixCycle_odd_of_even (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (hi : Even (D.position i)) :
    Odd (D.prefixCycle i).length := by
  rw [D.length_prefixCycle]
  exact hi.add_one

private lemma start_notMem_drop (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) :
    x ∉ (D.path.drop (D.position i)).support := by
  intro hx
  obtain ⟨n, hget, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hsum : D.position i + n ≤ D.path.length := by
    rw [Walk.drop_length] at hn
    have hle := D.position_le i
    omega
  have hzero : D.position i + n = 0 :=
    (D.isPath.getVert_eq_start_iff hsum).mp (by
      rw [Walk.drop_getVert] at hget
      exact hget)
  have hpos := D.position_pos i
  omega

private lemma start_notMem_segment (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    x ∉ (D.segment i i' hii').support := by
  intro hx
  obtain ⟨n, hget, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hnle : n ≤ D.position i' - D.position i := by
    simpa using hn
  have hsum : D.position i + n ≤ D.path.length := by
    have hi' := D.position_le i'
    omega
  have hget' : D.path.getVert (D.position i + n) = x := by
    simpa [segment, Walk.drop_getVert, min_eq_right hnle] using hget
  have hzero := (D.isPath.getVert_eq_start_iff hsum).mp hget'
  have hpos := D.position_pos i
  omega

lemma segment_isPath (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    (D.segment i i' hii').IsPath := by
  simp only [segment, Walk.isPath_copy]
  exact (D.isPath.drop _).take _

lemma segment_support_subset (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    ∀ ⦃v⦄, v ∈ (D.segment i i' hii').support → v ∈ D.path.support := by
  intro v hv
  obtain ⟨r, hget, hr⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hr' : r ≤ D.position i' - D.position i := by simpa using hr
  have hindex : D.position i + r ≤ D.path.length := by
    have hi' := D.position_le i'
    omega
  apply Walk.mem_support_iff_exists_getVert.mpr
  refine ⟨D.position i + r, ?_, hindex⟩
  simpa [segment, Walk.drop_getVert, min_eq_right hr'] using hget

lemma betweenCycle_support_subset (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    ∀ ⦃v⦄, v ∈ (D.betweenCycle i i' hii').support → v ∈ D.path.support := by
  intro v hv
  rw [betweenCycle, Walk.support_cons, Walk.support_concat] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact D.path.start_mem_support
  · rcases List.mem_append.mp hv with hv | hv
    · exact D.segment_support_subset _ _ _ hv
    · simp only [List.mem_singleton] at hv
      rw [hv]
      exact D.path.start_mem_support

lemma betweenCycle_isCycle (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i') :
    (D.betweenCycle i i' hii').IsCycle := by
  rw [betweenCycle, Walk.cons_isCycle_iff]
  have htail : ((D.segment i i' hii').concat (D.spoke i').symm).IsPath :=
    (D.segment_isPath i i' hii').concat
      (D.start_notMem_segment i i' hii') (D.spoke i').symm
  refine ⟨htail, ?_⟩
  intro hedge
  have hedge' : s(D.path.getVert (D.position i), x) ∈
      ((D.segment i i' hii').concat (D.spoke i').symm).edges := by
    exact Sym2.eq_swap ▸ hedge
  have hone := htail.length_eq_one_of_mem_edges hedge'
  simp only [Walk.length_concat, D.length_segment] at hone
  omega

lemma betweenCycle_odd_of_opposite (D : EndpointFanData G x y j)
    (i i' : Fin (2 * j + 1)) (hii' : D.position i < D.position i')
    (hopposite : D.position i % 2 ≠ D.position i' % 2) :
    Odd (D.betweenCycle i i' hii').length := by
  rw [D.length_betweenCycle]
  rw [Nat.odd_iff]
  omega

lemma shortcut_isPath (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) :
    (D.shortcut i).IsPath := by
  exact (D.isPath.drop (D.position i)).cons (D.start_notMem_drop i)

lemma shortcut_length_injective (D : EndpointFanData G x y j) :
    Function.Injective fun i ↦ (D.shortcut i).length := by
  intro i i' hii'
  change (D.shortcut i).length = (D.shortcut i').length at hii'
  rw [D.length_shortcut, D.length_shortcut] at hii'
  apply D.position_injective
  have hi := D.position_le i
  have hi' := D.position_le i'
  omega

lemma shortcut_sameParity_of_odd (D : EndpointFanData G x y j)
    {i i' : Fin (2 * j + 1)} (hi : Odd (D.position i))
    (hi' : Odd (D.position i')) :
    (D.shortcut i).length % 2 = (D.shortcut i').length % 2 := by
  rw [D.length_shortcut, D.length_shortcut]
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hi'
  rw [ha, hb]
  have hia := D.position_le i
  have hib := D.position_le i'
  omega

/-- Indices of spokes at even path positions. -/
def evenIndices (D : EndpointFanData G x y j) : Finset (Fin (2 * j + 1)) :=
  Finset.univ.filter fun i ↦ Even (D.position i)

/-- Indices of spokes at odd path positions. -/
def oddIndices (D : EndpointFanData G x y j) : Finset (Fin (2 * j + 1)) :=
  Finset.univ.filter fun i ↦ Odd (D.position i)

lemma oddIndices_nonempty_of_position_eq_one (D : EndpointFanData G x y j)
    (i : Fin (2 * j + 1)) (hi : D.position i = 1) :
    D.oddIndices.Nonempty := by
  refine ⟨i, ?_⟩
  simp [oddIndices, hi]

def evenPositions (D : EndpointFanData G x y j) : Finset ℤ :=
  D.evenIndices.image fun i ↦ (D.position i : ℤ)

def oddPositions (D : EndpointFanData G x y j) : Finset ℤ :=
  D.oddIndices.image fun i ↦ (D.position i : ℤ)

def signedGaps (D : EndpointFanData G x y j) : Finset ℤ :=
  D.evenPositions + D.oddPositions.image (-·)

def positiveGaps (D : EndpointFanData G x y j) : Finset ℤ :=
  D.signedGaps.filter (0 < ·)

def negativeGaps (D : EndpointFanData G x y j) : Finset ℤ :=
  D.signedGaps.filter (· < 0)

/-! ### Signed gaps on a prescribed subset of portals -/

/-- Even portals in a prescribed subset.  The common-singleton endpoint
application uses this with all portals except the terminal cycle vertex. -/
def evenIndicesWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset (Fin (2 * j + 1)) :=
  I.filter fun i ↦ Even (D.position i)

/-- Odd portals in a prescribed subset. -/
def oddIndicesWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset (Fin (2 * j + 1)) :=
  I.filter fun i ↦ Odd (D.position i)

def evenPositionsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset ℤ :=
  (D.evenIndicesWithin I).image fun i ↦ (D.position i : ℤ)

def oddPositionsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset ℤ :=
  (D.oddIndicesWithin I).image fun i ↦ (D.position i : ℤ)

def signedGapsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset ℤ :=
  D.evenPositionsWithin I + (D.oddPositionsWithin I).image (-·)

def positiveGapsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset ℤ :=
  (D.signedGapsWithin I).filter (0 < ·)

def negativeGapsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) : Finset ℤ :=
  (D.signedGapsWithin I).filter (· < 0)

lemma card_evenIndicesWithin_add_card_oddIndicesWithin
    (D : EndpointFanData G x y j) (I : Finset (Fin (2 * j + 1))) :
    (D.evenIndicesWithin I).card + (D.oddIndicesWithin I).card = I.card := by
  have hodd : D.oddIndicesWithin I =
      I.filter (fun i ↦ ¬Even (D.position i)) := by
    ext i
    simp only [oddIndicesWithin, Finset.mem_filter]
    by_cases hi : i ∈ I
    · simp only [hi, true_and]
      exact Nat.not_even_iff_odd.symm
    · simp [hi]
  rw [hodd, evenIndicesWithin]
  simpa using Finset.card_filter_add_card_filter_not (s := I)
    (fun i ↦ Even (D.position i))

lemma card_evenPositionsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) :
    (D.evenPositionsWithin I).card = (D.evenIndicesWithin I).card := by
  rw [evenPositionsWithin, Finset.card_image_of_injective]
  exact fun _ _ h ↦ D.position_injective (Int.ofNat_inj.mp h)

lemma card_oddPositionsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) :
    (D.oddPositionsWithin I).card = (D.oddIndicesWithin I).card := by
  rw [oddPositionsWithin, Finset.card_image_of_injective]
  exact fun _ _ h ↦ D.position_injective (Int.ofNat_inj.mp h)

lemma signedGapsWithin_card_lower (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1)))
    (heven : (D.evenIndicesWithin I).Nonempty)
    (hodd : (D.oddIndicesWithin I).Nonempty) :
    I.card - 1 ≤ (D.signedGapsWithin I).card := by
  have hE : (D.evenPositionsWithin I).Nonempty := by
    simpa [evenPositionsWithin] using
      heven.image (fun i ↦ (D.position i : ℤ))
  have hO : (D.oddPositionsWithin I).Nonempty := by
    simpa [oddPositionsWithin] using
      hodd.image (fun i ↦ (D.position i : ℤ))
  have hneg : ((D.oddPositionsWithin I).image (-·)).Nonempty :=
    hO.image (-·)
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hE hneg
  have hnegcard : ((D.oddPositionsWithin I).image (-·)).card =
      (D.oddPositionsWithin I).card := by
    rw [Finset.card_image_of_injective]
    exact neg_injective
  rw [hnegcard, D.card_evenPositionsWithin, D.card_oddPositionsWithin] at hcd
  have hpart := D.card_evenIndicesWithin_add_card_oddIndicesWithin I
  change I.card - 1 ≤
    (D.evenPositionsWithin I + (D.oddPositionsWithin I).image (-·)).card
  omega

lemma zero_notMem_signedGapsWithin (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) :
    0 ∉ D.signedGapsWithin I := by
  intro hzero
  obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hzero
  obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
  obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
  have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
  have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
  have heq : D.position ie = D.position io := by omega
  rw [heq] at hie'
  exact Nat.not_even_iff_odd.mpr hio' hie'

lemma card_positiveGapsWithin_add_card_negativeGapsWithin
    (D : EndpointFanData G x y j) (I : Finset (Fin (2 * j + 1))) :
    (D.positiveGapsWithin I).card + (D.negativeGapsWithin I).card =
      (D.signedGapsWithin I).card := by
  have hunion : D.positiveGapsWithin I ∪ D.negativeGapsWithin I =
      D.signedGapsWithin I := by
    ext d
    by_cases hd : d ∈ D.signedGapsWithin I
    · have hd0 : d ≠ 0 := fun h ↦
        D.zero_notMem_signedGapsWithin I (h ▸ hd)
      rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
      · simp [positiveGapsWithin, negativeGapsWithin, hd, hdneg,
          not_lt_of_ge hdneg.le]
      · simp [positiveGapsWithin, negativeGapsWithin, hd, hdpos,
          not_lt_of_ge hdpos.le]
    · simp [positiveGapsWithin, negativeGapsWithin, hd]
  have hdis : Disjoint (D.positiveGapsWithin I) (D.negativeGapsWithin I) := by
    rw [Finset.disjoint_left]
    intro d hdpos hdneg
    have hp := (Finset.mem_filter.mp hdpos).2
    have hn := (Finset.mem_filter.mp hdneg).2
    omega
  rw [← hunion, Finset.card_union_of_disjoint hdis]

lemma card_evenIndices_add_card_oddIndices (D : EndpointFanData G x y j) :
    D.evenIndices.card + D.oddIndices.card = 2 * j + 1 := by
  have hodd : D.oddIndices =
      Finset.univ.filter (fun i : Fin (2 * j + 1) ↦ ¬Even (D.position i)) := by
    ext i
    simp only [oddIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.not_even_iff_odd.symm
  rw [hodd, evenIndices]
  simpa using Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * j + 1))))
    (fun i ↦ Even (D.position i))

lemma card_evenPositions (D : EndpointFanData G x y j) :
    D.evenPositions.card = D.evenIndices.card := by
  rw [evenPositions, Finset.card_image_of_injective]
  exact fun _ _ h ↦ D.position_injective (Int.ofNat_inj.mp h)

lemma card_oddPositions (D : EndpointFanData G x y j) :
    D.oddPositions.card = D.oddIndices.card := by
  rw [oddPositions, Finset.card_image_of_injective]
  exact fun _ _ h ↦ D.position_injective (Int.ofNat_inj.mp h)

lemma signedGaps_card_lower (D : EndpointFanData G x y j)
    (heven : D.evenIndices.Nonempty) (hodd : D.oddIndices.Nonempty) :
    2 * j ≤ D.signedGaps.card := by
  have hE : D.evenPositions.Nonempty := by
    simpa [evenPositions] using heven.image (fun i ↦ (D.position i : ℤ))
  have hO : D.oddPositions.Nonempty := by
    simpa [oddPositions] using hodd.image (fun i ↦ (D.position i : ℤ))
  have hneg : (D.oddPositions.image (-·)).Nonempty :=
    hO.image (-·)
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hE hneg
  have hnegcard : (D.oddPositions.image (-·)).card = D.oddPositions.card := by
    rw [Finset.card_image_of_injective]
    exact neg_injective
  rw [hnegcard, D.card_evenPositions, D.card_oddPositions] at hcd
  have hpart := D.card_evenIndices_add_card_oddIndices
  change 2 * j ≤ (D.evenPositions + D.oddPositions.image (-·)).card
  omega

lemma zero_notMem_signedGaps (D : EndpointFanData G x y j) :
    0 ∉ D.signedGaps := by
  intro hzero
  obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hzero
  obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
  obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
  have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
  have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
  have heq : D.position ie = D.position io := by omega
  rw [heq] at hie'
  exact Nat.not_even_iff_odd.mpr hio' hie'

lemma card_positiveGaps_add_card_negativeGaps (D : EndpointFanData G x y j) :
    D.positiveGaps.card + D.negativeGaps.card = D.signedGaps.card := by
  have hunion : D.positiveGaps ∪ D.negativeGaps = D.signedGaps := by
    ext d
    by_cases hd : d ∈ D.signedGaps
    · have hd0 : d ≠ 0 := fun h ↦ D.zero_notMem_signedGaps (h ▸ hd)
      rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
      · simp [positiveGaps, negativeGaps, hd, hdneg, not_lt_of_ge hdneg.le]
      · simp [positiveGaps, negativeGaps, hd, hdpos, not_lt_of_ge hdpos.le]
    · simp [positiveGaps, negativeGaps, hd]
  have hdis : Disjoint D.positiveGaps D.negativeGaps := by
    rw [Finset.disjoint_left]
    intro d hdpos hdneg
    have hp := (Finset.mem_filter.mp hdpos).2
    have hn := (Finset.mem_filter.mp hdneg).2
    omega
  rw [← hunion, Finset.card_union_of_disjoint hdis]

lemma positiveGap_isOddCycleLength (D : EndpointFanData G x y j)
    {d : ℤ} (hd : d ∈ D.positiveGaps) :
    IsOddCycleLength G (d.toNat + 2) := by
  have hdpos : 0 < d := (Finset.mem_filter.mp hd).2
  have hdgap : d ∈ D.signedGaps := (Finset.mem_filter.mp hd).1
  obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hdgap
  obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
  obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
  have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
  have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
  have hlt : D.position io < D.position ie := by omega
  have hmod : D.position io % 2 ≠ D.position ie % 2 := by
    rw [Nat.odd_iff] at hio'
    rw [Nat.even_iff] at hie'
    omega
  refine ⟨x, D.betweenCycle io ie hlt, D.betweenCycle_isCycle io ie hlt,
    D.betweenCycle_odd_of_opposite io ie hlt hmod, ?_⟩
  rw [D.length_betweenCycle]
  have hnat : ((D.position ie : ℤ) + -(D.position io : ℤ)).toNat =
      D.position ie - D.position io := by omega
  omega

lemma negativeGap_isOddCycleLength (D : EndpointFanData G x y j)
    {d : ℤ} (hd : d ∈ D.negativeGaps) :
    IsOddCycleLength G ((-d).toNat + 2) := by
  have hdneg : d < 0 := (Finset.mem_filter.mp hd).2
  have hdgap : d ∈ D.signedGaps := (Finset.mem_filter.mp hd).1
  obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hdgap
  obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
  obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
  have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
  have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
  have hlt : D.position ie < D.position io := by omega
  have hmod : D.position ie % 2 ≠ D.position io % 2 := by
    rw [Nat.even_iff] at hie'
    rw [Nat.odd_iff] at hio'
    omega
  refine ⟨x, D.betweenCycle ie io hlt, D.betweenCycle_isCycle ie io hlt,
    D.betweenCycle_odd_of_opposite ie io hlt hmod, ?_⟩
  rw [D.length_betweenCycle]
  have hnat : (-((D.position ie : ℤ) + -(D.position io : ℤ))).toNat =
      D.position io - D.position ie := by omega
  omega

lemma positiveGap_lt_of_betweenCycles_lt (D : EndpointFanData G x y j)
    {bound : ℕ}
    (hbetween : ∀ i i' (hii' : D.position i < D.position i'),
      Odd (D.betweenCycle i i' hii').length →
        (D.betweenCycle i i' hii').length < bound)
    {d : ℤ} (hd : d ∈ D.positiveGaps) : d.toNat + 2 < bound := by
  have hdpos : 0 < d := (Finset.mem_filter.mp hd).2
  have hdgap : d ∈ D.signedGaps := (Finset.mem_filter.mp hd).1
  obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hdgap
  obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
  obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
  have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
  have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
  have hlt : D.position io < D.position ie := by omega
  have hmod : D.position io % 2 ≠ D.position ie % 2 := by
    rw [Nat.odd_iff] at hio'
    rw [Nat.even_iff] at hie'
    omega
  have hodd := D.betweenCycle_odd_of_opposite io ie hlt hmod
  have hsmall := hbetween io ie hlt hodd
  rw [D.length_betweenCycle] at hsmall
  have hnat : ((D.position ie : ℤ) + -(D.position io : ℤ)).toNat =
      D.position ie - D.position io := by omega
  omega

lemma negativeGap_lt_of_betweenCycles_lt (D : EndpointFanData G x y j)
    {bound : ℕ}
    (hbetween : ∀ i i' (hii' : D.position i < D.position i'),
      Odd (D.betweenCycle i i' hii').length →
        (D.betweenCycle i i' hii').length < bound)
    {d : ℤ} (hd : d ∈ D.negativeGaps) : (-d).toNat + 2 < bound := by
  have hdneg : d < 0 := (Finset.mem_filter.mp hd).2
  have hdgap : d ∈ D.signedGaps := (Finset.mem_filter.mp hd).1
  obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hdgap
  obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
  obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
  have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
  have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
  have hlt : D.position ie < D.position io := by omega
  have hmod : D.position ie % 2 ≠ D.position io % 2 := by
    rw [Nat.even_iff] at hie'
    rw [Nat.odd_iff] at hio'
    omega
  have hodd := D.betweenCycle_odd_of_opposite ie io hlt hmod
  have hsmall := hbetween ie io hlt hodd
  rw [D.length_betweenCycle] at hsmall
  have hnat : (-((D.position ie : ℤ) + -(D.position io : ℤ))).toNat =
      D.position io - D.position ie := by omega
  omega

lemma realizes_of_many_positiveGaps (D : EndpointFanData G x y j)
    (hcard : j ≤ D.positiveGaps.card) : RealizesOddCycleLengths G j := by
  classical
  let lengths := D.positiveGaps.image fun d ↦ d.toNat + 2
  refine ⟨lengths, ?_, ?_⟩
  · calc
      j ≤ D.positiveGaps.card := hcard
      _ = lengths.card := by
        symm
        apply Finset.card_image_of_injOn
        intro d hdmem d' hdmem' hlen
        have hd : 0 < d := (Finset.mem_filter.mp hdmem).2
        have hd' : 0 < d' := (Finset.mem_filter.mp hdmem').2
        have hdcast := Int.eq_natCast_toNat.mpr hd.le
        have hdcast' := Int.eq_natCast_toNat.mpr hd'.le
        change d.toNat + 2 = d'.toNat + 2 at hlen
        have hto : d.toNat = d'.toNat := by omega
        calc
          d = (d.toNat : ℤ) := hdcast
          _ = (d'.toNat : ℤ) := by exact_mod_cast hto
          _ = d' := hdcast'.symm
  · intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact D.positiveGap_isOddCycleLength hd

lemma realizes_of_many_negativeGaps (D : EndpointFanData G x y j)
    (hcard : j ≤ D.negativeGaps.card) : RealizesOddCycleLengths G j := by
  classical
  let lengths := D.negativeGaps.image fun d ↦ (-d).toNat + 2
  refine ⟨lengths, ?_, ?_⟩
  · calc
      j ≤ D.negativeGaps.card := hcard
      _ = lengths.card := by
        symm
        apply Finset.card_image_of_injOn
        intro d hdmem d' hdmem' hlen
        have hd : d < 0 := (Finset.mem_filter.mp hdmem).2
        have hd' : d' < 0 := (Finset.mem_filter.mp hdmem').2
        have hdcast := Int.eq_natCast_toNat.mpr (show 0 ≤ -d by omega)
        have hdcast' := Int.eq_natCast_toNat.mpr (show 0 ≤ -d' by omega)
        change (-d).toNat + 2 = (-d').toNat + 2 at hlen
        have hto : (-d).toNat = (-d').toNat := by omega
        have hneg : -d = -d' := by
          calc
            -d = ((-d).toNat : ℤ) := hdcast
            _ = ((-d').toNat : ℤ) := by exact_mod_cast hto
            _ = -d' := hdcast'.symm
        omega
  · intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact D.negativeGap_isOddCycleLength hd

lemma realizesBelow_of_many_positiveGaps (D : EndpointFanData G x y j)
    {bound : ℕ} (hcard : j ≤ D.positiveGaps.card)
    (hbetween : ∀ i i' (hii' : D.position i < D.position i'),
      Odd (D.betweenCycle i i' hii').length →
        (D.betweenCycle i i' hii').length < bound) :
    RealizesOddCycleLengthsBelow G j bound := by
  classical
  let lengths := D.positiveGaps.image fun d ↦ d.toNat + 2
  refine ⟨lengths, ?_, ?_⟩
  · calc
      j ≤ D.positiveGaps.card := hcard
      _ = lengths.card := by
        symm
        apply Finset.card_image_of_injOn
        intro d hdmem d' hdmem' hlen
        have hd : 0 < d := (Finset.mem_filter.mp hdmem).2
        have hd' : 0 < d' := (Finset.mem_filter.mp hdmem').2
        have hdcast := Int.eq_natCast_toNat.mpr hd.le
        have hdcast' := Int.eq_natCast_toNat.mpr hd'.le
        change d.toNat + 2 = d'.toNat + 2 at hlen
        have hto : d.toNat = d'.toNat := by omega
        calc
          d = (d.toNat : ℤ) := hdcast
          _ = (d'.toNat : ℤ) := by exact_mod_cast hto
          _ = d' := hdcast'.symm
  · intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨D.positiveGap_isOddCycleLength hd,
      D.positiveGap_lt_of_betweenCycles_lt hbetween hd⟩

lemma realizesBelow_of_many_negativeGaps (D : EndpointFanData G x y j)
    {bound : ℕ} (hcard : j ≤ D.negativeGaps.card)
    (hbetween : ∀ i i' (hii' : D.position i < D.position i'),
      Odd (D.betweenCycle i i' hii').length →
        (D.betweenCycle i i' hii').length < bound) :
    RealizesOddCycleLengthsBelow G j bound := by
  classical
  let lengths := D.negativeGaps.image fun d ↦ (-d).toNat + 2
  refine ⟨lengths, ?_, ?_⟩
  · calc
      j ≤ D.negativeGaps.card := hcard
      _ = lengths.card := by
        symm
        apply Finset.card_image_of_injOn
        intro d hdmem d' hdmem' hlen
        have hd : d < 0 := (Finset.mem_filter.mp hdmem).2
        have hd' : d' < 0 := (Finset.mem_filter.mp hdmem').2
        have hdcast := Int.eq_natCast_toNat.mpr (show 0 ≤ -d by omega)
        have hdcast' := Int.eq_natCast_toNat.mpr (show 0 ≤ -d' by omega)
        change (-d).toNat + 2 = (-d').toNat + 2 at hlen
        have hto : (-d).toNat = (-d').toNat := by omega
        have hneg : -d = -d' := by
          calc
            -d = ((-d).toNat : ℤ) := hdcast
            _ = ((-d').toNat : ℤ) := by exact_mod_cast hto
            _ = -d' := hdcast'.symm
        omega
  · intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨D.negativeGap_isOddCycleLength hd,
      D.negativeGap_lt_of_betweenCycles_lt hbetween hd⟩

/-- If both parities occur among the selected endpoint neighbours, the
two-spoke cycles realize at least `j` distinct odd lengths. -/
theorem realizes_of_mixed_parity (D : EndpointFanData G x y j)
    (heven : D.evenIndices.Nonempty) (hodd : D.oddIndices.Nonempty) :
    RealizesOddCycleLengths G j := by
  have hlower := D.signedGaps_card_lower heven hodd
  have hpart := D.card_positiveGaps_add_card_negativeGaps
  by_cases hpos : j ≤ D.positiveGaps.card
  · exact D.realizes_of_many_positiveGaps hpos
  · apply D.realizes_of_many_negativeGaps
    omega

theorem realizesBelow_of_mixed_parity (D : EndpointFanData G x y j)
    (heven : D.evenIndices.Nonempty) (hodd : D.oddIndices.Nonempty)
    {bound : ℕ}
    (hbetween : ∀ i i' (hii' : D.position i < D.position i'),
      Odd (D.betweenCycle i i' hii').length →
        (D.betweenCycle i i' hii').length < bound) :
    RealizesOddCycleLengthsBelow G j bound := by
  have hlower := D.signedGaps_card_lower heven hodd
  have hpart := D.card_positiveGaps_add_card_negativeGaps
  by_cases hpos : j ≤ D.positiveGaps.card
  · exact D.realizesBelow_of_many_positiveGaps hpos hbetween
  · apply D.realizesBelow_of_many_negativeGaps _ hbetween
    omega

/-- Restricted signed-gap form of the mixed-parity fan lemma.  If a chosen
set of exactly `2*j` portals contains both parities, it already supplies
`j` odd cycle lengths.  Only cycles whose two portals lie in the chosen set
are used; this is essential when the one omitted portal lies on the longest
odd cycle rather than in its exterior. -/
theorem realizesBelow_of_mixed_parity_within
    (D : EndpointFanData G x y j)
    (I : Finset (Fin (2 * j + 1))) (hcard : I.card = 2 * j)
    (heven : (D.evenIndicesWithin I).Nonempty)
    (hodd : (D.oddIndicesWithin I).Nonempty)
    {bound : ℕ}
    (hbetween : ∀ i, i ∈ I → ∀ i', i' ∈ I →
      ∀ (hii' : D.position i < D.position i'),
        Odd (D.betweenCycle i i' hii').length →
          (D.betweenCycle i i' hii').length < bound) :
    RealizesOddCycleLengthsBelow G j bound := by
  classical
  have hlower := D.signedGapsWithin_card_lower I heven hodd
  have hpart := D.card_positiveGapsWithin_add_card_negativeGapsWithin I
  rw [hcard] at hlower
  by_cases hpos : j ≤ (D.positiveGapsWithin I).card
  · let lengths := (D.positiveGapsWithin I).image fun d ↦ d.toNat + 2
    refine ⟨lengths, ?_, ?_⟩
    · calc
        j ≤ (D.positiveGapsWithin I).card := hpos
        _ = lengths.card := by
          symm
          apply Finset.card_image_of_injOn
          intro d hdmem d' hdmem' hlen
          have hd : 0 < d := (Finset.mem_filter.mp hdmem).2
          have hd' : 0 < d' := (Finset.mem_filter.mp hdmem').2
          have hdcast := Int.eq_natCast_toNat.mpr hd.le
          have hdcast' := Int.eq_natCast_toNat.mpr hd'.le
          change d.toNat + 2 = d'.toNat + 2 at hlen
          have hto : d.toNat = d'.toNat := by omega
          calc
            d = (d.toNat : ℤ) := hdcast
            _ = (d'.toNat : ℤ) := by exact_mod_cast hto
            _ = d' := hdcast'.symm
    · intro n hn
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
      have hdpos : 0 < d := (Finset.mem_filter.mp hd).2
      have hdgap : d ∈ D.signedGapsWithin I := (Finset.mem_filter.mp hd).1
      obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hdgap
      obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
      obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
      have hieI : ie ∈ I := (Finset.mem_filter.mp hie).1
      have hioI : io ∈ I := (Finset.mem_filter.mp hio).1
      have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
      have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
      have hlt : D.position io < D.position ie := by omega
      have hmod : D.position io % 2 ≠ D.position ie % 2 := by
        rw [Nat.odd_iff] at hio'
        rw [Nat.even_iff] at hie'
        omega
      have hoddCycle := D.betweenCycle_odd_of_opposite io ie hlt hmod
      have hnat : ((D.position ie : ℤ) + -(D.position io : ℤ)).toNat =
          D.position ie - D.position io := by omega
      refine ⟨?_, ?_⟩
      · refine ⟨x, D.betweenCycle io ie hlt,
          D.betweenCycle_isCycle io ie hlt, hoddCycle, ?_⟩
        rw [D.length_betweenCycle]
        omega
      · have hsmall := hbetween io hioI ie hieI hlt hoddCycle
        rw [D.length_betweenCycle] at hsmall
        omega
  · have hneg : j ≤ (D.negativeGapsWithin I).card := by
      omega
    let lengths := (D.negativeGapsWithin I).image fun d ↦ (-d).toNat + 2
    refine ⟨lengths, ?_, ?_⟩
    · calc
        j ≤ (D.negativeGapsWithin I).card := hneg
        _ = lengths.card := by
          symm
          apply Finset.card_image_of_injOn
          intro d hdmem d' hdmem' hlen
          have hd : d < 0 := (Finset.mem_filter.mp hdmem).2
          have hd' : d' < 0 := (Finset.mem_filter.mp hdmem').2
          have hdcast := Int.eq_natCast_toNat.mpr (show 0 ≤ -d by omega)
          have hdcast' := Int.eq_natCast_toNat.mpr (show 0 ≤ -d' by omega)
          change (-d).toNat + 2 = (-d').toNat + 2 at hlen
          have hto : (-d).toNat = (-d').toNat := by omega
          have hnegEq : -d = -d' := by
            calc
              -d = ((-d).toNat : ℤ) := hdcast
              _ = ((-d').toNat : ℤ) := by exact_mod_cast hto
              _ = -d' := hdcast'.symm
          omega
    · intro n hn
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
      have hdneg : d < 0 := (Finset.mem_filter.mp hd).2
      have hdgap : d ∈ D.signedGapsWithin I := (Finset.mem_filter.mp hd).1
      obtain ⟨e, he, no, hno, hsum⟩ := Finset.mem_add.mp hdgap
      obtain ⟨ie, hie, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hno
      obtain ⟨io, hio, rfl⟩ := Finset.mem_image.mp ho
      have hieI : ie ∈ I := (Finset.mem_filter.mp hie).1
      have hioI : io ∈ I := (Finset.mem_filter.mp hio).1
      have hie' : Even (D.position ie) := (Finset.mem_filter.mp hie).2
      have hio' : Odd (D.position io) := (Finset.mem_filter.mp hio).2
      have hlt : D.position ie < D.position io := by omega
      have hmod : D.position ie % 2 ≠ D.position io % 2 := by
        rw [Nat.even_iff] at hie'
        rw [Nat.odd_iff] at hio'
        omega
      have hoddCycle := D.betweenCycle_odd_of_opposite ie io hlt hmod
      have hnat : (-((D.position ie : ℤ) + -(D.position io : ℤ))).toNat =
          D.position io - D.position ie := by omega
      refine ⟨?_, ?_⟩
      · refine ⟨x, D.betweenCycle ie io hlt,
          D.betweenCycle_isCycle ie io hlt, hoddCycle, ?_⟩
        rw [D.length_betweenCycle]
        omega
      · have hsmall := hbetween ie hieI io hioI hlt hoddCycle
        rw [D.length_betweenCycle] at hsmall
        omega

/-- The exact portal split used for a common singleton cycle neighbour.
All portals except `iLast` lie in the exterior.  If both parities occur
there, restricted signed gaps give `j` exterior lengths below `bound`.  If
the exterior portals are all odd and the terminal portal is even, its
`2*j` two-spoke cycles already contain `j+1` distinct odd lengths.  In the
remaining case every portal is odd, so the arbitrary-pair supported fan
family is available. -/
theorem externalMixed_or_terminalOpposite_or_allOddSupported
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    (I : Finset (Fin (2 * j + 1)))
    {iFirst iLast : Fin (2 * j + 1)}
    (hI : I = Finset.univ.erase iLast)
    (hfirstMem : iFirst ∈ I) (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    (hbefore : ∀ i ∈ I, D.position i < D.position iLast)
    {bound : ℕ}
    (hbetween : ∀ i, i ∈ I → ∀ i', i' ∈ I →
      ∀ (hii' : D.position i < D.position i'),
        Odd (D.betweenCycle i i' hii').length →
          (D.betweenCycle i i' hii').length < bound) :
    RealizesOddCycleLengthsBelow G j bound ∨
      RealizesOddCycleLengths G (j + 1) ∨
      (∀ {a b : ℕ}, a ≤ D.path.length → b ≤ D.path.length → a ≠ b →
        Nonempty (FanSupportedPathFamily D (D.path.getVert a)
          (D.path.getVert b) (j + 1))) := by
  classical
  have hcard : I.card = 2 * j := by
    rw [hI, Finset.card_erase_of_mem (Finset.mem_univ iLast)]
    simp
  have hoddExt : (D.oddIndicesWithin I).Nonempty := by
    refine ⟨iFirst, ?_⟩
    simp [oddIndicesWithin, hfirstMem, hfirst]
  by_cases hevenExt : (D.evenIndicesWithin I).Nonempty
  · exact Or.inl
      (D.realizesBelow_of_mixed_parity_within I hcard hevenExt hoddExt hbetween)
  · have hallExt : ∀ i ∈ I, Odd (D.position i) := by
      intro i hi
      apply Nat.not_even_iff_odd.mp
      intro hie
      apply hevenExt
      exact ⟨i, by simp [evenIndicesWithin, hi, hie]⟩
    by_cases hlastEven : Even (D.position iLast)
    · right
      left
      have hmany : j + 1 ≤ I.card := by omega
      obtain ⟨chosen, hchosen, hchosenCard⟩ :=
        Finset.exists_subset_card_eq hmany
      let e : Fin (j + 1) ≃ chosen :=
        (Fintype.equivFinOfCardEq (by simpa using hchosenCard)).symm
      let select : Fin (j + 1) → Fin (2 * j + 1) := fun i ↦ (e i).1
      have hselectInj : Function.Injective select :=
        Subtype.val_injective.comp e.injective
      have hselectMem (i : Fin (j + 1)) : select i ∈ I :=
        hchosen (e i).2
      have hselectLt (i : Fin (j + 1)) :
          D.position (select i) < D.position iLast :=
        hbefore _ (hselectMem i)
      let lengths : Finset ℕ := Finset.univ.image fun i : Fin (j + 1) ↦
        (D.betweenCycle (select i) iLast (hselectLt i)).length
      refine ⟨lengths, ?_, ?_⟩
      · change j + 1 ≤ lengths.card
        have hinj : Function.Injective (fun i : Fin (j + 1) ↦
            (D.betweenCycle (select i) iLast (hselectLt i)).length) := by
          intro i k hik
          have hik' : D.position iLast - D.position (select i) + 2 =
              D.position iLast - D.position (select k) + 2 := by
            simpa only [D.length_betweenCycle] using hik
          have hi := hselectLt i
          have hk := hselectLt k
          apply hselectInj
          apply D.position_injective
          omega
        rw [Finset.card_image_of_injective _ hinj]
        simp
      · intro n hn
        obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
        have hoddPos := hallExt _ (hselectMem i)
        have hmod : D.position (select i) % 2 ≠ D.position iLast % 2 := by
          rw [Nat.odd_iff] at hoddPos
          rw [Nat.even_iff] at hlastEven
          omega
        have hoddCycle := D.betweenCycle_odd_of_opposite
          (select i) iLast (hselectLt i) hmod
        exact ⟨x, D.betweenCycle (select i) iLast (hselectLt i),
          D.betweenCycle_isCycle (select i) iLast (hselectLt i),
          hoddCycle, rfl⟩
    · right
      right
      have hall : ∀ i, Odd (D.position i) := by
        intro i
        by_cases hi : i = iLast
        · subst i
          exact Nat.not_even_iff_odd.mp hlastEven
        · apply hallExt
          rw [hI]
          simp [hi]
      intro a b ha hb hab
      exact D.allOdd_supportedPathFamily_between_positions
        hj hall hfirst hlast ha hb hab

lemma realizes_of_many_even (D : EndpointFanData G x y j)
    (hcard : j + 1 ≤ D.evenIndices.card) :
    RealizesOddCycleLengths G (j + 1) := by
  classical
  let lengths : Finset ℕ :=
    D.evenIndices.image fun i ↦ (D.prefixCycle i).length
  refine ⟨lengths, ?_, ?_⟩
  · calc
      j + 1 ≤ D.evenIndices.card := hcard
      _ = lengths.card := by
        symm
        apply Finset.card_image_of_injective
        intro i i' hii'
        change (D.prefixCycle i).length = (D.prefixCycle i').length at hii'
        rw [D.length_prefixCycle, D.length_prefixCycle] at hii'
        exact D.position_injective (by omega)
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hie : Even (D.position i) := (Finset.mem_filter.mp hi).2
    exact ⟨x, D.prefixCycle i, D.prefixCycle_isCycle_of_even i hie,
      D.prefixCycle_odd_of_even i hie, rfl⟩

lemma pathFamily_of_many_odd (D : EndpointFanData G x y j)
    (hcard : j + 1 ≤ D.oddIndices.card) :
    ∃ P : PathFamily G x y (Fin (j + 1)),
      ∃ select : Fin (j + 1) → Fin (2 * j + 1),
        Function.Injective select ∧
        (∀ i, select i ∈ D.oddIndices) ∧
        P.path = fun i ↦ D.shortcut (select i) := by
  classical
  obtain ⟨chosen, hchosen, hchosenCard⟩ :=
    Finset.exists_subset_card_eq hcard
  let e : Fin (j + 1) ≃ chosen :=
    (Fintype.equivFinOfCardEq (by simpa using hchosenCard)).symm
  let select : Fin (j + 1) → Fin (2 * j + 1) := fun i ↦ (e i).1
  have hselect_inj : Function.Injective select :=
    Subtype.val_injective.comp e.injective
  have hselect_mem : ∀ i, select i ∈ D.oddIndices := by
    intro i
    exact hchosen (e i).2
  let P : PathFamily G x y (Fin (j + 1)) :=
    { path := fun i ↦ D.shortcut (select i)
      isPath := fun i ↦ D.shortcut_isPath (select i)
      length_injective := D.shortcut_length_injective.comp hselect_inj
      sameParity := by
        intro i i'
        exact D.shortcut_sameParity_of_odd
          (Finset.mem_filter.mp (hselect_mem i)).2
          (Finset.mem_filter.mp (hselect_mem i')).2 }
  exact ⟨P, select, hselect_inj, hselect_mem, rfl⟩

/-- Endpoint-fan dichotomy with actual walks.

The second alternative records the selected odd-position spokes as well as
the resulting paths.  Thus it is not an abstract path-family assumption: it
is the concrete bipartite subfan cut out of the original path and spokes. -/
theorem endpointFan_dichotomy (D : EndpointFanData G x y j) :
    RealizesOddCycleLengths G (j + 1) ∨
      ∃ P : PathFamily G x y (Fin (j + 1)),
        ∃ select : Fin (j + 1) → Fin (2 * j + 1),
          Function.Injective select ∧
          (∀ i, select i ∈ D.oddIndices) ∧
          P.path = fun i ↦ D.shortcut (select i) := by
  have hsum := D.card_evenIndices_add_card_oddIndices
  by_cases heven : j + 1 ≤ D.evenIndices.card
  · exact Or.inl (D.realizes_of_many_even heven)
  · right
    apply D.pathFamily_of_many_odd
    omega

/-- The corrected endpoint alternative: as soon as both position parities
occur, signed gaps give `j` actual odd cycle lengths.  If no even position
occurs, all `2*j+1` selected spokes belong to the bipartite linear subfan,
and in particular give `j+1` distinct equal-parity paths from the hub to the
fixed terminal endpoint.

The hypothesis `hodd` is automatic when the selected positions include
position `1`, as they do in the longest-path application. -/
theorem mixedCycles_or_allOddEndpointPaths (D : EndpointFanData G x y j)
    (hodd : D.oddIndices.Nonempty) :
    RealizesOddCycleLengths G j ∨
      ∃ P : PathFamily G x y (Fin (j + 1)),
        ∃ select : Fin (j + 1) → Fin (2 * j + 1),
          Function.Injective select ∧
          (∀ i, select i ∈ D.oddIndices) ∧
          P.path = fun i ↦ D.shortcut (select i) := by
  by_cases heven : D.evenIndices.Nonempty
  · exact Or.inl (D.realizes_of_mixed_parity heven hodd)
  · right
    apply D.pathFamily_of_many_odd
    have hpart := D.card_evenIndices_add_card_oddIndices
    have hevenZero : D.evenIndices.card = 0 := Finset.not_nonempty_iff_eq_empty.mp heven ▸ rfl
    omega

/-- Complete actual-walk dichotomy for selected endpoint neighbours.

If both position parities occur, the two-spoke cycles give `j` distinct odd
cycle lengths.  Otherwise the portal at position `1` forces every position
to be odd, and the second branch supplies the arbitrary-pair path family
needed after first-hit truncation of external connectors. -/
theorem mixedCycles_or_allOddArbitraryPaths
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length) :
    RealizesOddCycleLengths G j ∨
      ∀ {a b : ℕ}, a ≤ D.path.length → b ≤ D.path.length → a ≠ b →
        Nonempty (PathFamily G (D.path.getVert a) (D.path.getVert b)
          (Fin (j + 1))) := by
  have hodd : D.oddIndices.Nonempty := D.oddIndices_nonempty_of_position_eq_one _ hfirst
  by_cases heven : D.evenIndices.Nonempty
  · exact Or.inl (D.realizes_of_mixed_parity heven hodd)
  · right
    have hall : ∀ i, Odd (D.position i) := by
      intro i
      apply Nat.not_even_iff_odd.mp
      intro hi
      apply heven
      exact ⟨i, by simp [evenIndices, hi]⟩
    intro a b ha hb hab
    exact D.allOdd_pathFamily_between_positions hj hall hfirst hlast ha hb hab

/-- Support-controlled and below-bound endpoint-fan dichotomy.  This is the
direct interface for the longest-odd-cycle application: in the mixed branch,
the caller supplies the strict upper bound for each concrete two-spoke cycle;
in the all-odd branch every path is certified to stay on the selected fan
spine. -/
theorem mixedCyclesBelow_or_allOddSupportedPaths
    (D : EndpointFanData G x y j) (hj : 1 ≤ j)
    {iFirst iLast : Fin (2 * j + 1)}
    (hfirst : D.position iFirst = 1)
    (hlast : D.position iLast = D.path.length)
    {bound : ℕ}
    (hbetween : ∀ i i' (hii' : D.position i < D.position i'),
      Odd (D.betweenCycle i i' hii').length →
        (D.betweenCycle i i' hii').length < bound) :
    RealizesOddCycleLengthsBelow G j bound ∨
      ∀ {a b : ℕ}, a ≤ D.path.length → b ≤ D.path.length → a ≠ b →
        Nonempty (FanSupportedPathFamily D (D.path.getVert a)
          (D.path.getVert b) (j + 1)) := by
  have hodd : D.oddIndices.Nonempty :=
    D.oddIndices_nonempty_of_position_eq_one _ hfirst
  by_cases heven : D.evenIndices.Nonempty
  · exact Or.inl (D.realizesBelow_of_mixed_parity heven hodd hbetween)
  · right
    have hall : ∀ i, Odd (D.position i) := by
      intro i
      apply Nat.not_even_iff_odd.mp
      intro hi
      apply heven
      exact ⟨i, by simp [evenIndices, hi]⟩
    intro a b ha hb hab
    exact D.allOdd_supportedPathFamily_between_positions
      hj hall hfirst hlast ha hb hab

end EndpointFanData

end Erdos58
