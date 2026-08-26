import ErdosProblems.Erdos547.GEBlockOptimality
import ErdosProblems.Erdos547.TransferControl
import Mathlib.Logic.Relation

/-!
# Alternating reachability from deficient singleton blocks

We propagate a defect through arbitrarily close saturation maximizers,
preserving every originally positive edge. This avoids assumptions about
distinct vertices when an alternating walk revisits an earlier vertex.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def AlternatingStep (μ : FractionalMatching G) (x z : V) : Prop :=
  ∃ y, G.Adj x y ∧ 0 < μ.weight y z

namespace GallaiEdmondsPartition

structure ApproxDefect (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (x : V) : Prop where
  singleton : x ∈ D.singletonVertices
  approximate : ∀ ε : ℝ, 0 < ε → ∃ ν : FractionalMatching G,
    D.IsMaxSaturation w c ν ∧ ν.load x < w.weight c x ∧
      (∀ u v, 0 < μ.weight u v → 0 < ν.weight u v) ∧
      ∀ u, |ν.load u - μ.load u| < ε

theorem IsMaxSaturation.approxDefect {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ : FractionalMatching G} (h : D.IsMaxSaturation w c μ) {x : V}
    (hx : x ∈ D.singletonVertices) (hdef : μ.load x < w.weight c x) : D.ApproxDefect w c μ x := by
  refine ⟨hx, ?_⟩
  intro ε hε
  exact ⟨μ, h, hdef, fun _ _ hp ↦ hp, fun _ ↦ by simpa using hε⟩

theorem ApproxDefect.partner_bounds {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ : FractionalMatching G} {x y z : V} (h : D.ApproxDefect w c μ x)
    (hxy : G.Adj x y) (hpos : 0 < μ.weight y z) :
    z ∈ D.singletonVertices ∧ μ.load z ≤ w.weight c z := by
  obtain ⟨ν, hν, hdef, hsupport, _⟩ := h.approximate 1 (by norm_num)
  have hz := hν.partner_is_singleton h.singleton hdef hxy (hsupport y z hpos)
  refine ⟨hz, ?_⟩
  by_contra hn
  have hgap : 0 < μ.load z - w.weight c z := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨ξ, hξ, hxdef, hξsupport, hclose⟩ := h.approximate
    ((μ.load z - w.weight c z) / 2) (by positivity)
  have hle := hξ.singleton_partner_le h.singleton hz hxdef hxy (hξsupport y z hpos)
  have hdist := (abs_lt.mp (hclose z)).1
  linarith

theorem ApproxDefect.step {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ : FractionalMatching G} {x z : V} (h : D.ApproxDefect w c μ x)
    (hstep : AlternatingStep μ x z) : D.ApproxDefect w c μ z := by
  classical
  obtain ⟨y, hxy, hpos⟩ := hstep
  by_cases hxz : x = z
  · exact hxz ▸ h
  have hzs := (h.partner_bounds hxy hpos).1
  refine ⟨hzs, ?_⟩
  intro ε hε
  obtain ⟨ν, hν, hxdef, hsupport, hclose⟩ := h.approximate (ε / 2) (by positivity)
  have hνpos : 0 < ν.weight z y := by
    rw [ν.symmetric z y]
    exact hsupport y z hpos
  have hzy : G.Adj z y := by
    by_contra hn
    rw [ν.supported z y hn] at hνpos
    exact (lt_irrefl 0) hνpos
  have hzload := hν.singleton_partner_le h.singleton hzs hxdef hxy (hsupport y z hpos)
  have hy := D.neighbour_of_singleton_mem_separator h.singleton hxy
  let t := min (ν.weight z y / 2) (min ((w.weight c x - ν.load x) / 2) (ε / 2))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by linarith) (by positivity))
  have hehalf : t ≤ ν.weight z y / 2 := min_le_left _ _
  have hestrict : t < ν.weight z y := by linarith
  have htx : t ≤ (w.weight c x - ν.load x) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htε : t ≤ ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hxallow : ν.load x + t ≤ w.weight c x := by linarith
  have hxcap : ν.load x + t ≤ 1 := hxallow.trans (w.at_most_one c x)
  let ξ := ν.transfer hxy hzy hxz t ht.le hestrict.le hxcap
  have hξge : D.IsFractionalGE ξ := hν.1.transfer_singletons h.singleton hzs hy
    hxy hzy hxz t ht.le hestrict.le hxcap
  have hsat : w.saturation ξ.load c = w.saturation ν.load c :=
    ν.transfer_saturation w c hxy hzy hxz t ht.le hestrict.le hxcap hxallow hzload
  have hξmax : D.IsMaxSaturation w c ξ :=
    ⟨hξge, fun η hη ↦ (hν.2 η hη).trans_eq hsat.symm⟩
  refine ⟨ξ, hξmax, ?_, ?_, ?_⟩
  · have hload : ξ.load z = ν.load z - t := by
      simp [ξ, FractionalMatching.transfer_load, Ne.symm hxz]
    rw [hload]
    linarith
  · intro u v huv
    exact ν.transfer_positive hxy hzy hxz t ht.le hestrict.le hxcap hestrict (hsupport u v huv)
  · intro u
    have hdist : |ξ.load u - ν.load u| ≤ t :=
      ν.transfer_load_dist_le hxy hzy hxz t ht.le hestrict.le hxcap u
    calc
      |ξ.load u - μ.load u| ≤ |ξ.load u - ν.load u| + |ν.load u - μ.load u| := abs_sub_le _ _ _
      _ ≤ t + |ν.load u - μ.load u| := add_le_add hdist le_rfl
      _ < ε := by linarith [hclose u]

theorem ApproxDefect.reachable {D : GallaiEdmondsPartition G} {w : EdgeWeights G}
    {c : V} {μ : FractionalMatching G} {x z : V} (h : D.ApproxDefect w c μ x)
    (hr : Relation.ReflTransGen (AlternatingStep μ) x z) : D.ApproxDefect w c μ z := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- Every separator reached from a deficient singleton by alternating steps
is covered, has only singleton matching partners, and those partners have
load at most the anchor allowance. -/
theorem IsMaxSaturation.alternating_properties {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {x u : V}
    (hx : x ∈ D.singletonVertices) (hdef : μ.load x < w.weight c x)
    (hr : Relation.ReflTransGen (AlternatingStep μ) x u) :
    u ∈ D.singletonVertices ∧ ∀ y, G.Adj u y → μ.load y = 1 ∧
      ∀ z, 0 < μ.weight y z → z ∈ D.singletonVertices ∧ μ.load z ≤ w.weight c z := by
  have hu := (h.approxDefect hx hdef).reachable hr
  refine ⟨hu.singleton, ?_⟩
  intro y huy
  exact ⟨h.1.load_separator (D.neighbour_of_singleton_mem_separator hu.singleton huy),
    fun _ hp ↦ hu.partner_bounds huy hp⟩

theorem exists_alternating_optimal (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V) :
    ∃ μ : FractionalMatching G, D.IsFractionalGE μ ∧
      ∀ x, x ∈ D.singletonVertices → μ.load x < w.weight c x →
      ∀ u, Relation.ReflTransGen (AlternatingStep μ) x u →
      u ∈ D.singletonVertices ∧ ∀ y, G.Adj u y → μ.load y = 1 ∧
        ∀ z, 0 < μ.weight y z → z ∈ D.singletonVertices ∧ μ.load z ≤ w.weight c z := by
  obtain ⟨μ, hμ⟩ := D.exists_max_saturation w c
  exact ⟨μ, hμ.1, fun _ hx hdef _ hr ↦ IsMaxSaturation.alternating_properties hμ hx hdef hr⟩

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_alternating_optimal
