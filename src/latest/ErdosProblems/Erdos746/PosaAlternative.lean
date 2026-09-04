import ErdosProblems.Erdos746.PathMax
import ErdosProblems.Erdos746.Posa
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A complete deterministic Pósa booster bound

This file combines the checked rotation primitives from `Posa` with the
maximum-path and fixed-edge model from `PathMax`.
-/

open scoped Sym2
open Finset

namespace Erdos746.PosaAlternative

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

open SimpleGraph

/-! ## Closing a path and extending from its cycle -/

/-- A path of length at least two does not use the edge joining its endpoints. -/
theorem endpoint_edge_not_mem {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  intro he
  have := hp.length_eq_one_of_mem_edges he
  omega

/-- An unordered pair together with its orientation bit remembers an ordered
pair, provided its two entries are distinct. -/
theorem sym2_orientation_injOn {I : Type*} [LinearOrder I]
    (key : V → I) (hkey : Function.Injective key) :
    Set.InjOn (fun x : V × V ↦ (s(x.1, x.2), decide (key x.1 < key x.2)))
      {x : V × V | x.1 ≠ x.2} := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [Set.mem_setOf_eq, Prod.mk.injEq] at hab hcd h ⊢
  rcases h with ⟨hedge, hbit⟩
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hedge
  rcases hedge with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact ⟨hac, hbd⟩
  · subst d
    subst c
    have hkab : key a ≠ key b := fun h ↦ hab (hkey h)
    rcases lt_or_gt_of_ne hkab with hablt | hbalt
    · simp [hablt, hablt.asymm] at hbit
    · simp [hbalt, hbalt.asymm] at hbit

/-! ## The two-to-one ordered-pair count -/

/-- Mapping ordered pairs to unordered pairs loses at most the two possible
orientations.  This is the finite counting step in Pósa's booster lemma. -/
theorem card_sigma_le_two_mul_card
    (R : Finset V) (T : V → Finset V) (B : Finset (Sym2 V))
    (hne : ∀ v ∈ R, ∀ w ∈ T v, v ≠ w)
    (hB : ∀ v ∈ R, ∀ w ∈ T v, s(v, w) ∈ B) :
    (R.sigma fun v ↦ T v).card ≤ 2 * B.card := by
  classical
  let key : V → Fin (Fintype.card V) := Fintype.equivFin V
  let f : (Σ _v : V, V) → Sym2 V × Bool :=
    fun x ↦ (s(x.1, x.2), decide (key x.1 < key x.2))
  have hmap : Set.MapsTo f (R.sigma fun v ↦ T v)
      ((B.product (Finset.univ : Finset Bool) : Finset (Sym2 V × Bool)) : Set (Sym2 V × Bool)) := by
    intro x hx
    change x ∈ R.sigma fun v ↦ T v at hx
    rw [Finset.mem_sigma] at hx
    change f x ∈ B.product (Finset.univ : Finset Bool)
    dsimp only [f]
    exact Finset.mem_product.mpr ⟨hB x.1 hx.1 x.2 hx.2, Finset.mem_univ _⟩
  have hinj : Set.InjOn f (R.sigma fun v ↦ T v) := by
    intro x hx y hy hxy
    change x ∈ R.sigma (fun v ↦ T v) at hx
    change y ∈ R.sigma (fun v ↦ T v) at hy
    rw [Finset.mem_sigma] at hx hy
    have hraw : (x.1, x.2) = (y.1, y.2) := by
      apply sym2_orientation_injOn key (Fintype.equivFin V).injective
      · exact hne x.1 hx.1 x.2 hx.2
      · exact hne y.1 hy.1 y.2 hy.2
      · exact hxy
    cases x with
    | mk xv xw =>
      cases y with
      | mk yv yw =>
        simp only at hraw
        cases hraw
        rfl
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa [Finset.card_product, Nat.mul_comm] using hc

/-- If there are at least `k+1` first endpoints and at least `k+1` second
endpoints over each first endpoint, then there are at least `(k+1)^2`
oriented pairs. -/
theorem sq_le_card_sigma {k : ℕ} (R : Finset V) (T : V → Finset V)
    (hR : k + 1 ≤ R.card) (hT : ∀ v ∈ R, k + 1 ≤ (T v).card) :
    (k + 1) ^ 2 ≤ (R.sigma fun v ↦ T v).card := by
  classical
  calc
    (k + 1) ^ 2 ≤ R.card * (k + 1) := by
      rw [pow_two]
      exact Nat.mul_le_mul_right (k + 1) hR
    _ = ∑ _v ∈ R, (k + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ R, (T v).card := by
      exact Finset.sum_le_sum fun v hv ↦ hT v hv
    _ = (R.sigma fun v ↦ T v).card := by
      simp [Finset.sigma]

/-! ## Pósa's booster theorem -/

/-- A finite connected non-Hamiltonian graph which two-expands through sets
of size `k` has at least `(k+1)^2 / 2` boosters. -/
theorem posa_boosterEdgeFinset_bound {G : SimpleGraph V} {k : ℕ}
    (hconn : G.Connected) (hnham : ¬ G.IsHamiltonian) (hk : 1 ≤ k)
    (hexpand : G.IsTwoExpanderUpTo k) :
    (k + 1) ^ 2 ≤ 2 * (Erdos746.PathMax.boosterEdgeFinset G).card := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨a, b, p, hpLong⟩ := Erdos746.PathMax.exists_isLongestPath G
  have hp : p.IsPath := hpLong.isPath
  have hmax : ∀ (u v : V) (r : G.Walk u v), r.IsPath → r.length ≤ p.length :=
    (Erdos746.PathMax.isLongestPath_iff.mp hpLong).2
  have hlen : 2 ≤ p.length :=
    SimpleGraph.Walk.IsTwoExpanderUpTo.two_le_longest_path hexpand hk a hmax
  let R : Finset V := p.posaEndpointFinset
  have hR : k + 1 ≤ R.card := by
    exact SimpleGraph.Walk.IsTwoExpanderUpTo.le_card_posaEndpointFinset
      hexpand hk hconn hnham hp hmax
  let q : (v : V) → G.Walk a v := fun v ↦
    if hv : v ∈ R then
      Classical.choose (SimpleGraph.Walk.mem_posaEndpointFinset p v |>.mp
        (by simpa [R] using hv))
    else
      Classical.choice (hconn.preconnected a v)
  have hqReach : ∀ v ∈ R, SimpleGraph.Walk.IsPosaReachable p (q v) := by
    intro v hv
    dsimp only [q]
    rw [dif_pos hv]
    exact Classical.choose_spec
      (SimpleGraph.Walk.mem_posaEndpointFinset p v |>.mp (by simpa [R] using hv))
  let T : V → Finset V := fun v ↦ (q v).reverse.posaEndpointFinset
  have hqPath : ∀ v ∈ R, (q v).IsPath := by
    intro v hv
    exact (hqReach v hv).isPath hp
  have hqLength : ∀ v ∈ R, (q v).length = p.length := by
    intro v hv
    exact (hqReach v hv).length_eq
  have hrevMax : ∀ v ∈ R, ∀ (u w : V) (r : G.Walk u w),
      r.IsPath → r.length ≤ (q v).reverse.length := by
    intro v hv u w r hr
    rw [SimpleGraph.Walk.length_reverse, hqLength v hv]
    exact hmax u w r hr
  have hT : ∀ v ∈ R, k + 1 ≤ (T v).card := by
    intro v hv
    dsimp only [T]
    exact SimpleGraph.Walk.IsTwoExpanderUpTo.le_card_posaEndpointFinset
      hexpand hk hconn hnham (hqPath v hv).reverse (hrevMax v hv)
  have hB : ∀ v ∈ R, ∀ w ∈ T v,
      s(v, w) ∈ Erdos746.PathMax.boosterFinset G := by
    intro v hv w hw
    dsimp only [T] at hw
    rw [SimpleGraph.Walk.mem_posaEndpointFinset] at hw
    obtain ⟨r, hr⟩ := hw
    apply Erdos746.PathMax.mem_boosterFinset.mpr
    exact SimpleGraph.Walk.isBooster_mk_of_isPosaReachable
      (hqPath v hv).reverse (hrevMax v hv) hconn hnham
      (by rw [SimpleGraph.Walk.length_reverse, hqLength v hv]; exact hlen) hr
  have hne : ∀ v ∈ R, ∀ w ∈ T v, v ≠ w := by
    intro v hv w hw hvw
    have hb := Erdos746.PathMax.mem_boosterFinset.mp (hB v hv w hw)
    apply hb.not_isDiag
    simpa [Sym2.mk_isDiag_iff] using hvw
  calc
    (k + 1) ^ 2 ≤ (R.sigma fun v ↦ T v).card :=
      sq_le_card_sigma R T hR hT
    _ ≤ 2 * (Erdos746.PathMax.boosterFinset G).card :=
      card_sigma_le_two_mul_card R T (Erdos746.PathMax.boosterFinset G) hne hB
    _ = 2 * (Erdos746.PathMax.boosterEdgeFinset G).card := by
      rw [Erdos746.PathMax.card_boosterEdgeFinset]

end


end Erdos746.PosaAlternative
