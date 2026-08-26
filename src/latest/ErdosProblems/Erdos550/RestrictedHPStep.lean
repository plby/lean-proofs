import Mathlib
import ErdosProblems.Erdos550.HPPackedness

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The two-case resource step in the stateful matching embedding

The whole-edge off--Turán proof reduces the local analytic choice at a matching
edge to the packedness dichotomy also used in Appendix A.2 of
Hladký--Piguet:

* a saturated edge has room on both cluster sides by the aggregate head
  surplus; or
* a nonsaturated edge has balanced loads, hence both root pools and both
  cluster sides remain available.

This file proves that dichotomy from explicit numerical hypotheses in the exact
form consumed by a rooted-pair embedding step.
-/

namespace Erdos550

/-- Resource selection for one component in the restricted regular-matching
algorithm.  `l,r` are the old loads, `a,b` its two colour-class sizes,
`L,R` the two head thresholds, `p,q` the fresh root pools, and `cap` the common
cluster capacity.  The returned Boolean chooses the component orientation. -/
theorem restricted_hp_choose_orientation
    (l r a b L R cap margin τ err rootNeed localNeed p q : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ τ)
    (hpack : HPPacked l r L R margin τ)
    (hrootSum : 2 * rootNeed ≤ p + q)
    (htypL : L - l - err ≤ p)
    (htypR : R - r - err ≤ q)
    (hrootMargin : rootNeed + τ + err ≤ margin)
    (hLcap : L ≤ cap) (hRcap : R ≤ cap)
    (hroomSat : l + r + localNeed + margin ≤ L + R)
    (hroomBal : 2 * localNeed + τ ≤ (cap - l) + (cap - r)) :
    ∃ swap : Bool,
      rootNeed ≤ (if swap then q else p) ∧
      localNeed ≤ cap - l ∧
      localNeed ≤ cap - r ∧
      HPPacked
        (if swap then l + b else l + a)
        (if swap then r + a else r + b)
        L R margin τ := by
  have hroot : rootNeed ≤ p ∨ rootNeed ≤ q :=
    one_side_large_of_sum p q rootNeed hrootSum
  have hboth :
      ¬ min L R - margin ≤ min l r →
        rootNeed ≤ p ∧ rootNeed ≤ q := by
    intro hnot
    exact both_root_pools_of_balanced_nonsaturated
      l r L R margin τ err p q rootNeed
      (hpack.resolve_left hnot) hnot htypL htypR hrootMargin
  obtain ⟨swap, hswapRoot, hswapPack⟩ :=
    hpPacked_choose_root_orientation
      l r a b L R margin τ rootNeed p q
      ha hb hab hpack hroot hboth
  have hroom : localNeed ≤ cap - l ∧ localNeed ≤ cap - r := by
    by_cases hsat : min L R - margin ≤ min l r
    · exact both_free_sides_of_saturated cap l r L R margin localNeed
        hLcap hRcap hsat hroomSat
    · have hbal : |l - r| ≤ τ := hpack.resolve_left hsat
      exact both_sides_large_of_sum_discrepancy
        (cap - l) (cap - r) localNeed τ
        (hpPacked_free_discrepancy l r cap τ hbal) hroomBal
  exact ⟨swap, hswapRoot, hroom.1, hroom.2, hswapPack⟩

/-- Averaging over the matching edges which are good for the current head
vertex, followed by the saturated/balanced resource choice. -/
theorem restricted_hp_select_good_edge
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Good : Finset κ) (hGood : Good.Nonempty)
    (l r L R p q : κ → ℝ)
    (a b cap margin τ err rootNeed localNeed : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ τ)
    (hpacked : ∀ k, HPPacked (l k) (r k) (L k) (R k) margin τ)
    (hsumRoot :
      (Good.card : ℝ) * (2 * rootNeed) ≤
        ∑ k ∈ Good, (p k + q k))
    (htypL : ∀ k ∈ Good, L k - l k - err ≤ p k)
    (htypR : ∀ k ∈ Good, R k - r k - err ≤ q k)
    (hrootMargin : rootNeed + τ + err ≤ margin)
    (hLcap : ∀ k ∈ Good, L k ≤ cap)
    (hRcap : ∀ k ∈ Good, R k ≤ cap)
    (hroomSat : ∀ k ∈ Good,
      l k + r k + localNeed + margin ≤ L k + R k)
    (hroomBal : ∀ k ∈ Good,
      2 * localNeed + τ ≤ (cap - l k) + (cap - r k)) :
    ∃ k ∈ Good, ∃ swap : Bool,
      rootNeed ≤ (if swap then q k else p k) ∧
      localNeed ≤ cap - l k ∧
      localNeed ≤ cap - r k ∧
      HPPacked
        (if swap then l k + b else l k + a)
        (if swap then r k + a else r k + b)
        (L k) (R k) margin τ := by
  have hedge : ∃ k ∈ Good, 2 * rootNeed ≤ p k + q k := by
    by_contra h
    push_neg at h
    have hlt :
        (∑ k ∈ Good, (p k + q k)) <
          ∑ _k ∈ Good, (2 * rootNeed) :=
      Finset.sum_lt_sum_of_nonempty hGood (fun k hk => h k hk)
    have hconst :
        (∑ _k ∈ Good, (2 * rootNeed)) =
          (Good.card : ℝ) * (2 * rootNeed) := by
      simp [mul_comm]
    rw [hconst] at hlt
    exact (not_lt_of_ge hsumRoot) hlt
  obtain ⟨k, hk, hkRoot⟩ := hedge
  obtain ⟨swap, hroot, hfreeL, hfreeR, hpack⟩ :=
    restricted_hp_choose_orientation
      (l k) (r k) a b (L k) (R k) cap margin τ err
      rootNeed localNeed (p k) (q k)
      ha hb hab (hpacked k) hkRoot
      (htypL k hk) (htypR k hk) hrootMargin
      (hLcap k hk) (hRcap k hk)
      (hroomSat k hk) (hroomBal k hk)
  exact ⟨k, hk, swap, hroot, hfreeL, hfreeR, hpack⟩

/-- Sharp one-edge resource choice.  In the nonsaturated case the packedness
balance and the local margin alone force room on both sides; only a saturated
edge needs the summed threshold-room inequality. -/
theorem restricted_hp_choose_orientation_sharp
    (l r a b L R cap margin τ err rootNeed localNeed p q : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ τ)
    (hpack : HPPacked l r L R margin τ)
    (hrootSum : 2 * rootNeed ≤ p + q)
    (htypL : L - l - err ≤ p)
    (htypR : R - r - err ≤ q)
    (hrootMargin : rootNeed + τ + err ≤ margin)
    (hlocalMargin : localNeed + τ ≤ margin)
    (hLcap : L ≤ cap) (hRcap : R ≤ cap)
    (hroomSat : l + r + localNeed + margin ≤ L + R) :
    ∃ swap : Bool,
      rootNeed ≤ (if swap then q else p) ∧
      localNeed ≤ cap - l ∧
      localNeed ≤ cap - r ∧
      HPPacked
        (if swap then l + b else l + a)
        (if swap then r + a else r + b)
        L R margin τ := by
  have hroot : rootNeed ≤ p ∨ rootNeed ≤ q :=
    one_side_large_of_sum p q rootNeed hrootSum
  have hboth :
      ¬ min L R - margin ≤ min l r →
        rootNeed ≤ p ∧ rootNeed ≤ q := by
    intro hnot
    exact both_root_pools_of_balanced_nonsaturated
      l r L R margin τ err p q rootNeed
      (hpack.resolve_left hnot) hnot htypL htypR hrootMargin
  obtain ⟨swap, hswapRoot, hswapPack⟩ :=
    hpPacked_choose_root_orientation
      l r a b L R margin τ rootNeed p q
      ha hb hab hpack hroot hboth
  have hroom : localNeed ≤ cap - l ∧ localNeed ≤ cap - r := by
    by_cases hsat : min L R - margin ≤ min l r
    · exact both_free_sides_of_saturated cap l r L R margin localNeed
        hLcap hRcap hsat hroomSat
    · exact both_free_sides_of_balanced_nonsaturated
        cap l r L R margin τ localNeed hLcap hRcap
        (hpack.resolve_left hsat) hsat hlocalMargin
  exact ⟨swap, hswapRoot, hroom.1, hroom.2, hswapPack⟩

/-- The matching-wide BHX selection in the form needed by the parity-refined
proof.  One aggregate threshold surplus chooses an edge with enough total
room.  Typicality then converts that same surplus into a large root-neighbour
pool, so the root and capacity requirements are obtained at the *same* edge.

This statement permits `L k = 0` or `R k = 0`.  On such a one-sided edge the
saturation alternative of `HPPacked` is automatic, exactly as in the
restricted Appendix A.2 argument. -/
theorem restricted_hp_select_joint_surplus
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Good : Finset κ) (hGood : Good.Nonempty)
    (l r L R p q : κ → ℝ)
    (a b cap margin τ err rootNeed localNeed : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ τ)
    (hpacked : ∀ k, HPPacked (l k) (r k) (L k) (R k) margin τ)
    (hsurplus :
      (∑ k ∈ Good, (l k + r k)) +
          (Good.card : ℝ) * (localNeed + margin) ≤
        ∑ k ∈ Good, (L k + R k))
    (htypL : ∀ k ∈ Good, L k - l k - err ≤ p k)
    (htypR : ∀ k ∈ Good, R k - r k - err ≤ q k)
    (hrootFromRoom :
      2 * rootNeed + 2 * err ≤ localNeed + margin)
    (hrootMargin : rootNeed + τ + err ≤ margin)
    (hlocalMargin : localNeed + τ ≤ margin)
    (hLcap : ∀ k ∈ Good, L k ≤ cap)
    (hRcap : ∀ k ∈ Good, R k ≤ cap) :
    ∃ k ∈ Good, ∃ swap : Bool,
      rootNeed ≤ (if swap then q k else p k) ∧
      localNeed ≤ cap - l k ∧
      localNeed ≤ cap - r k ∧
      HPPacked
        (if swap then l k + b else l k + a)
        (if swap then r k + a else r k + b)
        (L k) (R k) margin τ := by
  have hedge :
      ∃ k ∈ Good,
        l k + r k + localNeed + margin ≤ L k + R k := by
    by_contra h
    push_neg at h
    have hlt :
        (∑ k ∈ Good, (L k + R k)) <
          ∑ k ∈ Good, (l k + r k + (localNeed + margin)) :=
      Finset.sum_lt_sum_of_nonempty hGood
        (fun k hk => by simpa [add_assoc] using! h k hk)
    have hsum :
        (∑ k ∈ Good, (l k + r k + (localNeed + margin))) =
          (∑ k ∈ Good, (l k + r k)) +
            (Good.card : ℝ) * (localNeed + margin) := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    rw [hsum] at hlt
    exact (not_lt_of_ge hsurplus) hlt
  obtain ⟨k, hk, hkRoom⟩ := hedge
  have hkRoot : 2 * rootNeed ≤ p k + q k := by
    have hp := htypL k hk
    have hq := htypR k hk
    nlinarith
  obtain ⟨swap, hroot, hfreeL, hfreeR, hpack⟩ :=
    restricted_hp_choose_orientation_sharp
      (l k) (r k) a b (L k) (R k) cap margin τ err
      rootNeed localNeed (p k) (q k)
      ha hb hab (hpacked k) hkRoot
      (htypL k hk) (htypR k hk)
      hrootMargin hlocalMargin
      (hLcap k hk) (hRcap k hk) hkRoom
  exact ⟨k, hk, swap, hroot, hfreeL, hfreeR, hpack⟩

end Erdos550
