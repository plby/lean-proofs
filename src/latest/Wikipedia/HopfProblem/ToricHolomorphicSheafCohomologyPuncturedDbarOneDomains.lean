import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentRadius

/-!
# The actual disc–annulus exhaustion of `ℂ × ℂ*`
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

def domain : Set (ℂ × ℂ) := {q | q.2 ≠ 0}

theorem isOpen_domain : IsOpen domain :=
  isOpen_ne_fun continuous_snd continuous_const

def annularOpen (R : ℝ) : Set (ℂ × ℂ) :=
  ball (0 : ℂ) R ×ˢ HolomorphicCousin.annulus R⁻¹ R

def annularClosed (R : ℝ) : Set (ℂ × ℂ) :=
  closedBall (0 : ℂ) R ×ˢ (closedBall 0 R \ ball 0 R⁻¹)

theorem isOpen_annularOpen (R : ℝ) : IsOpen (annularOpen R) :=
  isOpen_ball.prod (HolomorphicCousin.isOpen_annulus R⁻¹ R)

theorem annularClosed_subset_domain {R : ℝ} (hR : 0 < R) :
    annularClosed R ⊆ domain := by
  intro q hq
  exact Laurent.closedAnnulus_subset_punctured (inv_pos.mpr hR) hq.2

theorem annularOpen_subset_closed (R : ℝ) : annularOpen R ⊆ annularClosed R := by
  intro q hq
  refine ⟨ball_subset_closedBall hq.1, ?_, ?_⟩
  · exact mem_closedBall_zero_iff.mpr hq.2.2.le
  · simpa only [mem_ball, dist_zero_right, not_lt] using hq.2.1.le

theorem annularClosed_mono {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    annularClosed r ⊆ annularClosed R := by
  have hR : 0 < R := hr.trans_le hrR
  have hi : R⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hR hr).mpr hrR
  intro q hq
  refine ⟨closedBall_subset_closedBall hrR hq.1,
    closedBall_subset_closedBall hrR hq.2.1, ?_⟩
  exact fun hw => hq.2.2 (ball_subset_ball hi hw)

theorem annularOpen_mono {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    annularOpen r ⊆ annularOpen R := by
  have hR : 0 < R := hr.trans_le hrR
  have hi : R⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hR hr).mpr hrR
  intro q hq
  exact ⟨ball_subset_ball hrR hq.1, hi.trans_lt hq.2.1, hq.2.2.trans_le hrR⟩

theorem annularClosed_subset_open {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    annularClosed r ⊆ annularOpen R := by
  have hR : 0 < R := hr.trans hrR
  have hi : R⁻¹ < r⁻¹ := (inv_lt_inv₀ hR hr).mpr hrR
  intro q hq
  have hlo : r⁻¹ ≤ ‖q.2‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hq.2.2
  have hhi : ‖q.2‖ ≤ r := mem_closedBall_zero_iff.mp hq.2.1
  exact ⟨closedBall_subset_ball hrR hq.1, hi.trans_le hlo, hhi.trans_lt hrR⟩

def exhaustionDomain (n : ℕ) : Set (ℂ × ℂ) := annularOpen ((n : ℝ) + 2)

def primitiveStageSet (n : ℕ) : Set (ℂ × ℂ) := annularClosed ((n : ℝ) + 3)

theorem isOpen_exhaustionDomain (n : ℕ) : IsOpen (exhaustionDomain n) :=
  isOpen_annularOpen _

theorem monotone_exhaustionDomain : Monotone exhaustionDomain := by
  intro n m hnm
  apply annularOpen_mono (by positivity)
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  linarith

theorem monotone_primitiveStageSet : Monotone primitiveStageSet := by
  intro n m hnm
  apply annularClosed_mono (by positivity)
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  linarith

theorem exhaustionDomain_subset_domain (n : ℕ) : exhaustionDomain n ⊆ domain :=
  (annularOpen_subset_closed _).trans (annularClosed_subset_domain (by positivity))

theorem primitiveStageSet_subset_domain (n : ℕ) : primitiveStageSet n ⊆ domain :=
  annularClosed_subset_domain (by positivity)

theorem exhaustionDomain_subset_primitiveStageSet (n : ℕ) :
    exhaustionDomain n ⊆ primitiveStageSet n :=
  (annularOpen_subset_closed _).trans (annularClosed_mono (by positivity) (by linarith))

theorem cover_exhaustionDomain (q : ℂ × ℂ) (hq : q ∈ domain) :
    ∃ n, q ∈ exhaustionDomain n := by
  have hp : 0 < ‖q.2‖ := norm_pos_iff.mpr hq
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖q.1‖ (max ‖q.2‖ ‖q.2‖⁻¹))
  have hz : ‖q.1‖ < (n : ℝ) + 2 :=
    ((le_max_left _ _).trans_lt hn).trans (by linarith)
  have hw : ‖q.2‖ < (n : ℝ) + 2 :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hn.trans (by linarith))
  have hwi : ‖q.2‖⁻¹ < (n : ℝ) + 2 :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hn.trans (by linarith))
  have hl : ((n : ℝ) + 2)⁻¹ < ‖q.2‖ :=
    (inv_lt_comm₀ (by positivity) hp).mpr hwi
  exact ⟨n, mem_ball_zero_iff.mpr hz, hl, hw⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
