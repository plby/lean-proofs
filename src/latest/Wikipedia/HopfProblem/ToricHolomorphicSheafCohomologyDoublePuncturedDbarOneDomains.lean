import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneDomains

/-!
# The actual product-of-annuli exhaustion of `(ℂ*)²`
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

def domain : Set (ℂ × ℂ) := {q | q.1 ≠ 0 ∧ q.2 ≠ 0}

theorem isOpen_domain : IsOpen domain :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    (isOpen_ne_fun continuous_snd continuous_const)

def closedAnnulus (R : ℝ) : Set ℂ := closedBall 0 R \ ball 0 R⁻¹

def annularOpen (R : ℝ) : Set (ℂ × ℂ) :=
  HolomorphicCousin.annulus R⁻¹ R ×ˢ HolomorphicCousin.annulus R⁻¹ R

def annularClosed (R : ℝ) : Set (ℂ × ℂ) := closedAnnulus R ×ˢ closedAnnulus R

theorem closedAnnulus_subset_punctured {R : ℝ} (hR : 0 < R) :
    closedAnnulus R ⊆ {0}ᶜ := Laurent.closedAnnulus_subset_punctured (inv_pos.mpr hR)

theorem annulus_subset_closedAnnulus (R : ℝ) :
    HolomorphicCousin.annulus R⁻¹ R ⊆ closedAnnulus R := by
  intro z hz
  refine ⟨mem_closedBall_zero_iff.mpr hz.2.le, ?_⟩
  simpa only [mem_ball, dist_zero_right, not_lt] using hz.1.le

theorem closedAnnulus_mono {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    closedAnnulus r ⊆ closedAnnulus R := by
  have hi : R⁻¹ ≤ r⁻¹ := (inv_le_inv₀ (hr.trans_le hrR) hr).mpr hrR
  intro z hz
  exact ⟨closedBall_subset_closedBall hrR hz.1,
    fun hw => hz.2 (ball_subset_ball hi hw)⟩

theorem closedAnnulus_subset_annulus {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    closedAnnulus r ⊆ HolomorphicCousin.annulus R⁻¹ R := by
  have hi : R⁻¹ < r⁻¹ := (inv_lt_inv₀ (hr.trans hrR) hr).mpr hrR
  intro z hz
  have hlo : r⁻¹ ≤ ‖z‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hz.2
  exact ⟨hi.trans_le hlo, (mem_closedBall_zero_iff.mp hz.1).trans_lt hrR⟩

theorem isOpen_annularOpen (R : ℝ) : IsOpen (annularOpen R) :=
  (HolomorphicCousin.isOpen_annulus R⁻¹ R).prod (HolomorphicCousin.isOpen_annulus R⁻¹ R)

theorem annularClosed_subset_domain {R : ℝ} (hR : 0 < R) :
    annularClosed R ⊆ domain := by
  intro q hq
  exact ⟨closedAnnulus_subset_punctured hR hq.1, closedAnnulus_subset_punctured hR hq.2⟩

theorem annularOpen_subset_closed (R : ℝ) : annularOpen R ⊆ annularClosed R := by
  intro q hq
  exact ⟨annulus_subset_closedAnnulus R hq.1, annulus_subset_closedAnnulus R hq.2⟩

theorem annularClosed_mono {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    annularClosed r ⊆ annularClosed R :=
  prod_mono (closedAnnulus_mono hr hrR) (closedAnnulus_mono hr hrR)

theorem annularOpen_mono {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    annularOpen r ⊆ annularOpen R := by
  have hi : R⁻¹ ≤ r⁻¹ := (inv_le_inv₀ (hr.trans_le hrR) hr).mpr hrR
  intro q hq
  exact ⟨⟨hi.trans_lt hq.1.1, hq.1.2.trans_le hrR⟩,
    ⟨hi.trans_lt hq.2.1, hq.2.2.trans_le hrR⟩⟩

theorem annularClosed_subset_open {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    annularClosed r ⊆ annularOpen R :=
  prod_mono (closedAnnulus_subset_annulus hr hrR) (closedAnnulus_subset_annulus hr hrR)

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
  obtain ⟨n, hn⟩ := PuncturedDbarOne.cover_exhaustionDomain q hq.2
  obtain ⟨m, hm⟩ := PuncturedDbarOne.cover_exhaustionDomain (q.2, q.1) hq.1
  have hn' := PuncturedDbarOne.monotone_exhaustionDomain (le_max_left n m) hn
  have hm' := PuncturedDbarOne.monotone_exhaustionDomain (le_max_right n m) hm
  exact ⟨max n m, hm'.2, hn'.2⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
