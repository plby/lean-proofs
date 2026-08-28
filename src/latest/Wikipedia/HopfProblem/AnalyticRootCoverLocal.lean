import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsRoots
import Wikipedia.HopfProblem.AnalyticRootCoverLocalGerms

/-!
# Local analytic square roots at zeros of even order

Factoring an analytic germ by its order of vanishing leaves an analytic unit.
An actual local square root of that unit gives a square root of the original
germ, including the case of order zero. The germ equality is then restricted
to a genuine disc on which the root is analytic and the square identity is
pointwise exact.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

/-- A finite even-order analytic germ has an actual analytic square root,
whose order is half of the original order. -/
theorem exists_analytic_square_root {F : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧
      (∀ᶠ z in 𝓝 a, r z ^ 2 = F z) ∧ analyticOrderAt r a = n := by
  obtain ⟨u, hu, hua, hFu⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  obtain ⟨q, hq, hqa, hqpow⟩ :=
    SpecialPeriods.exists_analytic_unit_root hu hua (by norm_num : 0 < (2 : ℕ))
  let r : ℂ → ℂ := fun z => (z - a) ^ n * q z
  have hr : AnalyticAt ℂ r a := ((analyticAt_id.sub analyticAt_const).pow n).mul hq
  refine ⟨r, hr, ?_, ?_⟩
  · filter_upwards [hFu, hqpow] with z hFz hqz
    change ((z - a) ^ n * q z) ^ 2 = F z
    rw [mul_pow, hqz, ← pow_mul, Nat.mul_comm n 2]
    simpa only [smul_eq_mul] using hFz.symm
  · apply hr.analyticOrderAt_eq_natCast.mpr
    refine ⟨q, hq, hqa, ?_⟩
    exact Eventually.of_forall (fun _ => rfl)

/-- The square root exists on an actual disc inside any prescribed neighborhood. -/
theorem exists_analytic_square_root_ball {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {S : Set ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ))
    (hS : S ∈ 𝓝 a) :
    ∃ ε > 0, ∃ r : ℂ → ℂ, ball a ε ⊆ S ∧
      AnalyticOnNhd ℂ r (ball a ε) ∧
      EqOn (fun z => r z ^ 2) F (ball a ε) ∧ analyticOrderAt r a = n := by
  obtain ⟨r, hr, hroot, horderR⟩ := exists_analytic_square_root hF horder
  have hn : {z | z ∈ S ∧ AnalyticAt ℂ r z ∧ r z ^ 2 = F z} ∈ 𝓝 a :=
    Filter.Eventually.and hS (hr.eventually_analyticAt.and hroot)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε, hε, r, ?_, ?_, ?_, horderR⟩
  · exact fun z hz => (hball hz).1
  · exact fun z hz => (hball hz).2.1
  · exact fun z hz => (hball hz).2.2

/-- In particular the root disc can be chosen inside any open domain containing the point. -/
theorem exists_analytic_square_root_ball_subset {F : ℂ → ℂ} {a : ℂ} {n : ℕ}
    {S : Set ℂ} (hS : IsOpen S) (ha : a ∈ S)
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ ε > 0, ∃ r : ℂ → ℂ, ball a ε ⊆ S ∧
      AnalyticOnNhd ℂ r (ball a ε) ∧
      EqOn (fun z => r z ^ 2) F (ball a ε) ∧ analyticOrderAt r a = n :=
  exists_analytic_square_root_ball hF horder (hS.mem_nhds ha)

/-- Finite order rules out coincidence of a square-root germ with its negative,
even when the root itself vanishes at the center. -/
theorem root_germ_ne_neg {F r : ℂ → ℂ} {a : ℂ}
    (hfinite : analyticOrderAt F a ≠ ⊤)
    (hroot : ∀ᶠ z in 𝓝 a, r z ^ 2 = F z) :
    ¬ r =ᶠ[𝓝 a] (fun z => -r z) := by
  intro hneg
  apply hfinite
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hroot, hneg] with z hz hn
  have hrz : r z = 0 := CharZero.eq_neg_self_iff.mp hn
  rw [← hz, hrz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Every point of an open root-section domain has two distinct signed root germs. -/
theorem root_germ_ne_neg_on {F r : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hfinite : ∀ z ∈ V, analyticOrderAt F z ≠ ⊤)
    (hroot : EqOn (fun z => r z ^ 2) F V) {a : ℂ} (ha : a ∈ V) :
    ¬ r =ᶠ[𝓝 a] (fun z => -r z) :=
  root_germ_ne_neg (hfinite a ha)
    (eventually_of_mem (hV.mem_nhds ha) (fun _ hz => hroot hz))

end Wikipedia.HopfProblem.AnalyticRootCover
