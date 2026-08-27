import Arxiv.Arxiv2411_18291.FiniteHistoryProcess

/-!
# Conditional means for increments depending on the whole past

The trajectory fixes its supplied history almost surely. Thus an
integrable function of the current history and next finite state has
conditional mean given by the actual transition probability mass function.
-/

open MeasureTheory ProbabilityTheory Finset Preorder

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem history_fixed_ae (p : (n : ℕ) → History S n → PMF S) (n : ℕ) (h : History S n) :
    ∀ᵐ ω ∂Kernel.traj (X := fun _ => S) (transition p) n h, frestrictLe n ω = h := by
  have hmap : (Kernel.traj (X := fun _ => S) (transition p) n h).map (frestrictLe n) =
      Measure.dirac h := by
    rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
  have hm : Measurable (frestrictLe n : (ℕ → S) → History S n) := measurable_frestrictLe n
  apply ae_of_ae_map (μ := Kernel.traj (X := fun _ => S) (transition p) n h)
    (p := fun h' => h' = h) hm.aemeasurable
  rw [hmap]
  simp

theorem initial_state_ae (start : S) (p : (n : ℕ) → History S n → PMF S) :
    ∀ᵐ ω ∂probability start p, ω 0 = start := by
  filter_upwards [history_fixed_ae p 0 (fun _ => start)] with ω hω
  exact congrFun hω ⟨0, mem_Iic.mpr le_rfl⟩

theorem integrable_step (start : S) (p : (n : ℕ) → History S n → PMF S)
    (n : ℕ) (f : History S n → S → ℝ) :
    Integrable (fun ω => f (frestrictLe n ω) (ω (n + 1))) (probability start p) := by
  have hm : Measurable (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) := by fun_prop
  have hi : Integrable f.uncurry
      ((probability start p).map (fun ω => (frestrictLe n ω, ω (n + 1)))) := .of_finite
  exact hi.comp_measurable hm

theorem integral_step (p : (n : ℕ) → History S n → PMF S) (n : ℕ)
    (h : History S n) (f : History S n → S → ℝ) :
    (∫ ω, f (frestrictLe n ω) (ω (n + 1))
      ∂Kernel.traj (X := fun _ => S) (transition p) n h) =
        ∫ s, f h s ∂(p n h).toMeasure := by
  calc
    _ = ∫ ω, f h (ω (n + 1)) ∂Kernel.traj (X := fun _ => S) (transition p) n h := by
      apply integral_congr_ae
      filter_upwards [history_fixed_ae p n h] with ω hω
      rw [hω]
    _ = _ := integral_next p n h (f h)

theorem condExp_step (start : S) (p : (n : ℕ) → History S n → PMF S)
    (n : ℕ) (f : History S n → S → ℝ) :
    (probability start p)[fun ω => f (frestrictLe n ω) (ω (n + 1)) | Filtration.piLE n]
      =ᵐ[probability start p] fun ω =>
        ∫ s, f (frestrictLe n ω) s ∂(p n (frestrictLe n ω)).toMeasure := by
  have hc := Kernel.condExp_traj (X := fun _ => S) (κ := transition p)
    (a := 0) (b := n) (x₀ := fun _ => start)
    (f := fun ω => f (frestrictLe n ω) (ω (n + 1))) (Nat.zero_le n)
    (integrable_step start p n f)
  filter_upwards [hc] with ω hω
  exact hω.trans (integral_step p n (frestrictLe n ω) f)

end Arxiv2411_18291.FiniteHistoryProcess
