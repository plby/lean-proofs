import Arxiv.Arxiv2411_18291.AdaptiveConcentration
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Processes with finite states and history-dependent transitions

The trajectory measure is constructed from actual probability mass
functions. Its conditional expectation at each step is the expectation
under the prescribed transition law. This connects finite greedy choices
to the previously proved adaptive concentration inequality.
-/

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

abbrev History (S : Type*) (n : ℕ) := Iic n → S

def transition (p : (n : ℕ) → History S n → PMF S) (n : ℕ) :
    Kernel (History S n) S := Kernel.ofFunOfCountable fun h => (p n h).toMeasure

instance transition_isMarkov (p : (n : ℕ) → History S n → PMF S) (n : ℕ) :
    IsMarkovKernel (transition p n) := by
  constructor
  intro h
  change IsProbabilityMeasure (p n h).toMeasure
  infer_instance

def probability (start : S) (p : (n : ℕ) → History S n → PMF S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S) (transition p) 0 (fun _ => start)

instance probability_isProbability (start : S) (p : (n : ℕ) → History S n → PMF S) :
    IsProbabilityMeasure (probability start p) := by
  unfold probability
  infer_instance

theorem integrable_coordinate (start : S) (p : (n : ℕ) → History S n → PMF S)
    (n : ℕ) (f : S → ℝ) : Integrable (fun ω => f (ω n)) (probability start p) := by
  have hi : Integrable f ((probability start p).map (fun ω => ω n)) := .of_finite
  exact hi.comp_measurable (measurable_pi_apply n)

theorem integral_next (p : (n : ℕ) → History S n → PMF S) (n : ℕ)
    (h : History S n) (f : S → ℝ) :
    (∫ ω, f (ω (n + 1)) ∂Kernel.traj (X := fun _ => S) (transition p) n h) =
      ∫ s, f s ∂(p n h).toMeasure := by
  have hm : (Kernel.traj (X := fun _ => S) (transition p) n h).map (fun ω => ω (n + 1)) =
      (p n h).toMeasure := by
    rw [← Kernel.map_apply _ (measurable_pi_apply _), Kernel.map_traj_succ_self]
    rfl
  rw [← hm]
  exact (integral_map (measurable_pi_apply _).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable).symm

/-- Conditional means are computed using the actual finite transition law. -/
theorem condExp_next (start : S) (p : (n : ℕ) → History S n → PMF S)
    (n : ℕ) (f : S → ℝ) :
    (probability start p)[(fun ω => f (ω (n + 1))) | Filtration.piLE n] =ᵐ[probability start p]
      fun ω => ∫ s, f s ∂(p n (frestrictLe n ω)).toMeasure := by
  have hc := Kernel.condExp_traj (X := fun _ => S) (κ := transition p)
    (a := 0) (b := n) (x₀ := fun _ => start) (f := fun ω => f (ω (n + 1)))
    (Nat.zero_le n) (integrable_coordinate start p (n + 1) f)
  filter_upwards [hc] with ω hω
  exact hω.trans (integral_next p n (frestrictLe n ω) f)

theorem next_mem_support (start : S) (p : (n : ℕ) → History S n → PMF S) (n : ℕ) :
    ∀ᵐ ω : ℕ → S ∂probability start p, ω (n + 1) ∈ (p n (frestrictLe n ω)).support := by
  have hs : ∀ᵐ z ∂(Kernel.partialTraj (X := fun _ => S) (transition p) 0 n (fun _ => start))
      ⊗ₘ transition p n,
      z.2 ∈ (p n z.1).support := by
    apply Measure.ae_compProd_of_ae_ae (Set.toFinite _).measurableSet
    apply ae_of_all
    intro h
    change ∀ᵐ s ∂(p n h).toMeasure, s ∈ (p n h).support
    change (p n h).support ∈ ae (p n h).toMeasure
    apply (mem_ae_iff_prob_eq_one (p n h).support_countable.measurableSet).mpr
    exact ((p n h).toMeasure_apply_eq_one_iff (p n h).support_countable.measurableSet).mpr
      Set.Subset.rfl
  rw [Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)] at hs
  exact ae_of_ae_map (by fun_prop) hs

/-- A bad-event probability below one gives a good path in all transition supports. -/
theorem exists_supported_path (start : S) (p : (n : ℕ) → History S n → PMF S)
    (Q : (ℕ → S) → Prop) (hbad : (probability start p).real {ω | ¬ Q ω} < 1) :
    ∃ ω : ℕ → S, (∀ n, ω (n + 1) ∈ (p n (frestrictLe n ω)).support) ∧ Q ω := by
  classical
  have hsupport : ∀ᵐ ω : ℕ → S ∂probability start p, ∀ n,
      ω (n + 1) ∈ (p n (frestrictLe n ω)).support :=
    ae_all_iff.mpr fun n => next_mem_support start p n
  by_contra hex
  have hnot : ∀ᵐ ω ∂probability start p, ¬ Q ω := by
    filter_upwards [hsupport] with ω hω
    exact fun hQ => hex ⟨ω, hω, hQ⟩
  have heq : {ω | ¬ Q ω} =ᵐ[probability start p] Set.univ := by
    filter_upwards [hnot] with ω hω
    exact propext ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
  have hone : (probability start p).real {ω | ¬ Q ω} = 1 :=
    (measureReal_congr heq).trans probReal_univ
  linarith

end Arxiv2411_18291.FiniteHistoryProcess
