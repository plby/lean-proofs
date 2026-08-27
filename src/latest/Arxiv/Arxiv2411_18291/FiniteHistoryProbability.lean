import Arxiv.Arxiv2411_18291.FiniteHistoryStep

/-!
# Exact probabilities of finite histories

Two transition systems assign the same probability to an event whenever
their transitions agree along every history in that event. This allows
degree stopping to be removed from a successful greedy trajectory.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem prefix_probability_zero (start : S) (p : (n : ℕ) → History S n → PMF S)
    (h : History S 0) :
    probability start p {ω | frestrictLe 0 ω = h} = Measure.dirac (fun _ => start) {h} := by
  change probability start p (frestrictLe 0 ⁻¹' {h}) = _
  rw [← Measure.map_apply (measurable_frestrictLe 0) (measurableSet_singleton h)]
  unfold probability
  rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]

theorem prefix_probability_succ (start : S) (p : (n : ℕ) → History S n → PMF S)
    (n : ℕ) (h : History S (n + 1)) :
    probability start p {ω | frestrictLe (n + 1) ω = h} =
      p n (frestrictLe₂ (π := fun _ => S) n.le_succ h) (h ⟨n + 1, mem_Iic.mpr le_rfl⟩) *
        probability start p {ω | frestrictLe n ω = frestrictLe₂ (π := fun _ => S) n.le_succ h} := by
  let h₀ := frestrictLe₂ (π := fun _ => S) n.le_succ h
  let a := h ⟨n + 1, mem_Iic.mpr le_rfl⟩
  have hevent : {ω | frestrictLe (n + 1) ω = h} =
      (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) ⁻¹' ({h₀} ×ˢ {a}) := by
    ext ω
    change frestrictLe (n + 1) ω = h ↔ frestrictLe n ω = h₀ ∧ ω (n + 1) = a
    constructor
    · intro hh
      constructor
      · funext i
        exact congrFun hh ⟨i, mem_Iic.mpr ((mem_Iic.mp i.property).trans n.le_succ)⟩
      · exact congrFun hh ⟨n + 1, mem_Iic.mpr le_rfl⟩
    · rintro ⟨hprev, hlast⟩
      funext i
      by_cases hi : (i : ℕ) ≤ n
      · exact congrFun hprev ⟨i, mem_Iic.mpr hi⟩
      · have hi' : (i : ℕ) = n + 1 := by have := mem_Iic.mp i.property; omega
        have hie : i = ⟨n + 1, mem_Iic.mpr le_rfl⟩ := Subtype.ext hi'
        subst i
        exact hlast
  rw [hevent, ← Measure.map_apply (by fun_prop)
    ((measurableSet_singleton h₀).prod (measurableSet_singleton a))]
  change ((Kernel.traj (X := fun _ => S) (transition p) 0 (fun _ => start)).map
    (fun ω => (frestrictLe n ω, ω (n + 1)))) ({h₀} ×ˢ {a}) = _
  rw [← Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n),
    Measure.compProd_apply_prod (measurableSet_singleton h₀) (measurableSet_singleton a),
    lintegral_singleton]
  change (p n h₀).toMeasure {a} *
    (Kernel.partialTraj (X := fun _ => S) (transition p) 0 n (fun _ => start)) {h₀} = _
  rw [(p n h₀).toMeasure_apply_singleton a (measurableSet_singleton a),
    ← Kernel.traj_map_frestrictLe_apply,
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton h₀)]
  rfl

theorem prefix_probability_eq_of_transitions (start : S)
    (p q : (n : ℕ) → History S n → PMF S) (n : ℕ) (h : History S n)
    (hpq : ∀ i (hi : i < n),
      p i (frestrictLe₂ (π := fun _ => S) hi.le h) = q i (frestrictLe₂ (π := fun _ => S) hi.le h)) :
    probability start p {ω | frestrictLe n ω = h} =
      probability start q {ω | frestrictLe n ω = h} := by
  induction n with
  | zero => rw [prefix_probability_zero, prefix_probability_zero]
  | succ n ih =>
    have htrans := hpq n n.lt_succ_self
    have hprev := ih (frestrictLe₂ (π := fun _ => S) n.le_succ h)
      (fun i hi => hpq i (hi.trans_le n.le_succ))
    rw [prefix_probability_succ start p n h, prefix_probability_succ start q n h]
    exact congrArg₂ (fun x y : ℝ≥0∞ => x * y)
      (congrArg (fun μ : PMF S => μ (h ⟨n + 1, mem_Iic.mpr le_rfl⟩)) htrans) hprev

theorem history_event_probability_eq_of_transitions (start : S)
    (p q : (n : ℕ) → History S n → PMF S) (n : ℕ) (E : Set (History S n))
    (hpq : ∀ h ∈ E, ∀ i (hi : i < n),
      p i (frestrictLe₂ (π := fun _ => S) hi.le h) = q i (frestrictLe₂ (π := fun _ => S) hi.le h)) :
    probability start p (frestrictLe n ⁻¹' E) =
      probability start q (frestrictLe n ⁻¹' E) := by
  classical
  let s := E.toFinite.toFinset
  have hs : (s : Set (History S n)) = E := Set.Finite.coe_toFinset _
  rw [← hs, ← sum_measure_preimage_singleton s
    (fun h _ => (measurableSet_singleton h).preimage (measurable_frestrictLe n)),
    ← sum_measure_preimage_singleton s
      (fun h _ => (measurableSet_singleton h).preimage (measurable_frestrictLe n))]
  apply sum_congr rfl
  intro h hh
  exact prefix_probability_eq_of_transitions start p q n h
    (hpq h (by simpa only [s, Set.Finite.mem_toFinset] using hh))

end Arxiv2411_18291.FiniteHistoryProcess
