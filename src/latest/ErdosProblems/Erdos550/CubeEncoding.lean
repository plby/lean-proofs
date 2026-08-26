import Mathlib
import ErdosProblems.Erdos550.Rounding
import ErdosProblems.Erdos550.NullBlocker

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Null-blocker compactness (Theorem `thm:compactness` of the paper)

This file states and develops the paper's **null-blocker compactness theorem**:
a uniform finite robustification of the exact countable rounding theorem
`Erdos550.exact_rounding`.

The exact theorem (`exact_rounding`, file `NullBlocker.lean`) says: for a
countable ground set, if the densities satisfy the *exact* null-intersection
hypotheses (N1)–(N3), then the ground set is cooperatively colourable after
deleting at most `a-1` vertices.  The compactness theorem upgrades this to a
*finite, robust* statement: there is a single threshold `ε₀ = ε₀(q,a,r⋆) > 0`
so that *every* finite system whose hypotheses hold up to slack `ε ≤ ε₀`
(with hypergraphs of rank `≤ r⋆`) is cooperatively colourable after deleting at
most `a-1` vertices.

The paper proves this by contradiction through a diagonal-subsequence /
Kolmogorov-extension limiting argument with *shadow hypergraphs*
(`lem:fdlimit`, `lem:orderedimpurity`, `lem:shadowblockers`,
`lem:finitetransfer`), reducing to `exact_rounding` on the limiting countable
system.

## Densities

For a finite probability space `(Ω i, μ i)` and a set `A i x ⊆ Ω i`, the density
is `ρ_i(x) = (μ i (A i x)).toReal ∈ [0,1]`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Erdos550

/-- The real-valued density `ρ_i(x) = μ_i(A_i(x))`. -/
noncomputable def dens {q : ℕ} {X : Type*} {Ω : Fin q → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    (A : ∀ i, X → Set (Ω i)) (i : Fin q) (x : X) : ℝ :=
  (μ i (A i x)).toReal

/-
A cylinder set in the Boolean cube is clopen (hence boundaryless), so its
measure is continuous under weak convergence (portmanteau).
-/
theorem isClopen_cube_cylinder {X : Type*} (S : Finset X) :
    IsClopen {σ : X → Bool | ∀ x ∈ S, σ x = true} := by
  constructor;
  · rw [ Set.setOf_forall ];
    refine' isClosed_iInter fun i => _;
    by_cases hi : i ∈ S <;> simp +decide [ hi ];
    exact isClosed_eq ( continuous_apply i ) continuous_const;
  · rw [ isOpen_pi_iff ];
    intro f hf; use S, fun x => { true } ; aesop;

/-- **Cube encoding.** A probability space `(Ω, μ)` together with measurable
events `A x ⊆ Ω` pushes forward to a probability measure on the Boolean cube
`X → Bool` whose cylinder masses reproduce all finite-intersection measures
`μ (⋂_{x∈S} A x)`. -/
theorem cube_pushforward {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Type*} (A : X → Set Ω)
    (hA : ∀ x, MeasurableSet (A x)) :
    ∃ ρ : Measure (X → Bool), IsProbabilityMeasure ρ ∧
      ∀ S : Finset X, ρ {σ | ∀ x ∈ S, σ x = true} = μ (⋂ x ∈ S, A x) := by
  classical
  set f : Ω → (X → Bool) := fun ω x => decide (ω ∈ A x) with hf
  have hfmeas : Measurable f := by
    apply measurable_pi_lambda
    intro x
    refine (measurable_to_bool ?_)
    have : (fun ω => decide (ω ∈ A x)) ⁻¹' {true} = A x := by ext ω; simp
    rw [this]; exact hA x
  have hcyl : ∀ S : Finset X, MeasurableSet {σ : X → Bool | ∀ x ∈ S, σ x = true} := by
    intro S
    have hrw : {σ : X → Bool | ∀ x ∈ S, σ x = true}
        = ⋂ x ∈ S, {σ : X → Bool | σ x = true} := by ext σ; simp
    rw [hrw]
    refine MeasurableSet.biInter S.countable_toSet (fun x _ => ?_)
    exact measurableSet_eq_fun (measurable_pi_apply x) measurable_const
  refine ⟨μ.map f, Measure.isProbabilityMeasure_map hfmeas.aemeasurable, ?_⟩
  intro S
  rw [Measure.map_apply hfmeas (hcyl S)]
  congr 1
  ext ω
  simp only [hf, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iInter, decide_eq_true_eq]

open Filter Topology in
/-- **Cube encoding into a common space.** Encoding the events `A x` via an
injection `e : X ↪ ℕ` (padding the unused coordinates by the constant `false`)
gives a probability measure on `ℕ → Bool` whose embedded-cylinder masses
reproduce the finite-intersection measures of the original system. -/
theorem cube_pushforward_nat {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Type*} (e : X ↪ ℕ) (A : X → Set Ω)
    (hA : ∀ x, MeasurableSet (A x)) :
    ∃ ρ : Measure (ℕ → Bool), IsProbabilityMeasure ρ ∧
      ∀ S : Finset X, ρ {σ | ∀ x ∈ S, σ (e x) = true} = μ (⋂ x ∈ S, A x) := by
  by_contra h_contra;
  have := @cube_pushforward;
  convert! this μ ( fun x => if h : ∃ y, e y = x then A h.choose else Set.univ ) _;
  any_goals intro x; by_cases hx : ∃ y, e y = x <;> simp +decide [ hx, hA ];
  all_goals try infer_instance;
  constructor <;> intro h;
  · contradiction;
  · obtain ⟨ ρ, hρ₁, hρ₂ ⟩ := h;
    refine' h_contra ⟨ ρ, hρ₁, fun S => _ ⟩;
    convert! hρ₂ ( Finset.image e S ) using 1;
    · simp +decide [ Finset.mem_image ];
    · congr! 1;
      ext; simp [Finset.mem_image]

open Filter Topology in
/-- **Weak-limit subsequence extraction.** Any sequence of `q`-tuples of
probability measures on the compact metrizable space `ℕ → Bool` has a subsequence
converging coordinatewise (in all `q` colours) to a limit tuple. -/
theorem exists_weak_limit_subseq {q : ℕ}
    (ρ : ℕ → Fin q → ProbabilityMeasure (ℕ → Bool)) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧ ∃ L : Fin q → ProbabilityMeasure (ℕ → Bool),
      ∀ i, Tendsto (fun n => ρ (ψ n) i) atTop (𝓝 (L i)) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ L : (Fin q → ProbabilityMeasure (ℕ → Bool)), (Filter.Tendsto (fun n => (fun i => ρ (ψ n) i)) Filter.atTop (nhds L)) := by
    have h_compact : IsCompact (Set.univ : Set (Fin q → ProbabilityMeasure (ℕ → Bool))) := by
      exact isCompact_univ;
    have := h_compact.isSeqCompact fun n => Set.mem_univ ( ρ n );
    tauto;
  exact ⟨ ψ, hψ.1, hψ.2.choose, fun i => tendsto_pi_nhds.mp hψ.2.choose_spec i ⟩

/-- The cylinder mass `ρ_i(⋂_{x∈S} {σ | σ x = true})` as a real number, for a
normal-form system on the Boolean cube `ℕ → Bool`. -/
noncomputable def cdens (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
    (i : Fin q) (S : Finset ℕ) : ℝ :=
  ((ρ i).toMeasure {σ | ∀ x ∈ S, σ x = true}).toReal

open Filter Topology in
/-- `cdens` is nonnegative. -/
lemma cdens_nonneg (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
    (i : Fin q) (S : Finset ℕ) : 0 ≤ cdens q ρ i S :=
  ENNReal.toReal_nonneg

open Filter Topology in
/-- `cdens` is at most one (it is the mass of a set under a probability measure). -/
lemma cdens_le_one (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
    (i : Fin q) (S : Finset ℕ) : cdens q ρ i S ≤ 1 := by
  unfold cdens
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono (by simp) prob_le_one

open Filter Topology in
/-- **Portmanteau for cylinder masses.**  Cylinder masses `cdens` are continuous
under weak convergence of probability measures (the cylinder events are clopen,
hence boundaryless), along *any* filter `L`. -/
lemma cdens_tendsto {q : ℕ} {ι : Type*} {L : Filter ι}
    (ρ : ι → Fin q → ProbabilityMeasure (ℕ → Bool))
    (Lm : Fin q → ProbabilityMeasure (ℕ → Bool))
    (hconv : ∀ i, Tendsto (fun n => ρ n i) L (𝓝 (Lm i)))
    (i : Fin q) (S : Finset ℕ) :
    Tendsto (fun n => cdens q (ρ n) i S) L (𝓝 (cdens q Lm i S)) := by
  have hclopen : IsClopen {σ : ℕ → Bool | ∀ x ∈ S, σ x = true} := isClopen_cube_cylinder S
  have hnn := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (μs := fun n => ρ n i) (μ := Lm i) (hconv i) hclopen
  -- transfer from the NNReal-valued application to the real-valued `cdens`
  have : Tendsto
      (fun n => ((ρ n i {σ : ℕ → Bool | ∀ x ∈ S, σ x = true} : NNReal) : ℝ)) L
      (𝓝 ((Lm i {σ : ℕ → Bool | ∀ x ∈ S, σ x = true} : NNReal) : ℝ)) := by
    exact (NNReal.continuous_coe.tendsto _).comp hnn
  simpa only [cdens, MeasureTheory.ProbabilityMeasure.coeFn_def,
    MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.toReal] using! this

/-- A finite-intersection cylinder mass over a finset of `↑Xset` equals the
`cdens` of the image finset in `ℕ`. -/
lemma cdens_eq_inter_toReal (q : ℕ) (L : Fin q → ProbabilityMeasure (ℕ → Bool))
    (i : Fin q) {Xset : Set ℕ} (S : Finset (↑Xset)) :
    ((L i).toMeasure (⋂ x ∈ S, {σ : ℕ → Bool | σ (x : ℕ) = true})).toReal
      = cdens q L i (S.map (Function.Embedding.subtype Xset)) := by
  unfold cdens
  congr 2
  ext σ
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_map,
    Function.Embedding.coe_subtype]
  constructor
  · rintro h y ⟨z, hz, rfl⟩; exact h z hz
  · intro h z hz; exact h z ⟨z, hz, rfl⟩

end Erdos550
