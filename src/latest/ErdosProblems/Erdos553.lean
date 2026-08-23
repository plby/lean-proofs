/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 553.
https://www.erdosproblems.com/forum/thread/553

Informal authors:
- Noga Alon
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos553.md
-/
import ErdosProblems.Erdos925

/-!
# Erdős Problem 553

Let `R₃(m) = r(K₃, K₃, K_m)` and `R₂(m) = r(K₃, K_m)`.  This file proves

`R₃(m) / R₂(m) → ∞`.

The exact three-colour Ramsey number is defined below from pairs of triangle-free
graphs.  `Erdos925.projective_eventual_counterexamples` supplies the proved lower
bound `R₃(m) ≫ m³ / log(m)⁶`; the elementary two-colour Ramsey recurrence gives
`R₂(m) ≤ m²` eventually.  Their quotient is bounded below by
`A * m / log(m)⁶`, which tends to infinity.

The detailed mathematical reconstruction of Alon--Rödl's sharper published proof
and the Leanization plan are in `tex/553.tex`.
-/

open Filter Real
open scoped Topology

namespace Erdos553

noncomputable section

/-! ## The exact three-colour Ramsey number -/

/-- On `N` vertices, every pair of graphs contains either a triangle in the first
graph, a triangle in the second graph, or an `m`-set independent in their union.

Allowing the two graphs to overlap is equivalent to an exact three-edge-colouring:
give an overlapping edge the first colour, give the second colour to the remaining
edges of the second graph, and give every other edge the third colour. -/
def ThreeColorRamseyProperty (m N : ℕ) : Prop :=
  ∀ red blue : SimpleGraph (Fin N),
    ¬ (red.CliqueFree 3 ∧ blue.CliqueFree 3 ∧ (red ⊔ blue).IndepSetFree m)

/-- Failure of `ThreeColorRamseyProperty` is exactly the concrete counterexample
predicate used by the fully checked construction for Erdős Problem 925. -/
lemma not_threeColorRamseyProperty_iff (m N : ℕ) :
    ¬ ThreeColorRamseyProperty m N ↔ Erdos925.ThreeColorCounterexample m N := by
  simp only [ThreeColorRamseyProperty, Erdos925.ThreeColorCounterexample,
    not_forall, not_not]

/-- The three-colour Ramsey property is monotone in the number of vertices. -/
lemma threeColorRamseyProperty_mono_vertices {m N M : ℕ} (hNM : N ≤ M) :
    ThreeColorRamseyProperty m N → ThreeColorRamseyProperty m M := by
  intro h red blue hbad
  let f : Fin N ↪ Fin M := Fin.castLEEmb hNM
  have hred : (red.comap f).CliqueFree 3 :=
    hbad.1.comap (SimpleGraph.Embedding.comap f red).isContained
  have hblue : (blue.comap f).CliqueFree 3 :=
    hbad.2.1.comap (SimpleGraph.Embedding.comap f blue).isContained
  have hunion : ((red ⊔ blue).comap f).IndepSetFree m :=
    SimpleGraph.IndepSetFree.comap
      (SimpleGraph.Embedding.comap f (red ⊔ blue)) hbad.2.2
  apply h (red.comap f) (blue.comap f)
  refine ⟨hred, hblue, ?_⟩
  change ((red ⊔ blue).comap f).IndepSetFree m
  exact hunion

/-- An explicit iterated two-colour Ramsey bound proves that the three-colour
property holds at some finite number of vertices. -/
theorem threeColorRamseyProperty_exists (m : ℕ) :
    ∃ N, ThreeColorRamseyProperty m N := by
  let a := Ramsey.ramseyNumber 3 m
  let N := Ramsey.ramseyNumber 3 a
  refine ⟨N, ?_⟩
  intro red blue hbad
  have hredNotFree : ¬ red.IndepSetFree a := by
    intro hredFree
    exact (Ramsey.ramseyNumber_spec 3 a) red ⟨hbad.1, hredFree⟩
  simp only [SimpleGraph.IndepSetFree, not_forall, not_not] at hredNotFree
  obtain ⟨S, hS⟩ := hredNotFree
  let H : SimpleGraph {x // x ∈ (↑S : Set (Fin N))} :=
    blue.induce (↑S : Set (Fin N))
  have hcard : Fintype.card {x // x ∈ (↑S : Set (Fin N))} = a := by
    simpa [a] using hS.card_eq
  have hHclique : H.CliqueFree 3 := by
    exact hbad.2.1.comap
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) blue).isContained
  have hinducedEq :
      (red ⊔ blue).induce (↑S : Set (Fin N)) = H := by
    ext x y
    change (red.Adj x y ∨ blue.Adj x y) ↔ blue.Adj x y
    constructor
    · rintro (hred | hblue)
      · have hnot := hS.isIndepSet
          x.property y.property hred.ne
        exact (hnot hred).elim
      · exact hblue
    · exact Or.inr
  have hHfree : H.IndepSetFree m := by
    have hunion :
        ((red ⊔ blue).induce (↑S : Set (Fin N))).IndepSetFree m :=
      SimpleGraph.IndepSetFree.comap
        (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) (red ⊔ blue))
        hbad.2.2
    rwa [hinducedEq] at hunion
  exact (Ramsey.ramseyProperty_of_card hcard (Ramsey.ramseyNumber_spec 3 m))
    H ⟨hHclique, hHfree⟩

/-- The generalized Ramsey number `r(K₃, K₃, K_m)`. -/
def threeColorRamseyNumber (m : ℕ) : ℕ :=
  sInf {N : ℕ | ThreeColorRamseyProperty m N}

/-- The defining Ramsey property holds at `threeColorRamseyNumber m`. -/
lemma threeColorRamseyNumber_spec (m : ℕ) :
    ThreeColorRamseyProperty m (threeColorRamseyNumber m) := by
  change sInf {N : ℕ | ThreeColorRamseyProperty m N} ∈
    {N : ℕ | ThreeColorRamseyProperty m N}
  exact csInf_mem (threeColorRamseyProperty_exists m)

/-- A concrete counterexample on `N` vertices gives the strict lower bound
`N < r(K₃, K₃, K_m)`. -/
lemma lt_threeColorRamseyNumber_of_counterexample {m N : ℕ}
    (h : Erdos925.ThreeColorCounterexample m N) :
    N < threeColorRamseyNumber m := by
  by_contra hnot
  have hle : threeColorRamseyNumber m ≤ N := Nat.le_of_not_gt hnot
  have hproperty : ThreeColorRamseyProperty m N :=
    threeColorRamseyProperty_mono_vertices hle (threeColorRamseyNumber_spec m)
  exact (not_threeColorRamseyProperty_iff m N).2 h hproperty

/-! ## Ramsey bounds -/

/-- The checked projective construction gives an eventual cubic-over-log-six
lower bound for the exact three-colour Ramsey number. -/
theorem eventual_threeColorRamsey_lower_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ m : ℕ in atTop,
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤
        (threeColorRamseyNumber m : ℝ) := by
  obtain ⟨A, hA, hwitness⟩ := Erdos925.projective_eventual_counterexamples
  refine ⟨A, hA, ?_⟩
  filter_upwards [hwitness] with m hw
  obtain ⟨N, hN, hcounterexample⟩ := hw
  have hlt : N < threeColorRamseyNumber m :=
    lt_threeColorRamseyNumber_of_counterexample hcounterexample
  exact hN.trans (by exact_mod_cast hlt.le)

/-- The elementary two-colour Ramsey recurrence gives the eventual bound
`r(K₃, K_m) ≤ m²`. -/
lemma eventual_twoColorRamsey_upper_bound :
    ∀ᶠ m : ℕ in atTop,
      (Ramsey.ramseyNumber 3 m : ℝ) ≤ (m : ℝ) ^ (2 : ℕ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hnat : Ramsey.ramseyNumber 3 m ≤ Nat.choose (m + 1) 2 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Ramsey.ramseyNumber_le_choose 2 m
  have hreal : (Ramsey.ramseyNumber 3 m : ℝ) ≤ (Nat.choose (m + 1) 2 : ℝ) := by
    exact_mod_cast hnat
  calc
    (Ramsey.ramseyNumber 3 m : ℝ) ≤ (Nat.choose (m + 1) 2 : ℝ) := hreal
    _ = ((m : ℝ) + 1) * (m : ℝ) / 2 := by
      rw [Nat.cast_choose_two]
      norm_num
    _ ≤ (m : ℝ) ^ (2 : ℕ) := by
      have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith

/-! ## The logarithmic limit and the quotient -/

/-- The two-colour Ramsey number, characterized without choosing an existence proof. -/
def twoColorRamseyNumber (m : ℕ) : ℕ :=
  sInf {N : ℕ | Ramsey.RamseyProperty 3 m N}

lemma twoColorRamseyNumber_eq (m : ℕ) :
    twoColorRamseyNumber m = Ramsey.ramseyNumber 3 m := by
  apply le_antisymm
  · exact csInf_le' (Ramsey.ramseyNumber_spec 3 m)
  · apply Ramsey.ramseyNumber_le_of_property
    change sInf {N : ℕ | Ramsey.RamseyProperty 3 m N} ∈
      {N : ℕ | Ramsey.RamseyProperty 3 m N}
    exact csInf_mem ⟨Ramsey.ramseyNumber 3 m, Ramsey.ramseyNumber_spec 3 m⟩

/-- Every fixed power of the logarithm is dominated by the identity; the
specialized quotient needed here therefore tends to infinity. -/
lemma tendsto_nat_div_log_pow_six_atTop :
    Tendsto (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ) ^ (6 : ℕ)) atTop atTop := by
  have hzero : Tendsto
      (fun m : ℕ ↦ Real.log (m : ℝ) ^ (6 : ℕ) / (m : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, one_mul, add_zero] using h
  have hpos : ∀ᶠ m : ℕ in atTop,
      0 < Real.log (m : ℝ) ^ (6 : ℕ) / (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
    have hlogpos : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast hm)
    positivity
  have hinv :=
    (tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩).inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  change (Real.log (m : ℝ) ^ (6 : ℕ) / (m : ℝ))⁻¹ =
    (m : ℝ) / Real.log (m : ℝ) ^ (6 : ℕ)
  exact inv_div _ _

/-- The exact limit statement in Erdős Problem 553. -/
def Problem553 : Prop :=
  Tendsto
    (fun m : ℕ ↦
      (threeColorRamseyNumber m : ℝ) / (twoColorRamseyNumber m : ℝ))
    atTop atTop

/-- Alon--Rödl's affirmative resolution of Erdős Problem 553. -/
theorem problem553 : Problem553 := by
  simp only [Problem553, twoColorRamseyNumber_eq]
  obtain ⟨A, hA, hlower⟩ := eventual_threeColorRamsey_lower_bound
  have hgrowth : Tendsto
      (fun m : ℕ ↦ A * ((m : ℝ) / Real.log (m : ℝ) ^ (6 : ℕ)))
      atTop atTop :=
    tendsto_nat_div_log_pow_six_atTop.const_mul_atTop hA
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower, eventual_twoColorRamsey_upper_bound,
    eventually_ge_atTop (2 : ℕ)] with m hlower hupper hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hlogpos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm)
  have hdenpos : 0 < (Ramsey.ramseyNumber 3 m : ℝ) := by
    exact_mod_cast Ramsey.ramseyNumber_pos (u := 3) (m := m) (by omega) (by omega)
  have hlowerNonneg :
      0 ≤ A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) := by
    positivity
  calc
    A * ((m : ℝ) / Real.log (m : ℝ) ^ (6 : ℕ)) =
        (A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ)) /
          (m : ℝ) ^ (2 : ℕ) := by
            field_simp
    _ ≤ (A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ)) /
          (Ramsey.ramseyNumber 3 m : ℝ) :=
      div_le_div_of_nonneg_left hlowerNonneg hdenpos hupper
    _ ≤ (threeColorRamseyNumber m : ℝ) /
          (Ramsey.ramseyNumber 3 m : ℝ) :=
      div_le_div_of_nonneg_right hlower hdenpos.le

/-- Erdős Problem 553 has a positive answer. -/
theorem erdos_553 : Problem553 := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    exact problem553
  · intro _
    trivial

#print axioms Erdos553.erdos_553

end

end Erdos553
