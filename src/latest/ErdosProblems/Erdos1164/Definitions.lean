import ErdosProblems.Erdos1165.Basic

/-!
# Pathwise covered discs for planar simple random walk

The probability law is the existing IID uniform four-direction walk. A disc
is Euclidean: its lattice points satisfy the integer squared-radius inequality.
Coverage includes both time zero and time `n`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Erdos1164

abbrev Point := Erdos1165.Point
abbrev WalkPath := Erdos1165.WalkPath
abbrev StepPath := Erdos1165.StepPath

noncomputable abbrev walkLaw : Measure WalkPath := Erdos1165.simpleRandomWalk

/-- The closed Euclidean lattice disc of integer radius `r`, centered at zero. -/
def latticeDisc (r : ℕ) : Set Point :=
  {x | x.1 ^ 2 + x.2 ^ 2 ≤ (r : ℤ) ^ 2}

/-- All lattice points in the disc have been visited by time `n`. -/
def CoversBy (s : WalkPath) (n r : ℕ) : Prop :=
  ∀ x ∈ latticeDisc r, ∃ k ≤ n, s k = x

/-- The finite range through time `n`, including its two endpoints. -/
def visitedBy (s : WalkPath) (n : ℕ) : Finset Point :=
  (Finset.range (n + 1)).image s

theorem mem_visitedBy {s : WalkPath} {n : ℕ} {x : Point} :
    x ∈ visitedBy s n ↔ ∃ k ≤ n, s k = x := by
  simp only [visitedBy, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h⟩

theorem latticeDisc_mono {r t : ℕ} (h : r ≤ t) : latticeDisc r ⊆ latticeDisc t := by
  intro x hx
  have hrt : (r : ℤ) ≤ t := by exact_mod_cast h
  have hr : (0 : ℤ) ≤ r := by positivity
  change x.1 ^ 2 + x.2 ^ 2 ≤ (t : ℤ) ^ 2
  change x.1 ^ 2 + x.2 ^ 2 ≤ (r : ℤ) ^ 2 at hx
  nlinarith

theorem CoversBy.mono_radius {s : WalkPath} {n r t : ℕ}
    (h : CoversBy s n t) (hrt : r ≤ t) : CoversBy s n r := by
  intro x hx
  exact h x (latticeDisc_mono hrt hx)

theorem CoversBy.mono_time {s : WalkPath} {m n r : ℕ}
    (h : CoversBy s m r) (hmn : m ≤ n) : CoversBy s n r := by
  intro x hx
  obtain ⟨k, hk, hs⟩ := h x hx
  exact ⟨k, hk.trans hmn, hs⟩

theorem axis_mem_latticeDisc {j r : ℕ} (hjr : j ≤ r) :
    ((j : ℤ), 0) ∈ latticeDisc r := by
  have hj : (0 : ℤ) ≤ j := by positivity
  have h : (j : ℤ) ≤ r := by exact_mod_cast hjr
  change (j : ℤ) ^ 2 + 0 ^ 2 ≤ (r : ℤ) ^ 2
  nlinarith

/-- A covered radius cannot exceed elapsed time, even for an arbitrary path. -/
theorem CoversBy.radius_le_time {s : WalkPath} {n r : ℕ}
    (h : CoversBy s n r) : r ≤ n := by
  let axis : ℕ → Point := fun j ↦ ((j : ℤ), 0)
  have hi : Function.Injective axis := by
    intro i j hij
    have heq := congrArg Prod.fst hij
    change (i : ℤ) = (j : ℤ) at heq
    exact_mod_cast heq
  have hsub : (Finset.range (r + 1)).image axis ⊆ visitedBy s n := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    apply mem_visitedBy.mpr
    exact h (axis j) (axis_mem_latticeDisc (by simpa using Finset.mem_range.mp hj))
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_image_le : (visitedBy s n).card ≤ (Finset.range (n + 1)).card)
  rw [Finset.card_image_of_injective _ hi, Finset.card_range, Finset.card_range] at hcard
  omega

/-- The largest completely covered integer disc radius. The fallback value
zero matters only for paths that have not visited the origin. -/
noncomputable def coveredRadius (s : WalkPath) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (CoversBy s n)).sup id

theorem coveredRadius_le_time (s : WalkPath) (n : ℕ) : coveredRadius s n ≤ n := by
  classical
  apply Finset.sup_le
  intro r hr
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  exact Nat.le_of_lt_succ h

theorem CoversBy.le_coveredRadius {s : WalkPath} {n r : ℕ}
    (h : CoversBy s n r) : r ≤ coveredRadius s n := by
  classical
  apply Finset.le_sup (f := id)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h.radius_le_time), h⟩

@[simp] theorem latticeDisc_zero : latticeDisc 0 = {0} := by
  ext x
  change x.1 ^ 2 + x.2 ^ 2 ≤ (0 : ℤ) ^ 2 ↔ x = 0
  constructor
  · intro hx
    have h1 : x.1 = 0 := by nlinarith [sq_nonneg x.2, sq_nonneg x.1]
    have h2 : x.2 = 0 := by nlinarith [sq_nonneg x.2, sq_nonneg x.1]
    exact Prod.ext h1 h2
  · rintro rfl
    norm_num

theorem coversBy_zero {s : WalkPath} (hs : s 0 = 0) (n : ℕ) : CoversBy s n 0 := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  exact ⟨0, Nat.zero_le n, hs.trans hx0.symm⟩

theorem coversBy_coveredRadius {s : WalkPath} (hs : s 0 = 0) (n : ℕ) :
    CoversBy s n (coveredRadius s n) := by
  classical
  apply Finset.sup_induction (p := CoversBy s n)
  · exact coversBy_zero hs n
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa only [sup_eq_right.mpr h] using hb
    · simpa only [sup_eq_left.mpr h] using ha
  · intro r hr
    exact (Finset.mem_filter.mp hr).2

theorem le_coveredRadius_iff {s : WalkPath} (hs : s 0 = 0) (n r : ℕ) :
    r ≤ coveredRadius s n ↔ CoversBy s n r :=
  ⟨fun h ↦ (coversBy_coveredRadius hs n).mono_radius h, CoversBy.le_coveredRadius⟩

theorem coveredRadius_mono {s : WalkPath} (hs : s 0 = 0) :
    Monotone (coveredRadius s) := by
  intro m n hmn
  exact ((coversBy_coveredRadius hs m).mono_time hmn).le_coveredRadius

theorem measurableSet_coversBy (n r : ℕ) :
    MeasurableSet {s : WalkPath | CoversBy s n r} := by
  unfold CoversBy
  measurability

theorem measurable_coveredRadius (n : ℕ) :
    Measurable fun s : WalkPath ↦ coveredRadius s n := by
  classical
  have hf : Measurable fun s : WalkPath ↦
      (Finset.range (n + 1)).filter (CoversBy s n) := by
    rw [measurable_finset_iff]
    intro r
    apply measurable_to_prop
    have heq : (fun s : WalkPath ↦ r ∈ (Finset.range (n + 1)).filter (CoversBy s n))
        ⁻¹' {True} = {s : WalkPath | r < n + 1} ∩ {s | CoversBy s n r} := by
      ext s
      simp
    rw [heq]
    exact (MeasurableSet.const _).inter (measurableSet_coversBy n r)
  exact (measurable_of_countable (fun t : Finset ℕ ↦ t.sup id)).comp hf

/-- The exact logarithm of the covered radius. Lean uses `Real.log 0 = 0`;
this convention is immaterial to the eventual probability estimates. -/
noncomputable def logRadius (s : WalkPath) (n : ℕ) : ℝ :=
  Real.log (coveredRadius s n : ℝ)

/-- A convenient auxiliary logarithm defined uniformly at radius zero. -/
noncomputable def regularizedLogRadius (s : WalkPath) (n : ℕ) : ℝ :=
  Real.log (1 + (coveredRadius s n : ℝ))

theorem measurable_logRadius (n : ℕ) : Measurable fun s : WalkPath ↦ logRadius s n := by
  exact Real.measurable_log.comp
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp (measurable_coveredRadius n))

/-- The exact two-sided order in probability: constants may depend on the
requested exceptional probability, but not on time. -/
def LogRadiusOrderInProbability : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
    ∀ᶠ n : ℕ in atTop,
      walkLaw.real {s | logRadius s n < a * Real.sqrt (Real.log (n : ℝ))} < ε ∧
      walkLaw.real {s | b * Real.sqrt (Real.log (n : ℝ)) < logRadius s n} < ε

end Erdos1164
