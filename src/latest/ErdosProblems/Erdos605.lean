/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 605.
https://www.erdosproblems.com/forum/thread/605

Informal authors:
- Paul Erdős
- Dean Hickerson
- János Pach

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos605.md
-/
import Mathlib

/-!
# Erdős Problem 605

An explicit point--line incidence construction.  The detailed mathematics and
Leanization plan are in `tex/605.tex`.
-/

open Filter Set
open scoped Topology

namespace Erdos605

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def pairDistance {n : ℕ} (x : Fin n → E3) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ dist (x i) (x j), fun _ _ ↦ dist_comm _ _⟩

/-- A finite set of non-diagonal `Sym2` values counts unordered geometric pairs. -/
def Erdos605Statement : Prop :=
  ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
    ∃ center : E3, ∃ radius : ℝ, 0 < radius ∧ ∀ n : ℕ,
      ∃ x : Fin n → E3, ∃ d : ℝ, ∃ E : Finset (Sym2 (Fin n)),
        Function.Injective x ∧
        (∀ i, dist (x i) center = radius) ∧
        0 < d ∧
        (∀ e ∈ E, ¬ e.IsDiag ∧ pairDistance x e = d) ∧
        f n * (n : ℝ) ≤ (E.card : ℝ)

/-! ## The all-`n` scale -/

def scale (n : ℕ) : ℕ :=
  Nat.findGreatest (fun q ↦ 3 * q ^ 3 ≤ n) n

lemma scale_spec (n : ℕ) : 3 * scale n ^ 3 ≤ n := by
  exact Nat.findGreatest_spec (P := fun q ↦ 3 * q ^ 3 ≤ n) (Nat.zero_le n) (by simp)

lemma scale_le (n : ℕ) : scale n ≤ n := Nat.findGreatest_le n

lemma le_scale_of_cube_le {q n : ℕ} (h : 3 * q ^ 3 ≤ n) : q ≤ scale n := by
  apply Nat.le_findGreatest (P := fun r ↦ 3 * r ^ 3 ≤ n)
  · by_cases hq : q = 0
    · simp [hq]
    · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
      have hsq : 1 * 1 ≤ q * q := Nat.mul_le_mul hq1 hq1
      have hcube : q ≤ q ^ 3 := by
        calc
          q = q * (1 * 1) := by ring
          _ ≤ q * (q * q) := Nat.mul_le_mul_left q hsq
          _ = q ^ 3 := by ring
      have htriple : q ^ 3 ≤ 3 * q ^ 3 := by omega
      exact hcube.trans (htriple.trans h)
  · exact h

lemma scale_tendsto : Tendsto scale atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro q
  refine ⟨3 * q ^ 3, ?_⟩
  intro n hn
  exact le_scale_of_cube_le hn

lemma lt_three_succ_scale_cube (n : ℕ) : n < 3 * (scale n + 1) ^ 3 := by
  by_cases hqn : scale n + 1 ≤ n
  · have hnot : ¬3 * (scale n + 1) ^ 3 ≤ n :=
      Nat.findGreatest_is_greatest (P := fun r ↦ 3 * r ^ 3 ≤ n)
        (Nat.lt_succ_self _) hqn
    exact Nat.lt_of_not_ge hnot
  · have hnq : n < scale n + 1 := by omega
    have hs1 : 1 ≤ scale n + 1 := by omega
    have hsq : 1 * 1 ≤ (scale n + 1) * (scale n + 1) := Nat.mul_le_mul hs1 hs1
    have hcube : scale n + 1 ≤ (scale n + 1) ^ 3 := by
      calc
        scale n + 1 = (scale n + 1) * (1 * 1) := by ring
        _ ≤ (scale n + 1) * ((scale n + 1) * (scale n + 1)) :=
          Nat.mul_le_mul_left (scale n + 1) hsq
        _ = (scale n + 1) ^ 3 := by ring
    have htriple : (scale n + 1) ^ 3 ≤ 3 * (scale n + 1) ^ 3 := by omega
    exact hnq.trans_le (hcube.trans htriple)

lemma n_le_twentyfour_scale_cube {n : ℕ} (hscale : 0 < scale n) :
    n ≤ 24 * scale n ^ 3 := by
  have hlt := lt_three_succ_scale_cube n
  have hs : scale n + 1 ≤ 2 * scale n := by omega
  have hc : (scale n + 1) ^ 3 ≤ (2 * scale n) ^ 3 := Nat.pow_le_pow_left hs 3
  calc
    n ≤ 3 * (scale n + 1) ^ 3 := Nat.le_of_lt hlt
    _ ≤ 3 * (2 * scale n) ^ 3 := Nat.mul_le_mul_left 3 hc
    _ = 24 * scale n ^ 3 := by ring

noncomputable def growth (n : ℕ) : ℝ := (scale n : ℝ) / 24

lemma growth_tendsto : Tendsto growth atTop atTop := by
  have hcast : Tendsto (fun n ↦ (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp scale_tendsto
  have h := hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 24)
  change Tendsto (fun n ↦ (scale n : ℝ) / 24) atTop atTop
  simpa [div_eq_mul_inv, mul_comm] using h

lemma growth_mul_le_fourth_power (n : ℕ) :
    growth n * (n : ℝ) ≤ ((scale n) ^ 4 : ℕ) := by
  by_cases hq : scale n = 0
  · simp [growth, hq]
  · have hbound := n_le_twentyfour_scale_cube (Nat.pos_of_ne_zero hq)
    rw [growth]
    push_cast
    have hbound' : (n : ℝ) ≤ 24 * (scale n : ℝ) ^ 3 := by exact_mod_cast hbound
    have hq0 : (0 : ℝ) ≤ scale n := by positivity
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [sq_nonneg ((scale n : ℝ) ^ 2)]

/-! ## Finite index sets -/

abbrev PointIndex (q : ℕ) := Fin q × Fin (2 * q ^ 2)
abbrev LineIndex (q : ℕ) := Fin q × Fin (q ^ 2)
abbrev GridIndex (n q : ℕ) := (PointIndex q ⊕ LineIndex q) ⊕ Fin (n - 3 * q ^ 3)
abbrev Incidence (q : ℕ) := (Fin q × Fin (q ^ 2)) × Fin q

lemma card_gridIndex {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) :
    Fintype.card (GridIndex n q) = n := by
  simp only [GridIndex, PointIndex, LineIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  have hcalc : q * (2 * q ^ 2) + q * q ^ 2 = 3 * q ^ 3 := by ring
  rw [hcalc]
  omega

noncomputable def gridEquiv {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) :
    GridIndex n q ≃ Fin n :=
  Fintype.equivOfCardEq (by simpa using card_gridIndex hfit)

lemma card_incidence (q : ℕ) : Fintype.card (Incidence q) = q ^ 4 := by
  simp only [Incidence, Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## Vectors on the unit sphere -/

noncomputable def vec3 (a b c : ℝ) : E3 := WithLp.toLp 2 ![a, b, c]

@[simp] lemma vec3_apply (a b c : ℝ) (i : Fin 3) :
    (vec3 a b c).ofLp i = ![a, b, c] i := by
  rfl

lemma vec3_ne_zero_of_second {a b c : ℝ} (hb : b ≠ 0) : vec3 a b c ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : E3 ↦ v.ofLp 1) h
  apply hb
  simpa [vec3] using h1

lemma vec3_ne_zero_of_third {a b c : ℝ} (hc : c ≠ 0) : vec3 a b c ≠ 0 := by
  intro h
  have h2 := congrArg (fun v : E3 ↦ v.ofLp 2) h
  apply hc
  simpa [vec3] using h2

noncomputable def normalize (v : E3) : E3 := ‖v‖⁻¹ • v

lemma norm_normalize {v : E3} (hv : v ≠ 0) : ‖normalize v‖ = 1 := by
  rw [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr hv

lemma inv_norm_pos {v : E3} (hv : v ≠ 0) : 0 < ‖v‖⁻¹ :=
  inv_pos.mpr (norm_pos_iff.mpr hv)

noncomputable def pointRaw (p : PointIndex q) : E3 :=
  vec3 (p.1 : ℝ) (p.2 : ℝ) 1

noncomputable def lineRaw (l : LineIndex q) : E3 :=
  vec3 (l.1 : ℝ) (-1) (l.2 : ℝ)

noncomputable def extraRaw (t : Fin m) : E3 :=
  vec3 (t : ℝ) 1 0

lemma pointRaw_ne_zero (p : PointIndex q) : pointRaw p ≠ 0 :=
  vec3_ne_zero_of_third one_ne_zero

lemma lineRaw_ne_zero (l : LineIndex q) : lineRaw l ≠ 0 :=
  vec3_ne_zero_of_second (by norm_num)

lemma extraRaw_ne_zero (t : Fin m) : extraRaw t ≠ 0 :=
  vec3_ne_zero_of_second one_ne_zero

noncomputable def pointLocation (p : PointIndex q) : E3 := normalize (pointRaw p)
noncomputable def lineLocation (l : LineIndex q) : E3 := normalize (lineRaw l)
noncomputable def extraLocation (t : Fin m) : E3 := normalize (extraRaw t)

@[simp] lemma norm_pointLocation (p : PointIndex q) : ‖pointLocation p‖ = 1 :=
  norm_normalize (pointRaw_ne_zero p)

@[simp] lemma norm_lineLocation (l : LineIndex q) : ‖lineLocation l‖ = 1 :=
  norm_normalize (lineRaw_ne_zero l)

@[simp] lemma norm_extraLocation (t : Fin m) : ‖extraLocation t‖ = 1 :=
  norm_normalize (extraRaw_ne_zero t)

noncomputable def gridLocation : GridIndex n q → E3
  | Sum.inl (Sum.inl p) => pointLocation p
  | Sum.inl (Sum.inr l) => lineLocation l
  | Sum.inr t => extraLocation t

lemma pointLocation_injective : Function.Injective (pointLocation : PointIndex q → E3) := by
  intro p r h
  have hz := congrArg (fun v : E3 ↦ v.ofLp 2) h
  have hx := congrArg (fun v : E3 ↦ v.ofLp 0) h
  have hy := congrArg (fun v : E3 ↦ v.ofLp 1) h
  change ‖pointRaw p‖⁻¹ * 1 = ‖pointRaw r‖⁻¹ * 1 at hz
  change ‖pointRaw p‖⁻¹ * (p.1 : ℝ) = ‖pointRaw r‖⁻¹ * (r.1 : ℝ) at hx
  change ‖pointRaw p‖⁻¹ * (p.2 : ℝ) = ‖pointRaw r‖⁻¹ * (r.2 : ℝ) at hy
  norm_num at hz
  have hp : 0 < ‖pointRaw p‖⁻¹ := inv_norm_pos (pointRaw_ne_zero p)
  have hx' : ‖pointRaw p‖⁻¹ * (p.1 : ℝ) = ‖pointRaw p‖⁻¹ * (r.1 : ℝ) := by
    rwa [← hz] at hx
  have hy' : ‖pointRaw p‖⁻¹ * (p.2 : ℝ) = ‖pointRaw p‖⁻¹ * (r.2 : ℝ) := by
    rwa [← hz] at hy
  have hxr : (p.1 : ℝ) = (r.1 : ℝ) := mul_left_cancel₀ (ne_of_gt hp) hx'
  have hyr : (p.2 : ℝ) = (r.2 : ℝ) := mul_left_cancel₀ (ne_of_gt hp) hy'
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hxr
  · apply Fin.ext
    exact_mod_cast hyr

lemma lineLocation_injective : Function.Injective (lineLocation : LineIndex q → E3) := by
  intro l r h
  have hy := congrArg (fun v : E3 ↦ v.ofLp 1) h
  have hx := congrArg (fun v : E3 ↦ v.ofLp 0) h
  have hz := congrArg (fun v : E3 ↦ v.ofLp 2) h
  change ‖lineRaw l‖⁻¹ * (-1) = ‖lineRaw r‖⁻¹ * (-1) at hy
  change ‖lineRaw l‖⁻¹ * (l.1 : ℝ) = ‖lineRaw r‖⁻¹ * (r.1 : ℝ) at hx
  change ‖lineRaw l‖⁻¹ * (l.2 : ℝ) = ‖lineRaw r‖⁻¹ * (r.2 : ℝ) at hz
  have hn : ‖lineRaw l‖⁻¹ = ‖lineRaw r‖⁻¹ := by linarith
  have hp : 0 < ‖lineRaw l‖⁻¹ := inv_norm_pos (lineRaw_ne_zero l)
  have hx' : ‖lineRaw l‖⁻¹ * (l.1 : ℝ) = ‖lineRaw l‖⁻¹ * (r.1 : ℝ) := by
    rwa [← hn] at hx
  have hz' : ‖lineRaw l‖⁻¹ * (l.2 : ℝ) = ‖lineRaw l‖⁻¹ * (r.2 : ℝ) := by
    rwa [← hn] at hz
  have hxr : (l.1 : ℝ) = (r.1 : ℝ) := mul_left_cancel₀ (ne_of_gt hp) hx'
  have hzr : (l.2 : ℝ) = (r.2 : ℝ) := mul_left_cancel₀ (ne_of_gt hp) hz'
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hxr
  · apply Fin.ext
    exact_mod_cast hzr

lemma extraLocation_injective : Function.Injective (extraLocation : Fin m → E3) := by
  intro t u h
  have hy := congrArg (fun v : E3 ↦ v.ofLp 1) h
  have hx := congrArg (fun v : E3 ↦ v.ofLp 0) h
  change ‖extraRaw t‖⁻¹ * 1 = ‖extraRaw u‖⁻¹ * 1 at hy
  change ‖extraRaw t‖⁻¹ * (t : ℝ) = ‖extraRaw u‖⁻¹ * (u : ℝ) at hx
  norm_num at hy
  have hp : 0 < ‖extraRaw t‖⁻¹ := inv_norm_pos (extraRaw_ne_zero t)
  have hx' : ‖extraRaw t‖⁻¹ * (t : ℝ) = ‖extraRaw t‖⁻¹ * (u : ℝ) := by
    rwa [← hy] at hx
  have htu : (t : ℝ) = (u : ℝ) := mul_left_cancel₀ (ne_of_gt hp) hx'
  apply Fin.ext
  exact_mod_cast htu

lemma pointLocation_ne_lineLocation (p : PointIndex q) (l : LineIndex q) :
    pointLocation p ≠ lineLocation l := by
  intro h
  have hy := congrArg (fun v : E3 ↦ v.ofLp 1) h
  change ‖pointRaw p‖⁻¹ * (p.2 : ℝ) = ‖lineRaw l‖⁻¹ * (-1) at hy
  have hp : 0 < ‖pointRaw p‖⁻¹ := inv_norm_pos (pointRaw_ne_zero p)
  have hl : 0 < ‖lineRaw l‖⁻¹ := inv_norm_pos (lineRaw_ne_zero l)
  have hp2 : (0 : ℝ) ≤ p.2 := by positivity
  have hleft : 0 ≤ ‖pointRaw p‖⁻¹ * (p.2 : ℝ) := mul_nonneg hp.le hp2
  nlinarith

lemma pointLocation_ne_extraLocation (p : PointIndex q) (t : Fin m) :
    pointLocation p ≠ extraLocation t := by
  intro h
  have hz := congrArg (fun v : E3 ↦ v.ofLp 2) h
  change ‖pointRaw p‖⁻¹ * 1 = ‖extraRaw t‖⁻¹ * 0 at hz
  norm_num at hz
  exact pointRaw_ne_zero p hz

lemma lineLocation_ne_extraLocation (l : LineIndex q) (t : Fin m) :
    lineLocation l ≠ extraLocation t := by
  intro h
  have hy := congrArg (fun v : E3 ↦ v.ofLp 1) h
  change ‖lineRaw l‖⁻¹ * (-1) = ‖extraRaw t‖⁻¹ * 1 at hy
  have hl : 0 < ‖lineRaw l‖⁻¹ := inv_norm_pos (lineRaw_ne_zero l)
  have ht : 0 < ‖extraRaw t‖⁻¹ := inv_norm_pos (extraRaw_ne_zero t)
  nlinarith

lemma gridLocation_injective : Function.Injective (gridLocation : GridIndex n q → E3) := by
  intro i j h
  rcases i with (i | t)
  · rcases i with (p | l)
    · rcases j with (j | u)
      · rcases j with (r | k)
        · cases pointLocation_injective h
          rfl
        · exact (pointLocation_ne_lineLocation p k h).elim
      · exact (pointLocation_ne_extraLocation p u h).elim
    · rcases j with (j | u)
      · rcases j with (r | k)
        · exact (pointLocation_ne_lineLocation r l h.symm).elim
        · cases lineLocation_injective h
          rfl
      · exact (lineLocation_ne_extraLocation l u h).elim
  · rcases j with (j | u)
    · rcases j with (p | l)
      · exact (pointLocation_ne_extraLocation p t h.symm).elim
      · exact (lineLocation_ne_extraLocation l t h.symm).elim
    · cases extraLocation_injective h
      rfl

lemma norm_gridLocation (i : GridIndex n q) : ‖gridLocation i‖ = 1 := by
  rcases i with (i | t)
  · rcases i with (p | l)
    · exact norm_pointLocation p
    · exact norm_lineLocation l
  · exact norm_extraLocation t

/-! ## Incidences and equal-distance pairs -/

def incidencePoint (t : Incidence q) : PointIndex q :=
  (t.2, ⟨t.1.1 * t.2 + t.1.2, by
    have hmul : t.1.1.val * t.2.val ≤ q * q :=
      Nat.mul_le_mul (Nat.le_of_lt t.1.1.isLt) (Nat.le_of_lt t.2.isLt)
    have hb := t.1.2.isLt
    have hqq : q * q = q ^ 2 := by ring
    omega⟩)

def incidenceLine (t : Incidence q) : LineIndex q := t.1

def incidencePair (t : Incidence q) : Sym2 (GridIndex n q) :=
  s(Sum.inl (Sum.inl (incidencePoint t)), Sum.inl (Sum.inr (incidenceLine t)))

lemma incidencePair_injective :
    Function.Injective (incidencePair : Incidence q → Sym2 (GridIndex n q)) := by
  intro s t h
  rw [incidencePair, incidencePair, Sym2.eq_iff] at h
  rcases h with h | h
  · have hp : incidencePoint s = incidencePoint t := by
      exact Sum.inl.inj (Sum.inl.inj h.1)
    have hl : incidenceLine s = incidenceLine t := by
      exact Sum.inr.inj (Sum.inl.inj h.2)
    apply Prod.ext
    · exact hl
    · exact congrArg Prod.fst hp
  · have hbad := Sum.inl.inj h.1
    cases hbad

lemma sym2_map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro s t h
  induction s using Sym2.inductionOn with
  | _ a b =>
    induction t using Sym2.inductionOn with
    | _ c d =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
      rcases h with (⟨hac, hbd⟩ | ⟨had, hbc⟩)
      · exact Or.inl ⟨hf hac, hf hbd⟩
      · exact Or.inr ⟨hf had, hf hbc⟩

lemma inner_pointRaw_lineRaw_incidence (t : Incidence q) :
    inner ℝ (pointRaw (incidencePoint t)) (lineRaw (incidenceLine t)) = 0 := by
  simp [pointRaw, lineRaw, incidencePoint, incidenceLine, vec3, PiLp.inner_apply,
    Fin.sum_univ_three]

lemma inner_point_line_incidence (t : Incidence q) :
    inner ℝ (pointLocation (incidencePoint t)) (lineLocation (incidenceLine t)) = 0 := by
  change inner ℝ (‖pointRaw (incidencePoint t)‖⁻¹ • pointRaw (incidencePoint t))
    (‖lineRaw (incidenceLine t)‖⁻¹ • lineRaw (incidenceLine t)) = 0
  rw [inner_smul_left, inner_smul_right, inner_pointRaw_lineRaw_incidence]
  simp

lemma dist_eq_sqrt_two_of_norm_eq_one_of_inner_eq_zero {u v : E3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    dist u v = Real.sqrt 2 := by
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [norm_sub_sq_real, hu, hv, huv, Real.sq_sqrt (by norm_num)]
  norm_num

lemma incidence_distance (t : Incidence q) :
    dist (pointLocation (incidencePoint t)) (lineLocation (incidenceLine t)) = Real.sqrt 2 :=
  dist_eq_sqrt_two_of_norm_eq_one_of_inner_eq_zero
    (norm_pointLocation _) (norm_lineLocation _) (inner_point_line_incidence t)

/-! ## Transport to exactly `n` indices and count the pairs -/

noncomputable def configuration {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) : Fin n → E3 :=
  fun i ↦ gridLocation ((gridEquiv hfit).symm i)

lemma configuration_injective {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) :
    Function.Injective (configuration hfit) :=
  gridLocation_injective.comp (gridEquiv hfit).symm.injective

lemma configuration_on_unit_sphere {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) (i : Fin n) :
    dist (configuration hfit i) 0 = 1 := by
  rw [dist_zero_right]
  exact norm_gridLocation _

noncomputable def incidenceEmbedding {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) :
    Incidence q ↪ Sym2 (Fin n) where
  toFun t := Sym2.map (gridEquiv hfit) (incidencePair t)
  inj' := by
    intro s t h
    apply incidencePair_injective
    exact sym2_map_injective (gridEquiv hfit).injective h

noncomputable def equalDistancePairs {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) :
    Finset (Sym2 (Fin n)) :=
  Finset.univ.map (incidenceEmbedding hfit)

lemma card_equalDistancePairs {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) :
    (equalDistancePairs hfit).card = q ^ 4 := by
  rw [equalDistancePairs, Finset.card_map, Finset.card_univ, card_incidence]

lemma incidencePair_not_diag (t : Incidence q) : ¬(incidencePair t : Sym2 (GridIndex n q)).IsDiag := by
  rw [incidencePair, Sym2.mk_isDiag_iff]
  intro h
  have hbad := Sum.inl.inj h
  cases hbad

lemma pairDistance_incidence {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n) (t : Incidence q) :
    pairDistance (configuration hfit) ((incidenceEmbedding hfit) t) = Real.sqrt 2 := by
  simp [pairDistance, configuration, incidenceEmbedding, incidencePair]
  change dist (pointLocation (incidencePoint t)) (lineLocation (incidenceLine t)) = Real.sqrt 2
  exact incidence_distance t

lemma mem_equalDistancePairs {n q : ℕ} (hfit : 3 * q ^ 3 ≤ n)
    {e : Sym2 (Fin n)} (he : e ∈ equalDistancePairs hfit) :
    ¬e.IsDiag ∧ pairDistance (configuration hfit) e = Real.sqrt 2 := by
  rw [equalDistancePairs, Finset.mem_map] at he
  obtain ⟨t, -, rfl⟩ := he
  constructor
  · change ¬(Sym2.map (gridEquiv hfit) (incidencePair t)).IsDiag
    rw [Sym2.isDiag_map (gridEquiv hfit).injective]
    exact incidencePair_not_diag t
  · exact pairDistance_incidence hfit t

/-! ## Resolution of Problem 605 -/

theorem erdos_605 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∃ center : E3, ∃ radius : ℝ, 0 < radius ∧ ∀ n : ℕ,
        ∃ x : Fin n → E3, ∃ d : ℝ, ∃ E : Finset (Sym2 (Fin n)),
          Function.Injective x ∧
          (∀ i, dist (x i) center = radius) ∧
          0 < d ∧
          (∀ e ∈ E, ¬ e.IsDiag ∧ pairDistance x e = d) ∧
          f n * (n : ℝ) ≤ (E.card : ℝ) := by
  refine ⟨growth, growth_tendsto, 0, 1, by norm_num, ?_⟩
  intro n
  let hfit : 3 * scale n ^ 3 ≤ n := scale_spec n
  refine ⟨configuration hfit, Real.sqrt 2, equalDistancePairs hfit,
    configuration_injective hfit, ?_, Real.sqrt_pos.2 (by norm_num), ?_, ?_⟩
  · intro i
    exact configuration_on_unit_sphere hfit i
  · intro e he
    exact mem_equalDistancePairs hfit he
  · rw [card_equalDistancePairs]
    exact growth_mul_le_fourth_power n

end Erdos605

#print axioms Erdos605.erdos_605
