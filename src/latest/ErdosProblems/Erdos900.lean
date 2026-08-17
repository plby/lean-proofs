/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos900.Probability

/-!
# Erdős Problem 900

Ajtai--Komlós--Szemerédi's theorem that every supercritical uniform random
graph has, with high probability, a path of positive linear length.  The
accompanying reconstruction and formalization guide is `tex/900.tex`.
-/

open Filter Set
open scoped BigOperators SimpleGraph Topology

noncomputable section

namespace Erdos900

/-- Densities above the phase transition `1/2`. -/
abbrev Density := Set.Ioi (1 / 2 : ℝ)

/-- The right-hand filter at the excluded endpoint `1/2`. -/
def densityAtHalf : Filter Density :=
  Filter.comap ((↑) : Density → ℝ) (𝓝[>] (1 / 2 : ℝ))

/-- The finite universe of possible edges on `Fin n`. -/
def allEdges (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).edgeFinset

@[simp] theorem card_allEdges (n : ℕ) :
    (allEdges n).card = n.choose 2 := by
  simpa [allEdges] using
    (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))

/-- The exact sample space of labelled graphs on `Fin n` having `m` edges. -/
def fixedSamples (n m : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  (allEdges n).powersetCard m

@[simp] theorem card_fixedSamples (n m : ℕ) :
    (fixedSamples n m).card = (n.choose 2).choose m := by
  simp [fixedSamples]

/-- The graph whose edges are the pairs in `S`. -/
def graphOfEdges {n : ℕ} (S : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))

noncomputable instance graphOfEdgesEdgeSetFintype {n : ℕ}
    (S : Finset (Sym2 (Fin n))) : Fintype (graphOfEdges S).edgeSet :=
  Fintype.ofFinite _

theorem graphOfEdges_edgeFinset {n : ℕ} {S : Finset (Sym2 (Fin n))}
    (hS : S ⊆ allEdges n) : (graphOfEdges S).edgeFinset = S := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Finset.mem_coe]
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    have htop := hS he
    simpa [allEdges] using htop

/-- A graph on `Fin n` contains a simple path with at least `a*n` edges.

The path with `k+1` vertices has `k` edges, so the ceiling makes this exactly
the usual real-valued lower bound on path length. -/
def HasLongPath (n : ℕ) (a : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  SimpleGraph.pathGraph (⌈a * n⌉₊ + 1) ⊑ G

theorem HasLongPath.mono {n : ℕ} {a b : ℝ} {G : SimpleGraph (Fin n)}
    (hab : a ≤ b) (h : HasLongPath n b G) : HasLongPath n a G := by
  have hceil : ⌈a * n⌉₊ + 1 ≤ ⌈b * n⌉₊ + 1 := by
    gcongr
  exact ⟨h.some.comp (pathInitialCopy hceil)⟩

theorem HasLongPath.mono_graph {n : ℕ} {a : ℝ} {G H : SimpleGraph (Fin n)}
    (hGH : G ≤ H) (h : HasLongPath n a G) : HasLongPath n a H := by
  exact h.mono_right hGH

/-- The integer number of edges prescribed by density `c`. -/
def edgeBudget (c : ℝ) (n : ℕ) : ℕ := ⌊c * n⌋₊

/-- Exact success probability in the uniform `floor(c*n)`-edge model.

The Boolean coordinates are indexed by the canonical enumeration of the
`n.choose 2` possible edges.  The infeasible small-`n` case has probability
zero; for every fixed `c` it disappears eventually. -/
def fixedPathProbability (c a : ℝ) (n : ℕ) : ℝ := by
  classical
  let m := edgeBudget c n
  if h : m ≤ n.choose 2 then
    letI : Nonempty (Erdos88.Fourier.BoolSlice (Fin (n.choose 2)) m) :=
      boolSliceNonempty (by simpa using h)
    exact Erdos88.Concentration.uniformProbability
      (fun omega : Erdos88.Fourier.BoolSlice (Fin (n.choose 2)) m ↦
        HasLongPath n a (canonicalGraph n omega.1))
  else
    exact 0

/-- "With high probability" for a fixed density and path fraction. -/
def WHP (c a : ℝ) : Prop :=
  Tendsto (fixedPathProbability c a) atTop (𝓝 1)

theorem fixedPathProbability_nonneg (c a : ℝ) (n : ℕ) :
    0 ≤ fixedPathProbability c a n := by
  classical
  by_cases h : edgeBudget c n ≤ n.choose 2
  · letI : Nonempty (Erdos88.Fourier.BoolSlice
        (Fin (n.choose 2)) (edgeBudget c n)) :=
      boolSliceNonempty (by simpa using h)
    simpa [fixedPathProbability, h] using
      (Erdos88.Concentration.uniformProbability_nonneg
        (fun omega : Erdos88.Fourier.BoolSlice
            (Fin (n.choose 2)) (edgeBudget c n) ↦
          HasLongPath n a (canonicalGraph n omega.1)))
  · simp [fixedPathProbability, h]

theorem fixedPathProbability_le_one (c a : ℝ) (n : ℕ) :
    fixedPathProbability c a n ≤ 1 := by
  classical
  by_cases h : edgeBudget c n ≤ n.choose 2
  · letI : Nonempty (Erdos88.Fourier.BoolSlice
        (Fin (n.choose 2)) (edgeBudget c n)) :=
      boolSliceNonempty (by simpa using h)
    simpa [fixedPathProbability, h] using
      (Erdos88.Concentration.uniformProbability_le_one
        (fun omega : Erdos88.Fourier.BoolSlice
            (Fin (n.choose 2)) (edgeBudget c n) ↦
          HasLongPath n a (canonicalGraph n omega.1)))
  · simp [fixedPathProbability, h]

theorem fixedPathProbability_mono_fraction {c a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    fixedPathProbability c b n ≤ fixedPathProbability c a n := by
  classical
  by_cases h : edgeBudget c n ≤ n.choose 2
  · letI : Nonempty (Erdos88.Fourier.BoolSlice
        (Fin (n.choose 2)) (edgeBudget c n)) :=
      boolSliceNonempty (by simpa using h)
    simp only [fixedPathProbability, h, dite_true]
    apply Erdos88.Concentration.uniformProbability_mono
    intro omega hpath
    exact hpath.mono hab
  · simp [fixedPathProbability, h]

theorem WHP.mono_fraction {c a b : ℝ} (h : WHP c b) (hab : a ≤ b) : WHP c a := by
  have hlo : ∀ n, fixedPathProbability c b n ≤ fixedPathProbability c a n :=
    fixedPathProbability_mono_fraction hab
  have hhi : ∀ n, fixedPathProbability c a n ≤ 1 :=
    fixedPathProbability_le_one c a
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    h tendsto_const_nhds hlo hhi

/-! ## The adaptive-DFS asymptotic lemma -/

private def queryBudget (A : ℝ) (n : ℕ) : ℕ :=
  ⌊A * (n : ℝ) ^ 2⌋₊

private def lowerWindow (L : ℝ) (n : ℕ) : ℕ := ⌈L * n⌉₊
private def upperWindow (U : ℝ) (n : ℕ) : ℕ := ⌊U * n⌋₊
private def rootCap (s : ℝ) (n : ℕ) : ℕ := ⌈s * n⌉₊ + 1

private theorem floorLinear_ratio_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (⌊a * (n : ℝ)⌋₊ : ℝ) / n)
      atTop (𝓝 a) := by
  simpa [Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

private theorem ceilLinear_ratio_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (⌈a * (n : ℝ)⌉₊ : ℝ) / n)
      atTop (𝓝 a) := by
  simpa [Function.comp_def] using
    (tendsto_nat_ceil_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

private theorem floorQuadratic_ratio_tendsto {A : ℝ} (hA : 0 ≤ A) :
    Tendsto (fun n : ℕ ↦ (queryBudget A n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 A) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hn2 : Tendsto (fun n : ℕ ↦ (n : ℝ) * n) atTop atTop :=
    hn.atTop_mul_atTop₀ hn
  simpa [queryBudget, pow_two, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop hA).comp hn2

private theorem chooseTwo_ratio_tendsto :
    Tendsto (fun n : ℕ ↦ (n.choose 2 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlim :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      tendsto_one_div_atTop_nhds_zero_nat).div_const 2
  have hlim' : Tendsto (fun n : ℕ ↦ (1 - 1 / (n : ℝ)) / 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Nat.cast_choose_two]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

private theorem choose_root_le_rootCap {A s : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) (hroot : 2 * A < s ^ 2)
    (n r : ℕ) (hr : r.choose 2 ≤ queryBudget A n) :
    r ≤ rootCap s n := by
  by_cases hn : n = 0
  · subst n
    simp only [queryBudget, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, Nat.floor_zero, rootCap, Nat.ceil_zero, zero_add] at hr ⊢
    have hz : r.choose 2 = 0 := by omega
    have hlt : r < 2 := Nat.choose_eq_zero_iff.mp hz
    omega
  by_contra hle
  have hrcap : rootCap s n < r := Nat.lt_of_not_ge hle
  have hceil : s * (n : ℝ) ≤ (⌈s * (n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hrCast : ((rootCap s n : ℕ) : ℝ) < r := by exact_mod_cast hrcap
  have hsn0 : 0 ≤ s * (n : ℝ) := mul_nonneg hs (Nat.cast_nonneg n)
  have hsnr : s * (n : ℝ) < (r : ℝ) := by
    simp only [rootCap, Nat.cast_add, Nat.cast_one] at hrCast
    linarith
  have hsnrm1 : s * (n : ℝ) < (r : ℝ) - 1 := by
    simp only [rootCap, Nat.cast_add, Nat.cast_one] at hrCast
    linarith
  have hmul : (s * (n : ℝ)) * (s * (n : ℝ)) <
      (r : ℝ) * ((r : ℝ) - 1) := by
    nlinarith [mul_pos (sub_pos.mpr hsnr) (sub_pos.mpr hsnrm1)]
  have hrReal : (r.choose 2 : ℝ) ≤ (queryBudget A n : ℝ) := by
    exact_mod_cast hr
  rw [Nat.cast_choose_two] at hrReal
  have hqReal : (queryBudget A n : ℝ) ≤ A * (n : ℝ) ^ 2 := by
    exact Nat.floor_le (mul_nonneg hA (sq_nonneg _))
  have hnpos : (0 : ℝ) < n := by positivity
  nlinarith [mul_pos (sub_pos.mpr hroot) (sq_pos_of_pos hnpos)]

/-- The analytic/probabilistic engine.  Its hypotheses are the strict
inequalities left by the DFS counting certificate after normalization. -/
theorem WHP_of_DFS_parameters {c A s D L U : ℝ}
    (hc : 0 < c) (hA : 0 < A) (hAhalf : A < 1 / 2)
    (hs : 0 < s) (hroot : 2 * A < s ^ 2)
    (hD : 0 ≤ D) (hDL : D < L) (hLM : L < 2 * c * A)
    (hMU : 2 * c * A < U) (hUs : U + s < 1)
    (hrectangle : A < (L - D) * (1 - U - s)) :
    WHP c D := by
  let m : ℕ → ℕ := edgeBudget c
  let q : ℕ → ℕ := queryBudget A
  let lo : ℕ → ℕ := lowerWindow L
  let hi : ℕ → ℕ := upperWindow U
  let roots : ℕ → ℕ := rootCap s
  let km : ℕ → ℕ := fun n ↦ ⌈D * (n : ℝ)⌉₊
  let N : ℕ → ℕ := fun n ↦ n.choose 2
  let center : ℕ → ℝ := fun n ↦
    (m n : ℝ) / (N n : ℝ) * (min (q n) (N n) : ℕ)
  have hL0 : 0 ≤ L := le_trans hD hDL.le
  have hM0 : 0 < 2 * c * A := by positivity
  have hU0 : 0 ≤ U := (hM0.trans hMU).le
  have hmLim : Tendsto (fun n : ℕ ↦ (m n : ℝ) / n) atTop (𝓝 c) := by
    simpa [m, edgeBudget] using floorLinear_ratio_tendsto hc.le
  have hqLim : Tendsto (fun n : ℕ ↦ (q n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 A) := by
    simpa [q] using floorQuadratic_ratio_tendsto hA.le
  have hloLim : Tendsto (fun n : ℕ ↦ (lo n : ℝ) / n)
      atTop (𝓝 L) := by
    simpa [lo, lowerWindow] using ceilLinear_ratio_tendsto hL0
  have hhiLim : Tendsto (fun n : ℕ ↦ (hi n : ℝ) / n)
      atTop (𝓝 U) := by
    simpa [hi, upperWindow] using floorLinear_ratio_tendsto hU0
  have hkmLim : Tendsto (fun n : ℕ ↦ (km n : ℝ) / n)
      atTop (𝓝 D) := by
    simpa [km] using ceilLinear_ratio_tendsto hD
  have hrootsLim : Tendsto (fun n : ℕ ↦ (roots n : ℝ) / n)
      atTop (𝓝 s) := by
    have h := (ceilLinear_ratio_tendsto hs.le).add
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
    have h' : Tendsto
        (fun n : ℕ ↦ (⌈s * (n : ℝ)⌉₊ : ℝ) / n + 1 / n)
        atTop (𝓝 s) := by simpa using h
    apply h'.congr'
    filter_upwards [] with n
    simp [roots, rootCap, add_div]
  have hNLim : Tendsto (fun n : ℕ ↦ (N n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa [N] using chooseTwo_ratio_tendsto
  have hqN : ∀ᶠ n : ℕ in atTop, q n ≤ N n := by
    have hlt := hqLim.eventually_lt hNLim hAhalf
    filter_upwards [hlt, eventually_ge_atTop 1] with n hnratio hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hcast : (q n : ℝ) < N n := by
      exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).mp hnratio
    exact (Nat.cast_lt.mp hcast).le
  have hkmlo : ∀ᶠ n : ℕ in atTop, km n ≤ lo n := by
    have hlt := hkmLim.eventually_lt hloLim hDL
    filter_upwards [hlt, eventually_ge_atTop 1] with n hnratio hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hcast : (km n : ℝ) < lo n :=
      (div_lt_div_iff_of_pos_right hnpos).mp hnratio
    exact (Nat.cast_lt.mp hcast).le
  have hsumLim : Tendsto (fun n : ℕ ↦ ((hi n + roots n : ℕ) : ℝ) / n)
      atTop (𝓝 (U + s)) := by
    have h := hhiLim.add hrootsLim
    apply h.congr'
    filter_upwards [] with n
    simp [add_div]
  have hsumN : ∀ᶠ n : ℕ in atTop, hi n + roots n < n := by
    have hlt := hsumLim.eventually_lt tendsto_const_nhds hUs
    filter_upwards [hlt, eventually_ge_atTop 1] with n hnratio hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hcast : ((hi n + roots n : ℕ) : ℝ) < n := by
      have := (div_lt_iff₀ hnpos).mp hnratio
      simpa using this
    exact Nat.cast_lt.mp hcast
  have hleftLim : Tendsto
      (fun n : ℕ ↦ ((lo n - km n : ℕ) : ℝ) / n)
      atTop (𝓝 (L - D)) := by
    have h := hloLim.sub hkmLim
    apply h.congr'
    filter_upwards [hkmlo] with n hn
    rw [Nat.cast_sub hn, sub_div]
  have hrightLim : Tendsto
      (fun n : ℕ ↦ ((n - hi n - roots n : ℕ) : ℝ) / n)
      atTop (𝓝 (1 - U - s)) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hsumLim
    have h' : Tendsto (fun n : ℕ ↦ 1 - ((hi n + roots n : ℕ) : ℝ) / n)
        atTop (𝓝 (1 - U - s)) := by
      convert h using 1 <;> ring
    apply h'.congr'
    filter_upwards [hsumN, eventually_ge_atTop 1] with n hsum hn
    have hle : hi n + roots n ≤ n := hsum.le
    rw [Nat.sub_sub, Nat.cast_sub hle]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hproductLim : Tendsto
      (fun n : ℕ ↦
        (((lo n - km n) * (n - hi n - roots n) : ℕ) : ℝ) /
          (n : ℝ) ^ 2)
      atTop (𝓝 ((L - D) * (1 - U - s))) := by
    have h := hleftLim.mul hrightLim
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hrectN : ∀ᶠ n : ℕ in atTop,
      q n < (lo n - km n) * (n - hi n - roots n) := by
    have hlt := hqLim.eventually_lt hproductLim hrectangle
    filter_upwards [hlt, eventually_ge_atTop 1] with n hnratio hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hcast : (q n : ℝ) <
        ((lo n - km n) * (n - hi n - roots n) : ℕ) :=
      (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).mp hnratio
    exact Nat.cast_lt.mp hcast
  have hcenterLim : Tendsto (fun n : ℕ ↦ center n / n)
      atTop (𝓝 (2 * c * A)) := by
    have hraw' : Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / n) *
          ((q n : ℝ) / (n : ℝ) ^ 2) /
          ((N n : ℝ) / (n : ℝ) ^ 2))
        atTop (𝓝 (c * A / (1 / 2 : ℝ))) :=
      (hmLim.mul hqLim).div hNLim (by norm_num)
    have hraw'' : Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / n) *
          ((q n : ℝ) / (n : ℝ) ^ 2) /
          ((N n : ℝ) / (n : ℝ) ^ 2))
        atTop (𝓝 (2 * c * A)) := by
      convert hraw' using 1 <;> ring
    apply hraw''.congr'
    filter_upwards [hqN, eventually_ge_atTop 2] with n hqn hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hNpos : (0 : ℝ) < N n := by
      dsimp [N]
      rw [Nat.cast_pos]
      exact Nat.choose_pos hn
    simp only [center, min_eq_left hqn]
    field_simp
  let tau : ℝ := min (2 * c * A - L) (U - 2 * c * A) / 2
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hlower : L + tau < 2 * c * A := by
    have hmin := min_le_left (2 * c * A - L) (U - 2 * c * A)
    dsimp [tau]
    nlinarith
  have hupper : 2 * c * A < U - tau := by
    have hmin := min_le_right (2 * c * A - L) (U - 2 * c * A)
    dsimp [tau]
    nlinarith
  have hcenterWindow : ∀ᶠ n : ℕ in atTop,
      (L + tau) * n < center n ∧ center n < (U - tau) * n := by
    have hlo' := hcenterLim.eventually_const_lt hlower
    have hhi' := hcenterLim.eventually_lt_const hupper
    filter_upwards [hlo', hhi', eventually_ge_atTop 1] with n hlo' hhi' hn
    have hnpos : (0 : ℝ) < n := by positivity
    constructor
    · exact (lt_div_iff₀ hnpos).mp (by simpa [mul_comm] using hlo')
    · exact (div_lt_iff₀ hnpos).mp (by simpa [mul_comm] using hhi')
  have hmPos : ∀ᶠ n : ℕ in atTop, 0 < m n := by
    have h := hmLim.eventually_const_lt hc
    filter_upwards [h, eventually_ge_atTop 1] with n hratio hn
    have hnpos : (0 : ℝ) < n := by positivity
    have : (0 : ℝ) < m n := by
      rcases (div_pos_iff.mp hratio) with hpos | hneg
      · exact hpos.1
      · exact (not_lt_of_ge (Nat.cast_nonneg n) hneg.2).elim
    exact_mod_cast this
  have hmUpper : ∀ᶠ n : ℕ in atTop,
      (m n : ℝ) < (c + 1) * n := by
    have h := hmLim.eventually_lt_const (lt_add_one c)
    filter_upwards [h, eventually_ge_atTop 1] with n hratio hn
    have hnpos : (0 : ℝ) < n := by positivity
    exact (div_lt_iff₀ hnpos).mp (by simpa [mul_comm] using hratio)
  have hmN : ∀ᶠ n : ℕ in atTop, m n ≤ N n := by
    have hNquarter := hNLim.eventually_const_lt (by norm_num : (1 / 4 : ℝ) < 1 / 2)
    have hlarge : ∀ᶠ n : ℕ in atTop, 4 * (c + 1) < (n : ℝ) :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop) (eventually_gt_atTop _)
    filter_upwards [hmUpper, hNquarter, hlarge, eventually_ge_atTop 2]
      with n hmup hNq hnlarge hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hNlower : (n : ℝ) ^ 2 / 4 < N n := by
      have := (lt_div_iff₀ (sq_pos_of_pos hnpos)).mp hNq
      nlinarith
    have hmreal : (m n : ℝ) < N n := by
      nlinarith
    exact (Nat.cast_lt.mp hmreal).le
  let rate : ℕ → ℝ := fun n ↦
    (tau * (n : ℝ)) ^ 2 / (32 * (m n : ℝ))
  let tail : ℕ → ℝ := fun n ↦ 2 * Real.exp (-rate n)
  have hcoefficient : Tendsto
      (fun n : ℕ ↦ tau ^ 2 / (32 * ((m n : ℝ) / n))) atTop
      (𝓝 (tau ^ 2 / (32 * c))) := by
    exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul hmLim) (by positivity)
  have hcoefficientPos : 0 < tau ^ 2 / (32 * c) := by positivity
  have hrate : Tendsto rate atTop atTop := by
    have hraw :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).atTop_mul_pos
          hcoefficientPos hcoefficient
    apply hraw.congr'
    filter_upwards [hmPos, eventually_ge_atTop 1] with n hmpos hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hm0 : (m n : ℝ) ≠ 0 := by positivity
    simp only [rate]
    field_simp
  have htail : Tendsto tail atTop (𝓝 0) := by
    have hexp := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hrate)
    have hmul := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).mul hexp
    simpa [tail] using hmul
  have hlowerProbability : ∀ᶠ n : ℕ in atTop,
      1 - tail n ≤ fixedPathProbability c D n := by
    filter_upwards [hqN, hkmlo, hsumN, hrectN, hcenterWindow,
      hmPos, hmN, eventually_ge_atTop 2]
      with n hqn hkmn hsum hrect hwindow hmpos hmn hn
    letI : Nonempty (Erdos88.Fourier.BoolSlice (Fin (N n)) (m n)) :=
      boolSliceNonempty (by simpa using hmn)
    let X : Erdos88.Fourier.BoolSlice (Fin (N n)) (m n) → ℕ :=
      fun omega ↦ prefixWeight
        (AdaptiveTree.answerEquiv (canonicalDFSTree n) omega.1) (q n)
    let Good : Erdos88.Fourier.BoolSlice (Fin (N n)) (m n) → Prop :=
      fun omega ↦ HasLongPath n D (canonicalGraph n omega.1)
    let Bad : Erdos88.Fourier.BoolSlice (Fin (N n)) (m n) → Prop :=
      fun omega ↦ tau * n ≤ |(X omega : ℝ) - center n|
    have hpathOfWindow (omega : Erdos88.Fourier.BoolSlice (Fin (N n)) (m n))
        (hw : lo n ≤ X omega ∧ X omega ≤ hi n) : Good omega := by
      have hp := canonicalGraph_hasPath_of_prefix_window
        (n := n) (q := q n) (k := km n + 1)
        (lo := lo n) (hi := hi n) (rootCap := roots n)
        (by simpa [N] using hqn) (by omega)
        (fun r hr ↦ choose_root_le_rootCap hA.le hs.le hroot n r hr)
        hsum (by simpa using hrect) omega.1 hw.1 hw.2
      simpa [Good, HasLongPath, km] using hp
    have hfailureBad : ∀ omega, ¬Good omega → Bad omega := by
      intro omega hfailure
      have hnotWindow : ¬(lo n ≤ X omega ∧ X omega ≤ hi n) := by
        intro hw
        exact hfailure (hpathOfWindow omega hw)
      by_cases hloX : lo n ≤ X omega
      · have hhiX : hi n < X omega := by omega
        have hfloor : U * (n : ℝ) < (⌊U * (n : ℝ)⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one (U * (n : ℝ))
        have hXreal : U * (n : ℝ) < (X omega : ℝ) := by
          have hsucc : ⌊U * (n : ℝ)⌋₊ + 1 ≤ X omega := by
            dsimp [hi, upperWindow] at hhiX
            omega
          have hsuccCast : (⌊U * (n : ℝ)⌋₊ : ℝ) + 1 ≤ X omega := by
            exact_mod_cast hsucc
          linarith
        have habs : |(X omega : ℝ) - center n| =
            (X omega : ℝ) - center n := abs_of_nonneg (by
              nlinarith [hwindow.2])
        dsimp [Bad]
        rw [habs]
        nlinarith [hwindow.2]
      · have hXlo : X omega < lo n := Nat.lt_of_not_ge hloX
        have hcast : (X omega : ℝ) + 1 ≤ lo n := by exact_mod_cast hXlo
        have hceil : ((lo n : ℕ) : ℝ) < L * (n : ℝ) + 1 := by
          dsimp [lo, lowerWindow]
          exact Nat.ceil_lt_add_one (mul_nonneg hL0 (Nat.cast_nonneg n))
        have hXreal : (X omega : ℝ) < L * (n : ℝ) := by linarith
        have habs : |(X omega : ℝ) - center n| =
            center n - (X omega : ℝ) := by
          rw [abs_of_nonpos]
          · ring
          · nlinarith [hwindow.1]
        dsimp [Bad]
        rw [habs]
        nlinarith [hwindow.1]
    have hconc : Erdos88.Concentration.uniformProbability Bad ≤ tail n := by
      have h := adaptivePrefix_two_sided_probability
        (n := n) (m := m n) (q := q n) (by simpa [N] using hmn)
        hmpos (tau * n) (by positivity)
      have h' : Erdos88.Concentration.uniformProbability Bad ≤
          2 * Real.exp (-(tau * n) ^ 2 / (32 * (m n : ℝ))) := by
        simpa [Bad, X, center, N] using h
      change Erdos88.Concentration.uniformProbability Bad ≤
        2 * Real.exp (-((tau * n) ^ 2 / (32 * (m n : ℝ))))
      convert h' using 1 <;> ring
    have hfailProb :
        Erdos88.Concentration.uniformProbability (fun omega ↦ ¬Good omega) ≤
          Erdos88.Concentration.uniformProbability Bad :=
      Erdos88.Concentration.uniformProbability_mono hfailureBad
    have hgoodLower : 1 - tail n ≤
        Erdos88.Concentration.uniformProbability Good := by
      rw [uniformProbability_not] at hfailProb
      nlinarith
    simpa [fixedPathProbability, m, N, Good, hmn] using hgoodLower
  have hupperProbability : ∀ᶠ n : ℕ in atTop,
      fixedPathProbability c D n ≤ 1 :=
    Filter.Eventually.of_forall (fixedPathProbability_le_one c D)
  have hlowerLimit : Tendsto (fun n : ℕ ↦ 1 - tail n) atTop (𝓝 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub htail using 1 <;>
      ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerLimit
    tendsto_const_nhds hlowerProbability hupperProbability

/-- Every density strictly above `1/2` admits some positive certified path
fraction. -/
theorem exists_positive_WHP (c : ℝ) (hc : 1 / 2 < c) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ WHP c d := by
  let B : ℝ := (2 * c + 3) / 4
  let C : ℝ := (6 * c - 1) / 8
  let s : ℝ := (B - 1) / (16 * B * (C + 1))
  let A : ℝ := s ^ 2 / 4
  let M : ℝ := 2 * c * A
  let d : ℝ := (M - A) / 4
  let L : ℝ := (M + A) / 2
  let U : ℝ := (3 * M - A) / 2
  have hc0 : 0 < c := by linarith
  have hB : 1 < B := by
    dsimp [B]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    linarith
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsC : C * s < 1 / 16 := by
    dsimp [s]
    rw [show C * ((B - 1) / (16 * B * (C + 1))) =
      C * (B - 1) / (16 * B * (C + 1)) by ring]
    rw [div_lt_iff₀ (by positivity : 0 < 16 * B * (C + 1))]
    nlinarith
  have hsSmall : s < 1 / 16 := by
    dsimp [s]
    rw [div_lt_iff₀ (by positivity : 0 < 16 * B * (C + 1))]
    nlinarith [mul_pos (sub_pos.mpr hB) hC]
  have hA : 0 < A := by dsimp [A]; positivity
  have hAhalf : A < 1 / 2 := by
    dsimp [A]
    nlinarith [sq_nonneg (s - 1 / 16)]
  have hroot : 2 * A < s ^ 2 := by
    dsimp [A]
    nlinarith [sq_pos_of_pos hs]
  have hM : M = 2 * c * A := rfl
  have hd : 0 < d := by
    dsimp [d, M]
    nlinarith [mul_pos (sub_pos.mpr (by linarith : 1 < 2 * c)) hA]
  have hUformula : U = C * s ^ 2 := by
    dsimp [U, M, A, C]
    ring
  have hUs : U + s < 1 := by
    rw [hUformula]
    have hUsmall : C * s ^ 2 < s / 16 := by
      nlinarith [mul_pos hs (sub_pos.mpr hsC)]
    nlinarith
  have hd1 : d < 1 := by
    have hdU : d < U := by
      dsimp [d, U, M]
      nlinarith [mul_pos hc0 hA]
    nlinarith
  have hdL : d < L := by
    dsimp [d, L, M]
    nlinarith [mul_pos hc0 hA]
  have hLM : L < 2 * c * A := by
    dsimp [L, M]
    nlinarith [mul_pos (sub_pos.mpr (by linarith : 1 < 2 * c)) hA]
  have hMU : 2 * c * A < U := by
    dsimp [U, M]
    nlinarith [mul_pos (sub_pos.mpr (by linarith : 1 < 2 * c)) hA]
  have hBformula : L - d = B * A := by
    dsimp [L, d, M, B]
    ring
  have hmargin : 1 < B * (1 - U - s) := by
    have hratio : s < (B - 1) / B := by
      dsimp [s]
      rw [div_lt_div_iff₀ (by positivity : 0 < 16 * B * (C + 1))
        (by positivity : 0 < B)]
      nlinarith [mul_pos (sub_pos.mpr hB) hC]
    have hUsmall : U + s < (B - 1) / B := by
      rw [hUformula]
      have hquad : C * s ^ 2 < s / 16 := by
        nlinarith [mul_pos hs (sub_pos.mpr hsC)]
      have hscaled : 17 * s / 16 < (B - 1) / B := by
        dsimp [s]
        rw [show 17 * ((B - 1) / (16 * B * (C + 1))) / 16 =
          17 * (B - 1) / (16 * (16 * B * (C + 1))) by
            field_simp
            <;> ring]
        rw [div_lt_div_iff₀
          (by positivity : 0 < 16 * (16 * B * (C + 1)))
          (by positivity : 0 < B)]
        have hfac : 0 < (B - 1) * B := by positivity
        have hgap : 0 < 256 * (C + 1) - 17 := by nlinarith
        nlinarith [mul_pos hfac hgap]
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hUsmall (by positivity : 0 < B)
    have hmul' : B * (U + s) < B - 1 := by
      calc
        B * (U + s) < B * ((B - 1) / B) := hmul
        _ = B - 1 := by field_simp
    nlinarith
  have hrect : A < (L - d) * (1 - U - s) := by
    rw [hBformula]
    nlinarith [mul_pos hA (sub_pos.mpr hmargin)]
  refine ⟨d, hd, hd1, ?_⟩
  exact WHP_of_DFS_parameters hc0 hA hAhalf hs hroot hd.le hdL hLM hMU
    hUs hrect

theorem WHP_zero (c : ℝ) (hc : 1 / 2 < c) : WHP c 0 := by
  obtain ⟨d, hd, hd1, hwhp⟩ := exists_positive_WHP c hc
  exact hwhp.mono_fraction hd.le

/-- Uniformly for all sufficiently large densities, the certified path
fraction is at least `1 - eps`. -/
theorem dense_WHP (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ C : ℝ, ∀ c : ℝ, C ≤ c → WHP c (1 - eps) := by
  let D : ℝ := 1 - eps
  let s : ℝ := eps / 8
  let M : ℝ := 1 - eps / 2
  let L : ℝ := 1 - 3 * eps / 4
  let U : ℝ := 1 - eps / 4
  let C : ℝ := max 1 (65 * M / eps ^ 2)
  refine ⟨C, ?_⟩
  intro c hc
  let A : ℝ := M / (2 * c)
  have hM : 0 < M := by dsimp [M]; linarith
  have hM1 : M < 1 := by dsimp [M]; linarith
  have hC1 : 1 ≤ C := le_max_left _ _
  have hc1 : 1 ≤ c := hC1.trans hc
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hCbig : 65 * M / eps ^ 2 ≤ C := le_max_right _ _
  have hcbig : 65 * M / eps ^ 2 ≤ c := hCbig.trans hc
  have hA : 0 < A := by dsimp [A]; positivity
  have hAhalf : A < 1 / 2 := by
    dsimp [A]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * c)]
    nlinarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hroot : 2 * A < s ^ 2 := by
    have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
    have hscaled := (div_le_iff₀ heps2).mp hcbig
    dsimp [A, s]
    rw [show 2 * (M / (2 * c)) = M / c by field_simp]
    rw [div_lt_iff₀ hc0]
    nlinarith
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hDL : D < L := by dsimp [D, L]; linarith
  have hmean : 2 * c * A = M := by
    dsimp [A]
    field_simp
  have hLM : L < 2 * c * A := by rw [hmean]; dsimp [L, M]; linarith
  have hMU : 2 * c * A < U := by rw [hmean]; dsimp [M, U]; linarith
  have hUs : U + s < 1 := by dsimp [U, s]; linarith
  have hrectValue : (L - D) * (1 - U - s) = eps ^ 2 / 32 := by
    dsimp [L, D, U, s]
    ring
  have hrect : A < (L - D) * (1 - U - s) := by
    rw [hrectValue]
    have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
    have hscaled := (div_le_iff₀ heps2).mp hcbig
    dsimp [A]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * c)]
    nlinarith
  exact WHP_of_DFS_parameters hc0 hA hAhalf hs hroot hD hDL hLM hMU
    hUs hrect

/-! ## Assemble one function with both endpoint limits -/

def denseFraction (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 2)

theorem denseFraction_nonneg (k : ℕ) : 0 ≤ denseFraction k := by
  unfold denseFraction
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpos : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  rw [sub_nonneg, div_le_one hpos]
  linarith

theorem denseFraction_lt_one (k : ℕ) : denseFraction k < 1 := by
  unfold denseFraction
  have : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  linarith

private theorem exists_denseThreshold (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ (k : ℝ) ≤ C ∧
      ∀ c : ℝ, C ≤ c → WHP c (denseFraction k) := by
  let eps : ℝ := 1 / ((k : ℝ) + 2)
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps < 1 := by
    dsimp [eps]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [div_lt_one (by linarith : (0 : ℝ) < (k : ℝ) + 2)]
    linarith
  obtain ⟨C, hC⟩ := dense_WHP eps heps heps1
  let T : ℝ := max (k : ℝ) (max 1 C)
  refine ⟨T, ?_, ?_, ?_⟩
  · exact (le_max_left 1 C).trans (le_max_right (k : ℝ) (max 1 C))
  · exact le_max_left _ _
  · intro c hc
    have hTC : C ≤ T := (le_max_right 1 C).trans
      (le_max_right (k : ℝ) (max 1 C))
    simpa [denseFraction, eps] using hC c (hTC.trans hc)

noncomputable def denseThreshold (k : ℕ) : ℝ :=
  Classical.choose (exists_denseThreshold k)

theorem denseThreshold_one_le (k : ℕ) : 1 ≤ denseThreshold k :=
  (Classical.choose_spec (exists_denseThreshold k)).1

theorem denseThreshold_index_le (k : ℕ) :
    (k : ℝ) ≤ denseThreshold k :=
  (Classical.choose_spec (exists_denseThreshold k)).2.1

theorem denseThreshold_WHP (k : ℕ) (c : ℝ)
    (hc : denseThreshold k ≤ c) : WHP c (denseFraction k) :=
  (Classical.choose_spec (exists_denseThreshold k)).2.2 c hc

noncomputable def denseLevel (c : Density) : ℕ :=
  Nat.findGreatest (fun k ↦ denseThreshold k ≤ (c : ℝ)) ⌊(c : ℝ)⌋₊

noncomputable def densePart (c : Density) : ℝ :=
  if denseThreshold (denseLevel c) ≤ (c : ℝ) then
    denseFraction (denseLevel c) else 0

theorem densePart_nonneg (c : Density) : 0 ≤ densePart c := by
  classical
  simp only [densePart]
  split_ifs
  · exact denseFraction_nonneg _
  · exact le_rfl

theorem densePart_lt_one (c : Density) : densePart c < 1 := by
  classical
  simp only [densePart]
  split_ifs
  · exact denseFraction_lt_one _
  · norm_num

theorem densePart_WHP (c : Density) : WHP (c : ℝ) (densePart c) := by
  classical
  simp only [densePart]
  split_ifs with h
  · exact denseThreshold_WHP _ _ h
  · exact WHP_zero c c.property

private theorem coe_density_tendsto_atTop :
    Tendsto ((↑) : Density → ℝ) atTop atTop := by
  show Filter.map ((↑) : Density → ℝ) atTop ≤ atTop
  rw [Filter.map_val_Ioi_atTop]

theorem denseLevel_tendsto_atTop : Tendsto denseLevel atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro K
  have hcoe := coe_density_tendsto_atTop
  have hevT : ∀ᶠ c : Density in atTop, denseThreshold K ≤ (c : ℝ) :=
    hcoe (eventually_ge_atTop (denseThreshold K))
  have hevK : ∀ᶠ c : Density in atTop, (K : ℝ) ≤ (c : ℝ) :=
    hcoe (eventually_ge_atTop (K : ℝ))
  filter_upwards [hevT, hevK] with c hcT hcK
  apply Nat.le_findGreatest
  · exact Nat.le_floor hcK
  · exact hcT

theorem densePart_tendsto_one : Tendsto densePart atTop (𝓝 1) := by
  have hlevel := denseLevel_tendsto_atTop
  have hlevelSucc : Tendsto (fun c : Density ↦ denseLevel c + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun c ↦ Nat.le_add_right _ 1) hlevel
  have honeDiv : Tendsto
      (fun c : Density ↦ 1 / (((denseLevel c : ℕ) : ℝ) + 2))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hlevelSucc
    apply h.congr'
    filter_upwards [] with c
    norm_num [Nat.cast_add]
    ring
  have hfraction : Tendsto (fun c : Density ↦ denseFraction (denseLevel c))
      atTop (𝓝 1) := by
    simpa [denseFraction] using
      (tendsto_const_nhds : Tendsto (fun _ : Density ↦ (1 : ℝ)) atTop (𝓝 1)).sub
        honeDiv
  have hcoe := coe_density_tendsto_atTop
  have heasible : ∀ᶠ c : Density in atTop,
      denseThreshold (denseLevel c) ≤ (c : ℝ) := by
    have hev0 : ∀ᶠ c : Density in atTop, denseThreshold 0 ≤ (c : ℝ) :=
      hcoe (eventually_ge_atTop (denseThreshold 0))
    filter_upwards [hev0] with c hc0
    have hzeroFloor : 0 ≤ ⌊(c : ℝ)⌋₊ := Nat.zero_le _
    have hspec : denseThreshold (denseLevel c) ≤ (c : ℝ) := by
      change denseThreshold
        (Nat.findGreatest (fun k ↦ denseThreshold k ≤ (c : ℝ)) ⌊(c : ℝ)⌋₊) ≤ (c : ℝ)
      exact Nat.findGreatest_spec
        (P := fun k ↦ denseThreshold k ≤ (c : ℝ))
        (m := 0) (n := ⌊(c : ℝ)⌋₊) hzeroFloor hc0
    exact hspec
  apply hfraction.congr'
  filter_upwards [heasible] with c hc
  simp [densePart, hc]

noncomputable def baseFraction (c : Density) : ℝ :=
  Classical.choose (exists_positive_WHP (c : ℝ) c.property)

theorem baseFraction_pos (c : Density) : 0 < baseFraction c :=
  (Classical.choose_spec (exists_positive_WHP (c : ℝ) c.property)).1

theorem baseFraction_lt_one (c : Density) : baseFraction c < 1 :=
  (Classical.choose_spec (exists_positive_WHP (c : ℝ) c.property)).2.1

theorem baseFraction_WHP (c : Density) : WHP (c : ℝ) (baseFraction c) :=
  (Classical.choose_spec (exists_positive_WHP (c : ℝ) c.property)).2.2

noncomputable def smallPart (c : Density) : ℝ :=
  min (baseFraction c) ((c : ℝ) - 1 / 2)

theorem smallPart_pos (c : Density) : 0 < smallPart c := by
  exact lt_min (baseFraction_pos c) (sub_pos.mpr c.property)

theorem smallPart_lt_one (c : Density) : smallPart c < 1 :=
  (min_le_left _ _).trans_lt (baseFraction_lt_one c)

theorem smallPart_WHP (c : Density) : WHP (c : ℝ) (smallPart c) :=
  (baseFraction_WHP c).mono_fraction (min_le_left _ _)

noncomputable def erdos900Fraction (c : Density) : ℝ :=
  max (smallPart c) (densePart c)

theorem erdos900Fraction_pos (c : Density) : 0 < erdos900Fraction c :=
  (smallPart_pos c).trans_le (le_max_left _ _)

theorem erdos900Fraction_lt_one (c : Density) : erdos900Fraction c < 1 := by
  unfold erdos900Fraction
  rw [max_lt_iff]
  exact ⟨smallPart_lt_one c, densePart_lt_one c⟩

theorem erdos900Fraction_WHP (c : Density) :
    WHP (c : ℝ) (erdos900Fraction c) := by
  unfold erdos900Fraction
  rcases le_total (smallPart c) (densePart c) with h | h
  · rw [max_eq_right h]
    exact densePart_WHP c
  · rw [max_eq_left h]
    exact smallPart_WHP c

theorem erdos900Fraction_tendsto_atTop :
    Tendsto erdos900Fraction atTop (𝓝 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    densePart_tendsto_one tendsto_const_nhds
    (fun c ↦ le_max_right (smallPart c) (densePart c))
    (fun c ↦ (erdos900Fraction_lt_one c).le)

private theorem coe_density_tendsto_atHalf :
    Tendsto ((↑) : Density → ℝ) densityAtHalf (𝓝 (1 / 2 : ℝ)) := by
  unfold densityAtHalf
  show Filter.map ((↑) : Density → ℝ)
      (Filter.comap ((↑) : Density → ℝ) (𝓝[>] (1 / 2 : ℝ))) ≤
    𝓝 (1 / 2 : ℝ)
  exact Filter.map_comap_le.trans nhdsWithin_le_nhds

theorem erdos900Fraction_tendsto_atHalf :
    Tendsto erdos900Fraction densityAtHalf (𝓝 0) := by
  have hnear : ∀ᶠ c : Density in densityAtHalf, (c : ℝ) < 1 := by
    unfold densityAtHalf
    refine mem_of_superset
      (Filter.preimage_mem_comap
        (Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1))) ?_
    intro c hc
    exact hc.2
  have hdenseZero : ∀ᶠ c : Density in densityAtHalf, densePart c = 0 := by
    filter_upwards [hnear] with c hc
    simp only [densePart]
    rw [if_neg]
    exact not_le.mpr (hc.trans_le (denseThreshold_one_le _))
  have heqSmall : ∀ᶠ c : Density in densityAtHalf,
      erdos900Fraction c = smallPart c := by
    filter_upwards [hdenseZero] with c hc
    simp [erdos900Fraction, hc, (smallPart_pos c).le]
  have hcoe := coe_density_tendsto_atHalf
  have hdiff : Tendsto (fun c : Density ↦ (c : ℝ) - 1 / 2)
      densityAtHalf (𝓝 0) := by
    simpa using hcoe.sub
      (tendsto_const_nhds : Tendsto (fun _ : Density ↦ (1 / 2 : ℝ))
        densityAtHalf (𝓝 (1 / 2 : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Density ↦ (0 : ℝ))
      densityAtHalf (𝓝 0)) hdiff
  · exact Eventually.of_forall fun c ↦ (erdos900Fraction_pos c).le
  · filter_upwards [heqSmall] with c hc
    rw [hc]
    exact min_le_right _ _

/-- Erdős Problem 900, in the exact uniform `floor(c*n)`-edge model.

The value `f c` is strictly between zero and one, approaches zero as the
density approaches the critical value `1/2` from above, approaches one as the
density tends to infinity, and is a valid asymptotic lower bound for the
number of edges in a simple path, divided by `n`. -/
theorem erdos_900 :
    ∃ f : Density → ℝ,
      (∀ c, 0 < f c ∧ f c < 1) ∧
      Tendsto f densityAtHalf (𝓝 0) ∧
      Tendsto f atTop (𝓝 1) ∧
      ∀ c : Density, WHP (c : ℝ) (f c) := by
  exact ⟨erdos900Fraction,
    fun c ↦ ⟨erdos900Fraction_pos c, erdos900Fraction_lt_one c⟩,
    erdos900Fraction_tendsto_atHalf,
    erdos900Fraction_tendsto_atTop,
    erdos900Fraction_WHP⟩

end Erdos900

#print axioms Erdos900.erdos_900
