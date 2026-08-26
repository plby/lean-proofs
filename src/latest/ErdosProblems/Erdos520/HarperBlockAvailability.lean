import ErdosProblems.Erdos520.HarperBlockSchedule
import ErdosProblems.Erdos520.ThinSchedule

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Elementary availability of scheduled Harper blocks below a cutoff

The scheduled endpoint is

`harperBlockEndpoint j = 2 ^ (16 * 2^j) = 2 ^ (2^(j+4))`.

Accordingly, the natural amount of available block-index space below `y` is
the twice-iterated base-two logarithm `log₂(log₂ y)`.  The economical schedule
starts at a fixed analytic threshold plus a caller-supplied height shift and
uses every remaining index after the exact four-unit endpoint overhead.  The
older quarter--quarter--half allocation is retained as a convenient API for
callers which genuinely need a cutoff-dependent starting index.

Only elementary natural-logarithm and real-logarithm facts are used here.
-/

/-- Twice-iterated integer base-two logarithm of the ambient cutoff. -/
def harperAvailableLogScale (y : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 y)

/-- A base starting block which itself tends to infinity with the cutoff. -/
def harperAvailableBaseStart (y : ℕ) : ℕ :=
  harperAvailableLogScale y / 4

/-- Start after allowing a caller-supplied shift, for example one depending
logarithmically on the height of a vertical band. -/
def harperAvailableShiftedStart (y h : ℕ) : ℕ :=
  harperAvailableBaseStart y + h

/-- Canonical logarithmic shift for a vertical height parameter. -/
def harperHeightLogShift (height : ℕ) : ℕ :=
  Nat.log 2 (height + 1)

/-- A path using approximately half of the available block-index scale.  The
subtraction by four is the exact slack needed by the factor `16` in the
scheduled endpoint. -/
def harperAvailablePathLength (y : ℕ) : ℕ :=
  harperAvailableLogScale y / 2 - 4

/-- Economical start: a fixed analytic threshold `J`, followed only by the
caller-supplied shift `h`. -/
def harperEconomicalStart (J h : ℕ) : ℕ :=
  J + h

/-- The economical path uses every block-index unit remaining after its start
and the exact four-unit endpoint overhead. -/
def harperEconomicalPathLength (y J h : ℕ) : ℕ :=
  harperAvailableLogScale y - (harperEconomicalStart J h + 4)

/-! ## Endpoint availability from an abstract fit inequality -/

/-- If an index plus the four-unit endpoint overhead fits inside the
twice-iterated integer logarithm, its scheduled endpoint is below `y`. -/
theorem harperBlockEndpoint_le_of_add_four_le_available
    {y j : ℕ} (hy : y ≠ 0)
    (hfit : j + 4 ≤ harperAvailableLogScale y) :
    harperBlockEndpoint j ≤ y := by
  let l : ℕ := Nat.log 2 y
  let a : ℕ := harperAvailableLogScale y
  have ha4 : 4 ≤ a := by omega
  have hlne : l ≠ 0 := by
    intro hl
    have ha0 : a = 0 := by simp [a, harperAvailableLogScale, l, hl]
    omega
  have hpowIndex : 2 ^ (j + 4) ≤ l := by
    have hmono : 2 ^ (j + 4) ≤ 2 ^ a :=
      Nat.pow_le_pow_right (by norm_num) hfit
    exact hmono.trans (Nat.pow_log_le_self 2 hlne)
  have houter : 2 ^ l ≤ y := Nat.pow_log_le_self 2 hy
  have hexponent : 16 * 2 ^ j = 2 ^ (j + 4) := by
    rw [pow_add]
    norm_num [Nat.mul_comm]
  unfold harperBlockEndpoint
  rw [hexponent]
  exact (Nat.pow_le_pow_right (by norm_num) hpowIndex).trans houter

/-- Conversely, an available scheduled endpoint forces the corresponding
four-unit index inequality. -/
theorem add_four_le_harperAvailableLogScale_of_blockEndpoint_le
    {y j : ℕ} (hendpoint : harperBlockEndpoint j ≤ y) :
    j + 4 ≤ harperAvailableLogScale y := by
  have hfirst : Nat.log 2 (harperBlockEndpoint j) ≤ Nat.log 2 y :=
    Nat.log_mono_right hendpoint
  have hsecond :
      Nat.log 2 (Nat.log 2 (harperBlockEndpoint j)) ≤
        Nat.log 2 (Nat.log 2 y) :=
    Nat.log_mono_right hfirst
  have hexponent : 16 * 2 ^ j = 2 ^ (j + 4) := by
    rw [pow_add]
    norm_num [Nat.mul_comm]
  unfold harperBlockEndpoint at hsecond
  rw [Nat.log_pow (by norm_num : 1 < 2), hexponent,
    Nat.log_pow (by norm_num : 1 < 2)] at hsecond
  exact hsecond

/-- Exact elementary characterization of which scheduled endpoints fit. -/
theorem harperBlockEndpoint_le_iff_add_four_le_available
    {y j : ℕ} (hy : y ≠ 0) :
    harperBlockEndpoint j ≤ y ↔
      j + 4 ≤ harperAvailableLogScale y := by
  exact ⟨add_four_le_harperAvailableLogScale_of_blockEndpoint_le,
    harperBlockEndpoint_le_of_add_four_le_available hy⟩

/-- Reusable shifted-path form: every endpoint through `start + path` is
available whenever `start + path + 4` fits in the integer log scale. -/
theorem harperBlockEndpoint_add_le_of_shift_path_fits
    {y start path : ℕ} (hy : y ≠ 0)
    (hfit : start + path + 4 ≤ harperAvailableLogScale y)
    {m : ℕ} (hm : m ≤ path) :
    harperBlockEndpoint (start + m) ≤ y := by
  apply harperBlockEndpoint_le_of_add_four_le_available hy
  omega

/-- The same fit theorem in the exact form needed for each block of a
length-`path` walk: the upper endpoint of block `i` is available. -/
theorem harperBlockEndpoint_add_succ_le_of_shift_path_fits
    {y start path : ℕ} (hy : y ≠ 0)
    (hfit : start + path + 4 ≤ harperAvailableLogScale y)
    {i : ℕ} (hi : i < path) :
    harperBlockEndpoint (start + i + 1) ≤ y := by
  rw [show start + i + 1 = start + (i + 1) by omega]
  exact harperBlockEndpoint_add_le_of_shift_path_fits hy hfit (by omega)

/-! ## Economical fixed-threshold allocation -/

/-- Once the economical start and endpoint overhead fit, the path uses the
available index scale exactly: there is no fractional-scale loss. -/
theorem harperEconomicalStart_add_path_add_four_eq
    {y J h : ℕ}
    (hfit : harperEconomicalStart J h + 4 ≤
      harperAvailableLogScale y) :
    harperEconomicalStart J h + harperEconomicalPathLength y J h + 4 =
      harperAvailableLogScale y := by
  unfold harperEconomicalPathLength
  omega

/-- Every endpoint along the full economical path, including its final
endpoint, lies below the ambient cutoff. -/
theorem harperBlockEndpoint_economicalStart_add_le
    {y J h : ℕ} (hy : y ≠ 0)
    (hfit : harperEconomicalStart J h + 4 ≤
      harperAvailableLogScale y)
    {m : ℕ} (hm : m ≤ harperEconomicalPathLength y J h) :
    harperBlockEndpoint (harperEconomicalStart J h + m) ≤ y := by
  apply harperBlockEndpoint_add_le_of_shift_path_fits hy
    (le_of_eq (harperEconomicalStart_add_path_add_four_eq hfit))
  exact hm

/-- Availability of every complete block in the economical path. -/
theorem harperBlockEndpoint_economicalStart_add_succ_le
    {y J h : ℕ} (hy : y ≠ 0)
    (hfit : harperEconomicalStart J h + 4 ≤
      harperAvailableLogScale y)
    {i : ℕ} (hi : i < harperEconomicalPathLength y J h) :
    harperBlockEndpoint (harperEconomicalStart J h + i + 1) ≤ y := by
  apply harperBlockEndpoint_add_succ_le_of_shift_path_fits hy
    (le_of_eq (harperEconomicalStart_add_path_add_four_eq hfit))
  exact hi

/-- The economical path is nonempty as soon as one further index beyond the
start and endpoint overhead is available. -/
theorem harperEconomicalPathLength_pos
    {y J h : ℕ}
    (hroom : J + h + 5 ≤ harperAvailableLogScale y) :
    0 < harperEconomicalPathLength y J h := by
  unfold harperEconomicalPathLength harperEconomicalStart
  omega

/-- If the analytic threshold and height shift together use at most half of
the available scale, the economical path retains at least half of that scale,
up to the unavoidable four-unit endpoint overhead. -/
theorem harperAvailableLogScale_div_two_sub_four_le_economicalPathLength
    {y J h : ℕ}
    (hhalf : J + h ≤ harperAvailableLogScale y / 2) :
    harperAvailableLogScale y / 2 - 4 ≤
      harperEconomicalPathLength y J h := by
  unfold harperEconomicalPathLength harperEconomicalStart
  omega

/-- Multiplication-free reformulation of the preceding half-scale bound,
including the harmless parity slack from natural-number division. -/
theorem harperAvailableLogScale_le_two_mul_economicalPathLength_add_eight
    {y J h : ℕ}
    (hhalf : J + h ≤ harperAvailableLogScale y / 2) :
    harperAvailableLogScale y ≤
      2 * harperEconomicalPathLength y J h + 8 := by
  unfold harperEconomicalPathLength harperEconomicalStart
  omega

/-! ## Concrete quarter--quarter--half allocation -/

/-- If the extra shift uses at most one quarter of the available scale, the
shifted start and the chosen path leave the exact four-unit endpoint slack. -/
theorem harperAvailableShiftedStart_add_path_add_four_le
    {y h : ℕ} (havail : 16 ≤ harperAvailableLogScale y)
    (hh : h ≤ harperAvailableLogScale y / 4) :
    harperAvailableShiftedStart y h +
        harperAvailablePathLength y + 4 ≤
      harperAvailableLogScale y := by
  unfold harperAvailableShiftedStart harperAvailableBaseStart
    harperAvailablePathLength
  omega

/-- The base start is beyond any fixed analytic threshold `J` as soon as
four copies of `J` fit in the available scale. -/
theorem le_harperAvailableBaseStart_of_four_mul_le
    {y J : ℕ} (hJ : 4 * J ≤ harperAvailableLogScale y) :
    J ≤ harperAvailableBaseStart y := by
  unfold harperAvailableBaseStart
  omega

/-- Every endpoint selected by the concrete shifted schedule lies below the
ambient cutoff. -/
theorem harperBlockEndpoint_shiftedStart_add_le
    {y h : ℕ} (hy : y ≠ 0)
    (havail : 16 ≤ harperAvailableLogScale y)
    (hh : h ≤ harperAvailableLogScale y / 4)
    {m : ℕ} (hm : m ≤ harperAvailablePathLength y) :
    harperBlockEndpoint (harperAvailableShiftedStart y h + m) ≤ y := by
  exact harperBlockEndpoint_add_le_of_shift_path_fits hy
    (harperAvailableShiftedStart_add_path_add_four_le havail hh) hm

/-- Every complete block of the concrete path lies below the ambient cutoff. -/
theorem harperBlockEndpoint_shiftedStart_add_succ_le
    {y h : ℕ} (hy : y ≠ 0)
    (havail : 16 ≤ harperAvailableLogScale y)
    (hh : h ≤ harperAvailableLogScale y / 4)
    {i : ℕ} (hi : i < harperAvailablePathLength y) :
    harperBlockEndpoint (harperAvailableShiftedStart y h + i + 1) ≤ y := by
  exact harperBlockEndpoint_add_succ_le_of_shift_path_fits hy
    (harperAvailableShiftedStart_add_path_add_four_le havail hh) hi

/-- Concrete logarithmic-height shift.  The single displayed hypothesis is
exactly the statement that this `O(log height)` shift fits in its reserved
quarter of the block-index scale. -/
theorem harperBlockEndpoint_heightShiftedStart_add_succ_le
    {y height : ℕ} (hy : y ≠ 0)
    (havail : 16 ≤ harperAvailableLogScale y)
    (hheight : 4 * harperHeightLogShift height ≤
      harperAvailableLogScale y)
    {i : ℕ} (hi : i < harperAvailablePathLength y) :
    harperBlockEndpoint
        (harperAvailableShiftedStart y (harperHeightLogShift height) +
          i + 1) ≤ y := by
  apply harperBlockEndpoint_shiftedStart_add_succ_le hy havail
  · omega
  · exact hi

/-- A completely explicit sufficient lower cutoff for the concrete schedule
hypothesis `16 <= availableLogScale`. -/
theorem sixteen_le_harperAvailableLogScale_of_endpoint_twelve_le
    {y : ℕ} (hy : harperBlockEndpoint 12 ≤ y) :
    16 ≤ harperAvailableLogScale y := by
  have := add_four_le_harperAvailableLogScale_of_blockEndpoint_le hy
  norm_num at this ⊢
  exact this

/-! ## Comparison with the real `log log` scale -/

/-- The real log-log scale is at most the twice-iterated integer base-two
logarithm plus one.  The mild lower hypothesis is far weaker than the one
used by the concrete schedule below. -/
theorem logLogNat_le_harperAvailableLogScale_add_one
    {y : ℕ} (havail : 1 ≤ harperAvailableLogScale y) :
    logLogNat y ≤ (harperAvailableLogScale y : ℝ) + 1 := by
  let l : ℕ := Nat.log 2 y
  let a : ℕ := harperAvailableLogScale y
  have hlne : l ≠ 0 := by
    intro hl
    have ha0 : a = 0 := by simp [a, harperAvailableLogScale, l, hl]
    omega
  have hyne : y ≠ 0 := by
    intro hy
    have hl0 : l = 0 := by simp [l, hy]
    exact hlne hl0
  have hlogY := (Nat.log_eq_iff
    (b := 2) (m := l) (n := y)
    (Or.inr ⟨by norm_num, hyne⟩)).mp rfl
  have hlogL := (Nat.log_eq_iff
    (b := 2) (m := a) (n := l)
    (Or.inr ⟨by norm_num, hlne⟩)).mp (by
      rfl)
  have hyone : 1 < y := by
    have hlpos : 0 < l := Nat.pos_of_ne_zero hlne
    exact (Nat.log_pos_iff.mp hlpos).1
  have hlogyPos : 0 < Real.log (y : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hyone)
  have hlonePos : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by positivity
  have haPowPos : (0 : ℝ) < (2 : ℝ) ^ (a + 1) := by positivity
  have hyCast : (y : ℝ) < (2 : ℝ) ^ (l + 1) := by
    exact_mod_cast hlogY.2
  have hlogy : Real.log (y : ℝ) < (l + 1 : ℕ) := by
    have hlogPow :
        Real.log (y : ℝ) < Real.log ((2 : ℝ) ^ (l + 1)) :=
      Real.strictMonoOn_log
        (show (y : ℝ) ∈ Set.Ioi 0 by
          rw [Set.mem_Ioi]
          positivity)
        (show (2 : ℝ) ^ (l + 1) ∈ Set.Ioi 0 by
          rw [Set.mem_Ioi]
          positivity)
        hyCast
    rw [Real.log_pow] at hlogPow
    have hfactor : ((l + 1 : ℕ) : ℝ) * Real.log 2 < (l + 1 : ℕ) := by
      have hlogTwo : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      have hlpos : (0 : ℝ) < (l + 1 : ℕ) := by positivity
      nlinarith
    exact hlogPow.trans hfactor
  have hsecond :
      Real.log (Real.log (y : ℝ)) < Real.log ((l + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log
      (show Real.log (y : ℝ) ∈ Set.Ioi 0 by
        exact hlogyPos)
      (show ((l + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        exact hlonePos)
      hlogy
  have hlSucc : l + 1 ≤ 2 ^ (a + 1) := by omega
  have hlSuccCast : ((l + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (a + 1) := by
    exact_mod_cast hlSucc
  have hlogThird :
      Real.log ((l + 1 : ℕ) : ℝ) ≤
        Real.log ((2 : ℝ) ^ (a + 1)) :=
    Real.strictMonoOn_log.monotoneOn
      (show ((l + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by exact hlonePos)
      (show (2 : ℝ) ^ (a + 1) ∈ Set.Ioi 0 by exact haPowPos)
      hlSuccCast
  rw [Real.log_pow] at hlogThird
  have hlast : ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤ (a : ℝ) + 1 := by
    have hlogTwo : Real.log 2 ≤ 1 :=
      (Real.log_two_lt_d9.trans (by norm_num)).le
    have hnonneg : (0 : ℝ) ≤ (a + 1 : ℕ) := by positivity
    norm_num at hnonneg ⊢
    nlinarith
  unfold logLogNat
  change Real.log (Real.log (y : ℝ)) ≤ (a : ℝ) + 1
  exact hsecond.le.trans (hlogThird.trans hlast)

/-- The economical path loses only the fixed analytic start, the height
shift, and an absolute constant from the full real log-log scale. -/
theorem one_add_logLogNat_le_economicalPathLength_add_start_add_six
    {y J h : ℕ}
    (hfit : J + h + 4 ≤ harperAvailableLogScale y) :
    1 + logLogNat y ≤
      (harperEconomicalPathLength y J h : ℝ) +
        ((J + h : ℕ) : ℝ) + 6 := by
  have hlog := logLogNat_le_harperAvailableLogScale_add_one
    (show 1 ≤ harperAvailableLogScale y by omega)
  have hfit' : harperEconomicalStart J h + 4 ≤
      harperAvailableLogScale y := by
    simpa [harperEconomicalStart] using! hfit
  have hexact := harperEconomicalStart_add_path_add_four_eq hfit'
  have hnat : harperAvailableLogScale y =
      harperEconomicalPathLength y J h + (J + h) + 4 := by
    unfold harperEconomicalStart at hexact
    omega
  have hnatR : (harperAvailableLogScale y : ℝ) =
      (harperEconomicalPathLength y J h : ℝ) +
        ((J + h : ℕ) : ℝ) + 4 := by
    exact_mod_cast hnat
  linarith

/-- In the useful regime where the fixed start and shift consume at most
half of the available integer scale, the economical path itself controls the
whole real log-log scale up to an absolute additive constant. -/
theorem one_add_logLogNat_le_two_mul_economicalPathLength_add_ten
    {y J h : ℕ} (havail : 1 ≤ harperAvailableLogScale y)
    (hhalf : J + h ≤ harperAvailableLogScale y / 2) :
    1 + logLogNat y ≤
      2 * (harperEconomicalPathLength y J h : ℝ) + 10 := by
  have hlog := logLogNat_le_harperAvailableLogScale_add_one havail
  have hscale :=
    harperAvailableLogScale_le_two_mul_economicalPathLength_add_eight hhalf
  have hscaleR : (harperAvailableLogScale y : ℝ) ≤
      2 * (harperEconomicalPathLength y J h : ℝ) + 8 := by
    exact_mod_cast hscale
  linarith

/-- Explicit lower comparability of the concrete path length with the real
log-log scale.  Equivalently, the path length is at least half of
`1 + logLogNat y`, up to the additive constant `11/2`. -/
theorem one_add_logLogNat_le_two_mul_harperAvailablePathLength_add_eleven
    {y : ℕ} (havail : 16 ≤ harperAvailableLogScale y) :
    1 + logLogNat y ≤
      2 * (harperAvailablePathLength y : ℝ) + 11 := by
  have hlog := logLogNat_le_harperAvailableLogScale_add_one
    (show 1 ≤ harperAvailableLogScale y by omega)
  have hhalf : harperAvailableLogScale y ≤
      2 * (harperAvailableLogScale y / 2) + 1 := by omega
  have hsub : harperAvailableLogScale y / 2 =
      harperAvailablePathLength y + 4 := by
    unfold harperAvailablePathLength
    omega
  have hnat : harperAvailableLogScale y ≤
      2 * harperAvailablePathLength y + 9 := by omega
  have hnatR : (harperAvailableLogScale y : ℝ) ≤
      2 * (harperAvailablePathLength y : ℝ) + 9 := by
    exact_mod_cast hnat
  linarith

/-- The concrete path is nonempty at every cutoff satisfying the advertised
availability threshold. -/
theorem harperAvailablePathLength_pos
    {y : ℕ} (havail : 16 ≤ harperAvailableLogScale y) :
    0 < harperAvailablePathLength y := by
  unfold harperAvailablePathLength
  omega

end Problem520
end Erdos
